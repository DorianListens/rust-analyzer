use std::iter;

use hir::{HirDisplay, Semantics};
use ide_db::{
    assists::{AssistId, AssistKind},
    defs::Definition,
    search::FileReference,
    source_change::SourceChangeBuilder,
    RootDatabase,
};
use syntax::{
    algo::find_node_at_range,
    ast::{self, make, HasArgList},
    AstNode, SyntaxKind, SyntaxNode, TextRange,
};

use crate::{
    assist_context::{AssistContext, Assists},
    utils::suggest_name,
};

use super::extract_variable::expr_to_extract;

// Assist: introduce_parameter
//
// Introduce a new parameter to a function, using the selected value
// at all callsites.
//
// ```
// fn main() {
//   example_function();
// }
//
// fn example_function() {
//     let n = $01$0;
//     let m = n + 2;
// }
// ```
// ->
// ```
// fn main() {
//   example_function(1);
// }
//
// fn example_function(n: i32) {
//     let m = n + 2;
// }
// ```
pub(crate) fn introduce_parameter(acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()> {
    let new_param = NewParameter::from_ctx(ctx)?;

    let fn_ = new_param.parent_fn()?;
    let fn_def = Definition::Function(ctx.sema.to_def(&fn_)?);

    if within_trait_impl(&fn_) {
        cov_mark::hit!(test_not_applicable_in_trait_impl);
        return None;
    }

    let target = ctx.covering_element().text_range();
    acc.add(
        AssistId("introduce_parameter", AssistKind::RefactorExtract),
        "Introduce Parameter",
        target,
        move |builder| {
            let (param_name, param) = new_param.name_and_ast(ctx);

            builder.make_mut(fn_).add_param(param.clone_for_update());
            update_original_declaration(builder, &new_param, &param_name);

            for (file_id, references) in fn_def.usages(&ctx.sema).all() {
                let source_file = ctx.sema.parse(file_id);
                builder.edit_file(file_id);
                let call_sites: Vec<CallSite> = references
                    .iter()
                    .filter_map(|usage| find_call_site(&ctx.sema, builder, &source_file, usage))
                    .collect();

                for call_site in non_overlapping_changes(call_sites) {
                    call_site.add_arg(&new_param.original_expr, builder);
                }
            }
        },
    )
}

struct NewParameter {
    original_expr: ast::Expr,
    ty: hir::Type,
    module: hir::Module,
}

impl NewParameter {
    fn from_ctx(ctx: &AssistContext<'_>) -> Option<Self> {
        let original_expr = expr_to_extract(ctx, valid_target)?;
        let ty = ctx.sema.type_of_expr(&original_expr)?.adjusted();
        if ty.is_unit() {
            cov_mark::hit!(test_not_applicable_for_unit);
            return None;
        }
        let module = ctx.sema.scope(&original_expr.syntax())?.module();
        Some(Self { original_expr, ty, module })
    }

    fn field_shorthand(&self) -> Option<ast::NameRef> {
        match self.original_expr.syntax().parent().and_then(ast::RecordExprField::cast) {
            Some(field) => field.name_ref(),
            None => None,
        }
    }

    fn parent_let_stmt(&self) -> Option<ast::LetStmt> {
        self.original_expr.syntax().parent().and_then(ast::LetStmt::cast)
    }

    fn parent_fn(&self) -> Option<ast::Fn> {
        self.original_expr.syntax().ancestors().find_map(ast::Fn::cast)
    }

    fn original_range(&self) -> TextRange {
        match self.field_shorthand() {
            Some(it) => it.syntax().text_range().cover(self.original_expr.syntax().text_range()),
            None => self.original_expr.syntax().text_range(),
        }
    }

    fn name_and_ast(&self, ctx: &AssistContext<'_>) -> (String, ast::Param) {
        let param_name = self.param_name(ctx);
        let name = make::name(&param_name);
        let pat = make::ext::simple_ident_pat(name);
        let ty = (&self.ty)
            .display_source_code(ctx.db(), self.module.into())
            .map(|it| make::ty(&it))
            .unwrap_or_else(|_| make::ty_placeholder());

        let param = make::param(pat.into(), ty);
        (param_name, param)
    }

    fn param_name(&self, ctx: &AssistContext<'_>) -> String {
        match self.field_shorthand() {
            Some(it) => it.to_string(),
            None => {
                if let Some(let_stmt) = self.parent_let_stmt() {
                    let_stmt.pat().unwrap().to_string()
                } else {
                    suggest_name::for_variable(&self.original_expr, &ctx.sema)
                }
            }
        }
    }
}

fn valid_target(node: SyntaxNode) -> Option<ast::Expr> {
    match node.kind() {
        SyntaxKind::LITERAL => ast::Literal::cast(node).map(|e| e.into()),
        SyntaxKind::TUPLE_EXPR => ast::TupleExpr::cast(node).map(|e| e.into()),
        _ => None,
    }
}

fn find_call_site(
    sema: &Semantics<'_, RootDatabase>,
    builder: &mut SourceChangeBuilder,
    source_file: &syntax::SourceFile,
    usage: &FileReference,
) -> Option<CallSite> {
    if let Some(macro_call) =
        find_node_at_range::<ast::MacroCall>(source_file.syntax(), usage.range)
    {
        let call = sema.find_node_at_offset_with_descend::<ast::CallableExpr>(
            macro_call.syntax(),
            usage.range.end(),
        )?;
        let range = sema.original_range(call.syntax());
        Some(CallSite::Macro(range.range, call))
    } else {
        let call = find_node_at_range(source_file.syntax(), usage.range)?;
        Some(CallSite::Standard(builder.make_mut(call)))
    }
}

enum CallSite {
    Macro(TextRange, ast::CallableExpr),
    Standard(ast::CallableExpr),
}

impl CallSite {
    fn add_arg(self, expr: &ast::Expr, builder: &mut SourceChangeBuilder) {
        match self {
            CallSite::Macro(range_to_replace, call_expr) => {
                let args = call_expr.arg_list().map(|it| it.args()).unwrap();
                let new_args = make::arg_list(args.chain(iter::once(expr.clone())));
                let replacement = match call_expr {
                    ast::CallableExpr::Call(call) => {
                        make::expr_call(call.expr().unwrap(), new_args)
                    }
                    ast::CallableExpr::MethodCall(call) => make::expr_method_call(
                        call.receiver().unwrap(),
                        call.name_ref().unwrap(),
                        new_args,
                    ),
                };
                builder.replace(range_to_replace, replacement.to_string());
            }
            CallSite::Standard(call) => {
                call.arg_list().map(|it| it.add_arg(expr.clone_for_update()));
            }
        }
    }

    fn overlaps_with(&self, range: TextRange) -> bool {
        match self {
            CallSite::Macro(range_to_replace, _) => range_to_replace.contains_range(range),
            CallSite::Standard(_) => false,
        }
    }
}

/// When a callsite is detected within a macro invocation, we need to manually
/// update it using the `builder.replace` API. This API does not support changes
/// that overlap, so in the case that there is a nested function call within a
/// macro invocation, we can only process one of the invocations.
fn non_overlapping_changes(call_sites: Vec<CallSite>) -> Vec<CallSite> {
    call_sites.into_iter().fold(vec![], |mut acc, edit| {
        match edit {
            CallSite::Macro(range_to_replace, _) => {
                if !acc.iter().any(|it| it.overlaps_with(range_to_replace)) {
                    acc.push(edit)
                }
            }
            CallSite::Standard(_) => acc.push(edit),
        }
        acc
    })
}

fn update_original_declaration(
    builder: &mut SourceChangeBuilder,
    new_param: &NewParameter,
    param_name: &str,
) {
    if let Some(let_stmt) = new_param.parent_let_stmt() {
        remove_let_stmt(builder, let_stmt);
    } else {
        let expr_range = new_param.original_range();
        builder.replace(expr_range, param_name);
    }
}

fn remove_let_stmt(builder: &mut SourceChangeBuilder, let_stmt: ast::LetStmt) {
    let text_range = let_stmt.syntax().text_range();
    let start = let_stmt
        .let_token()
        .and_then(|it| it.prev_token())
        .and_then(|prev| {
            if prev.kind() == SyntaxKind::WHITESPACE {
                Some(prev.text_range().start())
            } else {
                None
            }
        })
        .unwrap_or(text_range.start());
    builder.delete(TextRange::new(start, text_range.end()));
}

fn within_trait_impl(fn_: &ast::Fn) -> bool {
    fn_.syntax()
        .parent() // AssocItemList
        .and_then(|x| x.parent())
        .and_then(ast::Impl::cast)
        .map_or(false, |imp| imp.trait_().is_some())
}

#[cfg(test)]
mod tests {
    use crate::tests::{check_assist, check_assist_not_applicable};

    use super::*;

    #[test]
    fn not_applicable_in_trait_impl() {
        cov_mark::check!(test_not_applicable_in_trait_impl);
        check_assist_not_applicable(
            introduce_parameter,
            r#"
trait Foo {
    fn bar() -> i32;
}

struct Fooer;
impl Foo for Fooer {
    fn bar() {
        1 + $02$0
    }
}
             "#,
        )
    }

    #[test]
    fn not_applicable_for_unit() {
        cov_mark::check!(test_not_applicable_for_unit);
        check_assist_not_applicable(
            introduce_parameter,
            r#"
fn main() {
  example_function();
}

fn example_function() {
    $0let n = ();$0
    let m = n + 2;
}
            "#,
        )
    }

    #[test]
    fn basic_happy_path() {
        check_assist(
            introduce_parameter,
            r#"
fn main() {
  example_function();
}

fn example_function() {
    $0let n = 1;$0
    let m = n + 2;
}
            "#,
            r#"
fn main() {
  example_function(1);
}

fn example_function(n: i32) {
    let m = n + 2;
}
            "#,
        )
    }

    #[test]
    fn with_multiple_params() {
        check_assist(
            introduce_parameter,
            r#"
fn main() {
  example_function(1, 2);
}

fn example_function(a: i32, b: i32) {
    $0let n = 3;$0
    let m = n + 2;
}
            "#,
            r#"
fn main() {
  example_function(1, 2, 3);
}

fn example_function(a: i32, b: i32, n: i32) {
    let m = n + 2;
}
            "#,
        )
    }

    #[test]
    fn strukt_impl() {
        check_assist(
            introduce_parameter,
            r#"
struct Foo;
fn main() {
    Foo::example_function();
}

impl Foo {
    fn example_function() {
        $0let n = 1;$0
        let m = n + 2;
    }
}
            "#,
            r#"
struct Foo;
fn main() {
    Foo::example_function(1);
}

impl Foo {
    fn example_function(n: i32) {
        let m = n + 2;
    }
}
            "#,
        )
    }

    #[test]
    fn method_call() {
        check_assist(
            introduce_parameter,
            r#"
struct Foo;
fn main() {
    let f = Foo;
    f.example();
}

impl Foo {
    fn example(&self) {
        $0let n = 1;$0
        let m = n + 2;
    }
}
            "#,
            r#"
struct Foo;
fn main() {
    let f = Foo;
    f.example(1);
}

impl Foo {
    fn example(&self, n: i32) {
        let m = n + 2;
    }
}
            "#,
        )
    }

    #[test]
    fn multiple_files() {
        check_assist(
            introduce_parameter,
            r#"
//- /main.rs
fn main() {
  example_function();
}

fn example_function() {
    $0let n = 1;$0
    let m = n + 2;
}
mod foo;
//- /foo.rs
use crate::example_function;
fn f() {
    example_function();
    example_function();
}
            "#,
            r#"
//- /main.rs
fn main() {
  example_function(1);
}

fn example_function(n: i32) {
    let m = n + 2;
}
mod foo;
//- /foo.rs
use crate::example_function;
fn f() {
    example_function(1);
    example_function(1);
}
            "#,
        )
    }

    #[test]
    fn nested_call() {
        check_assist(
            introduce_parameter,
            r#"
fn main() {
  bar(
    foo()
  )
}

fn bar(n: i32) {}

fn foo() -> i32 {
    $0let n = 1;$0
    n + 2
}
            "#,
            r#"
fn main() {
  bar(
    foo(1)
  )
}

fn bar(n: i32) {}

fn foo(n: i32) -> i32 {
    n + 2
}
            "#,
        )
    }

    #[test]
    fn call_within_macro() {
        check_assist(
            introduce_parameter,
            r#"
struct Vec<T>;
macro_rules! vec {
   ($($item:expr),*) => {{
           let mut v = Vec::new();
           $( v.push($item); )*
           v
    }};
}
fn main() {
  bar(vec![foo(), foo()])
}

fn bar(v: Vec<i32>) {}

fn foo() -> i32 {
    $0let n = 1;$0
    n + 2
}
            "#,
            r#"
struct Vec<T>;
macro_rules! vec {
   ($($item:expr),*) => {{
           let mut v = Vec::new();
           $( v.push($item); )*
           v
    }};
}
fn main() {
  bar(vec![foo(1), foo(1)])
}

fn bar(v: Vec<i32>) {}

fn foo(n: i32) -> i32 {
    n + 2
}
            "#,
        )
    }

    #[test]
    fn method_call_within_macro() {
        check_assist(
            introduce_parameter,
            r#"
struct Vec<T>;
macro_rules! vec {
   ($($item:expr),*) => {{
           let mut v = Vec::new();
           $( v.push($item); )*
           v
    }};
}
struct Struct;
impl Struct {
    fn foo(&self) -> i32 {
        $0let n = 1;$0
        n + 2
    }
}
fn main() {
  let strukt = Struct;
  bar(vec![strukt.foo(), strukt.foo()])
}

fn bar(v: Vec<i32>) {}
            "#,
            r#"
struct Vec<T>;
macro_rules! vec {
   ($($item:expr),*) => {{
           let mut v = Vec::new();
           $( v.push($item); )*
           v
    }};
}
struct Struct;
impl Struct {
    fn foo(&self, n: i32) -> i32 {
        n + 2
    }
}
fn main() {
  let strukt = Struct;
  bar(vec![strukt.foo(1), strukt.foo(1)])
}

fn bar(v: Vec<i32>) {}
            "#,
        )
    }

    #[test]
    fn nested_method_call_within_macro() {
        check_assist(
            introduce_parameter,
            r#"
struct Vec<T>;
macro_rules! vec {
   ($($item:expr),*) => {{
           let mut v = Vec::new();
           $( v.push($item); )*
           v
    }};
}
struct Struct;
impl Struct {
    fn bar(v: Vec<i32>) {}
}
fn main() {
  let strukt = Struct;
  strukt.bar(vec![foo(), foo()])
}

fn foo() -> i32 {
    $0let n = 1;$0
    n + 2
}
            "#,
            r#"
struct Vec<T>;
macro_rules! vec {
   ($($item:expr),*) => {{
           let mut v = Vec::new();
           $( v.push($item); )*
           v
    }};
}
struct Struct;
impl Struct {
    fn bar(v: Vec<i32>) {}
}
fn main() {
  let strukt = Struct;
  strukt.bar(vec![foo(1), foo(1)])
}

fn foo(n: i32) -> i32 {
    n + 2
}
            "#,
        )
    }

    #[test]
    fn double_nested_call() {
        check_assist(
            introduce_parameter,
            r#"
fn main() {
  foo(
    foo(1)
  )
}

fn foo(x: i32) -> i32 {
    $0let n = 1;$0
    n + 2
}
            "#,
            r#"
fn main() {
  foo(
    foo(1, 1), 1
  )
}

fn foo(x: i32, n: i32) -> i32 {
    n + 2
}
            "#,
        )
    }

    // Next Steps
    // - Support cursor
    // - Support Ref + Mut
    // - Filter out some exprs that won't work
}
