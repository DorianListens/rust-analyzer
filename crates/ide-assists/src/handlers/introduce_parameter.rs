use std::iter;

use hir::Semantics;
use ide_db::{
    assists::{AssistId, AssistKind},
    defs::Definition,
    search::FileReference,
    RootDatabase,
};
use syntax::{
    ast::{self, make, HasArgList},
    AstNode, SyntaxKind, SyntaxNode, TextRange,
};

use crate::{
    assist_context::{AssistBuilder, AssistContext, Assists},
    utils::suggest_name,
};

use super::{
    extract_function::make_ty,
    extract_variable::{expr_to_extract, valid_target_expr},
};

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
pub(crate) fn introduce_parameter(acc: &mut Assists, ctx: &AssistContext) -> Option<()> {
    // Steps:
    //
    // Create

    // - Find Expression to Extract
    //   - This is the same as extract_variable for now
    //   - Can filter list more later to exclude things that will definitely not compile
    //   - Literals will always work
    //   - Can't reference any locals not in param list
    //   - How strict should we be about visibility?
    //     - Is it better to generate easily fixable broken code, or refuse?
    let to_extract = expr_to_extract(ctx, valid_target_expr)?;

    // - Check if we're in a function body
    let func = parent_fn(&to_extract.syntax())?;
    let func_def = ctx.sema.to_def(&func)?;
    let fn_def = { Definition::Function(func_def) };
    // - Can't be trait impl, but can be method
    if within_trait_impl(&func) {
        cov_mark::hit!(test_not_applicable_in_trait_impl);
        return None;
    }

    // - Find Type of expression
    let ty = ctx.sema.type_of_expr(&to_extract)?.adjusted();

    if ty.is_unit() {
        cov_mark::hit!(test_not_applicable_for_unit);
        return None;
    }

    let module = ctx.sema.scope(&to_extract.syntax())?.module();

    let target = ctx.covering_element().text_range();
    acc.add(
        AssistId("introduce_parameter", AssistKind::RefactorExtract),
        "Introduce Parameter",
        target,
        move |edit| {
            // Execute
            // - Pick name for parameter
            let field_shorthand =
                match to_extract.syntax().parent().and_then(ast::RecordExprField::cast) {
                    Some(field) => field.name_ref(),
                    None => None,
                };

            let param_name = match &field_shorthand {
                Some(it) => it.to_string(),
                None => suggest_name_for_param(&to_extract, ctx),
            };

            let param = make_param(ctx, &param_name, &ty, module);
            add_param_to_param_list(edit, func, param);

            replace_expr_with_name_or_remove_let_stmt(
                edit,
                &field_shorthand,
                &to_extract,
                &param_name,
            );

            // - Find all call sites
            let usages = fn_def.usages(&ctx.sema).all();
            let is_method_call = func_def.has_self_param(ctx.db());

            for (file_id, references) in usages {
                let source_file = ctx.sema.parse(file_id);
                edit.edit_file(file_id);
                let call_sites: Vec<CallSite> = references
                    .iter()
                    .filter_map(|it| {
                        find_call_site(&ctx.sema, edit, &source_file, it, is_method_call)
                    })
                    .collect();

                call_sites.iter().for_each(|it| it.add_arg(edit, &to_extract));
            }
        },
    )
}

fn find_call_site(
    sema: &Semantics<RootDatabase>,
    builder: &mut AssistBuilder,
    source_file: &syntax::SourceFile,
    usage: &FileReference,
    is_method_call: bool,
) -> Option<CallSite> {
    if is_method_call {
        let call_expr = sema.find_node_at_offset_with_descend::<ast::MethodCallExpr>(
            source_file.syntax(),
            usage.range.end(),
        )?;
        let text_range = sema.original_range(&call_expr.syntax()).range;
        return Some(CallSite::MethodCall(text_range, builder.make_mut(call_expr)));
    } else {
        let call_expr = sema.find_node_at_offset_with_descend::<ast::CallExpr>(
            source_file.syntax(),
            usage.range.end(),
        )?;
        let text_range = sema.original_range(&call_expr.syntax()).range;
        return Some(CallSite::Call(text_range, builder.make_mut(call_expr)));
    }
}

enum CallSite {
    Call(TextRange, ast::CallExpr),
    MethodCall(TextRange, ast::MethodCallExpr),
}

impl CallSite {
    fn arg_list(&self) -> Option<ast::ArgList> {
        match self {
            CallSite::Call(_, it) => it.arg_list(),
            CallSite::MethodCall(_, it) => it.arg_list(),
        }
    }

    /// This currently doesn't work for nested calls,
    /// ie: foo(foo(1))
    /// This is because calls to builder.replace can't overlap
    /// This problem does not occur if we use the `edit_in_place`
    /// style of tree manipulation.
    /// I switched to using `replace` because the ast editor
    /// didn't work within macro calls.
    /// no difference between `replace` and `replace_ast`.
    /// Worth noting: this panic also hits `remove_unused_parameter`,
    /// so atleast I'm not alone!
    /// Filed: https://github.com/rust-lang/rust-analyzer/issues/12784
    ///
    /// Plan of attack:
    /// We can solve each issue, but if they occur together, we'll need to drop the overlapping edits
    ///
    /// Instead of `add_arg` mutating directly, we'll need to produce
    /// a list of edits, and then filter out the ones that would overlap (take the largest one? smallest?)
    /// before executing them all.
    fn add_arg(&self, builder: &mut AssistBuilder, expr: &ast::Expr) {
        // - Will we need to manually qualify names, or will that "just work"?
        // If we want this to work, we'll need a path transform.
        let args = self.arg_list().map(|it| it.args()).unwrap();
        let new_args = make::arg_list(args.chain(iter::once(expr.clone())));
        // self.arg_list().map(|it| it.add_arg(expr.clone_for_update()));
        match self {
            CallSite::Call(range, call) => {
                let expr_call = make::expr_call(call.expr().unwrap(), new_args);
                builder.replace(*range, expr_call.to_string());
            }
            CallSite::MethodCall(range, call) => {
                let expr_call = make::expr_method_call(
                    call.receiver().unwrap(),
                    call.name_ref().unwrap(),
                    new_args,
                );

                builder.replace(*range, expr_call.to_string());
            }
        };
    }
}

fn suggest_name_for_param(to_extract: &ast::Expr, ctx: &AssistContext) -> String {
    if let Some(let_stmt) = to_extract.syntax().parent().and_then(ast::LetStmt::cast) {
        return let_stmt.pat().unwrap().to_string();
    }
    suggest_name::for_variable(to_extract, &ctx.sema)
}

fn replace_expr_with_name_or_remove_let_stmt(
    edit: &mut AssistBuilder,
    field_shorthand: &Option<ast::NameRef>,
    to_extract: &ast::Expr,
    param_name: &str,
) {
    if let Some(let_stmt) = to_extract.syntax().parent().and_then(ast::LetStmt::cast) {
        remove_let_stmt(edit, let_stmt);
    } else {
        let expr_range = match field_shorthand {
            Some(it) => it.syntax().text_range().cover(to_extract.syntax().text_range()),
            None => to_extract.syntax().text_range(),
        };
        edit.replace(expr_range, param_name);
    }
}

fn remove_let_stmt(edit: &mut AssistBuilder, let_stmt: ast::LetStmt) {
    let text_range = let_stmt.syntax().text_range();
    let start = let_stmt
        .let_token()
        .unwrap()
        .prev_token()
        .and_then(|prev| {
            if prev.kind() == SyntaxKind::WHITESPACE {
                Some(prev.text_range().start())
            } else {
                None
            }
        })
        .unwrap_or(text_range.start());
    edit.delete(TextRange::new(start, text_range.end()));
}

fn add_param_to_param_list(edit: &mut AssistBuilder, func: ast::Fn, param: ast::Param) {
    let fn_ = edit.make_mut(func);
    let param_list = fn_.get_or_create_param_list();
    param_list.add_param(param.clone_for_update());
}

fn make_param(
    ctx: &AssistContext,
    param_name: &str,
    ty: &hir::Type,
    module: hir::Module,
) -> ast::Param {
    let name = make::name(&param_name);
    let pat = make::ext::simple_ident_pat(name);
    let ty = make_ty(ty, ctx, module);

    make::param(pat.into(), ty)
}

fn within_trait_impl(func: &ast::Fn) -> bool {
    func.syntax()
        .parent() // AssocItemList
        .and_then(|x| x.parent())
        .and_then(ast::Impl::cast)
        .map_or(false, |imp| imp.trait_().is_some())
}

fn parent_fn(node: &SyntaxNode) -> Option<ast::Fn> {
    node.ancestors().find_map(ast::Fn::cast)
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
    // - Fix bug with macro calls
    // - Support cursor
    // - Support Ref + Mut
    // - Filter out some exprs that won't work
}
