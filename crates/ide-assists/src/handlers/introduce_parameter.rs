use ide_db::{
    assists::{AssistId, AssistKind},
    defs::Definition,
};
use syntax::{
    algo::find_node_at_range,
    ast::{self, make},
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
    let fn_def = {
        let func = ctx.sema.to_def(&func)?;
        Definition::Function(func)
    };
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
                field_shorthand,
                &to_extract,
                &param_name,
            );

            // - Find all call sites
            for (file_id, references) in fn_def.usages(&ctx.sema).all() {
                let source_file = ctx.sema.parse(file_id);
                edit.edit_file(file_id);
                for usage in references {
                    // - Place expression in arg list for all call sites
                    //   - Will we need to manually qualify names, or will that "just work"?
                    if let Some(call_expr) =
                        find_node_at_range::<ast::CallExpr>(source_file.syntax(), usage.range)
                    {
                        add_expr_to_arg_list(edit, call_expr, &to_extract);
                    } else if let Some(method_expr) =
                        find_node_at_range::<ast::MethodCallExpr>(source_file.syntax(), usage.range)
                    {
                        add_expr_to_arg_list(edit, method_expr, &to_extract);
                    }
                }
            }
        },
    )
}

fn add_expr_to_arg_list<CallType: ast::HasArgList>(
    edit: &mut AssistBuilder,
    call_expr: CallType,
    to_extract: &ast::Expr,
) {
    let call_expr = edit.make_mut(call_expr);
    call_expr.arg_list().unwrap().add_arg(to_extract.clone_for_update())
}

fn suggest_name_for_param(to_extract: &ast::Expr, ctx: &AssistContext) -> String {
    if let Some(let_stmt) = to_extract.syntax().parent().map(ast::LetStmt::cast).flatten() {
        return let_stmt.pat().unwrap().to_string();
    }
    suggest_name::for_variable(to_extract, &ctx.sema)
}

fn replace_expr_with_name_or_remove_let_stmt(
    edit: &mut AssistBuilder,
    field_shorthand: Option<ast::NameRef>,
    to_extract: &ast::Expr,
    param_name: &str,
) {
    if let Some(let_stmt) = to_extract.syntax().parent().map(ast::LetStmt::cast).flatten() {
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
    } else {
        let expr_range = match &field_shorthand {
            Some(it) => it.syntax().text_range().cover(to_extract.syntax().text_range()),
            None => to_extract.syntax().text_range(),
        };
        edit.replace(expr_range, param_name);
    }
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
    // Next Steps
    // - Support cursor
    // - Support Ref + Mut
    // - Filter out some exprs that won't work
}
