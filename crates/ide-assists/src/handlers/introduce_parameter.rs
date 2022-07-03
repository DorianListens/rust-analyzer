use ide_db::assists::{AssistId, AssistKind};
use syntax::{
    ast::{self, make},
    AstNode, SyntaxNode,
};

use crate::{
    assist_context::{AssistContext, Assists},
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
//     let n = $01;
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
            //   - Use exact same heuristics from extract variable (suggest_name::for_variable)
            let field_shorthand =
                match to_extract.syntax().parent().and_then(ast::RecordExprField::cast) {
                    Some(field) => field.name_ref(),
                    None => None,
                };

            let param_name = match &field_shorthand {
                Some(it) => it.to_string(),
                None => suggest_name::for_variable(&to_extract, &ctx.sema),
            };

            // - Add Name: Type to function's param list
            //   - Kinda like the opposite of remove_unused_parameter
            let param = make_param(ctx, &param_name, &ty, module);
            let param_list = func.param_list().unwrap();
            let offset = param_list.r_paren_token().unwrap().text_range().start();
            edit.insert(offset, param.to_string());

            // - Replace expression with Name
            //   - Exactly like extract_variable

            // - Find all call sites
            // - Place expression in arg list for all call sites
            //   - Will we need to manually qualify names, or will that "just work"?
            //   - Kinda like the opposite of remove_unused_parameter
            // let literal = ctx.find_node_at_offset::<ast::Literal>()?;
        },
    )
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

fn example_function($0n: i32) {
    let m = n + 2;
}
            "#,
        )
    }
}
