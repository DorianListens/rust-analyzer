use ide_db::assists::{AssistId, AssistKind};
use syntax::ast;

use crate::assist_context::{AssistContext, Assists};

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
//     // calculate
//     let k = m + n;
//     let g = 3;
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
//     // calculate
//     let k = m + n;
//     let g = 3;
// }
// ```
pub(crate) fn introduce_parameter(acc: &mut Assists, ctx: &AssistContext) -> Option<()> {
    // Steps:
    //
    // Create
    // - Check if we're in a function body
    //   - Can't be trait impl, but can be method
    // - Find Expression to Extract
    //   - This is the same as extract_variable for now
    //   - Can filter list more later to exclude things that will definitely not compile
    //   - Literals will always work
    //   - Can't reference any locals not in param list
    //   - How strict should we be about visibility?
    //     - Is it better to generate easily fixable broken code, or refuse?
    // - Find Type of expression
    //   - ctx.sema.type_of_exper
    //   - maybe need to bail out when unnameable?
    // Execute
    // - Pick name for parameter
    //   - Use exact same heuristics from extract variable (suggest_name::for_variable)
    // - Add Name: Type to function's param list
    //   - Kinda like the opposite of remove_unused_parameter
    // - Replace expression with Name
    //   - Exactly like extract_variable
    // - Find all call sites
    // - Place expression in arg list for all call sites
    //   - Will we need to manually qualify names, or will that "just work"?
    //   - Kinda like the opposite of remove_unused_parameter
    let literal = ctx.find_node_at_offset::<ast::Literal>()?;
    let target = ctx.covering_element().text_range();
    acc.add(
        AssistId("introduce_parameter", AssistKind::RefactorExtract),
        "Introduce Parameter",
        target,
        move |edit| {},
    )
}
