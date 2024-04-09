use crate::buchi;
use crate::ltl::automata;
use crate::ltl::expression::LTLExpression;
use std::convert::TryFrom;
use std::fs;

pub mod kripke;
pub mod model_checker;

//WARN: use only integration tests for now until the API is stable
pub fn verify<'a>(
    program_path: &'a str,
    property: &'a str,
) -> Result<
    (),
    (
        Vec<buchi::BuchiNode<(String, (String, usize))>>,
        Vec<buchi::BuchiNode<(String, (String, usize))>>,
    ),
> {
    let contents = fs::read_to_string(program_path).expect("cannot read program file");

    let kripke_program =
        kripke::KripkeStructure::try_from(contents).expect("cannot convert into kripke structure");
    let buchi_program: buchi::Buchi<String> = kripke_program.clone().into();

    let nnf_ltl_property = LTLExpression::try_from(property)
        .expect("cannot convert try form")
        .rewrite()
        .nnf();

    let nodes = automata::create_graph::<String>(nnf_ltl_property.clone());

    let gbuchi_property = buchi::extract_buchi(nodes, nnf_ltl_property);

    let buchi_property = gbuchi_property.to_buchi();

    let product_ba = buchi::product_automata(buchi_program.clone(), buchi_property.clone());

    model_checker::emptiness(product_ba)
}
