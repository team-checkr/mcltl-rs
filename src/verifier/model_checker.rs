use crate::{
    buchi::{Buchi, BuchiNode},
    state::State,
};
use std::collections::HashMap;

/// return true iff there exists a path to a cycle containing an accepting state
pub fn emptiness<S: State>(
    product_buchi: Buchi<S>,
) -> Result<(), (Vec<BuchiNode<S>>, Vec<BuchiNode<S>>)> {
    let mut stack1: Vec<BuchiNode<S>> =
        Vec::from([product_buchi.init_states.first().unwrap().clone()]); // S := {s0}
    let mut stack2: Vec<BuchiNode<S>> = Vec::new(); // S2 := ∅

    let mut visited1: HashMap<&S, bool> = HashMap::new(); // M1 := 0
    let mut visited2: HashMap<&S, bool> = HashMap::new(); // M2 := 0

    for n in product_buchi.adj_list.iter() {
        visited1.insert(&n.id, false);
        visited2.insert(&n.id, false);
    }

    let mut succ: HashMap<S, BuchiNode<S>> = HashMap::new();
    for adj in product_buchi.adj_list.iter() {
        succ.insert(adj.id.clone(), adj.clone());
    }

    //NOTE: All unwrap usages here should be safe because we work on known sets and that does not change.
    while !stack1.is_empty() {
        let x = stack1.last().unwrap().clone();

        // if there is a y in succ(x) with M1[h(y)] = 0
        let exist_y = x.adj.iter().any(|y| !visited1[&y.id]);

        if exist_y {
            // get first member of x
            let succ_x = &succ[&x.id];
            let y = succ_x.adj.first().unwrap();
            *visited1.get_mut(&y.id).unwrap() = true;
            stack1.push(y.clone());
        } else {
            let x = stack1.pop().unwrap().clone();

            // x ∈ F
            let x_in_f = product_buchi.accepting_states.iter().any(|f| f.id == x.id);

            if x_in_f {
                stack2.push(x.clone());

                while !stack2.is_empty() {
                    let v = stack2.last().unwrap();

                    let succ_v = &succ[&v.id];
                    let x_in_succv = succ_v.adj.iter().any(|succ| succ.id == x.id);
                    if x_in_succv {
                        return Err((stack1, stack2));
                    }

                    if succ_v.adj.iter().all(|a| visited2[&a.id]) {
                        stack2.pop();
                    } else {
                        let succ_v = &succ[&v.id];
                        let w = succ_v
                            .adj
                            .iter()
                            .find(|a| !visited2.get(&a.id).unwrap())
                            .map(|w| succ[&w.id].clone())
                            .unwrap(); // first succ(v) with M2[h(w)] = 0
                        *visited2.get_mut(&w.id).unwrap() = true;
                        stack2.push(w);
                    }
                }
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod test_emptiness {
    use super::*;

    use crate::buchi;

    use crate::ltl::expression::LTLExpression;

    #[test]
    fn it_should_found_non_empty() {
        let buchi = buchi! {
            q0
                [LTLExpression::lit("a")] => q1
            q1
                [LTLExpression::lit("b")] => q2
            q2
                [LTLExpression::lit("e")] => q3
                [LTLExpression::lit("c")] => q4 // cycle containing an accepting state
            q3
                [LTLExpression::lit("f")] => q1
            q4
                [LTLExpression::lit("d")] => q3
            ===
            init = [q0]
            accepting = [q1]
        };

        insta::assert_snapshot!(buchi, @r###"
        States:
         "q0" []
           =[a]=> "q1"
         "q1" []
           =[b]=> "q2"
         "q2" []
           =[e]=> "q3"
           =[c]=> "q4"
         "q3" []
           =[f]=> "q1"
         "q4" []
           =[d]=> "q3"
        Initial: "q0"
        Accept:  "q1"
        "###);

        let res = emptiness(buchi);

        let (stack1, stack2) = res.unwrap_err();

        assert_eq!(1, stack1.len());
        assert_eq!(3, stack2.len());
    }

    #[test]
    fn it_should_found_empty_because_the_cycle_doesnt_contain_an_accepting_state() {
        let buchi = buchi! {
            q0
                [LTLExpression::lit("a")] => q1
            q1
                [LTLExpression::lit("b")] => q2
            q2
                [LTLExpression::lit("e")] => q3
                [LTLExpression::lit("c")] => q4
            q3
            q4
                [LTLExpression::lit("d")] => q3
            ===
            init = [q0]
            accepting = [q1]
        };

        insta::assert_snapshot!(buchi, @r###"
        States:
         "q0" []
           =[a]=> "q1"
         "q1" []
           =[b]=> "q2"
         "q2" []
           =[e]=> "q3"
           =[c]=> "q4"
         "q3" []
         "q4" []
           =[d]=> "q3"
        Initial: "q0"
        Accept:  "q1"
        "###);

        let res = emptiness(buchi);

        assert!(res.is_ok());
    }

    #[test]
    fn it_should_found_emptiness() {
        let buchi = buchi! {
            q0
                [LTLExpression::lit("a")] => q1
            q1
            ===
            init = [q0]
            accepting = [q0, q1]
        };

        insta::assert_snapshot!(buchi, @r###"
        States:
         "q0" []
           =[a]=> "q1"
         "q1" []
        Initial: "q0"
        Accept:  "q0" "q1"
        "###);

        let res = emptiness(buchi);

        assert!(res.is_ok());
    }
}
