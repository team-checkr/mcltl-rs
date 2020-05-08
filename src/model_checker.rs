use crate::buchi::{Buchi, BuchiNode};
use std::collections::{HashMap, VecDeque};

/// return true iff there exists a path to a cycle containing an accepting state
pub fn emptiness(product_buchi: Buchi) -> Result<(), (Vec<BuchiNode>, Vec<BuchiNode>)> {
    let mut stack1: Vec<BuchiNode> =
        Vec::from([product_buchi.init_states.first().unwrap().clone()]); // S := {s0}
    let mut stack2: Vec<BuchiNode> = Vec::new(); // S2 := ∅

    let mut visited1: HashMap<&str, bool> = HashMap::new(); // M1 := 0
    let mut visited2: HashMap<&str, bool> = HashMap::new(); // M2 := 0

    for n in product_buchi.adj_list.iter() {
        visited1.insert(n.id.as_ref(), false);
        visited2.insert(n.id.as_ref(), false);
    }

    let mut succ: HashMap<String, BuchiNode> = HashMap::new();
    for adj in product_buchi.adj_list.iter() {
        succ.insert(adj.id.clone(), adj.clone());
    }

    //NOTE: All unwrap usages here should be safe because we work on known sets and that does not change.
    while !stack1.is_empty() {
        let x = stack1.last().unwrap().clone();

        // if there is a y in succ(x) with M1[h(y)] = 0
        let exist_y = x.adj.iter().any(|y| visited1[y.id.as_str()] == false);

        if exist_y {
            // get first member of x
            let succ_x = &succ[&x.id];
            let y = succ_x.adj.first().unwrap();
            *visited1.get_mut(y.id.as_str()).unwrap() = true;
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

                    if succ_v.adj.iter().all(|a| visited2[a.id.as_str()]) {
                        stack2.pop();
                    } else {
                        let succ_v = &succ[&v.id];
                        let w = succ_v
                            .adj
                            .iter()
                            .find(|a| !visited2.get(a.id.as_str()).unwrap())
                            .map(|w| succ[w.id.as_str()].clone())
                            .unwrap(); // first succ(v) with M2[h(w)] = 0
                        *visited2.get_mut(w.id.as_str()).unwrap() = true;
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

    use crate::expression::LTLExpression;

    #[test]
    fn it_should_found_non_empty() {
        let mut buchi = Buchi::new(); // accepts a(bef )^ω

        let mut q0 = BuchiNode::new("q0".into());
        let mut q1 = BuchiNode::new("q1".into());
        let mut q2 = BuchiNode::new("q2".into());
        let mut q3 = BuchiNode::new("q3".into());
        let mut q4 = BuchiNode::new("q4".into());

        q0.adj.push(BuchiNode {
            id: "q1".into(),
            labels: vec![LTLExpression::Literal("a".into())],
            adj: vec![],
        });

        q1.adj.push(BuchiNode {
            id: "q2".into(),
            labels: vec![LTLExpression::Literal("b".into())],
            adj: vec![],
        });

        q2.adj = vec![
            BuchiNode {
                id: "q3".into(),
                labels: vec![LTLExpression::Literal("e".into())],
                adj: vec![],
            },
            BuchiNode {
                id: "q4".into(),
                labels: vec![LTLExpression::Literal("c".into())],
                adj: vec![],
            },
        ];

        q3.adj.push(BuchiNode {
            id: "q1".into(),
            labels: vec![LTLExpression::Literal("f".into())],
            adj: vec![],
        });

        q4.adj.push(BuchiNode {
            id: "q3".into(),
            labels: vec![LTLExpression::Literal("d".into())],
            adj: vec![],
        });

        buchi.adj_list.push(q0.clone());
        buchi.adj_list.push(q1.clone());
        buchi.adj_list.push(q2);
        buchi.adj_list.push(q3);
        buchi.adj_list.push(q4);

        buchi.accepting_states.push(q1);
        buchi.init_states.push(q0);

        let res = emptiness(buchi);

        assert!(res.is_err());

        let stacks = res.unwrap_err();
        assert_eq!(1, stacks.0.len());
        assert_eq!(3, stacks.1.len());
    }

    #[test]
    fn it_should_found_empty_because_the_cycle_doesnt_contain_an_accepting_state() {
        let mut buchi = Buchi::new(); // accepts a(bef )^ω

        let mut q0 = BuchiNode::new("q0".into());
        let mut q1 = BuchiNode::new("q1".into());
        let mut q2 = BuchiNode::new("q2".into());
        let mut q3 = BuchiNode::new("q3".into());
        let q4 = BuchiNode::new("q4".into());

        q0.adj.push(BuchiNode {
            id: "q1".into(),
            labels: vec![LTLExpression::Literal("a".into())],
            adj: vec![],
        });

        q1.adj.push(BuchiNode {
            id: "q2".into(),
            labels: vec![LTLExpression::Literal("b".into())],
            adj: vec![],
        });

        q2.adj = vec![
            BuchiNode {
                id: "q3".into(),
                labels: vec![LTLExpression::Literal("e".into())],
                adj: vec![],
            },
            BuchiNode {
                id: "q4".into(),
                labels: vec![LTLExpression::Literal("c".into())],
                adj: vec![],
            },
        ];

        q3.adj.push(BuchiNode {
            id: "q1".into(),
            labels: vec![LTLExpression::Literal("f".into())],
            adj: vec![],
        });

        buchi.adj_list.push(q0.clone());
        buchi.adj_list.push(q1.clone());
        buchi.adj_list.push(q2);
        buchi.adj_list.push(q3);
        buchi.adj_list.push(q4.clone());

        buchi.accepting_states.push(q4);
        buchi.init_states.push(q0);

        let res = emptiness(buchi);

        assert!(res.is_ok());
    }

    #[test]
    fn it_should_found_emptiness() {
        let mut buchi = Buchi::new();

        let mut q0 = BuchiNode::new("q0".into());
        let q1 = BuchiNode::new("q1".into());

        q0.adj.push(BuchiNode {
            id: "q1".into(),
            labels: vec![LTLExpression::Literal("a".into())],
            adj: vec![],
        });

        buchi.adj_list.push(q0.clone());
        buchi.adj_list.push(q1.clone());

        buchi.accepting_states.push(q1);
        buchi.init_states.push(q0);

        let res = emptiness(buchi);

        assert!(res.is_ok());
    }
}
