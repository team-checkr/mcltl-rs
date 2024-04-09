use std::collections::HashSet as Set;
use std::fmt;

use crate::state::State;

use super::expression::LTLExpression;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Node<S> {
    pub id: S,
    pub incoming: Vec<Node<S>>,
    pub next: Vec<LTLExpression>,
    pub oldf: Vec<LTLExpression>,
    pub newf: Vec<LTLExpression>,
}

impl<S: State> Node<S> {
    pub fn new(id: S) -> Self {
        Self {
            id,
            incoming: vec![],
            next: vec![],
            oldf: vec![],
            newf: vec![],
        }
    }

    pub fn new2(
        id: S,
        incoming: Vec<Node<S>>,
        oldf: Vec<LTLExpression>,
        newf: Vec<LTLExpression>,
        next: Vec<LTLExpression>,
    ) -> Self {
        Self {
            id,
            incoming,
            next,
            oldf,
            newf,
        }
    }
}

impl<S> fmt::Display for Node<S>
where
    S: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buff = String::new();
        buff.push_str(&format!("{}id = {}\n", &buff, self.id));

        let incoming = self
            .incoming
            .iter()
            .fold("".to_string(), |acc, inc| acc + &format!("{},", inc.id));

        buff.push_str(&format!("{}{}.incoming = [{}]\n", &buff, self.id, incoming));

        let oldf = self
            .oldf
            .iter()
            .fold("".to_string(), |acc, f| acc + &format!("{}, ", f));
        buff.push_str(&format!("{}{}.oldf = [{}]\n", &buff, self.id, oldf));

        let newf = self
            .newf
            .iter()
            .fold("".to_string(), |acc, f| acc + &format!("{}, ", f));
        buff.push_str(&format!("{}{}.newf = [{}]\n", &buff, self.id, newf));

        let next = self
            .next
            .iter()
            .fold("".to_string(), |acc, f| acc + &format!("{}, ", f));
        buff.push_str(&format!("{}{}.next = [{}]", &buff, self.id, next));

        write!(f, "{}", buff)
    }
}

macro_rules! set {
    ( $( $x:expr ),* ) => {
            Set::from([$($x),*])
    };
}

/// Implementation of the method describe in the paper: Simple On-the-Fly Automatic Verification of Linear Temporal Logic.
/// The graph constructed by the algorithm can be used to deﬁne an LGBA accepting the inﬁnite words satisfying the formula.
/// The set of states Q will be the nodes returned by this algorithm.
pub fn create_graph<S: State>(f: LTLExpression) -> Vec<Node<S>> {
    let new_begin = vec![f];

    let init = Node::new(S::initial());
    let incoming = vec![init];

    let n = Node::new2(State::new_name(), incoming, vec![], new_begin, vec![]);
    let nodeset = vec![];

    expand(n, nodeset)
}

/// Implementation of the method describe in the paper: Simple On-the-Fly Automatic Verification of Linear Temporal Logic.
fn expand<S: State>(mut node: Node<S>, mut nodeset: Vec<Node<S>>) -> Vec<Node<S>> {
    if node.newf.is_empty() {
        for k in nodeset.iter_mut() {
            if check_equal_next_and_old(k, &node) {
                k.incoming.extend(node.incoming.iter().cloned());
                return nodeset;
            }
        }

        nodeset.push(node.clone());

        let incoming = vec![node.clone()];
        let next = vec![];
        let newfs = node.next.clone();
        let oldfs = vec![];
        let new_node = Node::new2(S::new_name(), incoming, oldfs, newfs, next);

        expand(new_node, nodeset)
    } else {
        let f = node.newf[0].clone();
        node.newf.remove(0);

        match f {
            LTLExpression::False => nodeset,
            LTLExpression::Not(_) if node.oldf.contains(&f) => nodeset,
            LTLExpression::Literal(_) | LTLExpression::True | LTLExpression::Not(_) => {
                node.oldf.push(f);
                expand(node, nodeset)
            }
            LTLExpression::And(ref f1, ref f2) => {
                let f = f.clone();
                node.oldf.push(f);
                node.newf.push(f1.as_ref().clone());
                node.newf.push(f2.as_ref().clone());
                expand(node, nodeset)
            }
            LTLExpression::U(_, _)
            | LTLExpression::Or(_, _)
            | LTLExpression::V(_, _)
            | LTLExpression::R(_, _) => {
                let incoming1 = node.incoming.clone();
                let mut next1 = node.next.clone();
                next1.push(f.clone());
                let mut newfs1 = node.newf.clone();

                let new1 = new1(f.clone());
                for t in new1.into_iter().filter(|f| !node.oldf.contains(f)) {
                    newfs1.push(t);
                }
                let mut oldfs1 = node.oldf.clone();
                oldfs1.push(f.clone());

                let node1 = Node::new2(S::new_name(), incoming1, oldfs1, newfs1, next1);

                let incoming2 = node.incoming.clone();
                let next2 = node.next.clone();
                let mut newfs2 = node.newf.clone();

                let new2 = new2(f.clone());
                for t in new2.into_iter().filter(|f| !node.oldf.contains(f)) {
                    newfs2.push(t);
                }
                let mut oldfs2 = node.oldf.clone();
                oldfs2.push(f.clone());

                let node2 = Node::new2(S::new_name(), incoming2, oldfs2, newfs2, next2);

                expand(node2, expand(node1, nodeset))
            }
            _ => panic!("Expression must be simplify"),
        }
    }
}

fn new1(ltle: LTLExpression) -> Set<LTLExpression> {
    match ltle {
        LTLExpression::U(f1, _) => set! { f1.as_ref().clone() },
        LTLExpression::V(_, f2) => set! { f2.as_ref().clone() },
        LTLExpression::Or(_, f2) => set! { f2.as_ref().clone() },
        _ => set! {},
    }
}

fn new2(ltle: LTLExpression) -> Set<LTLExpression> {
    match ltle {
        LTLExpression::U(_, f2) => set! { f2.as_ref().clone() },
        LTLExpression::V(f1, f2) => set! { f1.as_ref().clone() , f2.as_ref().clone() },
        LTLExpression::Or(f1, _) => set! { f1.as_ref().clone() },
        _ => set! {},
    }
}

//fn next1(ltle: LTLExpression) -> Set<LTLExpression> {
//    match ltle {
//        LTLExpression::U(f1, f2) => set! { LTLExpression::U(f1, f2) },
//        LTLExpression::R(f1, f2) => set! { LTLExpression::R(f1, f2) },
//        _ => set! {},
//    }
//}

fn check_equal_next_and_old<S: State>(k: &Node<S>, n: &Node<S>) -> bool {
    if k.id.is_initial() || n.id.is_initial() {
        return false;
    }

    for f in k.next.iter() {
        if !n.next.contains(f) {
            return false;
        }
    }

    for f in n.next.iter() {
        if !k.next.contains(f) {
            return false;
        }
    }

    for f in k.oldf.iter() {
        if !n.oldf.contains(f) {
            return false;
        }
    }

    for f in n.oldf.iter() {
        if !k.oldf.contains(f) {
            return false;
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_should_create_graph_from_ltl() {
        let expr = LTLExpression::lit("p").U(LTLExpression::lit("q")).rewrite();

        let nodes = create_graph::<String>(expr);
        assert_eq!(3, nodes.len());
    }
}
