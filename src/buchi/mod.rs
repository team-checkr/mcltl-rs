use std::collections::HashSet;
use std::fmt;

use crate::{
    ltl::{automata::Node, expression::LTLExpression},
    state::State,
};

#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub struct BuchiNode<S> {
    pub id: S,
    pub labels: Vec<LTLExpression>,
    pub adj: Vec<BuchiNode<S>>,
}

impl<S> BuchiNode<S> {
    pub fn new(id: S) -> Self {
        Self {
            id,
            labels: Vec::new(),
            adj: Vec::new(),
        }
    }
    pub fn map<T>(&self, f: &dyn Fn(&S) -> T) -> BuchiNode<T> {
        BuchiNode {
            id: f(&self.id),
            labels: self.labels.clone(),
            adj: self.adj.iter().map(|n| n.map(f)).collect(),
        }
    }
}

impl<S> fmt::Display for BuchiNode<S>
where
    S: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buff = String::new();
        buff.push_str(&format!("{}id = {}\n", &buff, self.id));

        let labels = self
            .labels
            .iter()
            .fold("".to_string(), |acc, label| acc + &format!("{},", label));
        buff.push_str(&format!("{}{}.labels = [{}]\n", &buff, self.id, labels));

        let adjs = self
            .adj
            .iter()
            .fold("".to_string(), |acc, a| acc + &format!("{},", a.id));
        buff.push_str(&format!("{}{}.adj = [{}]\n", &buff, self.id, adjs));

        write!(f, "{}", buff)
    }
}

///  generalized Büchi automaton (GBA) automaton.
/// The difference with the Büchi automaton is its accepting condition, i.e., a set of sets of states.
#[derive(Debug, Eq, PartialEq)]
pub struct GeneralBuchi<S> {
    pub states: Vec<S>,
    pub accepting_states: Vec<Vec<BuchiNode<S>>>,
    pub init_states: Vec<BuchiNode<S>>,
    pub adj_list: Vec<BuchiNode<S>>,
}

impl<S> Default for GeneralBuchi<S> {
    fn default() -> Self {
        Self {
            states: Default::default(),
            accepting_states: Default::default(),
            init_states: Default::default(),
            adj_list: Default::default(),
        }
    }
}

impl<S> fmt::Display for GeneralBuchi<S>
where
    S: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buff = String::new();
        for (i, ac) in self.accepting_states.iter().enumerate() {
            let states = ac
                .iter()
                .fold("".to_string(), |acc, a| acc + &format!("{},", a.id));
            buff.push_str(&format!("{}accepting_state[{}] = {:?}\n", &buff, i, states));
        }

        let init_states = self
            .init_states
            .iter()
            .fold("".to_string(), |acc, init| acc + &format!("{},", init.id));
        buff.push_str(&format!("{}init_states = [{}]\n", &buff, init_states));

        let adjs = self
            .adj_list
            .iter()
            .fold("".to_string(), |acc, adj| acc + &format!("{},", adj.id));
        buff.push_str(&format!("{}adj = [{}]\n", &buff, adjs));

        write!(f, "{}", buff)
    }
}

impl<S: State> GeneralBuchi<S> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get_node(&self, name: &S) -> Option<BuchiNode<S>> {
        for adj in self.adj_list.iter() {
            if &adj.id == name {
                return Some(adj.clone());
            }
        }

        None
    }

    pub fn get_node_mut(&mut self, name: &S) -> Option<&mut BuchiNode<S>> {
        self.adj_list.iter_mut().find(|adj| &adj.id == name)
    }
}

/// Büchi automaton is a type of ω-automaton, which extends
/// a finite automaton to infinite inputs.
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Buchi<S> {
    pub states: Vec<S>,
    pub accepting_states: Vec<BuchiNode<S>>,
    pub init_states: Vec<BuchiNode<S>>,
    pub adj_list: Vec<BuchiNode<S>>,
}

impl<S> Default for Buchi<S> {
    fn default() -> Self {
        Self {
            states: Default::default(),
            accepting_states: Default::default(),
            init_states: Default::default(),
            adj_list: Default::default(),
        }
    }
}

impl<S: State> Buchi<S> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get_node(&self, name: &S) -> Option<BuchiNode<S>> {
        for adj in self.adj_list.iter() {
            if &adj.id == name {
                return Some(adj.clone());
            }
        }

        None
    }

    pub fn get_node_mut(&mut self, name: &S) -> Option<&mut BuchiNode<S>> {
        self.adj_list.iter_mut().find(|adj| &adj.id == name)
    }
}

fn extract_unitl_subf(
    f: &LTLExpression,
    mut sub_formulas: Vec<LTLExpression>,
) -> Vec<LTLExpression> {
    match f {
        LTLExpression::True => sub_formulas,
        LTLExpression::False => sub_formulas,
        LTLExpression::Literal(_) => sub_formulas,
        LTLExpression::Not(_) => sub_formulas,
        LTLExpression::And(f1, f2) => extract_unitl_subf(f2, extract_unitl_subf(f1, sub_formulas)),
        LTLExpression::Or(f1, f2) => extract_unitl_subf(f2, extract_unitl_subf(f1, sub_formulas)),
        LTLExpression::U(f1, f2) => {
            sub_formulas.push(f1.clone().U(*f2.clone()));
            extract_unitl_subf(f2, extract_unitl_subf(f1, sub_formulas))
        }
        LTLExpression::R(f1, f2) => extract_unitl_subf(f1, extract_unitl_subf(f2, sub_formulas)),
        LTLExpression::V(f1, f2) => extract_unitl_subf(f1, extract_unitl_subf(f2, sub_formulas)),
        e => panic!(
            "unsuported operator, you should simplify the expression: {}",
            e
        ),
    }
}

/// LGBA construction from create_graph set Q result
pub fn extract_buchi<S: State>(result: Vec<Node<S>>, f: LTLExpression) -> GeneralBuchi<S> {
    let mut buchi = GeneralBuchi::new();

    for n in result.iter() {
        let mut buchi_node = BuchiNode::new(n.id.clone());
        buchi.states.push(n.id.clone());

        for l in n.oldf.iter() {
            match *l {
                LTLExpression::Literal(ref lit) => buchi_node.labels.push(LTLExpression::lit(lit)),
                LTLExpression::True => buchi_node.labels.push(LTLExpression::True),
                LTLExpression::False => buchi_node.labels.push(LTLExpression::False),
                LTLExpression::Not(ref e) => match **e {
                    LTLExpression::True => buchi_node.labels.push(LTLExpression::False),
                    LTLExpression::False => buchi_node.labels.push(LTLExpression::True),
                    LTLExpression::Literal(ref lit) => {
                        buchi_node.labels.push(!LTLExpression::lit(lit))
                    }
                    _ => {}
                },
                _ => {}
            }
        }
        buchi.adj_list.push(buchi_node);
    }

    let mut initial_states = Vec::new();

    for n in result.iter() {
        let buchi_node = buchi.get_node(&n.id).unwrap();

        for k in n.incoming.iter() {
            if k.id.is_initial() {
                initial_states.push(buchi_node.clone());
            } else {
                buchi
                    .get_node_mut(&k.id)
                    .unwrap()
                    .adj
                    .push(buchi_node.clone());
            }
        }
    }

    let mut init_state = BuchiNode::new(S::initial());
    buchi.states.push(S::initial());
    init_state.adj = initial_states.clone();
    buchi.adj_list.push(init_state);
    buchi.init_states = initial_states;

    let sub_formulas = extract_unitl_subf(&f, vec![]);

    for f in sub_formulas {
        let mut accepting_states = Vec::new();

        for n in result.iter() {
            match f {
                LTLExpression::U(_, ref f2) if !n.oldf.contains(&f) || n.oldf.contains(f2) => {
                    if let Some(node) = buchi.get_node(&n.id) {
                        accepting_states.push(node);
                    }
                }
                _ => {}
            }
        }

        buchi.accepting_states.push(accepting_states);
    }

    buchi
}

/// Multiple sets of states in acceptance condition can be translated into one set of states
/// by an automata construction, which is known as "counting construction".
/// Let's say `A = (Q, Σ, ∆, q0, {F1,...,Fn})` is a GBA, where `F1,...,Fn` are sets of accepting states
/// then the equivalent Büchi automaton is `A' = (Q', Σ, ∆',q'0,F')`, where
/// * `Q' = Q × {1,...,n}`
/// * `q'0 = ( q0,1 )`
/// * `∆' = { ( (q,i), a, (q',j) ) | (q,a,q') ∈ ∆ and if q ∈ Fi then j=((i+1) mod n) else j=i }`
/// * `F'=F1× {1}`
impl<S: State> From<GeneralBuchi<S>> for Buchi<(S, usize)> {
    fn from(general_buchi: GeneralBuchi<S>) -> Buchi<(S, usize)> {
        let mut ba: Buchi<(S, usize)> = Buchi::new();

        if general_buchi.accepting_states.is_empty() {
            // TODO: Is this right?
            ba.accepting_states = general_buchi
                .adj_list
                .iter()
                .map(|n| n.map(&|s| (s.clone(), usize::initial())))
                .collect();
            ba.adj_list = general_buchi
                .adj_list
                .iter()
                .map(|n| n.map(&|s| (s.clone(), usize::initial())))
                .collect();
            ba.init_states = general_buchi
                .init_states
                .iter()
                .map(|n| n.map(&|s| (s.clone(), usize::initial())))
                .collect();
            return ba;
        }
        for (i, _) in general_buchi.accepting_states.iter().enumerate() {
            for n in general_buchi.adj_list.iter() {
                let mut buchi_node = BuchiNode::new((n.id.clone(), i));
                buchi_node.labels = n.labels.clone();
                ba.adj_list.push(buchi_node);
            }
        }
        for (i, f) in general_buchi.accepting_states.iter().enumerate() {
            for node in general_buchi.adj_list.iter() {
                for adj in node.adj.iter() {
                    let j = if f.iter().any(|n| n.id == node.id) {
                        (i + 1) % general_buchi.accepting_states.len()
                    } else {
                        i
                    };
                    let ba_node = ba.get_node_mut(&(node.id.clone(), i)).unwrap();
                    ba_node.adj.push(BuchiNode {
                        id: (adj.id.clone(), j),
                        labels: adj.labels.clone(),
                        adj: vec![],
                    });
                }
            }
        }
        // q'0 = ( q0,1 ), here we start to count at 0
        let init_node = ba
            .get_node(&(S::initial(), usize::initial()))
            .unwrap_or_else(|| {
                panic!(
                    "cannot find the init node `{}` but it should exist",
                    (S::initial(), usize::initial()).name()
                )
            });
        ba.init_states.push(init_node.clone());
        // F'=F1 × {1}
        let f_1 = general_buchi.accepting_states.first().unwrap();
        for accepting_state in f_1.iter() {
            let node = ba
                .get_node(&(accepting_state.id.clone(), usize::initial()))
                .unwrap();
            ba.accepting_states.push(node);
        }
        ba
    }
}

/// Product of the program and the property
/// Let `A1 = (S1 ,Σ1 , ∆1 ,I1 ,F1)`
/// and  `A2 = (S2 ,Σ2 , ∆2 ,I2 ,F2 )` be two automata.
///
/// We define `A1 × A2` , as the quituple:
/// `(S,Σ,∆,I,F) := (S1 × S2, Σ1 × Σ2, ∆1 × ∆2, I1 × I2, F1 × F2)`,
///
/// where where ∆ is a function from `S × Σ` to `P(S1) × P(S2) ⊆ P(S)`,
///
/// given by `∆((q1, q2), a, (q1', q2')) ∈ ∆`
/// iff `(q1, a, q1') ∈ ∆1`
/// and `(q2, a, q2') ∈ ∆2`
pub fn product_automata<S: State, T: State>(
    program: Buchi<S>,
    property: Buchi<T>,
) -> Buchi<(S, T)> {
    let mut product_buchi = Buchi::new();

    for n1 in program.adj_list.iter() {
        for n2 in property.adj_list.iter() {
            let product_id = (n1.id.clone(), n2.id.clone());
            let product_node = BuchiNode::new(product_id);
            product_buchi.adj_list.push(product_node);
        }
    }

    // transition function ∆
    for bn1 in product_buchi.adj_list.clone().iter() {
        let q1 = program.get_node(&bn1.id.0).unwrap();
        let q1_prime = property.get_node(&bn1.id.1).unwrap();

        for bn2 in product_buchi.adj_list.clone().iter() {
            let q2 = program.get_node(&bn2.id.0).unwrap();
            let q2_prime = property.get_node(&bn2.id.1).unwrap();

            // collect all labels
            let mut labels = HashSet::new();
            labels.extend(q1_prime.labels.iter());
            labels.extend(q2_prime.labels.iter());

            for label in labels {
                // check if (q1, a, q1') ∈ ∆1
                // and check if (q2, a, q2') ∈ ∆2
                if q1
                    .adj
                    .iter()
                    .any(|b| b.id == q2.id && b.labels.contains(label))
                    && q1_prime
                        .adj
                        .iter()
                        .any(|b| b.id == q2_prime.id && b.labels.contains(label))
                {
                    if let Some(product_node) = product_buchi.get_node_mut(&bn1.id) {
                        let mut tmp_node = bn2.clone();
                        tmp_node.labels = vec![label.clone()];
                        product_node.adj.push(tmp_node.clone());
                    }
                }
            }
        }
    }

    // F := { F1 x Q2, Q1 x F2 }
    for a in program.accepting_states.iter() {
        for adj in product_buchi.adj_list.iter() {
            if a.id == adj.id.0 {
                product_buchi.accepting_states.push(adj.clone());
            }
        }
    }

    for a in property.accepting_states.iter() {
        for adj in product_buchi.adj_list.iter() {
            if a.id == adj.id.1 {
                product_buchi.accepting_states.push(adj.clone());
            }
        }
    }

    // I := I1 x I2
    // if let Some(node) = product_buchi.get_node("INIT_INIT0") {
    if let Some(node) = product_buchi.get_node(&State::initial()) {
        product_buchi.init_states = vec![node];
        // TODO: This is probably not correct
        // } else if let Some(node) = product_buchi.get_node("INIT_INIT") {
    } else if let Some(node) = product_buchi.get_node(&State::initial()) {
        product_buchi.init_states = vec![node];
    } else {
        unreachable!("cannot find the INIT product state, this should not happend");
    }

    product_buchi
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gbuchi;
    use crate::ltl::automata::create_graph;

    fn lit(s: &str) -> LTLExpression {
        LTLExpression::lit(s)
    }

    #[test]
    fn it_should_extract_buchi_from_nodeset() {
        // p U q
        let ltl_expr = lit("p").U(lit("q"));

        let nodes_result = create_graph::<String>(ltl_expr.clone());
        let buchi = extract_buchi(nodes_result, ltl_expr);

        assert_eq!(4, buchi.states.len());
        assert_eq!(1, buchi.accepting_states.len());
        assert_eq!(2, buchi.init_states.len());
        assert_eq!(4, buchi.adj_list.len());
    }

    #[test]
    fn it_should_convert_gba_construct_from_ltl_into_ba() {
        // Fp1 U Gp2
        let ltl_expr = lit("p").U(lit("q"));

        let nodes_result = create_graph::<String>(ltl_expr.clone());
        let gbuchi = extract_buchi(nodes_result, ltl_expr);

        let buchi: Buchi<_> = gbuchi.into();

        assert_eq!(2, buchi.accepting_states.len());
    }

    #[test]
    fn it_should_convert_gba_into_ba() {
        let gbuchi = gbuchi! {
            INIT
                [lit("a")] => INIT
                [lit("b")] => s1
            s1
                [lit("a")] => INIT
                [lit("b")] => s1
            ===
            init = [INIT]
            accepting = [vec![INIT]]
            accepting = [vec![s1]]
        };

        let buchi: Buchi<_> = gbuchi.into();

        assert_eq!(1, buchi.accepting_states.len());
        assert_eq!(4, buchi.adj_list.len());
    }

    #[test]
    fn it_should_convert_gba_into_ba2() {
        let gbuchi = gbuchi! {
            INIT
               [lit("a")] => q3
               [lit("b")] => q2
            q2
                [lit("b")] => q2
                [lit("a")] => q3
            q3
                [lit("a")] => q3
                [lit("b")] => q2
            q4
                [lit("a")] => q3
                [lit("b")] => q2
            ===
            init = [INIT]
            accepting = [vec![INIT.clone(), q3]]
            accepting = [vec![INIT, q2]]
        };

        let buchi: Buchi<_> = gbuchi.into();
        assert_eq!(2, buchi.accepting_states.len());
        assert_eq!(1, buchi.init_states.len());
        assert_eq!(8, buchi.adj_list.len());
    }

    #[test]
    fn it_should_do_product_of_automata() {
        let mut buchi1: Buchi<String> = Buchi::new();
        let mut r1 = BuchiNode::new("INIT".into());
        r1.labels.push(lit("a"));
        r1.labels.push(lit("b"));
        let mut r2 = BuchiNode::new("r2".into());
        r2.labels.push(lit("a"));
        r2.labels.push(lit("b"));

        r1.adj.push(BuchiNode {
            id: "INIT".into(),
            labels: vec![lit("a")],
            adj: vec![],
        });
        r1.adj.push(BuchiNode {
            id: "r2".into(),
            labels: vec![lit("b")],
            adj: vec![],
        });

        r2.adj.push(BuchiNode {
            id: "r2".into(),
            labels: vec![lit("b")],
            adj: vec![],
        });
        r2.adj.push(BuchiNode {
            id: "INIT".into(),
            labels: vec![lit("a")],
            adj: vec![],
        });

        buchi1.accepting_states.push(r1.clone());
        buchi1.init_states.push(r1.clone());
        buchi1.adj_list = vec![r1, r2];

        let mut buchi2: Buchi<String> = Buchi::new();
        let mut q1 = BuchiNode::new("INIT".into());
        q1.labels.push(lit("a"));
        q1.labels.push(lit("b"));
        let mut q2 = BuchiNode::new("q2".into());
        q2.labels.push(lit("a"));
        q2.labels.push(lit("b"));

        q1.adj.push(BuchiNode {
            id: "INIT".into(),
            labels: vec![lit("b")],
            adj: vec![],
        });
        q1.adj.push(BuchiNode {
            id: "q2".into(),
            labels: vec![lit("a")],
            adj: vec![],
        });

        q2.adj.push(BuchiNode {
            id: "q2".into(),
            labels: vec![lit("a")],
            adj: vec![],
        });
        q2.adj.push(BuchiNode {
            id: "INIT".into(),
            labels: vec![lit("b")],
            adj: vec![],
        });

        buchi2.accepting_states.push(q1.clone());
        buchi2.init_states.push(q1.clone());
        buchi2.adj_list = vec![q1, q2];

        let buchi_product = product_automata(buchi1, buchi2);

        assert_eq!(4, buchi_product.adj_list.len());
        assert_eq!(1, buchi_product.init_states.len());
    }

    #[test]
    fn it_should_extract_buchi_from_nodeset2() {
        // p1 U (p2 U p3)
        let ltl_expr = lit("p1").U(lit("p2").U(lit("p3")));

        let nodes_result = create_graph::<String>(ltl_expr.clone());
        let buchi = extract_buchi(nodes_result, ltl_expr);

        assert_eq!(7, buchi.states.len());
    }

    #[test]
    fn it_should_extract_buchi_from_nodeset3() {
        // Fp1 U Gp2
        let ltl_expr = LTLExpression::F(Box::new(lit("p"))).U(LTLExpression::G(Box::new(lit("q"))));

        let simplified_expr = ltl_expr.rewrite();

        let nodes_result = create_graph::<String>(simplified_expr.clone());
        let buchi = extract_buchi(nodes_result, simplified_expr);

        assert_eq!(19, buchi.states.len());
    }

    #[test]
    fn it_should_extract_buchi_from_nodeset4() {
        // Fp1 U Gp2
        let ltl_expr = LTLExpression::G(Box::new(lit("p1"))).U(lit("p2"));

        let simplified_expr = ltl_expr.rewrite();

        let nodes_result = create_graph::<String>(simplified_expr.clone());
        let buchi = extract_buchi(nodes_result, simplified_expr);

        assert_eq!(9, buchi.states.len());
    }
}
