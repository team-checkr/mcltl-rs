use crate::{
    buchi::{Buchi, GeneralBuchi},
    ltl::expression::LTLExpression,
    state::State,
};
use dot;
use itertools::Itertools;

type Node = String;
type Edge<'a> = (String, Vec<LTLExpression>, String);

impl<S: State> Buchi<S> {
    /// Produce the DOT of a Büchi automaton
    pub fn dot(&self) -> String {
        let mut buf = Vec::new();
        dot::render(self, &mut buf).unwrap();
        String::from_utf8(buf).unwrap()
    }
}

impl<'a, S: State> dot::Labeller<'a, Node, Edge<'a>> for Buchi<S> {
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new("buchi").unwrap()
    }

    fn node_id(&'a self, n: &Node) -> dot::Id<'a> {
        dot::Id::new(n.to_string()).unwrap()
    }

    fn node_label<'b>(&'b self, n: &Node) -> dot::LabelText<'b> {
        dot::LabelText::LabelStr(n.to_string().into())
    }
    fn edge_label<'b>(&'b self, e: &Edge) -> dot::LabelText<'b> {
        let tmp = e.1.iter().join(", ");
        let tmp2 = tmp.replace('¬', "~");
        let comma_separated = tmp2.replace('⊥', "F");

        dot::LabelText::LabelStr(comma_separated.into())
    }

    fn node_shape<'b>(&'b self, n: &Node) -> Option<dot::LabelText<'b>> {
        let is_an_accepting_state = self.accepting_states.iter().any(|bns| bns.id.name() == *n);

        if is_an_accepting_state {
            Some(dot::LabelText::LabelStr("doublecircle".into()))
        } else if n.starts_with("qi") {
            Some(dot::LabelText::LabelStr("point".into()))
        } else {
            None
        }
    }
}

impl<'a, S: State> dot::GraphWalk<'a, Node, Edge<'a>> for Buchi<S> {
    fn nodes(&self) -> dot::Nodes<'a, Node> {
        let mut adjs: Vec<Node> = self.adj_list.iter().map(|adj| adj.id.name()).collect();

        self.init_states
            .iter()
            .for_each(|i| adjs.push(format!("qi_{}", i.id.name())));

        adjs.into()
    }

    fn edges(&'a self) -> dot::Edges<'a, Edge<'a>> {
        let mut edges = vec![];
        for source in self.adj_list.iter() {
            for target in source.adj.iter() {
                edges.push((source.id.name(), target.labels.clone(), target.id.name()));

                if self.init_states.iter().any(|n| n.id == source.id) {
                    edges.push((format!("qi_{}", source.id.name()), vec![], source.id.name()));
                }
            }
        }

        edges.into()
    }
    fn source(&self, e: &Edge) -> Node {
        e.0.clone()
    }
    fn target(&self, e: &Edge) -> Node {
        e.2.clone()
    }
}

impl<S: State> GeneralBuchi<S> {
    /// Produce the DOT of a Generalized Büchi automaton
    pub fn dot(&self) -> String {
        let mut buf = Vec::new();
        dot::render(self, &mut buf).unwrap();
        String::from_utf8(buf).unwrap()
    }
}

impl<'a, S: State> dot::Labeller<'a, Node, Edge<'a>> for GeneralBuchi<S> {
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new("gbuchi").unwrap()
    }

    fn node_id(&'a self, n: &Node) -> dot::Id<'a> {
        dot::Id::new(n.to_string()).unwrap()
    }

    fn node_label<'b>(&'b self, n: &Node) -> dot::LabelText<'b> {
        dot::LabelText::LabelStr(n.to_string().into())
    }
    fn edge_label<'b>(&'b self, e: &Edge) -> dot::LabelText<'b> {
        let tmp = e.1.iter().join(", ");
        let tmp2 = tmp.replace('¬', "~");
        let comma_separated = tmp2.replace('⊥', "F");

        dot::LabelText::LabelStr(comma_separated.into())
    }

    fn node_shape<'b>(&'b self, n: &Node) -> Option<dot::LabelText<'b>> {
        let is_an_accepting_state = self
            .accepting_states
            .iter()
            .any(|bns| bns.iter().any(|m| n == &m.id.name()));

        if is_an_accepting_state {
            Some(dot::LabelText::LabelStr("doublecircle".into()))
        } else if n.starts_with("qi_") {
            Some(dot::LabelText::LabelStr("point".into()))
        } else {
            None
        }
    }
}

impl<'a, S: State> dot::GraphWalk<'a, Node, Edge<'a>> for GeneralBuchi<S> {
    fn nodes(&self) -> dot::Nodes<'a, Node> {
        let mut adjs: Vec<Node> = self.adj_list.iter().map(|adj| adj.id.name()).collect();

        self.init_states
            .iter()
            .for_each(|i| adjs.push(format!("qi_{}", i.id.name())));

        adjs.into()
    }

    fn edges(&'a self) -> dot::Edges<'a, Edge<'a>> {
        let mut edges = vec![];
        for source in self.adj_list.iter() {
            for target in source.adj.iter() {
                edges.push((source.id.name(), target.labels.clone(), target.id.name()));

                if self.init_states.iter().any(|n| n.id == source.id) {
                    edges.push((format!("qi_{}", source.id.name()), vec![], source.id.name()));
                }
            }
        }

        edges.into()
    }

    fn source(&self, e: &Edge) -> Node {
        e.0.clone()
    }
    fn target(&self, e: &Edge) -> Node {
        e.2.clone()
    }
}
