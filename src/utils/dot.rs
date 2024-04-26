use core::fmt;

use crate::{
    buchi::{AtomicProperty, AtomicPropertySet, Buchi, GeneralBuchi, Neighbors},
    state::State,
};
use dot;
use itertools::Itertools;

type Node = String;
type Edge<'a, AP> = (String, Neighbors<AP>, String);

const Q_INIT: &str = "qInitial";

impl<S: State, AP: AtomicProperty + fmt::Display> Buchi<S, AP> {
    /// Produce the DOT of a Büchi automaton
    pub fn dot(&self) -> String {
        let mut buf = Vec::new();
        dot::render(self, &mut buf).unwrap();
        String::from_utf8(buf).unwrap()
    }
}

impl<'a, S: State, AP: AtomicProperty + fmt::Display> dot::Labeller<'a, Node, Edge<'a, AP>>
    for Buchi<S, AP>
{
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new("buchi").unwrap()
    }

    fn node_id(&'a self, n: &Node) -> dot::Id<'a> {
        static COUNTER: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        static CACHE: once_cell::sync::Lazy<
            std::sync::Arc<std::sync::Mutex<std::collections::HashMap<String, usize>>>,
        > = once_cell::sync::Lazy::new(Default::default);

        let name = n.to_string();
        let id = *CACHE
            .lock()
            .unwrap()
            .entry(name)
            .or_insert_with(|| COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst));
        dot::Id::new(format!("n{id}")).unwrap()
    }

    fn node_label<'b>(&'b self, n: &Node) -> dot::LabelText<'b> {
        dot::LabelText::LabelStr(n.to_string().into())
    }
    fn edge_label<'b>(&'b self, e: &Edge<AP>) -> dot::LabelText<'b> {
        if e.0 == Q_INIT {
            return dot::LabelText::LabelStr("".into());
        }

        match &e.1 {
            Neighbors::Any => dot::LabelText::LabelStr("*".into()),
            Neighbors::Just(props) => {
                let tmp = props
                    .iter()
                    .map(|ap| {
                        ap.iter()
                            .map(|s| s.to_string())
                            .chain(
                                self.alphabet()
                                    .symbols()
                                    .filter(|s| !ap.contains(s))
                                    .map(|s| format!("~{s}")),
                            )
                            .format(",")
                    })
                    .join(" | ");
                let tmp2 = tmp.replace('¬', "~");
                let comma_separated = tmp2.replace('⊥', "F");

                dot::LabelText::LabelStr(comma_separated.into())
            }
        }
    }

    fn node_shape<'b>(&'b self, n: &Node) -> Option<dot::LabelText<'b>> {
        let is_an_accepting_state = self
            .accepting_states()
            .iter()
            .any(|bns| self.id(bns).name() == *n);

        if is_an_accepting_state {
            Some(dot::LabelText::LabelStr("doublecircle".into()))
        } else if n == Q_INIT {
            Some(dot::LabelText::LabelStr("point".into()))
        } else {
            None
        }
    }
}

impl<'a, S: State, AP: AtomicProperty + fmt::Display> dot::GraphWalk<'a, Node, Edge<'a, AP>>
    for Buchi<S, AP>
{
    fn nodes(&self) -> dot::Nodes<'a, Node> {
        let mut adjs: Vec<Node> = self.nodes().ids().map(|adj| self.id(adj).name()).collect();
        adjs.push(Q_INIT.to_string());

        adjs.into()
    }

    fn edges(&'a self) -> dot::Edges<'a, Edge<'a, AP>> {
        let mut edges = self
            .init_states()
            .iter()
            .map(|id| (Q_INIT.to_string(), [].into(), self.id(id).name()))
            .collect_vec();
        for source in self.nodes().ids() {
            for (target, target_labels) in self.adj(source).iter() {
                edges.push((
                    self.id(source).name(),
                    target_labels.clone(),
                    self.id(target).name(),
                ));
            }
        }

        edges.into()
    }
    fn source(&self, e: &Edge<AP>) -> Node {
        e.0.clone()
    }
    fn target(&self, e: &Edge<AP>) -> Node {
        e.2.clone()
    }
}

impl<S: State, AP: AtomicProperty + fmt::Display> GeneralBuchi<S, AP> {
    /// Produce the DOT of a Generalized Büchi automaton
    pub fn dot(&self) -> String {
        let mut buf = Vec::new();
        dot::render(self, &mut buf).unwrap();
        String::from_utf8(buf).unwrap()
    }
}

impl<'a, S: State, AP: AtomicProperty + fmt::Display> dot::Labeller<'a, Node, Edge<'a, AP>>
    for GeneralBuchi<S, AP>
{
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new("gbuchi").unwrap()
    }

    fn node_id(&'a self, n: &Node) -> dot::Id<'a> {
        dot::Id::new(n.to_string()).unwrap()
    }

    fn node_label<'b>(&'b self, n: &Node) -> dot::LabelText<'b> {
        dot::LabelText::LabelStr(n.to_string().into())
    }
    fn edge_label<'b>(&'b self, e: &Edge<AP>) -> dot::LabelText<'b> {
        if e.0 == Q_INIT {
            return dot::LabelText::LabelStr("".into());
        }

        match &e.1 {
            Neighbors::Any => dot::LabelText::LabelStr("*".into()),
            Neighbors::Just(props) => {
                let tmp = props
                    .iter()
                    .map(|ap| {
                        ap.iter()
                            .map(|s| s.to_string())
                            .chain(
                                self.alphabet()
                                    .symbols()
                                    .filter(|s| !ap.contains(s))
                                    .map(|s| format!("~{s}")),
                            )
                            .format(",")
                    })
                    .join(" | ");
                let tmp2 = tmp.replace('¬', "~");
                let comma_separated = tmp2.replace('⊥', "F");

                dot::LabelText::LabelStr(comma_separated.into())
            }
        }
    }

    fn node_shape<'b>(&'b self, n: &Node) -> Option<dot::LabelText<'b>> {
        let is_an_accepting_state =
            if let Some(node) = self.nodes().ids().find(|node| self.id(*node).name() == *n) {
                self.is_accepting_state(node)
            } else {
                false
            };

        if is_an_accepting_state {
            Some(dot::LabelText::LabelStr("doublecircle".into()))
        } else if n == Q_INIT {
            Some(dot::LabelText::LabelStr("point".into()))
        } else {
            None
        }
    }
}

impl<'a, S: State, AP: AtomicProperty + fmt::Display> dot::GraphWalk<'a, Node, Edge<'a, AP>>
    for GeneralBuchi<S, AP>
{
    fn nodes(&self) -> dot::Nodes<'a, Node> {
        let mut adjs: Vec<Node> = self.nodes().ids().map(|adj| self.id(adj).name()).collect();
        adjs.push(Q_INIT.to_string());

        adjs.into()
    }

    fn edges(&'a self) -> dot::Edges<'a, Edge<'a, AP>> {
        let mut edges = self
            .init_states()
            .iter()
            .map(|id| (Q_INIT.to_string(), [].into(), self.id(id).name()))
            .collect_vec();
        for source in self.nodes().ids() {
            for (target, target_labels) in self.adj(source).iter() {
                edges.push((
                    self.id(source).name(),
                    target_labels.clone(),
                    self.id(target).name(),
                ));
            }
        }

        edges.into()
    }

    fn source(&self, e: &Edge<AP>) -> Node {
        e.0.clone()
    }
    fn target(&self, e: &Edge<AP>) -> Node {
        e.2.clone()
    }
}
