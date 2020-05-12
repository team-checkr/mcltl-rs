use crate::{buchi::Buchi, ltl::expression::LTLExpression};
use dot;
use std::io::{Result as IOResult};

type Node = String;
type Edge<'a> = (String, LTLExpression, String);

pub fn render_to(buchi: Buchi, file_name: &str) -> IOResult<()> {
    let mut f = std::fs::File::create(file_name).unwrap();
    dot::render(&buchi, &mut f)
}

impl<'a> dot::Labeller<'a, Node, Edge<'a>> for Buchi {
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new("buchi").unwrap()
    }

    fn node_id(&'a self, n: &Node) -> dot::Id<'a> {
        dot::Id::new(format!("{}", n)).unwrap()
    }

    fn node_label<'b>(&'b self, n: &Node) -> dot::LabelText<'b> {
        dot::LabelText::LabelStr(format!("{}", n).into())
    }
    fn edge_label<'b>(&'b self, e: &Edge) -> dot::LabelText<'b> {
        dot::LabelText::LabelStr(format!("{}", e.1).into())
    }

    fn node_color<'b>(&'b self, n: &Node) -> Option<dot::LabelText<'b>> {
        if self.init_states.iter().any(|bn| bn.id == *n) {
            Some(dot::LabelText::LabelStr("yellow".into()))

        } else {
            Some(dot::LabelText::LabelStr("black".into()))
        }
    }

    fn node_shape<'b>(&'b self, n: &Node) -> Option<dot::LabelText<'b>> {
        let is_an_accepting_state = self
            .accepting_states
            .iter()
            .any(|bns| bns.id == *n);


        if is_an_accepting_state {
            Some(dot::LabelText::LabelStr("doublecircle".into()))
        }
        //} else if is_an_init_state {
        //    Some(dot::LabelText::LabelStr("point".into()))
        //}
        else {
            None
        }
    }
}

impl<'a> dot::GraphWalk<'a, Node, Edge<'a>> for Buchi {
    fn nodes(&self) -> dot::Nodes<'a, Node> {
        self.adj_list.iter().map(|adj| adj.id.clone()).collect()
    }

    fn edges(&'a self) -> dot::Edges<'a, Edge<'a>> {
        let mut edges = vec![];
        for source in self.adj_list.iter() {
            for target in source.adj.iter() {
                let label = target.labels.get(0).unwrap_or(&LTLExpression::True).clone();
                edges.push((source.id.clone(), label, target.id.clone()));
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