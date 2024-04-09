use std::{
    hash::Hash,
    sync::atomic::{AtomicUsize, Ordering},
};

pub trait State: Clone + PartialEq + Eq + Hash {
    fn initial() -> Self;
    fn is_initial(&self) -> bool {
        self == &Self::initial()
    }
    fn new_name() -> Self;
    fn name(&self) -> String;
}

static NODE_NAME_COUNTER: AtomicUsize = AtomicUsize::new(1);

impl State for String {
    fn initial() -> Self {
        const INIT_NODE_ID: &str = "INIT";
        INIT_NODE_ID.to_string()
    }
    fn new_name() -> Self {
        let counter = NODE_NAME_COUNTER.fetch_add(1, Ordering::SeqCst);
        format!("n{counter}")
    }
    fn name(&self) -> String {
        self.clone()
    }
}

impl State for usize {
    fn initial() -> Self {
        0
    }
    fn new_name() -> Self {
        NODE_NAME_COUNTER.fetch_add(1, Ordering::SeqCst)
    }
    fn name(&self) -> String {
        self.to_string()
    }
}

impl<A, B> State for (A, B)
where
    A: State,
    B: State,
{
    fn initial() -> Self {
        (A::initial(), B::initial())
    }
    fn new_name() -> Self {
        (A::new_name(), B::new_name())
    }
    fn name(&self) -> String {
        format!("({}, {})", self.0.name(), self.1.name())
    }
}
