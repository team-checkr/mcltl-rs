use std::{
    collections::{BTreeSet, HashMap},
    fmt,
    hash::Hash,
    sync::{Arc, Mutex},
};

use ahash::{AHashMap, AHashSet};
use itertools::Itertools;

use crate::{
    ltl::expression::{Literal, NnfLtl},
    nodes::{NodeArena, NodeId, NodeMap, NodeSet, SmartNodeMap, SmartNodeSet},
    state::State,
};

pub trait AtomicPropertySet<AP: AtomicProperty>:
    AtomicProperty + std::fmt::Debug + Default + Clone + Ord + Hash + FromIterator<AP> + Extend<AP>
{
    fn set(&mut self, ap: AP);
    fn contains(&self, ap: &AP) -> bool;
    fn is_empty(&self) -> bool;
    fn iter<'a>(&'a self) -> impl Iterator<Item = &'a AP>
    where
        AP: 'a;
    fn union(&self, other: &Self) -> Self;
    fn intersection(&self, other: &Self) -> Self;
    fn is_disjoint(&self, other: &Self) -> bool;
}

impl<AP: AtomicProperty> AtomicPropertySet<AP> for BTreeSet<AP> {
    fn set(&mut self, ap: AP) {
        self.insert(ap);
    }
    fn contains(&self, ap: &AP) -> bool {
        self.contains(ap)
    }
    fn is_empty(&self) -> bool {
        self.is_empty()
    }
    fn iter<'a>(&'a self) -> impl Iterator<Item = &'a AP>
    where
        AP: 'a,
    {
        self.iter()
    }
    fn union(&self, other: &Self) -> Self {
        self.union(other).cloned().collect()
    }
    fn intersection(&self, other: &Self) -> Self {
        self.intersection(other).cloned().collect()
    }
    fn is_disjoint(&self, other: &Self) -> bool {
        self.is_disjoint(other)
    }
}
impl<AP: AtomicProperty> AtomicPropertySet<AP> for Vec<AP> {
    fn set(&mut self, ap: AP) {
        if !self.contains(&ap) {
            self.push(ap);
        }
    }
    fn contains(&self, ap: &AP) -> bool {
        self.iter().any(|x| x == ap)
    }
    fn is_empty(&self) -> bool {
        self.is_empty()
    }
    fn iter<'a>(&'a self) -> impl Iterator<Item = &'a AP>
    where
        AP: 'a,
    {
        self.as_slice().iter()
    }
    fn union(&self, other: &Self) -> Self {
        let mut new = self.clone();
        new.extend(other.iter().filter(|x| !self.contains(x)).cloned());
        new
    }
    fn intersection(&self, b: &Self) -> Self {
        if self.len() < b.len() {
            self.iter().filter(|x| b.contains(x)).cloned().collect()
        } else {
            b.iter().filter(|x| self.contains(x)).cloned().collect()
        }
    }
    fn is_disjoint(&self, b: &Self) -> bool {
        if self.len() < b.len() {
            self.iter().all(|x| !b.contains(x))
        } else {
            b.iter().all(|x| !self.contains(x))
        }
    }
}
impl<AP: AtomicProperty> AtomicProperty for BTreeSet<AP> {
    type Set = BTreeSet<Self>;
}

impl<AP: AtomicProperty> AtomicProperty for Vec<AP> {
    type Set = Vec<Self>;
}

pub trait AtomicProperty: Clone + Ord + Eq + Hash + fmt::Debug {
    type Set: AtomicPropertySet<Self>;
}

impl<L: AtomicProperty> AtomicProperty for NnfLtl<L> {
    type Set = BTreeSet<Self>;
}

impl AtomicProperty for Literal {
    type Set = BTreeSet<Self>;
}

impl AtomicProperty for String {
    type Set = BTreeSet<Self>;
}
impl<'a> AtomicProperty for &'a str {
    type Set = BTreeSet<Self>;
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Alphabet<AP> {
    symbols: Arc<BTreeSet<AP>>,
}
impl<AP> Alphabet<AP> {
    pub fn symbols(&self) -> impl Iterator<Item = &AP> {
        self.symbols.iter()
    }
    fn union(&self, other: &Self) -> Self
    where
        AP: Clone + Ord,
    {
        Self {
            symbols: Arc::new(
                self.symbols
                    .iter()
                    .chain(other.symbols.iter())
                    .cloned()
                    .collect(),
            ),
        }
    }
}

impl<AP: Ord> FromIterator<AP> for Alphabet<AP> {
    fn from_iter<T: IntoIterator<Item = AP>>(iter: T) -> Self {
        Self {
            symbols: Arc::new(iter.into_iter().collect()),
        }
    }
}

impl<AP: Ord, const N: usize> From<[AP; N]> for Alphabet<AP> {
    fn from(arr: [AP; N]) -> Self {
        Alphabet {
            symbols: Arc::new(arr.into()),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub enum Neighbors<AP: AtomicProperty> {
    Any,
    Just(BTreeSet<AP::Set>),
}
impl<AP: AtomicProperty> Neighbors<AP> {
    pub fn none() -> Self {
        Neighbors::Just(BTreeSet::new())
    }

    fn intersection(&self, other: &Self) -> Self {
        match (self, other) {
            (Neighbors::Just(a), Neighbors::Just(b)) => {
                Neighbors::Just(a.intersection(b).cloned().collect())
            }
            (Neighbors::Any, Neighbors::Any) => Neighbors::Any,
            (Neighbors::Any, just @ Neighbors::Just(_))
            | (just @ Neighbors::Just(_), Neighbors::Any) => just.clone(),
        }
    }

    fn is_disjoint(&self, other: &Self) -> bool {
        match (self, other) {
            (Neighbors::Just(a), Neighbors::Just(b)) => a.is_disjoint(b),
            _ => false,
        }
    }

    fn union(&self, other: &Self) -> Self {
        match (self, other) {
            (Neighbors::Just(a), Neighbors::Just(b)) => {
                Neighbors::Just(a.union(b).cloned().collect())
            }
            (Neighbors::Any, Neighbors::Any) => Neighbors::Any,
            (Neighbors::Any, Neighbors::Just(_)) | (Neighbors::Just(_), Neighbors::Any) => {
                Neighbors::Any
            }
        }
    }

    fn is_empty(&self) -> bool {
        match self {
            Neighbors::Just(set) => set.is_empty(),
            Neighbors::Any => false,
        }
    }

    pub fn any(_alphabet: &Alphabet<AP>) -> Neighbors<AP> {
        Neighbors::Any
    }
}
impl<AP: AtomicProperty> FromIterator<AP> for Neighbors<AP> {
    fn from_iter<T: IntoIterator<Item = AP>>(iter: T) -> Self {
        let mut set = AP::Set::default();
        for i in iter {
            set.set(i);
        }
        Neighbors::Just([set].into())
    }
}
impl<AP: AtomicProperty, const N: usize> From<[AP; N]> for Neighbors<AP> {
    fn from(arr: [AP; N]) -> Self {
        let mut set = AP::Set::default();
        for i in arr {
            set.set(i);
        }
        Neighbors::Just([set].into())
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub struct BuchiNode<S, AP: AtomicProperty> {
    id: S,
    adj: SmartNodeMap<BuchiNode<S, AP>, Neighbors<AP>>,
}

impl<S, AP: AtomicProperty> BuchiNode<S, AP> {
    pub fn new(id: S) -> Self {
        Self {
            id,
            adj: Default::default(),
        }
    }
}

impl<S, AP: AtomicProperty> fmt::Display for BuchiNode<S, AP>
where
    S: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buff = String::new();
        buff.push_str(&format!("{}id = {}\n", &buff, self.id));

        let adjs = self
            .adj
            .iter()
            .fold("".to_string(), |acc, a| acc + &format!("{},", a.0));
        buff.push_str(&format!("{}{}.adj = [{}]\n", &buff, self.id, adjs));

        write!(f, "{}", buff)
    }
}

///  generalized Büchi automaton (GBA) automaton.
/// The difference with the Büchi automaton is its accepting condition, i.e., a set of sets of states.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct GeneralBuchi<S, AP: AtomicProperty> {
    alphabet: Alphabet<AP>,
    nodes: NodeArena<BuchiNode<S, AP>>,
    accepting_states: Vec<NodeSet<BuchiNode<S, AP>>>,
    init_states: NodeSet<BuchiNode<S, AP>>,
}

impl<S: State, AP: AtomicProperty + fmt::Display> fmt::Display for GeneralBuchi<S, AP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "States:")?;
        for state in self.nodes.iter().sorted_by_key(|s| format!("{:?}", s.id)) {
            writeln!(f, " {:?} []", state.id)?;
            for (adj, adj_labels) in state.adj.iter() {
                writeln!(
                    f,
                    "   =[{}]=> {:?}",
                    match adj_labels {
                        Neighbors::Any => "*".to_string(),
                        Neighbors::Just(labels) =>
                            labels.iter().map(|ap| ap.iter().format(",")).join(" | "),
                    },
                    self.id(adj)
                )?;
            }
        }
        writeln!(
            f,
            "Initial: {:?}",
            self.init_states.iter().map(|s| self.id(s)).format(" ")
        )?;
        writeln!(
            f,
            "Accept:  [{}]",
            self.accepting_states
                .iter()
                .map(|s| format!("{{{:?}}}", s.iter().map(|s| self.id(s)).format(" ")))
                .format(", ")
        )?;
        Ok(())
    }
}

impl<S: State, AP: AtomicProperty> GeneralBuchi<S, AP> {
    pub fn new(alphabet: Alphabet<AP>) -> Self {
        Self {
            alphabet,
            nodes: Default::default(),
            accepting_states: Default::default(),
            init_states: Default::default(),
        }
    }

    pub fn push(&mut self, state: S) -> BuchiNodeId<S, AP> {
        self.get_node(&state)
            .unwrap_or_else(|| self.nodes.push(BuchiNode::new(state)))
    }

    pub fn get_node(&self, name: &S) -> Option<BuchiNodeId<S, AP>> {
        self.nodes
            .iter_with_ids()
            .find_map(|(id, adj)| if &adj.id == name { Some(id) } else { None })
    }

    pub fn id(&self, node_id: BuchiNodeId<S, AP>) -> &S {
        &self.nodes[node_id].id
    }

    pub fn nodes(&self) -> &NodeArena<BuchiNode<S, AP>> {
        &self.nodes
    }

    pub fn init_states(&self) -> &NodeSet<BuchiNode<S, AP>> {
        &self.init_states
    }

    pub fn accepting_states(&self) -> &[NodeSet<BuchiNode<S, AP>>] {
        &self.accepting_states
    }

    pub fn is_accepting_state(&self, node_id: BuchiNodeId<S, AP>) -> bool {
        self.accepting_states.iter().all(|s| s.contains(node_id))
    }

    pub fn adj(&self, node: BuchiNodeId<S, AP>) -> &SmartNodeMap<BuchiNode<S, AP>, Neighbors<AP>> {
        &self.nodes[node].adj
    }

    pub fn add_accepting_state(&mut self, node_ids: impl IntoIterator<Item = BuchiNodeId<S, AP>>) {
        self.accepting_states.push(node_ids.into_iter().collect());
    }

    pub fn add_init_state(&mut self, node_id: BuchiNodeId<S, AP>) {
        self.init_states.insert(node_id);
    }

    pub fn add_transition(
        &mut self,
        from: BuchiNodeId<S, AP>,
        to: BuchiNodeId<S, AP>,
        labels: Neighbors<AP>,
    ) {
        self.nodes[from].adj.insert(to, labels);
    }

    pub fn alphabet(&self) -> &Alphabet<AP> {
        &self.alphabet
    }
}

impl<S: State, AP: AtomicProperty> std::ops::Index<BuchiNodeId<S, AP>> for GeneralBuchi<S, AP> {
    type Output = BuchiNode<S, AP>;

    fn index(&self, index: BuchiNodeId<S, AP>) -> &Self::Output {
        &self.nodes[index]
    }
}

pub type BuchiNodeId<S, AP> = NodeId<BuchiNode<S, AP>>;

/// Büchi automaton is a type of ω-automaton, which extends
/// a finite automaton to infinite inputs.
#[derive(Debug, Clone)]
pub struct Buchi<S, AP: AtomicProperty> {
    alphabet: Alphabet<AP>,
    mapping: HashMap<S, BuchiNodeId<S, AP>>,
    nodes: NodeArena<BuchiNode<S, AP>>,
    accepting_states: SmartNodeSet<BuchiNode<S, AP>>,
    init_states: SmartNodeSet<BuchiNode<S, AP>>,
}

impl<S: State, AP: AtomicProperty> Buchi<S, AP> {
    pub fn new(alphabet: Alphabet<AP>) -> Self {
        Self {
            alphabet,
            nodes: Default::default(),
            mapping: Default::default(),
            accepting_states: Default::default(),
            init_states: Default::default(),
        }
    }

    pub fn push(&mut self, state: S) -> BuchiNodeId<S, AP> {
        self.get_node(&state).unwrap_or_else(|| {
            let id = self.nodes.push(BuchiNode::new(state.clone()));
            self.mapping.insert(state, id);
            id
        })
    }

    pub fn get_node(&self, name: &S) -> Option<BuchiNodeId<S, AP>> {
        self.mapping.get(name).copied()
        // self.nodes
        //     .iter_with_ids()
        //     .find_map(|(id, adj)| if &adj.id == name { Some(id) } else { None })
    }

    pub fn id(&self, node_id: BuchiNodeId<S, AP>) -> &S {
        &self.nodes[node_id].id
    }

    pub fn nodes(&self) -> &NodeArena<BuchiNode<S, AP>> {
        &self.nodes
    }

    pub fn init_states(&self) -> &SmartNodeSet<BuchiNode<S, AP>> {
        &self.init_states
    }

    pub fn accepting_states(&self) -> &SmartNodeSet<BuchiNode<S, AP>> {
        &self.accepting_states
    }

    pub fn adj(&self, node: BuchiNodeId<S, AP>) -> &SmartNodeMap<BuchiNode<S, AP>, Neighbors<AP>> {
        &self.nodes[node].adj
    }

    pub fn add_accepting_state(&mut self, node_id: BuchiNodeId<S, AP>) {
        self.accepting_states.insert(node_id);
    }

    pub fn add_init_state(&mut self, node_id: BuchiNodeId<S, AP>) {
        self.init_states.insert(node_id);
    }

    pub fn add_transition(
        &mut self,
        from: BuchiNodeId<S, AP>,
        to: BuchiNodeId<S, AP>,
        labels: Neighbors<AP>,
    ) {
        self.nodes[from].adj.insert(to, labels);
    }

    pub fn add_necessary_self_loops(&mut self) {
        for state in self.nodes().ids() {
            if self.adj(state).is_empty() {
                let neighbors = self
                    .nodes()
                    .ids()
                    .flat_map(|id| self.adj(id).iter())
                    .filter_map(|(id, adj)| if id == state { Some(adj) } else { None })
                    .fold(Neighbors::none(), |a, b| a.union(b));

                // self.add_transition(state, state, Neighbors::any(self.alphabet()));
                self.add_transition(state, state, neighbors);
            }
        }
    }

    pub fn pruned(&self) -> Buchi<S, AP> {
        let mut pruned: Buchi<S, AP> = Buchi::new(self.alphabet().clone());
        let mut stack = self.init_states().iter().collect_vec();
        let mut visited = NodeSet::default();
        let mut mapping: HashMap<BuchiNodeId<S, AP>, BuchiNodeId<S, AP>> = HashMap::default();

        while let Some(state) = stack.pop() {
            visited.insert(state);

            let new_state = *mapping
                .entry(state)
                .or_insert_with(|| pruned.push(self.id(state).clone()));

            for (adj, labels) in self.adj(state).iter() {
                let new_adj = *mapping
                    .entry(adj)
                    .or_insert_with(|| pruned.push(self.id(adj).clone()));
                pruned.add_transition(new_state, new_adj, labels.clone());
                if !visited.insert(adj) {
                    stack.push(adj);
                }
            }
        }

        for state in self.init_states().iter() {
            pruned.add_init_state(mapping[&state]);
        }

        for state in self.accepting_states().iter() {
            if let Some(id) = mapping.get(&state) {
                pruned.add_accepting_state(*id);
            }
        }

        pruned
    }

    pub fn alphabet(&self) -> &Alphabet<AP> {
        &self.alphabet
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
    pub fn product<'a, 'b, T: State>(
        &'a self,
        other: &'b Buchi<T, AP>,
    ) -> ProductBuchi<'a, 'b, S, T, AP> {
        ProductBuchi::new(self, other)
    }
}

pub struct ProductBuchi<'a, 'b, S, T, AP: AtomicProperty> {
    a: &'a Buchi<S, AP>,
    b: &'b Buchi<T, AP>,
    adj_ids_cache: Mutex<
        AHashMap<
            ProductBuchiNodeId<S, T, AP>,
            smallvec::SmallVec<[ProductBuchiNodeId<S, T, AP>; 16]>,
        >,
    >,
}

pub type ProductBuchiNodeId<S, T, AP> = (BuchiNodeId<S, AP>, BuchiNodeId<T, AP>);

pub struct ProductBuchiNodeSet<S, T, AP: AtomicProperty>(
    NodeMap<BuchiNode<S, AP>, SmartNodeSet<BuchiNode<T, AP>>>,
);

impl<S, T: State, AP: AtomicProperty> Default for ProductBuchiNodeSet<S, T, AP> {
    fn default() -> Self {
        Self(NodeMap::new())
    }
}

impl<S, T: State, AP: AtomicProperty> ProductBuchiNodeSet<S, T, AP> {
    pub fn clear(&mut self) {
        self.0.clear();
    }
    pub fn insert(&mut self, node: ProductBuchiNodeId<S, T, AP>) {
        if self.0.contains_key(node.0) {
            self.0[node.0].insert(node.1);
        } else {
            let mut set = SmartNodeSet::new();
            set.insert(node.1);
            self.0.insert(node.0, set);
        }
    }
    pub fn contains(&self, node: ProductBuchiNodeId<S, T, AP>) -> bool {
        self.0.get(node.0).map_or(false, |set| set.contains(node.1))
    }
}

impl<'a, 'b, S, T, AP> ProductBuchi<'a, 'b, S, T, AP>
where
    S: State,
    T: State,
    AP: AtomicProperty,
{
    pub fn new(a: &'a Buchi<S, AP>, b: &'b Buchi<T, AP>) -> Self {
        Self {
            a,
            b,
            adj_ids_cache: Default::default(),
        }
    }

    #[inline(never)]
    pub fn init_states(&self) -> impl Iterator<Item = ProductBuchiNodeId<S, T, AP>> + '_ {
        Itertools::cartesian_product(self.a.init_states().iter(), self.b.init_states().iter())
    }

    #[inline(never)]
    pub fn accepting_states(&self) -> impl Iterator<Item = ProductBuchiNodeId<S, T, AP>> + '_ {
        Itertools::cartesian_product(
            self.a.accepting_states().iter(),
            self.b.accepting_states().iter(),
        )
    }

    pub fn adj(
        &self,
        (a, b): ProductBuchiNodeId<S, T, AP>,
    ) -> impl Iterator<Item = (ProductBuchiNodeId<S, T, AP>, Neighbors<AP>)> + '_ {
        Itertools::cartesian_product(self.a.adj(a).iter(), self.b.adj(b).iter()).filter_map(
            move |((a, a_labels), (b, b_labels))| {
                let dst = (a, b);
                let dst_labels = a_labels.intersection(b_labels);
                if dst_labels.is_empty() {
                    None
                } else {
                    Some((dst, dst_labels))
                }
            },
        )
    }

    pub fn adj_ids(
        &self,
        (a, b): ProductBuchiNodeId<S, T, AP>,
    ) -> impl Iterator<Item = ProductBuchiNodeId<S, T, AP>> {
        self.adj_ids_cache
            .lock()
            .unwrap()
            .entry((a, b))
            .or_insert_with(|| {
                Itertools::cartesian_product(self.a.adj(a).iter(), self.b.adj(b).iter())
                    .filter_map(move |((a, a_labels), (b, b_labels))| {
                        let dst = (a, b);
                        // DO NOT DELETE THIS MAKEs IT FASTER!@!!!!!
                        // let dst_labels = a_labels.intersection(b_labels);
                        // assert_eq!(dst_labels.is_empty(), a_labels.is_disjoint(b_labels));
                        if a_labels.is_disjoint(b_labels) {
                            None
                        } else {
                            Some(dst)
                        }
                    })
                    .collect()
            })
            .clone()
            .into_iter()
    }

    pub fn nodes(&self) -> AHashSet<ProductBuchiNodeId<S, T, AP>> {
        let mut nodes = AHashSet::default();

        let mut queue = self.init_states().collect_vec();

        while let Some(node) = queue.pop() {
            nodes.insert(node);
            for adj in self.adj_ids(node) {
                if !nodes.contains(&adj) {
                    queue.push(adj);
                }
            }
        }

        nodes
    }
}

impl<S: State, T: State, AP: AtomicProperty + fmt::Display> fmt::Display
    for ProductBuchi<'_, '_, S, T, AP>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let fmt = |(a, b): ProductBuchiNodeId<S, T, AP>| {
            format!("({:?}, {:?})", self.a.id(a), self.b.id(b))
        };

        writeln!(f, "States:")?;
        for &state in self.nodes().iter().sorted_by_key(|s| fmt(**s)) {
            writeln!(f, " {} []", fmt(state))?;
            for (adj, labels) in self.adj(state) {
                writeln!(
                    f,
                    "   =[{}]=> {}",
                    match labels {
                        Neighbors::Any => "*".to_string(),
                        Neighbors::Just(labels) =>
                            labels.iter().map(|ap| ap.iter().format(",")).join(" | "),
                    },
                    fmt(adj)
                )?;
            }
        }
        writeln!(f, "Initial: {}", self.init_states().map(fmt).format(" "))?;
        writeln!(
            f,
            "Accept:  [{}]",
            self.accepting_states()
                .map(fmt)
                .sorted()
                .dedup()
                .format(", ")
        )?;
        Ok(())
    }
}

impl<S: State, AP: AtomicProperty> std::ops::Index<BuchiNodeId<S, AP>> for Buchi<S, AP> {
    type Output = BuchiNode<S, AP>;

    fn index(&self, index: BuchiNodeId<S, AP>) -> &Self::Output {
        &self.nodes[index]
    }
}

impl<S: State, AP: AtomicProperty + fmt::Display> fmt::Display for Buchi<S, AP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "States:")?;
        for state in self
            .nodes
            .ids()
            .sorted_by_key(|s| format!("{:?}", self.id(*s)))
        {
            writeln!(f, " {:?} []", self.id(state))?;
            for (adj, labels) in self.adj(state).iter() {
                writeln!(
                    f,
                    "   =[{}]=> {:?}",
                    match labels {
                        Neighbors::Any => "*".to_string(),
                        Neighbors::Just(labels) =>
                            labels.iter().map(|ap| ap.iter().format(",")).join(" | "),
                    },
                    self.id(adj)
                )?;
            }
        }
        writeln!(
            f,
            "Initial: {:?}",
            self.init_states.iter().map(|s| self.id(s)).format(" ")
        )?;
        writeln!(
            f,
            "Accept:  [{}]",
            self.accepting_states
                .iter()
                .map(|s| format!("{:?}", self.id(s)))
                .sorted()
                .dedup()
                .format(", ")
        )?;
        Ok(())
    }
}

/// Multiple sets of states in acceptance condition can be translated into one set of states
/// by an automata construction, which is known as "counting construction".
/// Let's say `A = (Q, Σ, ∆, q0, {F1,...,Fn})` is a GBA, where `F1,...,Fn` are sets of accepting states
/// then the equivalent Büchi automaton is `A' = (Q', Σ, ∆',q'0,F')`, where
/// * `Q' = Q × {1,...,n}`
/// * `q'0 = ( q0,1 )`
/// * `∆' = { ( (q,i), a, (q',j) ) | (q,a,q') ∈ ∆ and if q ∈ Fi then j=((i+1) mod n) else j=i }`
/// * `F'=F1× {1}`
impl<S: State, AP: AtomicProperty> GeneralBuchi<S, AP> {
    pub fn to_buchi(&self) -> Buchi<(S, usize), AP> {
        let mut ba: Buchi<(S, usize), AP> = Buchi::new(self.alphabet().clone());

        if self.accepting_states.is_empty() {
            // tracing::debug!(%self, "no accepting states found, adding all states as accepting states");
            let mut gb = self.clone();
            gb.add_accepting_state(gb.nodes().ids());
            return gb.to_buchi();
        }
        // let F = {F0,...,Fk-1}

        // Q' = Q × 0..k
        for (k, _) in self.accepting_states().iter().enumerate() {
            for n in self.nodes().ids() {
                ba.push((self.id(n).clone(), k));
            }
        }

        // Q'0 = Q0 × {0} = { (q0,0) | q0 ∈ Q0 }
        for n in self.init_states().iter() {
            let init = ba.push((self.id(n).clone(), 0));
            ba.add_init_state(init);
        }

        // F' = F1 × {0} = { (qF,0) | qF ∈ F1 }
        for f in self.accepting_states()[0].iter() {
            let accepting = ba.push((self.id(f).clone(), 0));
            ba.add_accepting_state(accepting);
        }

        // ∆'((q, i), A) = if q ∈ Fi then { (q', i+1) | q' ∈ ∆(q, A) } else { (q', i) | q' ∈ ∆(q, A) }
        for (i, f) in self.accepting_states().iter().enumerate() {
            for n in self.nodes().ids() {
                for (adj, adj_labels) in self.adj(n).iter() {
                    let j = if f.iter().any(|n| self.id(n) == self.id(n)) {
                        (i + 1) % self.accepting_states.len()
                    } else {
                        i
                    };
                    let new = ba.push((self.id(adj).clone(), j));
                    ba.add_transition(
                        ba.get_node(&(self.id(n).clone(), i)).unwrap(),
                        new,
                        adj_labels.clone(),
                    );
                }
            }
        }

        ba
    }
}

#[cfg(test)]
mod tests;
