pub mod dot;

#[macro_export]
macro_rules! buchi{
    (
        $(
            $src: ident
                $([$( $ltl:expr ),*] => $dest: ident)*
        )*
        ===
        init = [$( $init:ident ),*]
        accepting = [$( $accepting_state:ident ),*]
    ) => {{
        let mut graph = Buchi::new();
        $(
            #[allow(unused_mut, non_snake_case)]
            let mut $src = BuchiNode::new(stringify!($src).to_string());
            $(
                $src.adj.push(
                    BuchiNode {
                        id: stringify!($dest).into(),
                        labels: vec![$($ltl),*],
                        adj: vec![],
                    }
                );
            )*

            graph.adj_list.push($src.clone());
        )*

        $(graph.init_states.push($init.clone());)*
        $(graph.accepting_states.push($accepting_state.clone());)*

        graph
    }};
}

#[macro_export]
macro_rules! gbuchi{
    (
        $(
            $src: ident
                $([$ltl:expr] => $dest: ident)*
        )*
        ===
        init = [$( $init:ident ),*]
        $(accepting = [$( $accepting_states:expr ),*])*
    ) => {{
        let mut graph = GeneralBuchi::new();
        $(
            #[allow(unused_mut, non_snake_case)]
            let mut $src = BuchiNode::new(stringify!($src).to_string());
            $(
                $src.adj.push(
                    BuchiNode {
                        id: stringify!($dest).into(),
                        labels: vec![$ltl],
                        adj: vec![],
                    }
                );
            )*

            graph.adj_list.push($src.clone());
        )*

        $(graph.init_states.push($init.clone());)*
        $($(graph.accepting_states.push($accepting_states.clone());)*)*

        graph
    }};
}

#[macro_export]
macro_rules! kripke{
    (
        $(
            $world:ident = [$( $prop:expr),*]
        )*
        ===
        $(
            $src:ident R $dst:ident
        )*
        ===
        init = [$( $init:ident ),*]
    ) => {{
        let mut kripke = KripkeStructure::new(vec![]);

        $(
            let mut $world = World {
                id: stringify!($world).into(),
                assignement: std::collections::HashMap::new(),
            };
            $(
                $world.assignement.insert($prop.0.into(), $prop.1);
            )*

            kripke.add_world($world.clone());
        )*

        $(
            kripke.add_relation($src.clone(), $dst.clone());
        )*

        kripke.inits = vec![$($init.id.clone(),)*];

        kripke
    }};
}
