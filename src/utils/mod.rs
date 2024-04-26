pub mod dot;

#[macro_export]
macro_rules! buchi {
    (
        $(
            $src: ident
                $([$($ltl:ident),*] => $dest: ident)*
        )*
        ===
        init = [$( $init:ident ),*]
        accepting = [$( $accepting_state:ident ),*]
    ) => {{
        let alphabet = [$($($(Literal::from(stringify!($ltl)),)*)*)*].into_iter().collect();
        let mut graph = Buchi::new(alphabet);
        $(
            #[allow(unused, unused_mut, non_snake_case)]
            let mut $src = graph.push(stringify!($src).to_string());
            $(
                let dest = graph.push(stringify!($dest).into());
                graph.add_transition($src, dest, [$(Literal::from(stringify!($ltl))),*].into());
            )*
        )*

        $(graph.add_init_state($init);)*
        $(graph.add_accepting_state($accepting_state);)*

        graph
    }};
}

#[macro_export]
macro_rules! gbuchi {
    (
        $(
            $src: ident
                $([$ltl:ident] => $dest: ident)*
        )*
        ===
        init = [$( $init:ident ),*]
        $(accepting = [$( $accepting_states:expr ),*])*
    ) => {{
        let alphabet = [$($(Literal::from(stringify!($ltl)),)*)*].into_iter().collect();
        let mut graph = GeneralBuchi::new(alphabet);
        $(
            #[allow(unused_mut, non_snake_case)]
            let mut $src = graph.push(stringify!($src).to_string());
            $(
                let dest = graph.push(stringify!($dest).into());
                graph.add_transition($src, dest, [stringify!($ltl).into()].into());
            )*
        )*

        $(graph.add_init_state($init);)*
        $($(graph.add_accepting_state($accepting_states.into_iter());)*)*

        graph
    }};
}

#[macro_export]
macro_rules! kripke {
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
        let mut kripke = KripkeStructure::<String, Literal>::new(vec![]);

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
