use std::fmt;
use std::{convert::TryFrom, ops::Not};

use super::parser::{lexer::Lexer, parser};

#[derive(Debug, Eq, PartialEq)]
pub enum LTLExpressionError {
    True,
    False,
    // In case an invalid variable in references from the expression.
    InvalidVariable,
    // In case of an invalid operation.
    InvalidOperation,
}

/// The inductive set of LTL formulas over AP
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum LTLExpression {
    True,
    False,
    Literal(String),
    Not(Box<LTLExpression>),
    And(Box<LTLExpression>, Box<LTLExpression>),
    Or(Box<LTLExpression>, Box<LTLExpression>),
    G(Box<LTLExpression>),
    F(Box<LTLExpression>),
    U(Box<LTLExpression>, Box<LTLExpression>),
    R(Box<LTLExpression>, Box<LTLExpression>),
    V(Box<LTLExpression>, Box<LTLExpression>),
}

impl TryFrom<&str> for LTLExpression {
    type Error = &'static str;

    fn try_from(formula: &str) -> Result<Self, Self::Error> {
        let lexer = Lexer::new(formula);
        parser::parse(lexer).map(|span| span.expr).map_err(|e| e.1)
    }
}

impl fmt::Display for LTLExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LTLExpression::True => write!(f, "T"),
            LTLExpression::False => write!(f, "⊥"),
            LTLExpression::Literal(l) => write!(f, "{}", l),
            LTLExpression::Not(e) => write!(f, "¬{}", e),
            LTLExpression::And(p, q) => write!(f, "{} ∧ {}", p, q),
            LTLExpression::Or(p, q) => write!(f, "{} ∨ {}", p, q),
            LTLExpression::G(e) => write!(f, "G ({})", e),
            LTLExpression::F(e) => write!(f, "F ({})", e),
            LTLExpression::U(p, q) => write!(f, "({} U {})", p, q),
            LTLExpression::R(p, q) => write!(f, "({} R {})", p, q),
            LTLExpression::V(p, q) => write!(f, "({} V {})", p, q),
        }
    }
}

impl std::ops::BitOr for LTLExpression {
    type Output = LTLExpression;

    fn bitor(self, rhs: LTLExpression) -> LTLExpression {
        LTLExpression::Or(Box::new(self), Box::new(rhs))
    }
}
impl std::ops::BitAnd for LTLExpression {
    type Output = LTLExpression;

    fn bitand(self, rhs: LTLExpression) -> LTLExpression {
        LTLExpression::And(Box::new(self), Box::new(rhs))
    }
}
impl std::ops::Not for LTLExpression {
    type Output = LTLExpression;

    fn not(self) -> LTLExpression {
        LTLExpression::Not(Box::new(self))
    }
}

impl LTLExpression {
    pub fn lit(s: impl fmt::Display) -> LTLExpression {
        LTLExpression::Literal(s.to_string())
    }

    /// Simplify this LTL formula by rewritting G, F, V subformula with the operators U and R
    pub fn rewrite(&self) -> LTLExpression {
        use LTLExpression::*;

        match self {
            True => True,
            False => False,
            Literal(l) => Literal(l.clone()),
            Not(e) => !e.rewrite(),
            And(p, q) => p.rewrite() & q.rewrite(),
            Or(p, q) => p.rewrite() | q.rewrite(),
            // Unabbreviate Gp = ⊥ R p
            G(p) => False.R(p.rewrite()),
            // Unabbreviate Fp = T U p
            F(p) => True.U(p.rewrite()),
            U(p, q) => p.rewrite().U(q.rewrite()),
            R(p, q) => p.rewrite().R(q.rewrite()),
            // p V q = ¬(¬p U ¬q)
            V(p, q) => !(!p.rewrite()).U(!q.rewrite()),
        }
    }

    #[allow(non_snake_case)]
    pub fn U(self, other: LTLExpression) -> LTLExpression {
        LTLExpression::U(Box::new(self), Box::new(other))
    }

    #[allow(non_snake_case)]
    pub fn R(self, other: LTLExpression) -> LTLExpression {
        LTLExpression::R(Box::new(self), Box::new(other))
    }

    #[allow(non_snake_case)]
    pub fn V(self, other: LTLExpression) -> LTLExpression {
        LTLExpression::V(Box::new(self), Box::new(other))
    }

    /// put LTL formula in a Negation normal form
    pub fn nnf(&self) -> LTLExpression {
        use LTLExpression::*;

        match self {
            True => True,
            False => False,
            Literal(l) => Literal(l.clone()),
            Not(e) => match e.as_ref() {
                True => False,
                False => True,
                Literal(_) => self.clone(),
                And(p, q) => p.nnf().not().nnf() | q.nnf().not().nnf(),
                Or(p, q) => p.nnf().not().nnf() & q.nnf().not().nnf(),
                // ¬G p ≡ F ¬p
                G(p) => F(Box::new(p.nnf().not().nnf())),
                // ¬F p ≡ G ¬p
                F(p) => G(Box::new(p.nnf().not().nnf())),
                // ¬ (p U q) ≡ (¬p V ¬q) or (¬p R ¬ψ), we use the dual V to respect the paper:
                // Simple On-the-Fly Automatic Verification of Linear Temporal Logic
                U(p, q) => (p.nnf().not().nnf()).V(q.nnf().not().nnf()),
                // ¬ (p R q) ≡ (¬p U ¬q)
                R(p, q) => (p.nnf().not().nnf()).U(q.nnf().not().nnf()),
                V(p, q) => (p.nnf().not().nnf()).U(q.nnf().not().nnf()),
                Not(p) => p.nnf(),
            },
            And(p, q) => p.nnf() & q.nnf(),
            Or(p, q) => p.nnf() | q.nnf(),
            G(e) => G(Box::new(e.nnf())),
            F(e) => F(Box::new(e.nnf())),
            U(p, q) => p.nnf().U(q.nnf()),
            R(p, q) => p.nnf().R(q.nnf()),
            V(p, q) => p.nnf().V(q.nnf()),
        }
    }
}

#[cfg(test)]
mod test_ltl_expression {
    use super::*;

    fn lit(s: &str) -> LTLExpression {
        LTLExpression::lit(s)
    }

    #[test]
    fn test_put_in_nnf() {
        let expr = !lit("p").U(lit("q"));
        let expected_nnf = (!lit("p")).V(!lit("q"));

        assert_eq!(expected_nnf, expr.nnf());
    }

    #[test]
    fn test_put_in_nnf_not_not() {
        let expr = !!!lit("p").U(lit("q"));
        let expected_nnf = (!lit("p")).V(!lit("q"));

        assert_eq!(expected_nnf, expr.nnf());
    }
}
