use plex::parser;

use crate::expression::LTLExpression;
use crate::parser::lexer::{Span, Token, Token::*};

#[derive(Debug)]
pub struct LTLExpressionSpan {
    pub span: Span,
    pub expr: LTLExpression,
}

parser! {
    fn parse_(Token, Span);

    (a, b) {
        Span {
            lo: a.lo,
            hi: b.hi,
        }
    }

    expr: LTLExpressionSpan {
        binexpr[b] => b,
        atom[a] => a,
        G expr[e] => LTLExpressionSpan {
            span: span!(),
            expr: LTLExpression::G(Box::new(e.expr)),
        },
        F expr[e] => LTLExpressionSpan {
            span: span!(),
            expr: LTLExpression::F(Box::new(e.expr)),
        },
        Not expr[e] => LTLExpressionSpan {
            span: span!(),
            expr: LTLExpression::Not(Box::new(e.expr)),
        },
        LParen expr[e] RParen => LTLExpressionSpan {
            span: span!(),
            expr: e.expr,
        },
    }

    binexpr: LTLExpressionSpan{
        atom[e1] U expr[e2] => LTLExpressionSpan {
            span: span!(),
            expr: LTLExpression::U(Box::new(e1.expr), Box::new(e2.expr)),
        },
        atom[e1] R expr[e2] => LTLExpressionSpan {
            span: span!(),
            expr: LTLExpression::R(Box::new(e1.expr), Box::new(e2.expr)),
        },
        atom[e1] V expr[e2] => LTLExpressionSpan {
            span: span!(),
            expr: LTLExpression::V(Box::new(e1.expr), Box::new(e2.expr)),
        },
        atom[e1] Or expr[e2] => LTLExpressionSpan {
            span: span!(),
            expr: LTLExpression::Or(Box::new(e1.expr), Box::new(e2.expr)),
        },
        atom[e1] And expr[e2] => LTLExpressionSpan {
            span: span!(),
            expr: LTLExpression::And(Box::new(e1.expr), Box::new(e2.expr)),
        },
    }

    atom: LTLExpressionSpan {
        Ident(i) => LTLExpressionSpan {
            span: span!(),
            expr: LTLExpression::Literal(i),
        },
        True => LTLExpressionSpan {
            span: span!(),
            expr: LTLExpression::True,
        },
        False => LTLExpressionSpan {
            span: span!(),
            expr: LTLExpression::False,
        },
    }
}

pub fn parse<I: Iterator<Item = (Token, Span)>>(
    i: I,
) -> Result<LTLExpressionSpan, (Option<(Token, Span)>, &'static str)> {
    parse_(i)
}
