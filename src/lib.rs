#![crate_type = "proc-macro"]

use proc_macro::{TokenStream, TokenTree, token_stream::IntoIter};
use std::iter::Peekable;

use std::cmp::{PartialOrd, Ordering};
use std::error::Error;
use std::fmt::{Display, Formatter};

#[proc_macro]
pub fn blend_formula(token_stream: TokenStream) -> TokenStream {
	let mut token_iter = token_stream.into_iter().peekable();
	
	let formula = match parse_formula(&mut token_iter, false) {
		Ok(t) => term_formula(simplify_term(t)),
		
		 // Operation Shortcuts:
		Err((None, ParseError::ExpectedTerm(TokenTree::Punct(punct))))
		if token_iter.peek().is_none() => match punct.as_char() {
			'*' => Some(("Dst", "Zero", "Add")),
			'+' => Some(("One", "One", "Add")),
			'<' => Some(("One", "One", "Min")),
			'>' => Some(("One", "One", "Max")),
			_ => panic!("{}", ParseError::ExpectedTerm(TokenTree::Punct(punct)))
		},
		Err((Some(Term::Zero), ParseError::ExpectedTerm(TokenTree::Punct(punct))))
		if token_iter.peek().is_none() && punct == '-' => {
			Some(("One", "One", "Sub"))
		},
		
		 // Parse Failure:
		Err((_, err)) => panic!("{}", err),
	};
	
	 // Valid Formula:
	if let Some((src_factor_name, dst_factor_name, op_name)) = formula {
		let text = format!("\
			blend_formula::BlendFormula {{\
				src_factor: blend_formula::BlendFactor::{},\
				dst_factor: blend_formula::BlendFactor::{},\
				operation: blend_formula::BlendOperation::{},\
			}}",
			src_factor_name,
			dst_factor_name,
			op_name,
		);
		return text.parse().unwrap()
	}
	
	 // Invalid Formula:
	panic!("formula must evaluate to 'Term*Factor Op Term*Factor', where:\
		\n- each Term is either 'src' or 'dst' (mutually-exclusive)\
		\n- each Factor is: '0', '1', 'Term', '1-Term', 'Term.a', '1-Term.a', 'c', '1-c', or 'src.a<1-dst.a'\
		\n- Op is: '+', '-', '<', or '>'\
	")
}

fn term_formula(term: Term) -> Option<(&'static str, &'static str, &'static str)> {
	let term = &*term.to_string();
	Some(include!("formula_map.in"))
}

#[test]
fn gen_formula_map() {
	use std::collections::HashSet;
	use std::fs::File;
	use std::io::Write;
	
	let operation_list = [
		("Add",    linear_term(Term::Src, LinearOp::Plus,  Term::Dst)),
		("Sub",    linear_term(Term::Src, LinearOp::Minus, Term::Dst)),
		("RevSub", linear_term(Term::Dst, LinearOp::Minus, Term::Src)),
		("Min",    comparison_term(Term::Src, ComparisonOp::Min, Term::Dst)),
		("Max",    comparison_term(Term::Src, ComparisonOp::Max, Term::Dst)),
	];
	
	let src_alpha = suffix_term(Term::Src, BlendSuffix::Alpha);
	let dst_alpha = suffix_term(Term::Dst, BlendSuffix::Alpha);
	let one_minus_dst_alpha = linear_term(Term::One, LinearOp::Minus, dst_alpha.clone());
	
	let factor_list = [
		("Zero",              Term::Zero),
		("One",               Term::One),
		("Src",               Term::Src),
		("SrcAlpha",          src_alpha.clone()),
		("Dst",               Term::Dst),
		("DstAlpha",          dst_alpha.clone()),
		("Constant",          Term::Constant),
		("OneMinusSrc",       linear_term(Term::One, LinearOp::Minus, Term::Src)),
		("OneMinusSrcAlpha",  linear_term(Term::One, LinearOp::Minus, src_alpha.clone())),
		("OneMinusDst",       linear_term(Term::One, LinearOp::Minus, Term::Dst)),
		("OneMinusDstAlpha",  one_minus_dst_alpha.clone()),
		("OneMinusConstant",  linear_term(Term::One, LinearOp::Minus, Term::Constant)),
		("SaturatedSrcAlpha", comparison_term(src_alpha, ComparisonOp::Min, one_minus_dst_alpha)),
	];
	
	let mut formula_set = HashSet::new();
	let mut match_text = String::from("match term {\n");
	
	for (op_name, term) in &operation_list {
	for (b_factor_name, b_factor) in &factor_list {
	for (a_factor_name, a_factor) in &factor_list {
		let term = match term {
			Term::LinearTerm(a, op, b) => simplify_linear_term(
				factor_term(*a.clone(), a_factor.clone()),
				op.clone(),
				factor_term(*b.clone(), b_factor.clone())
			),
			Term::Comparison(a, op, b) => simplify_comparison_term(
				factor_term(*a.clone(), a_factor.clone()),
				op.clone(),
				factor_term(*b.clone(), b_factor.clone())
			),
			_ => unreachable!()
		};
		if !formula_set.contains(&term) {
			match_text.push_str(&*format!(
				"\"{}\" => (\"{}\", \"{}\", \"{}\"),\n",
				term,
				if *op_name == "RevSub" { b_factor_name } else { a_factor_name },
				if *op_name == "RevSub" { a_factor_name } else { b_factor_name },
				op_name
			));
			formula_set.insert(term);
		}
	}}}
	
	match_text.push_str("_ => return None }");
	
	File::create("src/formula_map.in").unwrap()
		.write(match_text.as_bytes())
		.expect("failed to write");
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Term {
	Zero,
	One,
	Src,
	Dst,
	Constant,
	
	SuffixTerm(Box<Term>, BlendSuffix),
	FactorTerm(Box<Term>, Box<Term>),
	LinearTerm(Box<Term>, LinearOp, Box<Term>),
	Comparison(Box<Term>, ComparisonOp, Box<Term>),
}

impl Term {
	const fn order(&self) -> u8 {
		match self {
			Term::Zero           => 0,
			Term::One            => 1,
			Term::Src            => 2,
			Term::Dst            => 3,
			Term::Constant       => 4,
			Term::SuffixTerm(..) => 5,
			Term::FactorTerm(..) => 6,
			Term::LinearTerm(..) => 7,
			Term::Comparison(..) => 8,
		}
	}
}

impl PartialOrd for Term {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl Ord for Term {
	fn cmp(&self, other: &Self) -> Ordering {
		match (self, other) {
			(Term::SuffixTerm(a, a_s), Term::SuffixTerm(b, b_s)) => if a == b {
				(*a_s).cmp(b_s)
			} else {
				(*a).cmp(b)
			},
			(Term::FactorTerm(a, a_f), Term::FactorTerm(b, b_f)) => if a == b {
				(*a_f).cmp(b_f)
			} else {
				(*a).cmp(b)
			},
			(Term::LinearTerm(a, a_op, a_b), Term::LinearTerm(b, b_op, b_b)) => {
				if a == b {
					if a_b == b_b {
						(*a_op).cmp(b_op)
					} else {
						(*a_b).cmp(b_b)
					}
				} else {
					(*a).cmp(b)
				}
			},
			(Term::Comparison(a, a_op, a_b), Term::Comparison(b, b_op, b_b)) => {
				if a == b {
					if a_b == b_b {
						(*a_op).cmp(b_op)
					} else {
						(*a_b).cmp(b_b)
					}
				} else {
					(*a).cmp(b)
				}
			},
			(a, b) => a.order().cmp(&b.order())
		}
	}
}

impl Display for Term {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		fn par(outer: &Term, inner: &Term) -> String {
			if outer.order() > inner.order() {
				inner.to_string()
			} else {
				format!("({})", inner)
			}
		}
		match self {
			Term::Zero     => write!(f, "0"),
			Term::One      => write!(f, "1"),
			Term::Src      => write!(f, "src"),
			Term::Dst      => write!(f, "dst"),
			Term::Constant => write!(f, "c"),
			
			Term::SuffixTerm(term, suf) => write!(f,
				"{}.{}",
				par(self, term),
				suf
			),
			Term::FactorTerm(a, b) => write!(f,
				"{}*{}",
				par(self, a),
				par(self, b)
			),
			Term::LinearTerm(a, op, b) => write!(f,
				"{}{op}{}",
				par(self, a),
				par(self, b)
			),
			Term::Comparison(a, op, b) => write!(f,
				"{}{op}{}",
				par(self, a),
				par(self, b)
			),
		}
	}
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
enum BlendSuffix {
	Color,
	Alpha,
}

impl Display for BlendSuffix {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match *self {
			BlendSuffix::Color => write!(f, "rgb"),
			BlendSuffix::Alpha => write!(f, "a"),
		}
	}
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
enum LinearOp {
	Plus,
	Minus,
}

impl LinearOp {
	fn inverse(self) -> Self {
		match self {
			Self::Plus  => Self::Minus,
			Self::Minus => Self::Plus,
		}
	}
}

impl Display for LinearOp {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match *self {
			Self::Plus  => write!(f, "+"),
			Self::Minus => write!(f, "-"),
		}
	}
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
enum ComparisonOp {
	Min,
	Max,
}

impl ComparisonOp {
	fn inverse(self) -> Self {
		match self {
			Self::Min => Self::Max,
			Self::Max => Self::Min,
		}
	}
}

impl Display for ComparisonOp {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match *self {
			Self::Min => write!(f, "<"),
			Self::Max => write!(f, ">"),
		}
	}
}

fn suffix_term(term: Term, suf: BlendSuffix) -> Term {
	Term::SuffixTerm(Box::new(term), suf)
}
fn factor_term(a: Term, b: Term) -> Term {
	Term::FactorTerm(Box::new(a), Box::new(b))
}
fn linear_term(a: Term, op: LinearOp, b: Term) -> Term {
	Term::LinearTerm(Box::new(a), op, Box::new(b))
}
fn comparison_term(a: Term, op: ComparisonOp, b: Term) -> Term {
	Term::Comparison(Box::new(a), op, Box::new(b))
}

#[derive(Debug)]
enum ParseError {
	ExpectedTerm(TokenTree),
	ExpectedTermGotEnd,
	ExpectedOp(TokenTree),
	ExpectedSuffix(TokenTree),
	ExpectedSuffixGotEnd,
	AmbiguousComparison,
	NestedSuffix(Vec<BlendSuffix>),
}

impl Display for ParseError {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		const TERM_TEXT: &'static str = "'0', '1', 'src', 'dst', 'c'";
		const OP_TEXT: &'static str = "'.', '*', '+', '-', '<', '>'";
		const SUFFIX_TEXT: &'static str = "'rgb', 'a'";
		match self {
			Self::ExpectedTerm(token) => {
				write!(f, "expected term ({}); got '{}'", TERM_TEXT, token)
			}
			Self::ExpectedTermGotEnd => {
				write!(f, "expected term ({}); got end", TERM_TEXT)
			},
			Self::ExpectedOp(token) => {
				write!(f, "expected operator ({}); got '{}'", OP_TEXT, token)
			}
			Self::ExpectedSuffix(token) => {
				write!(f, "expected suffix ({}); got '{}'", SUFFIX_TEXT, token)
			}
			Self::ExpectedSuffixGotEnd => {
				write!(f, "expected suffix ({}); got end", SUFFIX_TEXT)
			},
			Self::AmbiguousComparison => {
				write!(f, "chained comparison operators require parentheses")
			},
			Self::NestedSuffix(suf_list) => {
				let mut text = String::new();
				for suf in suf_list {
					text.push('.');
					text.push_str(&*suf.to_string());
				}
				write!(f, "a term can only have one suffix; got '{}'", text)
			},
		}
	}
}

impl Error for ParseError {}

fn parse_formula(token_iter: &mut Peekable<IntoIter>, is_comparison: bool)
	-> Result<Term, (Option<Term>, ParseError)>
{
	let mut term = parse_term(token_iter)?;
	while let Some(token) = token_iter.next() {
		if let TokenTree::Punct(punct) = token {
			let prev = std::mem::replace(&mut term, Term::Zero);
			term = match punct.as_char() {
				'+' | '-' => {
					let op = if punct == '+' {
						LinearOp::Plus
					} else {
						LinearOp::Minus
					};
					match parse_term(token_iter) {
						Ok(next) => linear_term(prev, op, next),
						Err((None,       err)) => return Err((Some(prev), err)),
						Err((Some(next), err)) => return Err((
							Some(linear_term(prev, op, next)),
							err
						)),
					}
				},
				'<' | '>' => {
					if is_comparison {
						return Err((Some(prev), ParseError::AmbiguousComparison));
					}
					let op = if punct == '<' {
						ComparisonOp::Min
					} else {
						ComparisonOp::Max
					};
					match parse_formula(token_iter, true) {
						Ok(next) => comparison_term(prev, op, next),
						Err((None,       err)) => return Err((Some(prev), err)),
						Err((Some(next), err)) => return Err((
							Some(comparison_term(prev, op, next)),
							err
						)),
					}
				},
				_ => return Err((
					Some(prev),
					ParseError::ExpectedOp(TokenTree::Punct(punct))
				))
			};
		} else {
			return Err((Some(term), ParseError::ExpectedOp(token)))
		}
	}
	Ok(term)
}

fn parse_term(token_iter: &mut Peekable<IntoIter>)
	-> Result<Term, (Option<Term>, ParseError)>
{
	let mut term = match token_iter.next() {
		Some(TokenTree::Ident(ident)) => match ident.to_string().as_str() {
			"src" => Term::Src,
			"dst" => Term::Dst,
			"c"   => Term::Constant,
			_ => return Err((
				None,
				ParseError::ExpectedTerm(TokenTree::Ident(ident))
			))
		},
		Some(TokenTree::Literal(liter)) => match liter.to_string().as_str() {
			"0" => Term::Zero,
			"1" => Term::One,
			_ => return Err((
				None,
				ParseError::ExpectedTerm(TokenTree::Literal(liter))
			))
		},
		Some(TokenTree::Group(group)) => parse_formula(
			&mut group.stream().into_iter().peekable(),
			false
		)?,
		Some(TokenTree::Punct(punct)) => match punct.as_char() {
			'-' => match parse_term(token_iter) {
				Ok(t) => linear_term(Term::Zero, LinearOp::Minus, t),
				Err((None, ParseError::ExpectedTermGotEnd)) => return Err((
					Some(Term::Zero),
					ParseError::ExpectedTerm(TokenTree::Punct(punct))
				)),
				Err((None,    err)) => return Err((Some(Term::Zero), err)),
				Err((Some(t), err)) => return Err((
					Some(linear_term(Term::Zero, LinearOp::Minus, t)),
					err
				)),
			},
			_ => return Err((
				None,
				ParseError::ExpectedTerm(TokenTree::Punct(punct))
			))
		},
		None => return Err((None, ParseError::ExpectedTermGotEnd))
	};
	
	term = match parse_term_suffix(token_iter) {
		Ok(None) => term,
		Ok(Some(suffix)) => suffix_term(term, suffix),
		Err(error) => return Err((Some(term), error)),
	};
	
	term = match parse_term_factor(token_iter) {
		Ok(None) => term,
		Ok(Some(factor)) => factor_term(term, factor),
		Err((_, error)) => return Err((Some(term), error)),
	};
	
	Ok(term)
}

fn parse_term_suffix(token_iter: &mut Peekable<IntoIter>)
	-> Result<Option<BlendSuffix>, ParseError>
{
	match token_iter.peek() {
		Some(TokenTree::Punct(p)) => if *p == '.' {
			token_iter.next();
			if let Some(token) = token_iter.next() {
				if let TokenTree::Ident(suf) = token {
					let suf = match suf.to_string().as_str() {
						"rgb" => BlendSuffix::Color, // ??? .xyz
						"a"   => BlendSuffix::Alpha, // ??? .w
						_ => return Err(ParseError::ExpectedSuffix(TokenTree::Ident(suf)))
					};
					match parse_term_suffix(token_iter) {
						Ok(None) => Ok(Some(suf)),
						Ok(Some(next_suf)) => {
							Err(ParseError::NestedSuffix(vec![suf, next_suf]))
						},
						Err(ParseError::NestedSuffix(mut nested_suf_list)) => {
							nested_suf_list.insert(0, suf);
							Err(ParseError::NestedSuffix(nested_suf_list))
						}
						error => error
					}
				} else {
					Err(ParseError::ExpectedSuffix(token))
				}
			} else {
				Err(ParseError::ExpectedSuffixGotEnd)
			}
		} else {
			Ok(None)
		},
		None => Ok(None),
		_ => Err(ParseError::ExpectedOp(token_iter.next().unwrap())),
	}
}

fn parse_term_factor(token_iter: &mut Peekable<IntoIter>) -> Result<Option<Term>, (Option<Term>, ParseError)> {
	match token_iter.peek() {
		Some(TokenTree::Punct(p)) => if *p == '*' {
			token_iter.next();
			Ok(Some(parse_term(token_iter)?))
		} else {
			Ok(None)
		},
		None => Ok(None),
		_ => Err((
			None,
			ParseError::ExpectedOp(token_iter.next().unwrap())
		)),
	}
}

fn simplify_term(term: Term) -> Term {
	match term {
		Term::Comparison(a, op, b) => simplify_comparison_term(*a, op, *b),
		Term::LinearTerm(a, op, b) => simplify_linear_term(*a, op, *b),
		Term::FactorTerm(a, b) => simplify_factor_term(*a, *b),
		Term::SuffixTerm(term, suffix) => simplify_suffix_term(*term, suffix),
		term => term
	}
}

fn simplify_suffix_term(term: Term, suf: BlendSuffix) -> Term {
	match simplify_term(term) {
		Term::Comparison(sub_a, sub_op, sub_b) => comparison_term(
			simplify_suffix_term(*sub_a, suf),
			sub_op,
			simplify_suffix_term(*sub_b, suf)
		),
		Term::LinearTerm(sub_a, sub_op, sub_b) => linear_term(
			simplify_suffix_term(*sub_a, suf),
			sub_op,
			simplify_suffix_term(*sub_b, suf)
		),
		Term::FactorTerm(sub_a, sub_b) => factor_term(
			simplify_suffix_term(*sub_a, suf),
			simplify_suffix_term(*sub_b, suf)
		),
		Term::SuffixTerm(_, sub_suf) => {
			panic!("{}", ParseError::NestedSuffix(vec![sub_suf, suf]))
		},
		term => suffix_term(term, suf)
	}
}

fn simplify_factor_term(a: Term, b: Term) -> Term {
	match (simplify_term(a), simplify_term(b)) {
		(Term::Zero, _) |
		(_, Term::Zero) => Term::Zero,
		
		(Term::One, term) |
		(term, Term::One) => term,
		
		 // `(a_a > a_b) * b` => `(a_a * b) > (a_b * b)`:
		(Term::Comparison(a_a, a_op, a_b), b) |
		(b, Term::Comparison(a_a, a_op, a_b)) => comparison_term(
			simplify_factor_term(*a_a, b.clone()),
			a_op,
			simplify_factor_term(*a_b, b)
		),
		
		 // `(a_a ± a_b) * b` => `(a_a * b) ± (a_b * b)`:
		(Term::LinearTerm(a_a, a_op, a_b), b) |
		(b, Term::LinearTerm(a_a, a_op, a_b)) => linear_term(
			simplify_factor_term(*a_a, b.clone()),
			a_op,
			simplify_factor_term(*a_b, b)
		),
		
		 // `(a_a * a_b) * (b_a * b_b)` => `a_a * (a_b * (b_b * b_a))`:
		(Term::FactorTerm(a_a, a_b), Term::FactorTerm(b_a, b_b)) => simplify_factor_term(
			*a_a,
			factor_term(*a_b, Term::FactorTerm(b_a, b_b))
		),
		 
		 // `(a_a * a_b) * b`:
		(Term::FactorTerm(a_a, a_b), b) |
		(b, Term::FactorTerm(a_a, a_b)) => if b > *a_a {
			factor_term(*a_a, simplify_factor_term(*a_b, b))
		} else {
			factor_term(b, Term::FactorTerm(a_a, a_b))
		},
		
		 // `a * b`:
		(a, b) => if a < b {
			factor_term(a, b)
		} else {
			factor_term(b, a)
		}
	}
}

fn simplify_linear_term(a: Term, op: LinearOp, b: Term) -> Term {
	// 0 - (1 + (1 + (c + (c + (c + (src + (src + (src + (dst + (dst + dst))))))))))
	// trace::trace!("? [{a}] {op} [{b}]");
	match (simplify_term(a), op, simplify_term(b)) {
		(Term::Zero, LinearOp::Plus, term)  |
		(term, LinearOp::Plus,  Term::Zero) |
		(term, LinearOp::Minus, Term::Zero) => term,
		
		 // `min(a_a, a_b) ± b` => `min(a_a ± b, a_b ± b)`:
		(Term::Comparison(a_a, a_op, a_b), op, b) => simplify_comparison_term(
			linear_term(*a_a, op, b.clone()),
			a_op,
			linear_term(*a_b, op, b),
		),
		
		 // `a - min(b_a, b_b)` => `max(a - b_a, a - b_b)`:
		(a, op, Term::Comparison(b_a, b_op, b_b)) => simplify_comparison_term(
			linear_term(a.clone(), op, *b_a),
			match op {
				LinearOp::Plus  => b_op,
				LinearOp::Minus => b_op.inverse(),
			},
			linear_term(a, op, *b_b),
		),
		
		 // `a ± (b_a ± b_b)` => `(a ± b_b) ± b_a`:
		(a, op, Term::LinearTerm(b_a, b_op, b_b)) => simplify_linear_term(
			linear_term(
				a,
				match op {
					LinearOp::Plus  => b_op,
					LinearOp::Minus => b_op.inverse(),
				},
				*b_b
			),
			op,
			*b_a
		),
		
		 // `(a_a ± a_b) ± b`:
		(Term::LinearTerm(a_a, a_op, a_b), op, b) => if b > *a_a {
			 // => `a_a ± (a_b ± b)`:
			match simplify_linear_term(
				*a_b,
				match a_op {
					LinearOp::Plus  => op,
					LinearOp::Minus => op.inverse(),
				},
				b
			) {
				Term::Zero => *a_a,
				Term::LinearTerm(term_a, LinearOp::Minus, term_b)
				if *term_a == Term::Zero => if *a_a == Term::Zero {
					*term_b
				} else {
					Term::LinearTerm(a_a, a_op.inverse(), term_b)
				},
				term => linear_term(*a_a, a_op, term),
			}
		} else if op == LinearOp::Minus {
			 // => `0 - (b - (a_a ± a_b))`:
			if b == *a_a {
				match a_op {
					LinearOp::Plus  => *a_b,
					LinearOp::Minus => linear_term(Term::Zero, a_op, *a_b),
				}
			} else {
				linear_term(
					Term::Zero,
					op,
					linear_term(b, op, Term::LinearTerm(a_a, a_op, a_b))
				)
			}
		} else {
			 // `(a_a ± a_b) + b` => `b + (a_a ± a_b)`:
			linear_term(b, op, Term::LinearTerm(a_a, a_op, a_b))
		},
		
		 // `a ± b`:
		(a, op, b) => match b.cmp(&a) {
			Ordering::Less => match op {
				LinearOp::Plus  => linear_term(b, op, a),
				LinearOp::Minus => linear_term(Term::Zero, op, linear_term(b, op, a)),
			},
			Ordering::Equal => match op {
				LinearOp::Plus  => linear_term(a, op, b),
				LinearOp::Minus => Term::Zero,
			},
			Ordering::Greater => linear_term(a, op, b),
		}
	}
}

fn simplify_comparison_term(a: Term, op: ComparisonOp, b: Term) -> Term {
	match (simplify_term(a), op, simplify_term(b)) {
		//  // `min(0, b)` => `0`:
		// (Term::Zero, ComparisonOp::Min, Term::Zero)     |
		// (Term::Zero, ComparisonOp::Min, Term::One)      |
		// (Term::Zero, ComparisonOp::Min, Term::Src)      |
		// (Term::Zero, ComparisonOp::Min, Term::Dst)      |
		// (Term::Zero, ComparisonOp::Min, Term::Constant) => Term::Zero,
		
		//  // `max(0, b)` => `b`:
		// (Term::Zero, ComparisonOp::Max, Term::Zero)     => Term::Zero,
		// (Term::Zero, ComparisonOp::Max, Term::One)      => Term::One,
		// (Term::Zero, ComparisonOp::Max, Term::Src)      => Term::Src,
		// (Term::Zero, ComparisonOp::Max, Term::Dst)      => Term::Dst,
		// (Term::Zero, ComparisonOp::Max, Term::Constant) => Term::Constant,
		
		 // `(a_a < a_b) < (b_a < b_b)`:
		(Term::Comparison(a_a, a_op, a_b), op, Term::Comparison(b_a, b_op, b_b)) => {
			if op == a_op {
				simplify_comparison_term(*a_a, a_op, comparison_term(*a_b, op, Term::Comparison(b_a, b_op, b_b)))
			} else if op == b_op {
				simplify_comparison_term(*b_a, b_op, comparison_term(*b_b, op, Term::Comparison(a_a, a_op, a_b)))
			} else if a_a == b_a {
				simplify_comparison_term(*a_a, a_op, Term::Comparison(a_b, op, b_b)) 
			} else if a_a == b_b {
				simplify_comparison_term(*a_a, a_op, Term::Comparison(b_a, op, a_b))
			} else if a_b == b_a {
				simplify_comparison_term(*a_b, a_op, Term::Comparison(a_a, op, b_b))
			} else if a_b == b_b {
				simplify_comparison_term(*a_b, a_op, Term::Comparison(a_a, op, b_a))
			} else {
				let a = Term::Comparison(a_a, a_op, a_b);
				let b = Term::Comparison(b_a, b_op, b_b);
				match b.cmp(&a) {
					Ordering::Less => comparison_term(b, op, a),
					Ordering::Equal => a,
					Ordering::Greater => comparison_term(a, op, b),
				}
			}
		},
		
		 // `(a_a < a_b) < b`:
		(Term::Comparison(a_a, a_op, a_b), op, b) |
		(b, op, Term::Comparison(a_a, a_op, a_b)) => if op == a_op {
			match b.cmp(&a_a) {
				Ordering::Less => comparison_term(b, op, Term::Comparison(a_a, a_op, a_b)),
				Ordering::Equal => Term::Comparison(a_a, a_op, a_b),
				Ordering::Greater => comparison_term(*a_a, a_op, simplify_comparison_term(*a_b, op, b)),
			}
		} else if b == *a_a || b == *a_b {
			b
		} else {
			comparison_term(b, op, Term::Comparison(a_a, a_op, a_b))
		},
		
		 // `a < b`:
		(a, op, b) => match b.cmp(&a) {
			Ordering::Less => comparison_term(b, op, a),
			Ordering::Equal => a,
			Ordering::Greater => comparison_term(a, op, b),
		}
	}
}