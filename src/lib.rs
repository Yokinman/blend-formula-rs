#![crate_type = "proc-macro"]

use proc_macro::{TokenStream, TokenTree, token_stream::IntoIter, Delimiter};

use std::iter::Peekable;
use std::cmp::{PartialOrd, Ordering};
use std::collections::{hash_map, HashMap};
use std::fmt::{Display, Formatter};

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
enum Term {
	#[default]
	Zero,
	One,
	Constant,
	Src,
	Dst,
	
	SuffixTerm(Box<Term>, TermSuffix),
	LinearTerm(Box<Term>, LinearOp, Box<Term>),
	FactorTerm(Box<Term>, Box<Term>),
}

impl PartialOrd for Term {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl Ord for Term {
	fn cmp(&self, other: &Self) -> Ordering {
		fn order(term: &Term) -> u8 {
			match term {
				Term::Zero           => 0,
				Term::One            => 1,
				Term::Constant       => 2,
				Term::Src            => 3,
				Term::Dst            => 4,
				Term::SuffixTerm(..) => 5,
				Term::LinearTerm(..) => 6,
				Term::FactorTerm(..) => 7,
			}
		}
		match (self, other) {
			(Term::SuffixTerm(a, a_s), Term::SuffixTerm(b, b_s)) => if a == b {
				(*a_s).cmp(b_s)
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
			(Term::FactorTerm(a, a_f), Term::FactorTerm(b, b_f)) => if a == b {
				(*a_f).cmp(b_f)
			} else {
				(*a).cmp(b)
			},
			(a, Term::LinearTerm(b_a, _, b_b)) => if a <= b_a || a <= b_b {
				Ordering::Less
			} else {
				Ordering::Greater
			},
			(Term::LinearTerm(a_a, _, a_b), b) => if b <= a_a || b <= a_b {
				Ordering::Greater
			} else {
				Ordering::Less
			},
			(a, Term::FactorTerm(b_a, b_b)) => if a <= b_a || a <= b_b {
				Ordering::Less
			} else {
				Ordering::Greater
			},
			(Term::FactorTerm(a_a, a_b), b) => if b <= a_a || b <= a_b {
				Ordering::Greater
			} else {
				Ordering::Less
			},
			(a, b) => order(a).cmp(&order(b))
		}
	}
}

impl Display for Term {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match self {
			Term::Zero     => write!(f, "0"),
			Term::One      => write!(f, "1"),
			Term::Src      => write!(f, "src"),
			Term::Dst      => write!(f, "dst"),
			Term::Constant => write!(f, "c"),
			
			Term::SuffixTerm(term, suffix) => match &**term {
				Term::LinearTerm(..) => write!(f, "({term}).{suffix}"),
				Term::FactorTerm(..) => write!(f, "({term}).{suffix}"),
				_ => write!(f, "{term}.{suffix}")
			},
			Term::LinearTerm(a, op, b) => match (&**a, &**b) {
				(Term::LinearTerm(..), Term::LinearTerm(..)) => write!(f, "({a}) {op} ({b})"),
				(Term::FactorTerm(..), Term::FactorTerm(..)) => write!(f, "({a}) {op} ({b})"),
				(Term::LinearTerm(..), Term::FactorTerm(..)) => write!(f, "({a}) {op} ({b})"),
				(Term::FactorTerm(..), Term::LinearTerm(..)) => write!(f, "({a}) {op} ({b})"),
				(Term::LinearTerm(..), _) => write!(f, "({a}) {op} {b}"),
				(Term::FactorTerm(..), _) => write!(f, "({a}) {op} {b}"),
				(_, Term::LinearTerm(..)) => write!(f, "{a} {op} ({b})"),
				(_, Term::FactorTerm(..)) => write!(f, "{a} {op} ({b})"),
				_ => write!(f, "{a} {op} {b}")
			},
			Term::FactorTerm(a, b) => match (&**a, &**b) {
				(Term::LinearTerm(..), Term::LinearTerm(..)) => write!(f, "({a})*({b})"),
				(Term::FactorTerm(..), Term::FactorTerm(..)) => write!(f, "({a})*({b})"),
				(Term::LinearTerm(..), Term::FactorTerm(..)) => write!(f, "({a})*({b})"),
				(Term::FactorTerm(..), Term::LinearTerm(..)) => write!(f, "({a})*({b})"),
				(Term::LinearTerm(..), _) => write!(f, "({a})*{b}"),
				(Term::FactorTerm(..), _) => write!(f, "({a})*{b}"),
				(_, Term::LinearTerm(..)) => write!(f, "{a}*({b})"),
				(_, Term::FactorTerm(..)) => write!(f, "{a}*({b})"),
				_ => write!(f, "{a}*{b}")
			},
		}
	}
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
enum TermSuffix {
	Color, // .rgb | .xyz
	Alpha, // .a   | .w
}

impl Display for TermSuffix {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match *self {
			TermSuffix::Color => write!(f, "rgb"),
			TermSuffix::Alpha => write!(f, "a"),
		}
	}
}

#[derive(Debug, Copy, Clone, Default, Ord, PartialOrd, Eq, PartialEq, Hash)]
enum LinearOp {
	#[default]
	Plus,
	Minus,
	Min,
	Max,
}

impl LinearOp {
	fn inverse(self) -> Self {
		match self {
			LinearOp::Plus  => LinearOp::Minus,
			LinearOp::Minus => LinearOp::Plus,
			LinearOp::Min   => LinearOp::Max,
			LinearOp::Max   => LinearOp::Min,
		}
	}
}

impl Display for LinearOp {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match *self {
			LinearOp::Plus  => write!(f, "+"),
			LinearOp::Minus => write!(f, "-"),
			LinearOp::Min   => write!(f, "<"),
			LinearOp::Max   => write!(f, ">"),
		}
	}
}

macro_rules! panic_expected {
	($a:ty, $b:expr) => {
		panic!("expected {}; got '{}'", <$a>::TEXT, $b)
	};
	($a:literal, $b:expr) => {
		panic!("expected {}; got '{}'", $a, $b)
	};
}

impl Term       { const TEXT: &'static str =  "'0', '1', 'src', 'dst', or 'c'"; }
impl TermSuffix { const TEXT: &'static str = "'rgb' or 'a'"; }
impl LinearOp   { const TEXT: &'static str = "'*', '+', '-', '<', or '>'"; }

fn parse_formula(token_stream: TokenStream) -> Term {
	let mut token_iter = token_stream.into_iter().peekable();
	let mut main_term = parse_term(&mut token_iter);
	
	while let Some(op_token) = token_iter.next() {
		if let TokenTree::Punct(p) = op_token {
			let next_term = parse_term(&mut token_iter);
			let mut prev_term = std::mem::take(&mut main_term);
			main_term = match p.as_char() {
				'*' => if let Term::LinearTerm(.., ref mut sub_term) = prev_term {
					let prev_sub_term = std::mem::take(sub_term);
					*sub_term = Box::new(Term::FactorTerm(prev_sub_term, Box::new(next_term)));
					prev_term
				} else {
					Term::FactorTerm(Box::new(prev_term), Box::new(next_term))
				},
				'+' => Term::LinearTerm(Box::new(prev_term), LinearOp::Plus,  Box::new(next_term)),
				'-' => Term::LinearTerm(Box::new(prev_term), LinearOp::Minus, Box::new(next_term)),
				'<' => Term::LinearTerm(Box::new(prev_term), LinearOp::Min,   Box::new(next_term)),
				'>' => Term::LinearTerm(Box::new(prev_term), LinearOp::Max,   Box::new(next_term)),
				c => panic_expected!(LinearOp, c)
			};
		} else {
			panic_expected!(LinearOp, op_token);
		}
	}
	
	main_term
}

fn parse_term(token_iter: &mut Peekable<IntoIter>) -> Term {
	let term = match token_iter.next() {
		Some(TokenTree::Ident(t)) => match t.to_string().as_str() {
			"src" => Term::Src,
			"dst" => Term::Dst,
			"c"   => Term::Constant,
			str => panic_expected!(Term, str)
		},
		Some(TokenTree::Literal(t)) => match t.to_string().as_str() {
			"0" => Term::Zero,
			"1" => Term::One,
			str => panic_expected!(Term, str)
		},
		Some(TokenTree::Group(t)) => match t.delimiter() {
			Delimiter::Parenthesis => parse_formula(t.stream()),
			_ => panic_expected!("parentheses", t)
		},
		Some(TokenTree::Punct(t)) => panic_expected!(Term, t.as_char()),
		None => panic_expected!(Term, "None")
	};
	if let Some(suffix) = parse_term_suffix(token_iter) {
		Term::SuffixTerm(Box::new(term), suffix)
	} else {
		term
	}
}

fn parse_term_suffix(token_iter: &mut Peekable<IntoIter>) -> Option<TermSuffix> {
	let mut suffix = None;
	loop {
		match token_iter.peek() {
			Some(TokenTree::Punct(token)) => if *token != '.' { break },
			Some(t) => panic_expected!(LinearOp, t),
			None => break
		}
		token_iter.next();
		if let Some(token) = token_iter.next() {
			if suffix.is_some() {
				panic_expected!("one suffix", token);
			}
			if let TokenTree::Ident(ident) = token {
				suffix = Some(match ident.to_string().as_str() {
					"rgb" => TermSuffix::Color,
					"a"   => TermSuffix::Alpha,
					other => panic_expected!(TermSuffix, other)
				});
			} else {
				panic_expected!(TermSuffix, token);
			}
		} else {
			panic_expected!(TermSuffix, "None");
		}
	}
	suffix
}

fn simplify_term(term: Term) -> Term {
	// let old = term.clone();
	let new = match term {
		Term::SuffixTerm(term, suffix) => simplify_suffix_term(*term, suffix),
		Term::LinearTerm(a, op, b) => simplify_linear_term(*a, op, *b),
		Term::FactorTerm(a, b) => simplify_factor_term(*a, *b),
		term => term
	};
	// if old != new {
	// 	trace::trace!("{old} => {new}");
	// }
	new
}

fn simplify_suffix_term(term: Term, suf: TermSuffix) -> Term {
	match simplify_term(term) {
		Term::SuffixTerm(sub_term, sub_suf) => panic_expected!(
			"no nested suffixes",
			format!("{sub_term}.{sub_suf}.{suf}")
		),
		Term::LinearTerm(sub_a, sub_op, sub_b) => Term::LinearTerm(
			Box::new(simplify_suffix_term(*sub_a, suf)),
			sub_op,
			Box::new(simplify_suffix_term(*sub_b, suf))
		),
		Term::FactorTerm(sub_a, sub_b) => Term::FactorTerm(
			Box::new(simplify_suffix_term(*sub_a, suf)),
			Box::new(simplify_suffix_term(*sub_b, suf))
		),
		term => Term::SuffixTerm(Box::new(term), suf)
	}
}

fn simplify_linear_term(a: Term, op: LinearOp, b: Term) -> Term {
	//! 1 + (1 + (1 + (c + (c + (c + (src + (src + (src + (dst + (dst + dst))))))))))
	// trace::trace!("? [{a}] {op} [{b}]");
	match (simplify_term(a), op, simplify_term(b)) {
		(Term::Zero, LinearOp::Plus, term)  |
		(term, LinearOp::Plus,  Term::Zero) |
		(term, LinearOp::Minus, Term::Zero) => term,
		
		 // `min(0, b)` => `0`:
		// (Term::Zero, LinearOp::Min, Term::Zero)     |
		// (Term::Zero, LinearOp::Min, Term::One)      |
		// (Term::Zero, LinearOp::Min, Term::Constant) |
		// (Term::Zero, LinearOp::Min, Term::Src)      |
		// (Term::Zero, LinearOp::Min, Term::Dst)      => Term::Zero,
		
		 // `max(0, b)` => `b`:
		// (Term::Zero, LinearOp::Max, Term::Zero)     => Term::Zero,
		// (Term::Zero, LinearOp::Max, Term::One)      => Term::One,
		// (Term::Zero, LinearOp::Max, Term::Constant) => Term::Constant,
		// (Term::Zero, LinearOp::Max, Term::Src)      => Term::Src,
		// (Term::Zero, LinearOp::Max, Term::Dst)      => Term::Dst,
		
		// !!! min(a, max(b, c)) <=> max(min(a,b), min(a,c))
		
		 // `min(a_a, a_b) ± b` => `min(a_a ± b, a_b ± b)`:
		(Term::LinearTerm(a_a, a_op, a_b), LinearOp::Plus,  b) |
		(Term::LinearTerm(a_a, a_op, a_b), LinearOp::Minus, b) |
		(b, LinearOp::Plus, Term::LinearTerm(a_a, a_op, a_b))
		if a_op == LinearOp::Min || a_op == LinearOp::Max => simplify_linear_term(
			Term::LinearTerm(a_a, op, Box::new(b.clone())),
			a_op,
			Term::LinearTerm(a_b, op, Box::new(b)),
		),
		
		 // `a - min(b_a, b_b)` => `max(a - b_a, a - b_b)`:
		(a, LinearOp::Minus, Term::LinearTerm(b_a, b_op, b_b))
		if b_op == LinearOp::Min || b_op == LinearOp::Max => simplify_linear_term(
			Term::LinearTerm(Box::new(a.clone()), op, b_a),
			b_op.inverse(),
			Term::LinearTerm(Box::new(a), op, b_b),
		),
		
		 // `a ± (b_a ± b_b)` => `(a ± b_b) ± b_a`:
		(a, LinearOp::Plus,  Term::LinearTerm(b_a, b_op, b_b)) |
		(a, LinearOp::Minus, Term::LinearTerm(b_a, b_op, b_b))
		if b_op == LinearOp::Plus || b_op == LinearOp::Minus => simplify_linear_term(
			Term::LinearTerm(
				Box::new(a),
				if op == LinearOp::Minus { b_op.inverse() } else { b_op },
				b_b
			),
			op,
			*b_a
		),
		
		 // `(a_a ± a_b) ± b`:
		(Term::LinearTerm(a_a, a_op, a_b), LinearOp::Plus,  b) |
		(Term::LinearTerm(a_a, a_op, a_b), LinearOp::Minus, b)
		if a_op == LinearOp::Plus || a_op == LinearOp::Minus => if b > *a_a {
			 // => `a_a ± (a_b ± b)`:
			match simplify_linear_term(
				*a_b,
				if a_op == LinearOp::Minus { op.inverse() } else { op },
				b
			) {
				Term::Zero => *a_a,
				Term::LinearTerm(term_a, LinearOp::Minus, term_b)
				if *term_a == Term::Zero => {
					if *a_a == Term::Zero {
						*term_b
					} else {
						Term::LinearTerm(a_a, a_op.inverse(), term_b)
					}
				},
				term => Term::LinearTerm(a_a, a_op, Box::new(term)),
			}
		} else if op == LinearOp::Minus {
			 // => `0 - (b - (a_a ± a_b))`:
			if b == *a_a {
				if a_op == LinearOp::Minus {
					Term::LinearTerm(Box::new(Term::Zero), a_op, a_b)
				} else {
					*a_b
				}
			} else {
				Term::LinearTerm(
					Box::new(Term::Zero),
					op,
					Box::new(Term::LinearTerm(
						Box::new(b),
						op,
						Box::new(Term::LinearTerm(a_a, a_op, a_b))
					))
				)
			}
		} else {
			 // `(a_a ± a_b) + b` => `b + (a_a ± a_b)`:
			Term::LinearTerm(
				Box::new(b),
				op,
				Box::new(Term::LinearTerm(a_a, a_op, a_b))
			)
		},
		
		(a, op, b) => match b.cmp(&a) {
			 // Order Terms:
			Ordering::Less => if op == LinearOp::Minus {
				Term::LinearTerm(
					Box::new(Term::Zero),
					op,
					Box::new(Term::LinearTerm(Box::new(b), op, Box::new(a)))
				)
			} else {
				Term::LinearTerm(Box::new(b), op, Box::new(a))
			},
			
			 // Reduce Terms:
			Ordering::Equal => match op {
				LinearOp::Plus  => Term::LinearTerm(Box::new(a), op, Box::new(b)),
				LinearOp::Minus => Term::Zero,
				LinearOp::Min   => a,
				LinearOp::Max   => a,
			},
			
			 // No-op:
			Ordering::Greater => Term::LinearTerm(Box::new(a), op, Box::new(b)),
		}
	}
}

fn simplify_factor_term(a: Term, b: Term) -> Term {
	match (simplify_term(a), simplify_term(b)) {
		(Term::Zero, _) |
		(_, Term::Zero) => Term::Zero,
		
		(Term::One, term) |
		(term, Term::One) => term,
		
		 // `(a_a • a_b) * b` => `(a_a * b) • (a_b * b)`:
		(Term::LinearTerm(a_a, a_op, a_b), b) |
		(b, Term::LinearTerm(a_a, a_op, a_b)) => Term::LinearTerm(
			Box::new(simplify_factor_term(*a_a, b.clone())),
			a_op,
			Box::new(simplify_factor_term(*a_b, b))
		),
		
		 // `a * (b_a * b_b)` => `(a * b_b) * b_a`:
		(a, Term::FactorTerm(b_a, b_b)) => simplify_factor_term(
			Term::FactorTerm(Box::new(a), b_b),
			*b_a
		),
		
		 // `(a_a * a_b) * b`:
		(Term::FactorTerm(a_a, a_b), b) => if b > *a_a {
			 // => `a_a * (a_b * b)`:
			Term::FactorTerm(a_a, Box::new(simplify_factor_term(*a_b, b)))
		} else {
			 // => `b * (a_a * a_b)`:
			Term::FactorTerm(Box::new(b), Box::new(Term::FactorTerm(a_a, a_b)))
		},
		
		 // Order Terms:
		(a, b) => if a < b {
			Term::FactorTerm(Box::new(a), Box::new(b))
		} else {
			Term::FactorTerm(Box::new(b), Box::new(a))
		}
	}
}

#[proc_macro]
pub fn blend_formula(token_stream: TokenStream) -> TokenStream {
	let layout_list = [
		(Term::Src, LinearOp::Plus,  Term::Dst),
		(Term::Src, LinearOp::Minus, Term::Dst),
		(Term::Dst, LinearOp::Minus, Term::Src),
		(Term::Src, LinearOp::Min,   Term::Dst),
		(Term::Src, LinearOp::Max,   Term::Dst),
	];
	
	let factor_list = [
		simplify_term(Term::Zero),
		simplify_term(Term::One),
		simplify_term(Term::Src),
		simplify_term(Term::LinearTerm(Box::new(Term::One), LinearOp::Minus, Box::new(Term::Src))),
		simplify_term(Term::SuffixTerm(Box::new(Term::Src), TermSuffix::Alpha)),
		simplify_term(Term::LinearTerm(Box::new(Term::One), LinearOp::Minus, Box::new(Term::SuffixTerm(Box::new(Term::Src), TermSuffix::Alpha)))),
		simplify_term(Term::Dst),
		simplify_term(Term::LinearTerm(Box::new(Term::One), LinearOp::Minus, Box::new(Term::Dst))),
		simplify_term(Term::SuffixTerm(Box::new(Term::Dst), TermSuffix::Alpha)),
		simplify_term(Term::LinearTerm(Box::new(Term::One), LinearOp::Minus, Box::new(Term::SuffixTerm(Box::new(Term::Dst), TermSuffix::Alpha)))),
		simplify_term(Term::LinearTerm(Box::new(Term::SuffixTerm(Box::new(Term::Src), TermSuffix::Alpha)), LinearOp::Min, Box::new(Term::LinearTerm(Box::new(Term::One), LinearOp::Minus, Box::new(Term::SuffixTerm(Box::new(Term::Dst), TermSuffix::Alpha)))))),
		simplify_term(Term::Constant),
		simplify_term(Term::LinearTerm(Box::new(Term::One), LinearOp::Minus, Box::new(Term::Constant))),
	];
	
	let mut formula_blend_map = HashMap::new();
	
	// let mut i = 0;
	
	for layout in &layout_list {
		for dst_factor in &factor_list {
			for src_factor in &factor_list {
				let (src, op, dst) = layout;
				let term = simplify_term(Term::LinearTerm(
					Box::new(Term::FactorTerm(Box::new(src.clone()), Box::new(src_factor.clone()))),
					op.clone(),
					Box::new(Term::FactorTerm(Box::new(dst.clone()), Box::new(dst_factor.clone())))
				));
				if let hash_map::Entry::Vacant(formula) = formula_blend_map.entry(term) {
					formula.insert((
						src.clone(),
						src_factor.clone(),
						op.clone(),
						dst.clone(),
						dst_factor.clone()
					));
				}
				// i += 1;
			}
		}
	}
	
	// println!("{} vs {}", formula_blend_map.len(), i);
	
	let term = simplify_term(parse_formula(token_stream));
	
	// assert_eq!(
	// 	format!("{term}"), // src - 1 - (((dst + src).a)) - src.rgb * 0 - 1 + (src > (1 - src + dst.a)) + (1 * (c.a + src) * c)
	// 	"(0 - (1 + (1 - (src + (src + ((c*src) + ((c*c.a) - (src.a + dst.a)))))))) > (0 - (1 - ((c*src) + ((c*c.a) - src.a))))"
	// );
	
	let mut token_stream_output = TokenStream::new();
	
	if let hash_map::Entry::Occupied(layout) = formula_blend_map.entry(term) {
		panic!("{layout:?}");
	} else {
		panic!("must evaluate to 'Term*Factor Op Term*Factor', where:\
			\n- each 'Term' is 'src' or 'dst' (mutually-exclusive)\
			\n- each 'Factor' is '0', '1', 'Term', '1-Term', 'Term.a', '1-Term.a', 'c', '1-c', or 'src.a < (1-dst.a)'\
			\n- 'Op' is '+', '-', '<', or '>'\
		");
	}
	
	token_stream_output
}