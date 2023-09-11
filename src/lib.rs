pub use blend_formula_proc_macro::blend_formula;
pub use blend_formula_proc_macro::blend_equation;

#[derive(Debug, PartialEq)]
pub enum BlendFactor {
	Zero,
	One,
	Src,
	SrcAlpha,
	Dst,
	DstAlpha,
	Constant,
	OneMinusSrc,
	OneMinusSrcAlpha,
	OneMinusDst,
	OneMinusDstAlpha,
	OneMinusConstant,
    /// min(SrcAlpha, OneMinusDstAlpha)
	SaturatedSrcAlpha,
}

#[derive(Debug, PartialEq)]
pub enum BlendOperation {
	// src + dst
	Add,
	// src - dst
	Sub,
	// dst - src
	RevSub,
	// min(src, dst)
	Min,
	// max(src, dst)
	Max,
}

#[derive(Debug, PartialEq)]
pub struct BlendFormula {
	src_factor: BlendFactor,
	dst_factor: BlendFactor,
	operation: BlendOperation,
}

impl Default for BlendFormula {
	fn default() -> Self {
		BlendFormula {
			src_factor: BlendFactor::SrcAlpha,
			dst_factor: BlendFactor::OneMinusSrcAlpha,
			operation: BlendOperation::Add,
		}
	}
}

#[derive(Debug, PartialEq, Default)]
pub struct BlendEquation {
	color: BlendFormula,
	alpha: BlendFormula,
}

#[cfg(feature = "wgpu")]
mod wgpu {
	use crate::BlendFactor;
	use crate::BlendOperation;
	use crate::BlendFormula;
	use crate::BlendEquation;
	
	impl From<BlendFactor> for wgpu::BlendFactor {
		fn from(value: BlendFactor) -> Self {
			match value {
				BlendFactor::Zero              => Self::Zero,
				BlendFactor::One               => Self::One,
				BlendFactor::Src               => Self::Src,
				BlendFactor::SrcAlpha          => Self::SrcAlpha,
				BlendFactor::Dst               => Self::Dst,
				BlendFactor::DstAlpha          => Self::DstAlpha,
				BlendFactor::Constant          => Self::Constant,
				BlendFactor::OneMinusSrc       => Self::OneMinusSrc,
				BlendFactor::OneMinusSrcAlpha  => Self::OneMinusSrcAlpha,
				BlendFactor::OneMinusDst       => Self::OneMinusDst,
				BlendFactor::OneMinusDstAlpha  => Self::OneMinusDstAlpha,
				BlendFactor::OneMinusConstant  => Self::OneMinusConstant,
				BlendFactor::SaturatedSrcAlpha => Self::SrcAlphaSaturated,
			}
		}
	}
	
	impl From<BlendOperation> for wgpu::BlendOperation {
		fn from(value: BlendOperation) -> Self {
			match value {
				BlendOperation::Add    => Self::Add,
				BlendOperation::Sub    => Self::Subtract,
				BlendOperation::RevSub => Self::ReverseSubtract,
				BlendOperation::Min    => Self::Min,
				BlendOperation::Max    => Self::Max,
			}
		}
	}
	
	impl From<BlendFormula> for wgpu::BlendComponent {
		fn from(value: BlendFormula) -> Self {
			wgpu::BlendComponent {
				src_factor: value.src_factor.into(),
				dst_factor: value.dst_factor.into(),
				operation: value.operation.into(),
			}
		}
	}
	
	impl From<BlendEquation> for wgpu::BlendState {
		fn from(value: BlendEquation) -> Self {
			wgpu::BlendState {
				color: value.color.into(),
				alpha: value.alpha.into(),
			}
		}
	}
}

#[test]
fn blend_formulae() {
	use crate as blend_formula;
	
	use BlendFactor::*;
	use BlendOperation::*;
	
	assert_eq!(blend_formula!(0),       BlendFormula { src_factor: Zero, dst_factor: Zero, operation: Add });
	assert_eq!(blend_formula!(src),     BlendFormula { src_factor: One, dst_factor: Zero, operation: Add });
	assert_eq!(blend_formula!(-src),    BlendFormula { src_factor: One, dst_factor: Zero, operation: RevSub });
	assert_eq!(blend_formula!(dst),     BlendFormula { src_factor: Zero, dst_factor: One, operation: Add });
	assert_eq!(blend_formula!(-dst),    BlendFormula { src_factor: Zero, dst_factor: One, operation: Sub });
	assert_eq!(blend_formula!(src*dst), BlendFormula { src_factor: Dst, dst_factor: Zero, operation: Add });
	
	assert_eq!(blend_formula!(src*src.a + dst*(1 - src.a)), BlendFormula::default());
	assert_eq!(blend_formula!(src*src.a - dst*(1 - src.a)), BlendFormula { src_factor: SrcAlpha, dst_factor: OneMinusSrcAlpha, operation: Sub });
	assert_eq!(blend_formula!(src*src.a < dst*(1 - src.a)), BlendFormula { src_factor: SrcAlpha, dst_factor: OneMinusSrcAlpha, operation: Min });
	assert_eq!(blend_formula!(src*src.a > dst*(1 - src.a)), BlendFormula { src_factor: SrcAlpha, dst_factor: OneMinusSrcAlpha, operation: Max });
	assert_eq!(blend_formula!(dst*src.a + src*(1 - src.a)), BlendFormula { src_factor: OneMinusSrcAlpha, dst_factor: SrcAlpha, operation: Add });
	assert_eq!(blend_formula!(dst*src.a - src*(1 - src.a)), BlendFormula { src_factor: OneMinusSrcAlpha, dst_factor: SrcAlpha, operation: RevSub });
	assert_eq!(blend_formula!(dst*src.a < src*(1 - src.a)), BlendFormula { src_factor: OneMinusSrcAlpha, dst_factor: SrcAlpha, operation: Min });
	assert_eq!(blend_formula!(dst*src.a > src*(1 - src.a)), BlendFormula { src_factor: OneMinusSrcAlpha, dst_factor: SrcAlpha, operation: Max });
	
	assert_eq!(blend_formula!(*), blend_formula!(src*dst));
	assert_eq!(blend_formula!(+), blend_formula!(src+dst));
	assert_eq!(blend_formula!(-), blend_formula!(src-dst));
	assert_eq!(blend_formula!(<), blend_formula!(src<dst));
	assert_eq!(blend_formula!(>), blend_formula!(src>dst));
	
	assert_eq!(blend_equation!(+),    BlendEquation { color: blend_formula!(+), alpha: blend_formula!(+) });
	assert_eq!(blend_equation!(+, <), BlendEquation { color: blend_formula!(+), alpha: blend_formula!(<) });
	assert_eq!(blend_equation!(-, *), BlendEquation { color: blend_formula!(-), alpha: blend_formula!(*) });
	assert_eq!(blend_equation!(<, >), BlendEquation { color: blend_formula!(<), alpha: blend_formula!(>) });
	assert_eq!(blend_equation!(>, -), BlendEquation { color: blend_formula!(>), alpha: blend_formula!(-) });
	
	assert_eq!(blend_equation!(src.rgb*src.a + dst.rgb*(1 - src.a), src.a*dst.a), BlendEquation {
		color: blend_formula!(src*src.a + dst*(1 - src.a)),
		alpha: blend_formula!(src*dst)
	});
	assert_eq!(blend_equation!((src*src.a + dst*(1 - src.a)).rgb, (src*dst).a), BlendEquation {
		color: blend_formula!(src*src.a + dst*(1 - src.a)),
		alpha: blend_formula!(src*dst)
	});
	
	assert_eq!(blend_equation!(dst*(src.a < 1-dst.a)), BlendEquation {
		color: BlendFormula { src_factor: Dst, dst_factor: OneMinusDst, operation: Min },
		alpha: BlendFormula { src_factor: Dst, dst_factor: OneMinusDst, operation: Min }
	});
	assert_eq!(blend_equation!(dst.rgb*(src.a < 1-dst.a), dst.a*(src.a < 1-dst.a)), BlendEquation {
		color: BlendFormula { src_factor: Zero, dst_factor: SaturatedSrcAlpha, operation: Add },
		alpha: BlendFormula { src_factor: Dst,  dst_factor: OneMinusDst,       operation: Min }
	});
}