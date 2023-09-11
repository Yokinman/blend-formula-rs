//! Provides two macros, [`blend_formula!`](blend_formula) and
//! [`blend_equation!`](blend_equation), used to evaluate an arbitrary formula
//! to its equivalent GPU blend mode. If none exist, it's a compile-time error.
//! 
//! Valid formulae are equivalent to some `Term*Factor Op Term*Factor`, where:
//! 
//! - Each `Term` is either "`src`" or "`dst`" (mutually exclusive).
//! - Each `Factor` is a [`BlendFactor`].
//! - `Op` is a [`BlendOperation`].
//! 
//! If a formula is for a color or alpha [equation](BlendEquation), non-scalar
//! terms must be "converted" using the appropriate accessor (`.rgb` or `.a`).
//! 
//! For convenience, any valid operator can be used to combine the source and
//! destination without a factor (`+`, `-`, `<`, `>`, `*`).
//! 
//! # Examples
//! 
//! ```
//! use blend_formula::*;
//! 
//!  // Formulae:
//!	assert_eq!(blend_formula!(src*src.a + dst*(1 - src.a)), BlendFormula {
//!     src_factor: BlendFactor::SrcAlpha,
//!     dst_factor: BlendFactor::OneMinusSrcAlpha,
//!     operation: BlendOperation::Add
//! });
//!	assert_eq!(blend_formula!(-src), BlendFormula {
//!     src_factor: BlendFactor::One,
//!     dst_factor: BlendFactor::Zero,
//!     operation: BlendOperation::RevSub
//! });
//!	assert_eq!(blend_formula!(dst < src*c), BlendFormula {
//!     src_factor: BlendFactor::Constant,
//!     dst_factor: BlendFactor::One,
//!     operation: BlendOperation::Min
//! });
//! 
//!  // Equations:
//! assert_eq!(blend_equation!(src + dst*(1-src.a)), 
//!     BlendEquation::PREMULTIPLIED_ALPHA_BLENDING
//! );
//! assert_eq!(blend_equation!((dst+(src-dst)*src.a).rgb, (dst+src-dst*src).a),
//!     BlendEquation::ALPHA_BLENDING
//! );
//! 
//!  // Shortcuts:
//! assert_eq!(blend_formula!(+), blend_formula!(src+dst));
//! assert_eq!(blend_formula!(*), blend_formula!(src*dst));
//! assert_eq!(blend_equation!(-, dst.a), BlendEquation {
//!     color: blend_formula!(src-dst),
//!     alpha: blend_formula!(dst),
//! });
//! ```
//! 
//! # Conversion
//! 
//! If the feature `wgpu` is enabled, conversion traits are implemented for the
//! corresponding types of the [`wgpu`](https://wgpu.rs/) crate.
//! 
//! - `blend_formula::BlendFactor` -> `wgpu::BlendFactor`
//! - `blend_formula::BlendOperation` -> `wgpu::BlendOperation`
//! - `blend_formula::BlendComponent` -> `wgpu::BlendComponent`
//! - `blend_formula::BlendState` -> `wgpu::BlendState`

/// Produces a [`BlendEquation`] equivalent to some formulae, if one exists.
/// 
/// Two comma-separated formulas can be given to provide separate
/// formulas for the color and alpha channels.
/// 
/// See the main [crate] documentation for more details.
pub use blend_formula_proc_macro::blend_equation;

/// Produces a [`BlendFormula`] equivalent to some formula, if one exists.
/// 
/// See the main [crate] documentation for more details.
pub use blend_formula_proc_macro::blend_formula;

/// Corresponds to [`wgpu::BlendFactor`](https://docs.rs/wgpu/latest/wgpu/enum.BlendFactor.html).
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
pub enum BlendFactor {
	/** `0`               */ Zero,
	/** `1`               */ One,
	/** `src`             */ Src,
	/** `src.a`           */ SrcAlpha,
	/** `dst`             */ Dst,
	/** `dst.a`           */ DstAlpha,
	/** `c`               */ Constant,
	/** `1-src`           */ OneMinusSrc,
	/** `1-src.a`         */ OneMinusSrcAlpha,
	/** `1-dst`           */ OneMinusDst,
	/** `1-dst.a`         */ OneMinusDstAlpha,
	/** `1-c`             */ OneMinusConstant,
    /** `src.a < 1-dst.a` */ SaturatedSrcAlpha,
}

/// Corresponds to [`wgpu::BlendOperation`](https://docs.rs/wgpu/latest/wgpu/enum.BlendOperation.html).
#[derive(Copy, Clone, Debug, Default, Hash, Eq, PartialEq)]
pub enum BlendOperation {
	#[default]
	/** `src + dst` */ Add,
	/** `src - dst` */ Sub,
	/** `dst - src` */ RevSub,
	/** `src < dst` */ Min,
	/** `src > dst` */ Max,
}

/// Corresponds to [`wgpu::BlendComponent`](https://docs.rs/wgpu/latest/wgpu/struct.BlendComponent.html).
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub struct BlendFormula {
    /// Multiplier for the source, which is produced by the fragment shader.
	pub src_factor: BlendFactor,
    /// Multiplier for the destination, which is stored in the target.
	pub dst_factor: BlendFactor,
    /// The binary operation applied to the source and destination,
    /// multiplied by their respective factors.
	pub operation: BlendOperation,
}

impl BlendFormula {
    /// Default blending formula that replaces the destination with the source.
    /// 
	/// Equivalent to `blend_formula!(src)`.
    pub const REPLACE: Self = Self {
        src_factor: BlendFactor::One,
        dst_factor: BlendFactor::Zero,
        operation: BlendOperation::Add,
    };
	
	/// Alpha blending formula that combines the destination with the source.
	/// 
	/// Equivalent to `blend_formula!(src + dst*(1-src.a))`.
	pub const OVER: Self = Self {
		src_factor: BlendFactor::One,
		dst_factor: BlendFactor::OneMinusSrcAlpha,
		operation: BlendOperation::Add,
	};
}

impl Default for BlendFormula {
	fn default() -> Self {
		Self::REPLACE
	}
}

/// Corresponds to [`wgpu::BlendState`](https://docs.rs/wgpu/latest/wgpu/struct.BlendState.html).
#[derive(Copy, Clone, Debug, Default, Hash, Eq, PartialEq)]
pub struct BlendEquation {
	pub color: BlendFormula,
	pub alpha: BlendFormula,
}

impl BlendEquation {
    /// Default blending equation that replaces the destination with the source.
    /// 
    /// Equivalent to `blend_equation!(src)`.
	pub const REPLACE: Self = Self {
		color: BlendFormula::REPLACE,
		alpha: BlendFormula::REPLACE,
	};
	
	/// Standard alpha blending without premultiplied color channels.
	/// 
	/// Equivalent to
	/// `blend_equation!((src*src.a+dst*(1-src.a)).rgb, (src+dst*(1-src.a)).a)`.
	pub const ALPHA_BLENDING: Self = Self {
		color: BlendFormula {
			src_factor: BlendFactor::SrcAlpha,
			dst_factor: BlendFactor::OneMinusSrcAlpha,
			operation: BlendOperation::Add,
		},
		alpha: BlendFormula::OVER,
	};
	
	/// Standard alpha blending with premultiplied color channels.
	/// 
	/// Equivalent to `blend_equation!(src + dst*(1-src.a))`.
	pub const PREMULTIPLIED_ALPHA_BLENDING: Self = Self {
		color: BlendFormula::OVER,
		alpha: BlendFormula::OVER,
	};
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
fn saturated_src_alpha() {
	//! Saturated source alpha uses a factor of "1" for the alpha channel, so
	//! it's only usable as a color channel factor.
	
	use crate as blend_formula;
	
	use BlendFactor::*;
	use BlendOperation::*;
	
	assert_eq!(blend_equation!(dst*(src.a < 1-dst.a)), BlendEquation {
		color: BlendFormula { src_factor: Dst, dst_factor: OneMinusDst, operation: Min },
		alpha: BlendFormula { src_factor: Dst, dst_factor: OneMinusDst, operation: Min }
	});
	assert_eq!(blend_equation!(dst.rgb*(src.a < 1-dst.a), dst.a*(src.a < 1-dst.a)), BlendEquation {
		color: BlendFormula { src_factor: Zero, dst_factor: SaturatedSrcAlpha, operation: Add },
		alpha: BlendFormula { src_factor: DstAlpha, dst_factor: OneMinusDstAlpha, operation: Min }
	});
}