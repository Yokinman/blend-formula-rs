pub use blend_formula_proc_macro::blend_formula;

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
	SaturatedSrcAlpha,
}

#[derive(Debug, PartialEq)]
pub enum BlendOperation {
	Add,
	Sub,
	RevSub,
	Min,
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
	 
	// assert_eq!(blend_equation!(+),    BlendEquation { color: blend_formula!(+), alpha: blend_formula!(+) });
	// assert_eq!(blend_equation!(+, <), BlendEquation { color: blend_formula!(+), alpha: blend_formula!(<) });
	// assert_eq!(blend_equation!(-, +), BlendEquation { color: blend_formula!(-), alpha: blend_formula!(+) });
	// assert_eq!(blend_equation!(<, >), BlendEquation { color: blend_formula!(<), alpha: blend_formula!(>) });
	// assert_eq!(blend_equation!(>, -), BlendEquation { color: blend_formula!(>), alpha: blend_formula!(-) });
}

//      (rgba, 0)             => Zero;
//      (rgba, 1)             => One;
//      (rgba, src)           => Src;
//      (rgba, src.a)         => SrcAlpha;
//      (rgba, dst)           => Dst;
//      (rgba, dst.a)         => DstAlpha;
//      (rgba, c)             => Constant;
//      (rgba, 1-src)         => OneMinusSrc;
//      (rgba, 1-src.a)       => OneMinusSrcAlpha;
//      (rgba, 1-dst)         => OneMinusDst;
//      (rgba, 1-dst.a)       => OneMinusDstAlpha;
//      (rgba, 1-c)           => OneMinusConstant;
//      (rgba, src.a<1-dst.a) => SaturatedSrcAlpha;
//  	
//      (rgb, 0)             => Zero;
//      (rgb, 1)             => One;
//      (rgb, src)           => Src;
//      (rgb, src.a)         => SrcAlpha;
//      (rgb, dst)           => Dst;
//      (rgb, dst.a)         => DstAlpha;
//      (rgb, c)             => Constant;
//      (rgb, 1-src)         => OneMinusSrc;
//      (rgb, 1-src.a)       => OneMinusSrcAlpha;
//      (rgb, 1-dst)         => OneMinusDst;
//      (rgb, 1-dst.a)       => OneMinusDstAlpha;
//      (rgb, 1-c)           => OneMinusConstant;
//      (rgb, src.a<1-dst.a) => SaturatedSrcAlpha;
//  	
//      (a, 0)       => {wgpu::BlendFactor::Zero};
//      (a, 1)       => {wgpu::BlendFactor::One};
//      (a, src.a)   => {wgpu::BlendFactor::SrcAlpha};
//      (a, dst.a)   => {wgpu::BlendFactor::DstAlpha};
//      (a, c)       => {wgpu::BlendFactor::Constant};
//      (a, 1-src.a) => {wgpu::BlendFactor::OneMinusSrcAlpha};
//      (a, 1-dst.a) => {wgpu::BlendFactor::OneMinusDstAlpha};
//      (a, 1-c)     => {wgpu::BlendFactor::OneMinusConstant};
