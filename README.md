Provides two macros, `blend_formula!` and `blend_equation!`, used to evaluate an arbitrary formula to its equivalent GPU blend mode. If none exist, it's a compile-time error.

Provides conversion traits for the corresponding [`wgpu`](https://wgpu.rs/) types through the feature flag `wgpu`.

## Examples

```rust
use blend_formula::*;

 // Formulae:
assert_eq!(blend_formula!(src*src.a + dst*(1 - src.a)), BlendFormula {
    src_factor: BlendFactor::SrcAlpha,
    dst_factor: BlendFactor::OneMinusSrcAlpha,
    operation: BlendOperation::Add
});
assert_eq!(blend_formula!(-src), BlendFormula {
    src_factor: BlendFactor::One,
    dst_factor: BlendFactor::Zero,
    operation: BlendOperation::RevSub
});
assert_eq!(blend_formula!(dst < src*c), BlendFormula {
    src_factor: BlendFactor::Constant,
    dst_factor: BlendFactor::One,
    operation: BlendOperation::Min
});

 // Equations:
assert_eq!(blend_equation!(src + dst*(1-src.a)), 
    BlendEquation::PREMULTIPLIED_ALPHA_BLENDING
);
assert_eq!(blend_equation!((dst+(src-dst)*src.a).rgb, (dst+src-dst*src).a),
    BlendEquation::ALPHA_BLENDING
);

 // Shortcuts:
assert_eq!(blend_formula!(+), blend_formula!(src+dst));
assert_eq!(blend_formula!(*), blend_formula!(src*dst));
assert_eq!(blend_equation!(-, dst.a), BlendEquation {
    color: blend_formula!(src-dst),
    alpha: blend_formula!(dst),
});
```

