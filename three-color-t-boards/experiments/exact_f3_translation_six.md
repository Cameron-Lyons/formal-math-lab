# Translated native-F₃ model: six-solution prefix validation

The translated full-coordinate model with the four native `e3` constraints
reproduces the known **six** completions of the fixed nine-row prefix from
`exact_native_field_probe.py`. Both independent arbitrary-precision staircase
counters return six. This is a restricted validation, not the unrestricted
board count.

The input retains all 96 variables and all 176 translated-plus-`e3` generators.
It appends 81 equations fixing the **original** colors through `z_v=a+d_v`,
for 257 generators total. The original apex color is one, so its equation is
`x96+2=0`; the offset is fixed to one. No factor of three remains to apply.
The quotient dimension and board count are both six, with divisor and
multiplier one and no coefficient-extension variable.

The appended affine equations have coefficient and augmented rank 80. This
agrees with one existing unary relation among the fixed 81 colors and leaves
16 affine degrees of freedom before the nonlinear equations. The completed
leading ideal includes the linear leading monomial `x96`.

Exactly one solver process was launched, using reviewed build 6b SHA256
`9e17f4224f282a2effa0d7b39a2be793db9f186499313ca395163dee53b4bc3a`.
It used exact sparse linear algebra, one thread, a 16-pair batch limit,
a 30-second child limit, a 60-second outer guard, and 2 GiB address-space limit.

- Child result: exit zero, **one** export-completion marker, no error diagnostics.
- Strict basis header: characteristic three, all 96 expected variables, grevlex.
- Complete leading payload: 101 monomials; both integer counts equal six.
- Child time: 2.627 seconds wall, 2.539 seconds CPU; outer time 2.830 seconds.

The input SHA256 is
`3781763a4a35be2f5dc3f2e0da2ea0cecca805e84ccf38a07f6913fafa0f5b1c`;
the basis SHA256 is
`7a4362f04fd6df02d469349e7e471b1ea58b5d2f4386261978fc1d0cc3bf6f87`.

Artifacts:

- [Result metadata](exact_f3_translation_six.json) and [outer guard result](exact_f3_translation_six.outer.json).
- [Actual input](exact_f3_translation_six.ms) and [81 original-color fixes](exact_f3_translation_six.fixes.json).
- [Solver log](exact_f3_translation_six.log), [basis export](exact_f3_translation_six.basis), and [leading-ideal certificate](exact_f3_translation_six.leading.json).
- [Bounded runner](exact_f3_translation_six.py), which refuses to overwrite existing artifacts.

No unrestricted solve or additional trial was launched.
