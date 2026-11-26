# Translated native-F₃ model: six-solution prefix validation

The translated full-coordinate model with the four native `e3` equations reproduces the known **6** completions of the fixed nine-row prefix from `exact_native_field_probe.py`. Both independent big-integer staircase counters return 6. This validates a fixed prefix only and does not compute the unrestricted count.

The input keeps all 96 variables and all 176 translated-plus-`e3` generators, then appends 81 equations fixing the **original** cell colors via `z_v = a + d_v` (257 generators total). Because the original apex color is 1, its constraint `x96 + 2 = 0` pins `a = 1`, removing the three-way shift factor. Both the quotient dimension and board count are 6 directly (divisor and multiplier 1, with no extension-field variable).

Those 81 affine constraints have coefficient and augmented rank 80, matching one unary relation among the 81 fixed cells and leaving 16 affine degrees of freedom before nonlinear constraints. The completed leading ideal includes the linear leading monomial `x96`.

One solver process ran using reviewed build 6b (SHA256 `9e17f4224f282a2effa0d7b39a2be793db9f186499313ca395163dee53b4bc3a`), with exact sparse linear algebra, 1 thread, a 16-pair batch limit, a 30-second child limit, a 60-second outer guard, and a 2 GiB address-space cap:

- Child exit status: 0, **one** export-completion marker, no errors.
- Basis header: characteristic 3, all 96 expected variables, grevlex order.
- Leading ideal: 101 monomials; both integer counters returned 6.
- Runtime: 2.627 s child wall time, 2.539 s child CPU time, 2.830 s outer wall time.

Hashes:
- Input SHA256: `3781763a4a35be2f5dc3f2e0da2ea0cecca805e84ccf38a07f6913fafa0f5b1c`
- Basis SHA256: `7a4362f04fd6df02d469349e7e471b1ea58b5d2f4386261978fc1d0cc3bf6f87`

Artifacts:
- [Result metadata](exact_f3_translation_six.json) and [outer guard result](exact_f3_translation_six.outer.json)
- [Actual input](exact_f3_translation_six.ms) and [81 original-color fixes](exact_f3_translation_six.fixes.json)
- [Solver log](exact_f3_translation_six.log), [basis export](exact_f3_translation_six.basis), and [leading-ideal certificate](exact_f3_translation_six.leading.json)
- [Bounded runner](exact_f3_translation_six.py) (refuses to overwrite existing files)

No unrestricted run or extra trial was started.
