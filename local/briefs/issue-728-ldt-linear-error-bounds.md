# Issue 728: LDT Linear Error Bound

Source statements: `thm:main-formal` in
`references/ldt-paper/test_definition.tex:180-202`, its construction in
`references/ldt-paper/inductive_step.tex:68-234`, and
`prop:simeq-triangle-inequality` in
`references/ldt-paper/preliminaries.tex:649-684`.

First expose the current corrected theorem as
`Test.main_formal_explicit_baseline`, with exactly the existing hypotheses
`k >= 400md` and `k > 0`, the same projective polynomial witnesses, and the
explicit error

`100000 k^2 m^4 (eps^(1/40000) + (d/q)^(1/40000)
  + exp(-k/(2560000m^2)))`.

For complete measurements, use the projectivity defect
`u_A = <sum_a (A_a - A_a^2)>` and the exact identity
`2 C(A,B) = D(A,B) + u_A + u_B`.  The existing three-link squared-distance
triangle then gives the linear consistency triangle
`C(A,D) <= 3(C(A,B) + C(C,B) + C(C,D))`.  Completeness is essential; do not
export or apply this as a submeasurement theorem.

Apply the triangle to the existing unsymmetrized role-register witnesses.  If
`s = 2I`, the first triangle gives `z = 6s + 9eps + md/q`.  Keep the literal
completion terms

- `c = 200z^(1/4) + 40z^(1/8) + 2z`,
- `eta = z + 10z^(1/8)`,
- `v = 6z + 6c`.

The final point error is `3(s + eta + v/2)` and the full-polynomial error is
`v/2`.  For `z <= 1`, both are at most `2221z^(1/8)`.  The induction bound
gives

`z <= 120010 k^2 m^4
  (eps^(1/1024) + (d/q)^(1/1024) + exp(-k/(80000m^2)))`.

The certificates `120010 <= (9/2)^8` and `2221*(9/2) <= 10000`, together with
three square-root envelope steps, yield the uncapped error

`T = 10000 k^(1/4) m^(1/2)
  (eps^(1/8192) + (d/q)^(1/8192) + exp(-k/(640000m^2)))`.

The public theorem uses `min(1,T)`.  Its saturated branch comes directly from
the normalized consistency bound and is independent of the old error.  On
`eps >= 0`, `k > 0`, the new capped error is at most
`min(1, mainFormalError)`; when `mainFormalError < 1`, Lean proves the stronger
`10T <= mainFormalError` and hence strict improvement.

The implementation is additive.  Existing declarations and the source-labelled
blueprint theorem are unchanged.  Separate Lean-only blueprint entries record
the explicit baseline, complete-measurement triangle, improved headline, and
scalar comparison.  Canonical CI, independent review, publication, and merge
remain with the integration coordinator.
