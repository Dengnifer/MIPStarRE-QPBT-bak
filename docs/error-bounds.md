# Error bounds in the low individual degree and Pauli basis tests

> **Draft status, 2026-09-28.** This report records approved mathematical
> calculations at repository commit
> [`7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9`][baseline-commit]. The two
> selected improvements are **not implemented** in this draft: the LDT proof is
> in progress under issue [#728][issue-728], and the QPBT quantitative proof is
> in progress under issue [#729][issue-729]. No declaration name, pull request,
> validation result, or claim of a proved improved headline is inferred from
> those issues.

The main gains below concern powers and scaling, not only numerical
coefficients. For a small number `x`, replacing `x^(1/40000)` by
`x^(1/8192)` changes how quickly the error tends to zero. Replacing a factor
`k^2 m^4` by `k^(1/4) m^(1/2)` changes how the estimate behaves as the test
parameters grow. These changes are qualitatively different from replacing one
fixed coefficient by a slightly smaller one.

This distinction is especially important for the Pauli basis test. Its standard
error function is

```text
deltaQld(a,b,epsilon,m,d,q)
  = a (md)^a (epsilon^b + q^(-b) + 2^(-bmd)).
```

The same parameter `a` is both the leading coefficient and the polynomial
degree. Absorbing a large numerical coefficient by increasing `a` can therefore
turn a modest polynomial dependence into an enormous one. The selected QPBT
calculation avoids that loss until the final canonical corollary.

The LDT result is also an independent target. Its stronger conclusion is useful
even apart from its later import into QPBT.

## Notation and status convention

For the QPBT discussion, write

\[
 e=\min(\varepsilon,1),\qquad n=md,\qquad r=\frac{n}{q},
 \qquad E_b=e^b+q^{-b}+2^{-bn},
\]

and

\[
 \Delta_{a,b}(\varepsilon,m,d,q)
 =a n^a\bigl(\varepsilon^b+q^{-b}+2^{-bn}\bigr).
\]

The report uses the following status terms.

- **Baseline calculation** means that the number was reconstructed from the
  checked-in proof at the pinned commit, but the dedicated fixed-constant
  baseline theorem required for this project has not yet been verified.
- **NOT IMPLEMENTED (selected; proof in progress)** means that the calculation
  was selected for issues #728 or #729, but no completed declaration or merged
  pull request is evidence for it yet.
- **NOT IMPLEMENTED (deferred)** means that the idea remains outside the two
  selected scopes.
- **REJECTED** means that the proposed inference is unsupported or false for the
  stated proof route; it is not an available improvement.

## Part I: low individual degree test

### Current baseline calculation

The [source theorem `thm:main-formal`][ldt-paper-main] states the final quantum
soundness result for the low individual degree test. The paper prints the error

\[
 \boxed{
 B_{\mathrm{LDT}}
 =100000 k^2m^4\left(
 \varepsilon^{1/40000}+(d/q)^{1/40000}
 +\exp\!\left(-\frac{k}{2560000m^2}\right)
 \right).}
\]

The same expression is the definition of `mainFormalError` in the pinned Lean
tree, and `mainFormal` uses it for all three final consistency conclusions.
Nevertheless, this report treats the unfolded expression as a **baseline
calculation** until issue #728 supplies and verifies the assigned explicit
baseline theorem.

The upstream [definition `mainInductionError`][ldt-induction-error] makes the
current induction-level baseline explicit:

\[
 \begin{aligned}
 I(\varepsilon,\delta,\gamma)
 =m^2\Bigg(&1000k^2m^2\left(
 \varepsilon^{1/1024}+\delta^{1/1024}+\gamma^{1/1024}
 +(d/q)^{1/1024}\right)\\
 &+\exp\!\left(-\frac{k}{80000m^2}\right)\Bigg).
 \end{aligned}
\]

This is the input whose specialization at
\((3\varepsilon,3\varepsilon,3\varepsilon)\) is propagated through the final
consistency argument. It is not itself one of the selected headline changes.

The current Lean domain must be kept unchanged. It assumes a projective
two-space strategy passing with failure at most \(\varepsilon\), a field model,
and

\[
 k\ge 400md,\qquad k>0.
\]

It does not assume \(\varepsilon\le1\), \(d\le q\), or \(k\le q\), and it
includes \(d=0\). The paper prints only \(k\ge md\). The stronger Lean sampling
condition and the nonzero boundary are documented in the
[large-sampling correction][gap-k] and [zero-sampling correction][gap-zero].
The selected theorem strengthens the conclusion on this current Lean domain; it
does not restore the wider printed domain.

### Selected target

The selected calculation is

\[
 \boxed{
 B_{\triangle}
 =\min\!\left\{1,
 10000 k^{1/4}m^{1/2}\left(
 \varepsilon^{1/8192}+(d/q)^{1/8192}
 +\exp\!\left(-\frac{k}{640000m^2}\right)
 \right)\right\}.}
\]

Relative to the baseline calculation, the error and field exponent improves
from \(1/40000\) to \(1/8192\), the external powers improve from
\(k^2m^4\) to \(k^{1/4}m^{1/2}\), and the final exponential tail has a
four-times smaller denominator. This is a mathematical change to the final
consistency argument, not merely sharper coefficient bookkeeping.

#### The complete-measurement triangle

Let \(C_{AB}\) be the bipartite consistency defect of complete measurements
\(A,B\), and let \(D_{AB}\) be the squared state-dependent distance between
their placed operator families. Define the nonnegative projectivity defect

\[
 u_A=\mathbb E_x\sum_a
 \operatorname{ev}_\psi\!\left(\widehat A_a^x-(\widehat A_a^x)^2\right),
\]

and similarly for the other families. Completeness and opposite-factor
commutation give the exact identity

\[
 2C_{AB}=D_{AB}+u_A+u_B.
\]

Combining this identity with the existing three-step squared-distance triangle
gives

\[
 \begin{aligned}
 2C_{AD}
 &\le 6(C_{AB}+C_{CB}+C_{CD})
      -2u_A-6u_B-6u_C-2u_D,\\
 C_{AD}&\le3(C_{AB}+C_{CB}+C_{CD}).
 \end{aligned}
\]

Completeness is essential. The statement is false for arbitrary
submeasurements: if both intermediate submeasurements are zero, all three input
defects can vanish while the endpoint measurements remain inconsistent. The
three applications in the selected proof use only complete measurements:

- initial evaluated consistency follows
  \(G_A(u)\leftrightarrow B(u)\leftrightarrow A(u)\leftrightarrow G_B(u)\),
  with bounds \(s,3\varepsilon,s\);
- Alice's final point conclusion follows
  \(A(u)\leftrightarrow G_B(u)\leftrightarrow Q_A(u)\leftrightarrow Q_B(u)\),
  with bounds \(s,\eta,v/2\);
- Bob's final point conclusion follows
  \(Q_A(u)\leftrightarrow Q_B(u)\leftrightarrow G_A(u)\leftrightarrow B(u)\),
  with bounds \(v/2,\eta,s\).

Here \(G_A,G_B\) and the point families are measurements, while
\(Q_A,Q_B\) are their completed projective replacements. The intermediate
projective submeasurements used by orthogonalization do not enter these
triangles.

#### Scalar propagation

Put

\[
 I=\operatorname{mainInductionError}(3\varepsilon,3\varepsilon,3\varepsilon),
 \qquad s=2I,\qquad r=d/q.
\]

The first linear triangle, followed by the existing Schwartz--Zippel step,
gives

\[
 z=6s+9\varepsilon+mr.
\]

The existing projectivization and completion estimates from the
[source proof of `thm:main-formal`][ldt-paper-final] are then retained:

\[
 c=200z^{1/4}+40z^{1/8}+2z,
 \qquad \eta=z+10z^{1/8},
 \qquad v=6z+6c.
\]

Both corrections matter. The term \(+2z\) is the completion residual. The term
\(10z^{1/8}\) is the repaired replacement error at the paper's line 169; the
paper's exact-\(z\) inference is not valid. The repair is documented in the
[line-169 note][gap-line169].

The final point and full-polynomial consistency errors become

\[
 \begin{aligned}
 P&=3(s+\eta+v/2)
   =3s+30z+1800z^{1/4}+390z^{1/8},\\
 R&=v/2=9z+600z^{1/4}+120z^{1/8}.
 \end{aligned}
\]

When \(0\le z\le1\), the relation \(s\le z/6\) gives
\(P,R\le2221z^{1/8}\). With

\[
 E=\varepsilon^{1/1024}+r^{1/1024}
   +\exp\!\left(-\frac{k}{80000m^2}\right),
\]

the current induction estimates give

\[
 I\le10000k^2m^4E,
 \qquad z\le120010k^2m^4E.
\]

The numerical certificates

\[
 120010<(9/2)^8,
 \qquad 2221(9/2)=9994.5<10000
\]

and eighth-root subadditivity yield the displayed target. The proof must branch
on the **new** target being at least one. In that branch, the universal
consistency bound one applies. In the complementary branch the target itself
forces \(\varepsilon<1\), \(d/q<1\), and \(z<1\).

This treatment preserves the boundary cases. In particular, \(d=0\) remains
allowed. No \(k\le q\) premise is added: when \(d\ge1\), the case \(k>q\)
already lies in the saturated branch, while the \(d=0\) case still uses the
ordinary proof.

#### Why the scalar-only alternative is not a second implementation

An earlier calculation retained fractional prefactors in the existing proof and
gave

\[
 B_{\mathrm{frac}}
 =\min\!\left\{1,
 200k^{1/16}m^{1/8}\left(
 \varepsilon^{1/32768}+(d/q)^{1/32768}
 +\exp\!\left(-\frac{k}{2560000m^2}\right)
 \right)\right\}.
\]

This is dominated by the selected result after capping. Indeed, let

\[
 K=k^{1/16}m^{1/8},\quad
 x=\varepsilon^{1/32768},\quad
 y=(d/q)^{1/32768},\quad
 w=\exp\!\left(-\frac{k}{2560000m^2}\right).
\]

For the uncapped expressions

\[
 S=200K(x+y+w),\qquad
 T=10000K^4(x^4+y^4+w^4),
\]

one has

\[
 T\le\frac{S^4}{160000},
 \qquad \min(1,T)\le\min(1,S).
\]

Thus the scalar-only calculation is a fallback, not a separate selected
improvement.

### LDT candidate inventory

| Candidate and source | Baseline to calculated target | Headline effect | Cost and risk | Status and decision |
|---|---|---|---|---|
| Explicit current headline, [`mainFormalError`][ldt-error] and [`mainFormal`][ldt-main] | Named error to the unfolded formula \(B_{\mathrm{LDT}}\) above | Establishes the numerical point of comparison without changing the theorem | Low mathematical cost; dedicated theorem and audit evidence still required | **Baseline calculation; explicit baseline theorem NOT IMPLEMENTED** |
| **Complete-measurement consistency triangle**, using [`questionSDD_triangle_three`][ldt-distance], [`qBipartiteConsDefect_of_measurements`][ldt-algebra], and the common completion witnesses in [`Completion.lean`][ldt-completion] | \(B_{\mathrm{LDT}}\to B_\triangle\) | Error/field exponent \(1/40000\to1/8192\); \(k^2m^4\to k^{1/4}m^{1/2}\); tail denominator divided by four | Medium implementation; preserve one witness pair and apply the identity only to complete measurements | **NOT IMPLEMENTED (selected; proof in progress in #728)**. Strongest settled native-LDT target and pointwise dominates the scalar-only proposal after capping |
| Multiplicative Bernoulli tail in [`Scalar.lean`][ldt-bernoulli], source `lem:chernoff-bernoulli-matrix` | \(e^{-k/(80000m^2)}\to e^{-k/(1600m)}\) in induction; combined with the triangle would give final tail \(e^{-k/(12800m)}\) | Major improvement to exponential dependence on dimension, but not to the error/field exponent | Medium/high; must change the answer-valued induction and all boundary branches | **NOT IMPLEMENTED (deferred)**. Significant follow-up, but broader than the selected final-triangle proof |
| Preserve fractional prefactors in [`Final.lean`][ldt-final] | \(B_{\mathrm{LDT}}\to B_{\mathrm{frac}}\) | Better coefficient, polynomial powers, and exponent than the current LDT envelope | Low/medium scalar proof | **NOT IMPLEMENTED (deferred and dominated)**. The selected capped triangle bound is no larger everywhere |
| Linear accumulation over dimensions in [`PastingAssembly/ErrorBounds.lean`][ldt-dimension] | \(m^2(\nu+E_m)\to(2m-1)(\nu+E_m)\) | Would reduce the leading induction dependence from order \(k^2m^4\) to order \(k^2m^3\) | Medium/high; requires a new answer-valued induction recurrence | **NOT IMPLEMENTED (deferred)**. Useful scaling gain, but separate from the two final triangles |
| Remove axis-line degree padding in [`PolynomialAgreement.lean`][ldt-axis] | Local collision estimate \(md/q\to d/q\) | Improves the variance contribution \(24m(\varepsilon+\delta+md/q)\) to \(24m(\varepsilon+\delta+d/q)\) | Low locally, medium to propagate | **NOT IMPLEMENTED (deferred)**. Smaller final effect than the selected exponent change |
| Retain sharper projectivization and completion constants in [`Orthonormalization.lean`][ldt-ortho] and [`Completion.lean`][ldt-completion] | \(100z^{1/4}\to84z^{1/4}\); one completion-root coefficient can also be halved before weakening | Coefficient improvement only | Low/medium extraction from existing proofs | **NOT IMPLEMENTED (deferred)**. Does not change a headline rate |
| Retain evaluated commutator scaling in [`MainChain.lean`][ldt-eval-comm] | \(48m(\sqrt\gamma+\sqrt\zeta)\to24\sqrt\zeta+24\sqrt{\gamma(m+1)}\) | Better intermediate dimension dependence | Low locally, substantial downstream re-estimation | **NOT IMPLEMENTED (deferred)**. Existing later envelopes erase the gain |
| Exact distinct-sampling loss in [`DDistinct.lean`][ldt-distinct] | \(k^2/q\to1-(q)_k/q^k\le\min(1,k(k-1)/(2q))\) for \(k\le q\) | Primarily a coefficient improvement | Low, but the \(k>q\) empty-support branch must remain separate | **NOT IMPLEMENTED (deferred)** |
| Existing-cascade fallback in [`Zeta4.lean`][ldt-cascade] | Current repaired estimates imply roughly \(75000k^2m^4E_{1/32768}\) for the weaker conclusion | Improves only the final weakening to \(1/40000\) | Low, but leaves the dominant polynomial scaling | **NOT IMPLEMENTED (deferred)**. Substantially weaker than the selected target |
| Proposed removal of the expansion factor \(m\), compared with [`localToGlobal`][ldt-expansion] | No valid target: the factor is sharp for families depending on one coordinate | None | Mathematical obstruction | **REJECTED**; not an available improvement |
| Proposed restoration of a linear-in-\(k\) `fromHToGError`, compared with [`Statements.lean`][ldt-from-h-to-g] | No valid target: the telescope contains \(k\sqrt{\nu_4(k)}\), and \(\nu_4(k)\) already contains \(k^2\) | None | Would contradict the actual recurrence | **REJECTED**; not an available improvement |
| Direct improvement of the induction exponent \(1/1024\) | No settled replacement was derived | Potentially large, but would require new self-improvement or pasting mathematics | High and mathematically open within this survey | **NOT IMPLEMENTED (deferred)**; no approved proof plan |

## Part II: quantum Pauli basis test

### Current baseline calculation

The [source theorem `thm:pauli`][qpbt-paper-pauli] and Lean theorem
`pauli_soundness` assert the existence of universal \(a,b\) for the error
\(\Delta_{a,b}\). The checked-in theorem does not expose the numerical
witnesses. Tracing the current proof gives the following constants:

\[
 \begin{aligned}
 c&=1024(172+\sqrt{344}),\\
 t&=2(2c+4886363136+4),\\
 Q&=10560(344+3t)+24t+11008,\\
 L&=115\bigl(1+(16Q+8320)^{1/8}\bigr)+1,\\
 H&=1+6(Q^{1/2}+L^{1/4}+Q^{1/4}+1),\\
 D&=4+3\sqrt{Q+H}.
 \end{aligned}
\]

Set \(a=2500000000\), \(\beta=1/80000\), and

\[
 A=2\bigl[a4^a(D^\beta+2)+\sqrt Q+1\bigr]
   +a+\frac{33\beta}{32}+3.
\]

The reconstructed current witnesses are

\[
 \boxed{
 a_0=346\cdot21^3(16\cdot2800^2\cdot1024A)^4,
 \qquad b_0=\frac1{5242880000}.}
\]

The ordered Pauli-edge carrier contributes the cardinality \(86\), and the
extraction construction coefficient is \(48+32\cdot86=2800\). Global-pair
rounding gives exponent \(\beta/4096\); extraction and conversion to an
unsquared state norm divide it by another \(16\). Naimark reduction and
restoration of the raw answers preserve the exponent but square the shared
prefactor parameter twice.

The exact value \(a_0\) is already far more serious than a large leading
coefficient: it is also the degree of \((md)^{a_0}\). A simpler padded
baseline is

\[
 \boxed{a_{\mathrm{base}}=10^{140}4^{10^{10}}.}
\]

This exceeds \(a_0\), but it is not the exact reconstructed witness. Both
\((a_0,b_0)\) and \((a_{\mathrm{base}},b_0)\) remain **baseline calculations**
until issue #729 verifies an explicit fixed-witness theorem. The existing
`pauli_soundness` theorem remains existential.

### Selected target

The selected quantitative calculation is

\[
 \boxed{
 B_{\mathrm{QPBT}}
 =\min\{4,10^{14}(md)^4E_b\},
 \qquad b=\frac1{67108864}.}
\]

It is intended to yield the canonical corollary

\[
 \boxed{\Delta_{100,\,1/67108864}(\varepsilon,m,d,q)}
\]

and the corresponding qubit form by the existing exact unitary transport from
the [source lemma `lem:qld-unitary`][qpbt-paper-unitary]. The degree four
estimate is the sharper quantitative statement; `a = 100` is a convenient
canonical presentation, not an optimized degree.

The exponent improves by

\[
 \frac{5242880000}{67108864}=78.125.
\]

This is **one QPBT implementation scope**. It has three inseparable ingredients:

1. import the selected LDT theorem into the live one-coordinate direct
   low-degree theorem without the current extra square root;
2. keep numerical coefficients separate from polynomial degrees through the
   point, line, rounding, and global-pair estimates;
3. retain the stronger state estimate separately from the squared operator
   estimates through extraction, Naimark reduction, and raw-answer transfer.

This scope does not authorize the deferred commutation, pasting, or rounding
changes listed below.

#### The live low-degree route

The QPBT headline uses the one-coordinate Lean theorem
[`exists_direct_ld_soundness_of_k_eq_one`][direct-one-coordinate], not the
general simultaneous theorem or the seed-indexed theorem
`exists_ld_soundness`. It specializes the [source low-degree theorem
`lem:ld-soundness`][qpbt-paper-ld] to the route used in the Pauli analysis. In
this application, the direct-game simultaneity parameter equals one, while the
inherited LDT sampling parameter is

\[
 N=2560000M^3d.
\]

Applying the selected LDT estimate at \(\tau=1/8192\) gives a one-coordinate
bound that fits \(\delta_{\mathrm{LD}}(30,\tau)\) after using the unit cap. This
avoids the square root introduced only to reuse the older general scalar
helper.

The distinction from other nearby theorems is important. The general direct
transport and the seed-indexed theorem are valid, but they are off the Pauli
headline route. Similarly, the full Magic Square rigidity theorem with
coefficient \(2\cdot10^{12}\) is not the quantitative input used by Pauli
commutation. The live path uses the direct original-state anticommutator bound
\(1183680\varepsilon\). The combined-point construction also uses a
field-valued sandwich measurement and projective rounding, rather than the
separately proved quantum-linearity theorem.

#### Retaining the existing stronger estimates

At the extended dimension \(M=2m+2\le4m\), the existing passing calculation in
the route to [source lemma `lem:qld-4-7`][qpbt-paper-composition] gives, on the
small-parameter branch,

\[
 T_{\mathrm{pass}}
 \le10^8m\bigl(e^{1/512}+r^{1/32}\bigr).
\]

Set

\[
 u=\frac{1}{4194304},\qquad v=\frac{1}{33554432}.
\]

The direct low-degree and rounding estimates then give

\[
 \delta\le10^{22}n^{32}E_u,
 \qquad
 g\le10^7n^4E_v.
\]

For extraction, put

\[
 x=2800(g+\sqrt e+r).
\]

The existing construction already supplies one normalized auxiliary state for
which

\[
 s^2\le16x,
 \qquad
 D_{\mathrm{swap}}\le2x+2r+16\sqrt x.
\]

These estimates should remain attached to the same auxiliary state instead of
being enlarged immediately to a common fourth-root error. The current transfer
inequalities then give

\[
 \begin{aligned}
 D_{\mathrm{isometry}}
  &\le36x+4r+32\sqrt x,\\
 D_{\mathrm{Naimark}}
  &\le204x+12r+96\sqrt x,\\
 D_{\mathrm{raw}}
  &\le472x+24r+192\sqrt x+344e.
 \end{aligned}
\]

Since \(x\le10^{11}n^4E_v\), root subadditivity and exponent monotonicity
give, with \(b=v/2\),

\[
 s,\ D_{\mathrm{raw}}\le10^{14}n^4E_b.
\]

The full-domain proof uses \(e=\min(\varepsilon,1)\) and the independent
trivial bounds: a difference of unit states has norm at most two, and each raw
operator-family distance is at most four. The cases \(r\ge1\) and \(n=1\)
already make the proposed envelope at least four. Zero error is supported, and
no divisibility condition on \(2m+2\) is introduced.

The final theorem must retain the source-facing **raw prescribed-answer
effects**, not only the internally completed Pauli measurements. It must also
retain the range projections used by the existing isometry and Naimark
arguments.

### QPBT candidate inventory

| Candidate and source | Baseline to calculated target | Headline effect | Cost and risk | Status and decision |
|---|---|---|---|---|
| Explicit current existential witnesses, from [`deltaQld`][delta-qld] and [`pauli_soundness`][pauli-soundness] | Existential \((a,b)\) to reconstructed \((a_0,1/5242880000)\), optionally padded by \(a_{\mathrm{base}}\) | Establishes the true numerical baseline, including the enormous polynomial degree | High formal plumbing through opaque existential interfaces | **Baseline calculation; explicit baseline theorem NOT IMPLEMENTED** |
| **Selected quantitative composition**, using the improved one-coordinate LDT import, separate coefficient/degree bounds, and separate state/operator estimates from [`StateExtraction.lean`][state-extraction] through [`RawOperatorTransfer.lean`][raw-transfer] | \(\Delta_{a_0,1/5242880000}\to\min(4,10^{14}n^4E_{1/67108864})\), then canonical \(\Delta_{100,1/67108864}\) | Exponent multiplied by \(78.125\); sharp quantitative degree becomes four; raw effects and qubit form retained | High interface work; same witnesses must survive every estimate | **NOT IMPLEMENTED (selected; proof in progress in #729)** |
| Superseded pre-selection quantitative envelopes from the same mechanisms | Earlier calculations included \(\Delta_{100,1/2621440000}\), then \(\Delta_{100,1/327680000}\); extraction alone gave exponent \(1/655360000\), and an earlier joint LDT/extraction estimate gave \((a,b)=(10^{740},1/268435456)\) | Each improved the traced baseline, but all are weaker than the final selected calculation | Similar or greater plumbing, with worse retained constants | **NOT IMPLEMENTED (superseded)**. Recorded to preserve the survey history; not separate scopes |
| Linear consistency calculus in commutation, starting from [`consistencyDefect_trans_le`][consistency-calculus] and [`CommutingObs.lean`][point-commutation] | Square-root transport to a linear combination for complete POVMs | Could make expanded commutation \(O(\varepsilon)\) and double the downstream exponent | Medium/broad; completeness is load-bearing and propagation is substantial | **NOT IMPLEMENTED (deferred)** |
| Retain the Schmidt-mirror estimate in [`Pasting/Assembly.lean`][qpbt-pasting] | Pasting \(115(\eta^{1/4}+\delta^{1/8})\to12(\eta^{1/4}+\delta^{1/4})\) | Potential twofold headline exponent gain | Medium; localized proof needs a sharper parameterization | **NOT IMPLEMENTED (deferred)** |
| Linear complete-POVM triangle in direct-game passing, at [`EvaluatedLineComparison.lean`][passing-comparison] | Replace a \(4\sqrt{\delta_Q+2\delta_L}\) contribution by a linear one | Potential twofold headline exponent gain | Medium; both axis and diagonal estimates must be propagated | **NOT IMPLEMENTED (deferred)** |
| Linear rounding transport in [`RoundingTransport.lean`][rounding-transport] | Eighth-root loss becomes a fourth-root loss | Potential twofold headline exponent gain | Medium; depends on the stronger consistency calculus | **NOT IMPLEMENTED (deferred)** |
| Combine the preceding four commutation, pasting, passing, and rounding changes | Prospective sixteenfold exponent gain | Potentially larger than any one deferred local change | High, multi-construction; complete constants were not established | **NOT IMPLEMENTED (deferred)**. Not part of issue #729 |
| Sharper combined-point coefficient in [`Points.lean`][combined-points] | About \(3.10\cdot10^{14}\to2.35\cdot10^{11}\) | Coefficient only | Low scalar change | **NOT IMPLEMENTED (deferred)** |
| Retain \(\sqrt m\) in extended lines, beginning at [`Estimates.lean`][extended-lines] | Avoid weakening \(\sqrt m\) to \(m\) | Better intermediate dimension dependence | Medium propagation | **NOT IMPLEMENTED (deferred)**. Smaller effect than removing final degree inflation |
| Weighted projective-rounding triangle in [`ProjectiveRounding.lean`][projective-rounding] | Small-branch coefficient \(220\to(\sqrt{84}+\sqrt{26})^2\) | Coefficient only | Low locally; global threshold still requires checking | **NOT IMPLEMENTED (deferred)** |
| Actual-rounding arithmetic in [`ActualErrorBounds.lean`][actual-rounding] | Safe inspected coefficient \(1024\to734\) | Coefficient only | Low | **NOT IMPLEMENTED (deferred)**. More aggressive rounding was not supported by the inspected calculation |
| Smaller auxiliary LDT sample in [`Transport/Error.lean`][direct-parameter] | \(2560000m^3d\to400m^3d\) | Large raw coefficient reduction, no exponent gain | Medium transport work | **NOT IMPLEMENTED (deferred)** |
| Off-route seed-indexed triangle in [`LowDegreeGameTheorems.lean`][seed-indexed] | Remove the seed-compression exponent halving | Improves `exists_ld_soundness`, but not the live one-coordinate Pauli route | Medium | **NOT IMPLEMENTED (deferred, off route)** |
| Off-route general simultaneous transport in [`Combining/Error.lean`][general-transport] | Retain \(1/40000\) instead of weakening to \(1/80000\) | Improves a general theorem, but not the live one-coordinate Pauli route | Medium | **NOT IMPLEMENTED (deferred, off route)** |
| EPR normalization geometry in [`EPRState.lean`][epr-state] | Squared-state coefficient \(16\to8\) | Coefficient only | Low/medium; preserve the zero-projection branch | **NOT IMPLEMENTED (deferred)** |
| Full Magic Square rigidity in [`MagicSquareTheorems.lean`][ms-rigidity] | \(2\cdot10^{12}\to1788904972224\), about a \(10.6\%\) reduction | No current Pauli headline effect: the live route uses [`msVarObs_anticommutator_le`][ms-anticommutator] with coefficient \(1183680\). A separate optimization could keep the operator conclusions quadratic in \(\sqrt\varepsilon+\sqrt\delta\) while the state conclusion remains linear | Low arithmetic, but agreement hypotheses remain load-bearing | **NOT IMPLEMENTED (deferred, off route)** |
| Aggregate malformed-answer incidences in [`RawOperatorTransfer.lean`][raw-transfer] | \(86\varepsilon\to43\varepsilon\) before raw transfer | Coefficient only | Needs a new edge-sum proof | **NOT IMPLEMENTED (deferred)** |
| Replace the field-valued combined-point construction by quantum linearity | No established quantitative gain for the current proof | None in the live construction | Would change the construction rather than sharpen its present bound | **NOT IMPLEMENTED (deferred, off route)** |
| Condition a collision estimate on a good event in the [source Pauli composition][qpbt-paper-composition] | No valid target without the actual conditional law and restoration of the discarded probability mass | None from the proposed inference | The conditioning changes the distribution and cannot be omitted from the estimate | **REJECTED** |
| Remove symmetrization attainment slack by scalar optimization | No valid target: symmetrization already preserves a supplied strategy's value exactly | None | Supremum attainment is not an arithmetic loss | **REJECTED** |
| Hide the extended-line dimension factor inside the printed polynomial error | No valid target; [`not_exists_combining_quarter_power_bound`][dimension-obstruction] gives a scalar obstruction to that absorption | None | Contradicts the inspected scalar route | **REJECTED** |
| Use the literal multiplicative pasting-error contract | No valid target; the [pasting error note][pasting-product-gap] gives a counterexample and retains the additive correction | None | The product contract is false | **REJECTED** |

## Comparison with the pinned public `qldErr`

### Source and domain

The benchmark is Thomas Vidick's public `MIPRE-formalization` at exact commit
[`286b3ca44f811fa6e37517c04981bc2f164ee6b5`][public-commit]. The inspected
mirror contained 398 manifested source files, all of whose hashes matched its
provenance record. The pinned repository license is
[Apache-2.0][public-license]. No benchmark code was copied, and no benchmark
build was run for this report.

The public theorem [`qld_soundness`][public-soundness] covers arbitrary POVM
strategies. The construction of the mirror witness is present in
[`MirrorExists.lean`][public-mirror], and the divisibility \(4m\mid q\) needed
inside the small-error regime is derived in [`Regime.lean`][public-regime]. An
earlier preliminary concern that either piece was missing is therefore
superseded. Likewise, a suspected square-root mismatch in `deltaLegs_comp` was a
parsing error; the proof and definition agree. Neither concern is a defect of
the public repository.

The public theorem ranges over arbitrary finite fields of characteristic two.
The local theorem uses the fixed admissible field model with \(q=2^\ell\) for
odd \(\ell\), \(d\ge1\), and \(m\mid q\). Numerical comparisons below are on
the shared domain.

### The actual capped composition

The public error is a composed function, not merely an existential slogan. With
the notation \(e,n,r\) above, define

\[
 \begin{aligned}
 Q_V&=2\sqrt{57676416e}+\sqrt{86e}+86e,\\
 D_V&=80Q_V+9228227936e,\\
 P_V&=D_V/2+\sqrt{D_V/2}
  +\sqrt{32D_V+4\sqrt{172e}+2(n+1)/q},\\
 T_V&=5m^2P_V+4Q_V+(n+1)/q,\\
 A_V^{\mathrm{CL}}&=2\cdot10^{11},
 \qquad B_V^{\mathrm{CL}}=1/40000,\\
 L_V&=A_V^{\mathrm{CL}}(4n)^{A_V^{\mathrm{CL}}}
 \left(T_V^{B_V^{\mathrm{CL}}}+q^{-B_V^{\mathrm{CL}}}
 +2^{-4B_V^{\mathrm{CL}}n}\right),\\
 U_V&=2L_V+115352832e,\\
 S_V&=2\sqrt{U_V}+2/q+8U_V,\\
 X_V&=72(10S_V+860e+2\sqrt{172e}+r),\\
 H_V&=2\sqrt{X_V}+2X_V,
 \qquad \eta_V=2-2\sqrt{1-H_V},\\
 F_V&=66S_V+44\sqrt{688e}+46r+1892e+13\sqrt{\eta_V}.
 \end{aligned}
\]

The definition in [`QLDError.lean`][public-qlderr] is

\[
 \operatorname{qldErr}(e,m,d,q)=
 \begin{cases}
 \min(F_V,4),&48n\le q\text{ and }H_V<1,\\
 4,&\text{otherwise}.
 \end{cases}
\]

The component definitions occur in the public files
[`Combined.lean`][public-combined], [`Lines.lean`][public-lines],
[`PaddedLIDT.lean`][public-padded], the classical LDT
[`Parameters.lean`][public-lidt-parameters], [`SwapItemOne.lean`][public-swap-one],
and [`SwapItemTwo.lean`][public-swap-two].

### Existential witness and sharper calculated envelope

The public theorem [`exists_qldErr_le`][public-qlderr-witness] existentially
bounds `qldErr` by the same shape \(\Delta_{a,b}\). Reconstructing the witness
arithmetic used by that proof gives

\[
 b_V=\frac1{2560000}.
\]

If \(A=2\cdot10^{11}\) and

\[
 R=(A4^A+1)(A+9456574485125),
\]

then the traced coefficient parameter is

\[
 \boxed{a_V=10758960R+620538301950748.}
\]

It has \(\log_{10}a_V\approx120411998296.91\). These are reconstructed proof
witnesses, not numbers printed in the existential theorem.

A separate calculation from the definitions avoids the initial weakening
\(e\le e^{1/2}\) in the generic error-shape argument and gives the sharper
**unformalized scalar envelope**

\[
 \boxed{
 \operatorname{qldErr}(e,m,d,q)
 \le\min\!\left(4,\Delta_{10^{12},\,1/1280000}
   (\varepsilon,m,d,q)\right).}
\]

This envelope is not the witness proved by `exists_qldErr_le`; it is a distinct
calculation that still requires a dedicated formal theorem if it is to be
advertised as proved.

### Normalization and conclusion differences

Both comparisons use an **unsquared state norm** and, for each party and basis,
a **sum of squared operator-action norms**. There is no answer averaging and no
factor \(1/2\).

The answer maps differ. The public theorem uses `map rdPauliVec`, which sends
malformed answers to zero and thereby produces a completed answer family. The
local headline compares the raw effect of each prescribed Pauli answer directly
with the ideal projector. The two families agree on legally supported
strategies, but they are not definitionally the same for arbitrary strategies.

On a common encoding, if the state norm and completed-family operator distance
are both at most \(f=\operatorname{qldErr}\), the local raw-transfer calculation
gives

\[
 D_{\mathrm{raw}}\le2f+4f^2+344e\le104f,
\]

using \(4e\le f\le4\). This is a mathematical normalization calculation, not a
proved transport theorem between the two repositories.

The most useful scalar comparison is therefore:

| Bound | Polynomial parameter | Error exponent | Qualification |
|---|---:|---:|---|
| Selected local canonical target | \(100\) | \(1/67108864\) | **NOT IMPLEMENTED**; raw prescribed-answer effects and fixed odd-extension field model |
| Public reconstructed proof witness | \(a_V\) above | \(1/2560000\) | Witness used by the public existential error-shape proof |
| Public sharper calculated envelope | \(10^{12}\) | \(1/1280000\) | Unformalized scalar calculation from the public definitions |

The public calculated exponent is \(52.4288\) times the selected local exponent,
while the selected local polynomial dependence is far smaller. Neither scalar
envelope dominates throughout the shared parameter domain.

### Regimes in which each side is smaller

Take \(m=1\), \(d=n\), \(e=0\), and \(q=2^{n+1}\), with \(n\) an even power
of two. These parameters lie in the shared field domain.

- At \(n=2^{50}\), the selected local canonical expression is below
  \(2^{-16772208}\), while the actual public `qldErr` equals \(4\). The
  public quantity \(L_V\) already forces \(H_V\ge1\).
- At \(n=2^{80}\), the public calculated envelope is below
  \(2^{-9.44\cdot10^{17}}\), while the selected local canonical expression has
  base-two logarithmic size about \(-1.80\cdot10^{16}\). In this regime the
  public calculated envelope is the smaller displayed bound.

These are extreme regimes used to compare asymptotic behavior, not practical
parameter recommendations. At fixed \(md\), reducing \(\varepsilon\) and
increasing \(q\) cannot remove the positive tail term \(2^{-bmd}\). Every
finite-\(md\) envelope therefore has a nonzero floor.

## Implementation pending

As of this draft, there are no proved before/after declaration pairs, merged
pull requests, or validation records for the two selected targets. The rows for
issues #728 and #729 must remain **NOT IMPLEMENTED (selected; proof in
progress)** until exact evidence exists.

Final integration must perform all of the following.

1. Record the actual fixed-constant LDT baseline declaration and the actual
   improved declaration merged for #728. Verify that both retain the full
   `mainFormal` hypotheses, including \(k\ge400md\), \(k>0\), \(d=0\), and
   the three conclusions for one common pair of projective polynomial
   measurements.
2. Replace the LDT calculation status by the **proved** before/after formulas
   only if the merged theorem has exactly those constants. Record the pull
   request, merge commit, axiom-audit entry, and focused and full validation
   actually run.
3. Record the actual fixed-witness QPBT baseline declaration merged for #729,
   including whether it uses \(a_0\) or the padded \(a_{\mathrm{base}}\). Do not
   conflate the two.
4. Record the actual improved QPBT declaration, canonical `deltaQld` corollary,
   and any qubit corollary. Verify that they retain arbitrary strategies, the
   nonnegative error domain, the raw prescribed-answer effects, the isometry
   range projections, and one common auxiliary state.
5. Replace the QPBT calculation status by the **proved** target only if the
   merged theorem establishes \(\min(4,10^{14}(md)^4E_{1/67108864})\), the
   canonical \(a=100\) form, or a precisely documented stronger bound. Record
   the exact declarations and pull request rather than suggested names from the
   analysis.
6. Add every new headline to the appropriate LDT or QPBT axiom audit, and record
   the exact audit commands, file checks, project build, local CI, and
   independent review results from the merged heads. This draft supplies none
   of that proof evidence.
7. Update both candidate tables from **NOT IMPLEMENTED** to **IMPLEMENTED** only
   for results present on the merged main branch. All deferred and rejected rows
   remain unchanged.
8. Keep the benchmark qualifications: no cross-repository raw-answer transport
   has been proved, the public calculated \((10^{12},1/1280000)\) envelope is
   not the same as its reconstructed existential witness, and no benchmark
   build was run here.

The principal remaining implementation risk is not an unresolved mathematical
selection. It is extracting fixed numerical witnesses from existential
interfaces and preserving the same measurements, auxiliary state, isometries,
and range projections through the stronger estimates.

[baseline-commit]: https://github.com/Dengnifer/MIPStarRE-QPBT/commit/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9
[issue-728]: https://github.com/Dengnifer/MIPStarRE-QPBT/issues/728
[issue-729]: https://github.com/Dengnifer/MIPStarRE-QPBT/issues/729
[ldt-paper-main]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/references/ldt-paper/test_definition.tex#L177-L202
[ldt-paper-final]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/references/ldt-paper/inductive_step.tex#L108-L234
[ldt-error]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean#L28-L61
[ldt-main]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean#L288-L327
[ldt-induction-error]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/LDT/MainInductionStep/Defs.lean#L466-L480
[gap-k]: paper-gaps/issue-906-main-formal-k-bound.tex
[gap-zero]: paper-gaps/issue-422-main-formal-zero-k-boundary.tex
[gap-line169]: paper-gaps/issue-1099-line169-triangle-sub-loss.tex
[ldt-distance]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/LDT/Preliminaries/DistanceBounds.lean#L42-L70
[ldt-algebra]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/LDT/Test/StrategyRole/Algebra.lean#L94-L125
[ldt-completion]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/LDT/Test/MainTheorem/SourceRoleRegister/Completion.lean#L778-L835
[ldt-bernoulli]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/LDT/Pasting/Bernoulli/Scalar.lean#L394-L470
[ldt-final]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/LDT/Test/MainTheorem/SourceRoleRegister/Final.lean#L334-L430
[ldt-dimension]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly/ErrorBounds.lean#L25-L90
[ldt-axis]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/LDT/Preliminaries/PolynomialAgreement.lean#L205-L245
[ldt-ortho]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean#L20-L65
[ldt-eval-comm]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG/MainChain.lean#L150-L190
[ldt-distinct]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/LDT/Pasting/Core/DDistinct.lean#L1-L75
[ldt-cascade]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/Zeta4.lean#L190-L250
[ldt-expansion]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Results.lean#L300-L345
[ldt-from-h-to-g]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/LDT/Pasting/Statements.lean#L110-L145
[qpbt-paper-ld]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex#L410-L458
[qpbt-paper-pauli]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex#L1426-L1447
[qpbt-paper-composition]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex#L1267-L1404
[qpbt-paper-unitary]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex#L1666-L1876
[delta-qld]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Test/SoundnessDefs.lean#L30-L38
[pauli-soundness]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Test/Soundness.lean#L40-L64
[direct-one-coordinate]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Combining/DirectLowDegree/Soundness.lean#L228-L313
[state-extraction]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Extraction/StateExtraction.lean#L97-L130
[raw-transfer]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Test/Soundness/RawOperatorTransfer.lean#L391-L425
[consistency-calculus]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Games/DistanceTheorems/Calculus.lean#L300-L345
[point-commutation]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Observables/WinImplications/CommutingObs.lean#L450-L500
[qpbt-pasting]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Games/Sandwich/Pasting/Assembly.lean#L714-L790
[passing-comparison]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Combining/ExtendedLineGame/EvaluatedLineComparison.lean#L245-L285
[rounding-transport]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Games/DistanceTheorems/RoundingTransport.lean#L120-L175
[combined-points]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Combining/Points.lean#L55-L90
[extended-lines]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Combining/ExtendedLines/Estimates.lean#L235-L280
[projective-rounding]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Games/DistanceTheorems/ProjectiveRounding.lean#L475-L525
[actual-rounding]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Combining/ActualErrorBounds.lean#L20-L63
[direct-parameter]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Error.lean#L65-L95
[seed-indexed]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean#L70-L115
[general-transport]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/Error.lean#L215-L255
[epr-state]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Extraction/EPRState.lean#L135-L173
[ms-rigidity]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Test/MagicSquareTheorems.lean#L640-L675
[ms-anticommutator]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Observables/WinImplications/AnticommutingObs.lean#L131-L155
[dimension-obstruction]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/MIPStarRE/QPBT/Combining/ErrorObstruction.lean#L24-L50
[pasting-product-gap]: paper-gaps/qpbt_pasting-product-error.tex
[public-commit]: https://github.com/vidick/MIPRE-formalization/tree/286b3ca44f811fa6e37517c04981bc2f164ee6b5
[public-license]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/LICENSE
[public-qlderr]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/QLDError.lean#L78-L100
[public-qlderr-witness]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/QLDError.lean#L297-L305
[public-soundness]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/Soundness.lean#L525-L574
[public-mirror]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/MirrorExists.lean#L180-L207
[public-regime]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/Regime.lean#L45-L72
[public-combined]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/Combined.lean#L340-L360
[public-lines]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/Lines.lean#L1015-L1040
[public-padded]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/PaddedLIDT.lean#L160-L180
[public-lidt-parameters]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/LIDT/Adapter/Parameters.lean#L40-L60
[public-swap-one]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/SwapItemOne.lean#L138-L155
[public-swap-two]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/SwapItemTwo.lean#L295-L315
