# Error bounds in the low individual degree and Pauli basis tests

> **Authored report status, October 1, 2026.** The bounded two-improvement scope
> consists of the native LDT improvement from issue [#728][issue-728] and the
> quantitative QPBT improvement from issue [#729][issue-729]. The LDT result was
> proved and merged by [PR #731][pr-731] as
> [`fac99fdf22bbdbb83a2376ca48cd679dc7d13750`][ldt-merge]. The final QPBT source
> head [`6ea9f96bd86aaaad613130dea49eefdf6e80c5a9`][qpbt-final-head] was proved,
> reviewed, and merged normally by [PR #736][pr-736] as
> [`0b847308c30769be983bbd05c297e1014db76590`][qpbt-merge]. The stronger
> source-argument candidate in issue [#735][issue-735] remains mathematically
> accepted and unimplemented under the owner's stopping rule; this is a scope
> decision, not a ranking against the implemented result. This report and its
> separate ledger are authored and await their own normal CI, `review.sh`, and
> independent mathematical review; this status does not claim those gates have
> completed.

> **QPBT publication evidence.** Exact-head CI passed all eight steps and all
> nine contexts in 567 summed step-seconds. The canonical declaration check
> resolved 2,198 Lean references, and the blueprint axiom closure checked 2,187
> declarations across 407 modules with zero failures: 403 statement-only and
> 1,784 proof-level placements. Review
> [#5372229944][qpbt-mathematical-review] approved the mathematics and requested
> only prose and dependency repairs; review
> [#5372895844][qpbt-final-review] approved the final editorial patch after
> independently checking that code and formulas were unchanged. The ordinary
> seven-gate merge had no override. This report and its ledger have not
> themselves yet passed normal CI, `review.sh`, or the separate independent
> mathematical review.

In plain terms, the merged LDT theorem changes both the asymptotic error decay
and the parameter dependence. It replaces the baseline powers
\(\varepsilon^{1/40000}\), \((d/q)^{1/40000}\), and \(k^2m^4\) by
\(\varepsilon^{1/8192}\), \((d/q)^{1/8192}\), and
\(k^{1/4}m^{1/2}\), while improving the exponential-tail denominator from
\(2560000m^2\) to \(640000m^2\).

The merged QPBT theorem improves the exact baseline exponent from
\(1/5242880000\) to \(1/67108864\), a factor of \(625/8=78.125\), while
retaining the fractional dimension factor established by its scalar argument:

\[
 \boxed{H=\min\{4,10769120\,
 m^{20481/262144}d^{1/64}E_{1/67108864}\}}.
\]

One witness controls the unsquared state norm and both raw summed-squared
prescribed-answer operator errors, and the exact qubit theorem preserves all
three metrics. The older common bounds
\(I=\min\{4,10^9(md)^2E_b\}\) and
\(C=\min\{4,10^{14}(md)^4E_b\}\) remain available as compatibility
corollaries, with the proved chain \(H\le I\le C\); they are not the strongest
implemented common headline.

Separately, the source-argument survey with the LDT input frozen found a
higher-exponent structural candidate
\(\min\{4,10^{10}(md)^{15/4+5/262144}E_{1/1048576}\}\). Its exponent is
64 times larger than \(1/67108864\). That gain remains important, but issue
#735 is deferred by scope rather than by mathematical ranking. The merged #736
proof preserves the native capped LDT error and the mixed rounding/extraction
terms before deriving \(H\). The exact mixed construction remains a distinct
theorem; the common headline does not replace it. The scalar comparisons below
rank common envelopes only and do not order them against the native mixed
state/operator estimates.

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
turn a modest polynomial dependence into an enormous one. The current and
follow-up QPBT calculations avoid that loss until their final canonical
corollaries.

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

- **Baseline calculation** means that the number was reconstructed from a proof
  without a dedicated fixed-constant theorem. It remains useful historical
  evidence, but it is weaker than a proved explicit baseline.
- **Proved explicit baseline** means that a dedicated declaration with the
  displayed constants has passed exact-head validation. The report states
  separately whether that declaration is local or merged.
- **IMPLEMENTED (selected; proved and merged)** means that the selected LDT
  declaration, its baseline, and its comparison evidence are present on the
  merged branch.
- **IMPLEMENTED (proved and merged)** means that the QPBT declaration and its
  stated comparisons are present at final source head `6ea9f96b` and merge
  commit `0b847308`, with exact-head CI and independent review evidence.
- **IMPLEMENTED (retained compatibility result)** means that an older common
  envelope remains proved but is now a weakening of a sharper merged theorem.
- **MATHEMATICALLY CHECKED, NOT LEAN-IMPLEMENTED** means that an author derived
  the complete mathematical target and an independent referee accepted it, but
  the required Lean declarations do not yet exist.
- **MATHEMATICALLY CHECKED FROM EXISTING CONSTRUCTORS, NOT LEAN-IMPLEMENTED**
  means that the calculation was checked against the actual proved constructors
  and their hypotheses, but no dedicated Lean headline states the result.
- **NOT IMPLEMENTED (deferred)** means that the idea remains outside an adopted
  implementation scope.
- **REJECTED** means that the proposed inference is unsupported or false for the
  stated proof route; it is not an available improvement.

## Part I: low individual degree test

### Proved explicit baseline

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
tree, and `mainFormal` uses it for all three final consistency conclusions. The
merged theorem
[`MIPStarRE.LDT.Test.main_formal_explicit_baseline`][ldt-baseline-proved]
unfolds this expression and proves the same three conclusions for the same
witness pair under exactly the corrected hypotheses of `mainFormal`. Thus the
displayed expression is now a **proved explicit baseline**, not only a
reconstructed calculation. The source-labelled theorem and its named error
remain unchanged.

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

Both merged before/after declarations keep the current Lean domain unchanged.
They assume a heterogeneous projective strategy on two finite local spaces, a
field model, failure probability at most \(\varepsilon\), and

\[
 k\ge 400md,\qquad k>0.
\]

Each declaration produces one pair of projective polynomial measurements that
satisfies all three final consistency conclusions simultaneously. Neither adds
an assumption \(\varepsilon\le1\), \(d\le q\), or \(k\le q\); the cases
\(d=0\) and \(k>q\) remain included. The paper prints only \(k\ge md\). The
stronger Lean sampling condition and the nonzero boundary are documented in the
[large-sampling correction][gap-k] and [zero-sampling correction][gap-zero].
The merged theorem strengthens the conclusion on this current Lean domain; it
does not restore the wider printed domain.

### Implemented selected result

The merged theorem
[`MIPStarRE.LDT.Test.main_formal_linear_triangle_bound`][ldt-improved-proved]
proves

\[
 \boxed{
 B_{\triangle}
 =\min\!\left\{1,
 10000 k^{1/4}m^{1/2}\left(
 \varepsilon^{1/8192}+(d/q)^{1/8192}
 +\exp\!\left(-\frac{k}{640000m^2}\right)
 \right)\right\}.}
\]

Relative to the proved baseline, the error and field exponent improves
from \(1/40000\) to \(1/8192\), the external powers improve from
\(k^2m^4\) to \(k^{1/4}m^{1/2}\), and the final exponential tail has a
four-times smaller denominator. This is a mathematical change to the final
consistency argument, not merely sharper coefficient bookkeeping.

The proved comparison is precise about saturation. On
\(\varepsilon\ge0\) and \(k>0\),
[`mainFormalLinearTriangleError_le_min_mainFormalError`][ldt-comparison-le]
shows

\[
 B_{\triangle}\le \min\{1,B_{\mathrm{LDT}}\}.
\]

If \(B_{\mathrm{LDT}}<1\),
[`mainFormalLinearTriangleError_lt_min_mainFormalError`][ldt-comparison-lt]
proves the inequality is strict; its proof derives the scalar unit regime and
establishes that ten times the uncapped new error is at most the old error. No
uniform strictness is claimed when the old error is at least one, because the
new bound may also saturate at one.

#### The complete-measurement triangle

For complete measurements on a common Hilbert space, let \(C_{AB}\) be the
consistency defect formed from the real part of the off-diagonal expectation,
and let \(D_{AB}\) be their squared state-dependent distance. The real part is
essential because products of effects on a common space need not be Hermitian.
After placing the two measurements on opposite tensor factors, those products
are positive and their expectations are already real. Define the nonnegative
projectivity defect

\[
 u_A=\mathbb E_x\sum_a
 \operatorname{ev}_\psi\!\left(\widehat A_a^x-(\widehat A_a^x)^2\right),
\]

and similarly for the other families. Completeness and this real-expectation
convention give the exact identity

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

This is an alternative to the paper's mixed bound
\(\varepsilon+2\sqrt{\delta+\gamma}\), not a uniformly sharper form of that
bound. Both statements require complete measurements. The linear alternative
is useful in the three applications below because it avoids the square-root
loss along this particular final consistency argument.

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

### Remaining structural opportunities and limits

The accepted issue #733 survey identifies further native-LDT opportunities,
but none is part of the merged theorem or authorized here for implementation.
The strongest concrete tail improvement is a multiplicative Bernoulli estimate.
For \(Y\sim\operatorname{Binomial}(k,p)\), the calculation

\[
 \Pr(Y\le d)
 \le \exp(d)(1-p+p/\exp(1))^k
 \le \exp(d-5kp/8)
 \le \exp(-kp/8)
\]

holds when \(d\le kp/2\). At \(p=1/(200m)\), it would change the induction
tail from \(e^{-k/(80000m^2)}\) to \(e^{-k/(1600m)}\), and the merged final
construction would then give \(e^{-k/(12800m)}\). This is a genuine
source-level structural opportunity, not a coefficient tweak, but the scalar
bound still has to be transported through the answer-valued induction and all
boundary branches.

A second concrete direction is to replace the outer dimension accumulation
\(m^2\) by \(2m-1\). The established recurrence has enough scalar slack for
this change, which would reduce the leading induction dependence from order
\(k^2m^4\) to order \(k^2m^3\); after the merged eighth-root final argument,
the corresponding dimension power could become \(m^{3/8}\). The missing work
is an answer-valued induction propagation, so this is not yet a theorem.

The complete-measurement identity cannot simply be reused throughout native
LDT. If \(A\) is complete and \(H\) is only a submeasurement, then

\[
 2C(A,H)=D(A,H)+u_A+u_H-
 \bigl(1-\langle H_{\mathrm{total}}\rangle\bigr).
\]

The missing-mass term has the wrong sign for an unrestricted triangle chain.
Native self-improvement and commutativity also retain weighted boundedness data,
including the operator \(Z\), and their fine-graining steps use projective
submeasurements rather than complete measurements. Improving the
self-improvement exponent therefore requires simultaneous control of its
completeness, consistency, self-consistency, and boundedness conclusions.
Improving full-polynomial commutativity requires a stronger fine-graining
estimate that retains missing mass and boundedness. Improving the native
pasting power requires a new analysis of the slice telescope and incomplete
measurements; deleting the corrected \(k^2\) loss is unsupported.

Sharper orthogonalization, completion, collision, and distinct-sampling
constants remain useful secondary work. They do not supersede the structural
changes in error exponents, parameter powers, or tail decay.

### LDT candidate inventory

| Candidate and source | Baseline to calculated target | Headline effect | Cost and risk | Status and decision |
|---|---|---|---|---|
| Explicit current headline, [`mainFormalError`][ldt-error] and [`mainFormal`][ldt-main] | Named error to the unfolded formula \(B_{\mathrm{LDT}}\) above | Establishes the numerical point of comparison without changing the theorem | Low mathematical cost; preserve every hypothesis, witness, and conclusion | **IMPLEMENTED as the proved baseline in [PR #731][pr-731]** by [`main_formal_explicit_baseline`][ldt-baseline-proved] |
| **Complete-measurement consistency triangle**, using [`questionSDD_triangle_three`][ldt-distance], [`qBipartiteConsDefect_of_measurements`][ldt-algebra], the common completion witnesses in [`Completion.lean`][ldt-completion], and the [merged complete-measurement triangle][ldt-triangle-proved] | \(B_{\mathrm{LDT}}\to B_\triangle\) | Error/field exponent \(1/40000\to1/8192\); \(k^2m^4\to k^{1/4}m^{1/2}\); tail denominator divided by four | Medium implementation; preserve one witness pair and apply the identity only to complete measurements | **IMPLEMENTED (selected; proved and merged in [PR #731][pr-731])** by [`main_formal_linear_triangle_bound`][ldt-improved-proved]. On \(\varepsilon\ge0\) and \(k>0\), the capped result is no larger than the capped baseline and is proved strict when \(B_{\mathrm{LDT}}<1\); it also pointwise dominates the scalar-only proposal after capping |
| Multiplicative Bernoulli tail in [`Scalar.lean`][ldt-bernoulli], source `lem:chernoff-bernoulli-matrix` | \(e^{-k/(80000m^2)}\to e^{-k/(1600m)}\) in induction; combined with the triangle would give final tail \(e^{-k/(12800m)}\) | Major improvement to exponential dependence on dimension, but not to the error/field exponent | Medium/high; must change the answer-valued induction and all boundary branches | **NOT IMPLEMENTED (deferred)**. Significant follow-up, but broader than the selected final-triangle proof |
| Preserve fractional prefactors in [`Final.lean`][ldt-final] | \(B_{\mathrm{LDT}}\to B_{\mathrm{frac}}\) | Better coefficient, polynomial powers, and exponent than the current LDT envelope | Low/medium scalar proof | **NOT IMPLEMENTED (deferred and dominated)**. The selected capped triangle bound is no larger everywhere |
| Linear accumulation over dimensions in [`PastingAssembly/ErrorBounds.lean`][ldt-dimension] | \(m^2(\nu+E_m)\to(2m-1)(\nu+E_m)\) | Would reduce the leading induction dependence from order \(k^2m^4\) to order \(k^2m^3\) | Medium/high; requires a new answer-valued induction recurrence | **NOT IMPLEMENTED (deferred)**. Useful scaling gain, but separate from the merged final consistency change |
| Remove axis-line degree padding in [`PolynomialAgreement.lean`][ldt-axis] | Local collision estimate \(md/q\to d/q\) | Improves the variance contribution \(24m(\varepsilon+\delta+md/q)\) to \(24m(\varepsilon+\delta+d/q)\) | Low locally, medium to propagate | **NOT IMPLEMENTED (deferred)**. Smaller final effect than the selected exponent change |
| Retain sharper projectivization and completion constants in [`Orthonormalization.lean`][ldt-ortho] and [`Completion.lean`][ldt-completion] | \(100z^{1/4}\to84z^{1/4}\); one completion-root coefficient can also be halved before weakening | Coefficient improvement only | Low/medium extraction from existing proofs | **NOT IMPLEMENTED (deferred)**. Does not change a headline rate |
| Retain evaluated commutator scaling in [`MainChain.lean`][ldt-eval-comm] | \(48m(\sqrt\gamma+\sqrt\zeta)\to24\sqrt\zeta+24\sqrt{\gamma(m+1)}\) | Better intermediate dimension dependence | Low locally, substantial downstream re-estimation | **NOT IMPLEMENTED (deferred)**. Existing later envelopes erase the gain |
| Exact distinct-sampling loss in [`DDistinct.lean`][ldt-distinct] | \(k^2/q\to1-(q)_k/q^k\le\min(1,k(k-1)/(2q))\) for \(k\le q\) | Primarily a coefficient improvement | Low, but the \(k>q\) empty-support branch must remain separate | **NOT IMPLEMENTED (deferred)** |
| Existing-cascade fallback in [`Zeta4.lean`][ldt-cascade] | Current repaired estimates imply roughly \(75000k^2m^4E_{1/32768}\) for the weaker conclusion | Improves only the final weakening to \(1/40000\) | Low, but leaves the dominant polynomial scaling | **NOT IMPLEMENTED (deferred)**. Substantially weaker than the selected target |
| Improve self-improvement's \(1/32\) power | No settled replacement: all four completeness, consistency, self-consistency, and boundedness conclusions must improve together | Potentially large induction gain | Research-level; improving one consistency estimate does not improve the induction input | **NOT IMPLEMENTED (deferred)**; no approved proof plan |
| Improve full-polynomial commutativity quarter powers | No settled replacement without a stronger fine-graining theorem for projective submeasurements | Potentially large error-exponent gain | Must retain missing-mass and weighted-boundedness terms | **NOT IMPLEMENTED (deferred)**; the complete-measurement QPBT argument does not apply automatically |
| Improve native pasting's \(k^2\) or \(1/32\) dependence | No settled replacement for the corrected slice telescope | Potential scaling and exponent gain | Requires a new incomplete-measurement pasting analysis | **NOT IMPLEMENTED (deferred)**; restoring a linear-in-\(k\) expression by dropping the telescope loss is unsupported |
| Proposed removal of the expansion factor \(m\), compared with [`localToGlobal`][ldt-expansion] | No valid target: the factor is sharp for families depending on one coordinate | None | Mathematical obstruction | **REJECTED**; not an available improvement |
| Proposed restoration of a linear-in-\(k\) `fromHToGError`, compared with [`Statements.lean`][ldt-from-h-to-g] | No valid target: the telescope contains \(k\sqrt{\nu_4(k)}\), and \(\nu_4(k)\) already contains \(k^2\) | None | Would contradict the actual recurrence | **REJECTED**; not an available improvement |
| Direct improvement of the induction exponent \(1/1024\) | No settled replacement was derived | Potentially large, but would require new self-improvement or pasting mathematics | High and mathematically open within this survey | **NOT IMPLEMENTED (deferred)**; no approved proof plan |

## Part II: quantum Pauli basis test

### Proved fixed-witness baseline

The [source theorem `thm:pauli`][qpbt-paper-pauli] and Lean theorem
`pauli_soundness` assert the existence of universal \(a,b\) for the error
\(\Delta_{a,b}\). The source prints no numerical exponent. At the original
pinned baseline commit, tracing the proof gives the following constants:

\[
 \begin{aligned}
 c&=1024(172+\sqrt{344}),\\
 t_0&=2(2c+4886363136+4),\\
 Q_0&=10560(344+3t_0)+24t_0+11008,\\
 L_0&=115\bigl(1+(16Q_0+8320)^{1/8}\bigr)+1,\\
 H_0&=1+6(Q_0^{1/2}+L_0^{1/4}+Q_0^{1/4}+1),\\
 D_0&=4+3\sqrt{Q_0+H_0}.
 \end{aligned}
\]

Set \(a_L=2500000000\), \(\beta=1/80000\), and

\[
 A=2\bigl[a_L4^{a_L}(D_0^\beta+2)+\sqrt{Q_0}+1\bigr]
   +a_L+\frac{33\beta}{32}+3.
\]

The fixed coefficients must be distinguished from the error functions used by
the native construction. Define

\[
 Q(e)=Q_0e^{1/8},\qquad
 L(e,r)=L_0(e^{1/64}+r^{1/4}),\qquad
 L_{\mathrm{ext}}(e,r)=mH_0(e^{1/256}+r^{1/16}).
\]

These are respectively `pauliBaselinePointError e`,
`pauliBaselineLineError e r`, and the product of \(m\) with
`pauliBaselineExtendedLineError e r`. Below, \(Q\), \(L\), and
\(L_{\mathrm{ext}}\) abbreviate their values at the current \(e,r\). In
particular, the \(64Q\) term in the native global-pair error vanishes with
\(e\); it does not contain the fixed coefficient \(Q_0\) by itself.

The later fixed-witness proof keeps the enormous projective-setting
coefficient symbolic. Its exact constants are

\[
 \boxed{
 a_0=346\cdot21^3\,
   \operatorname{pauliBaselineProjectiveConstant}^{4},
 \qquad b_0=\frac1{5242880000}.}
\]

The ordered Pauli-edge carrier contributes the cardinality \(86\), and the
extraction construction coefficient is \(48+32\cdot86=2800\). Global-pair
rounding gives exponent \(\beta/4096\); extraction and conversion to an
unsquared state norm divide it by another \(16\). Naimark reduction and
restoration of the raw answers preserve the exponent but square the shared
prefactor parameter twice.

The exact value \(a_0\) is already far more serious than a large leading
coefficient: it is also the degree of \((md)^{a_0}\). The historical scalar
calculation also supplied the simpler padded upper bound

\[
 \boxed{a_{\mathrm{base}}=10^{140}4^{10^{10}}.}
\]

This exceeds \(a_0\), but it is not the exact theorem constant. The declarations
[`pauli_soundness_explicit_baseline`][qpbt-baseline-proved] and
[`pauli_soundness_qubit_explicit_baseline`][qpbt-qubit-baseline-proved] occur in
the merged QPBT proof source. Their assumptions match the source strategy and
nonnegative-error domain, and each produces one common normalized auxiliary
state with the unsquared state estimate and both raw prescribed-answer
summed-squared operator estimates. The padded \(a_{\mathrm{base}}\) remains a
scalar comparison only, and the source-facing `pauli_soundness` theorem remains
existential.

### Merged issue #729 implementation

The merged proof retains the historical structured error

\[
 C=\min\{4,10^{14}n^4E_b\},
 \qquad b=\frac1{67108864}.
\]

Its retained compatibility declarations are `pauli_soundness_quantitative`,
`pauli_soundness_quantitative_canonical`,
`pauli_soundness_qubit_quantitative`, and
`pauli_soundness_qubit_quantitative_canonical`. The bound-strength audit found
that the same constructors support the degree-two common envelope

\[
 \boxed{
 I=\min\{4,10^9n^2E_b\},
 \qquad b=\frac1{67108864}.}
\]

The corresponding paper-shaped corollary remains

\[
 \boxed{\Delta_{100,\,1/67108864}(\varepsilon,m,d,q)},
\]

with an exact qubit counterpart. The canonical coefficient 100 is a convenient
presentation of the source's common \(a(md)^a\) form; it is not the structured
degree. Relative to the exact fixed-witness baseline, the exponent gain is

\[
 \frac{5242880000}{67108864}=78.125.
\]

For every \(\varepsilon\ge0\), Lean proves that \(I\) is strictly below the
explicit baseline evaluated at the clipped error \(e=\min(\varepsilon,1)\):

\[
 I<\Delta_{a_0,b_0}(e,m,d,q).
\]

Since \(H\le I\), the same strict comparison holds for \(H\). This is a
full-domain comparison of the capped new bounds with the clipped historical
baseline; it is not an uncapped comparison with the baseline evaluated at the
original error when \(\varepsilon>1\).

The merged source proves the structured field-coordinate theorem
[`pauli_soundness_quantitative_degree_two`][qpbt-quantitative-proved], its exact
qubit transport, the mixed component theorem and its exact qubit transport, and
the comparisons with \(C\) and the historical baseline. The fractional theorem
constructs the actual witness on its nonsaturated branch; the retained
degree-two theorem reuses that witness through the proved comparison \(H\le I\).

#### The native low-degree route

The native rounded construction uses the arbitrary-strategy one-coordinate
Lean theorem
[`direct_ld_soundness_of_k_eq_one_any_strategy_at_native_error`][direct-one-coordinate],
not the existential common-error theorem, the general simultaneous theorem, or
the seed-indexed theorem `exists_ld_soundness`. It specializes the [source
low-degree theorem `lem:ld-soundness`][qpbt-paper-ld] to the route used in the
Pauli analysis and preserves the native error through Naimark compression. In
this application, the direct-game simultaneity parameter equals one, while the
inherited LDT sampling parameter is

\[
 N=2560000h^3d.
\]

Applying the selected LDT estimate at \(\tau=1/8192\) gives a one-coordinate
bound. If the direct-game dimension is denoted by \(h\), substitution of
\(N=2560000h^3d\) into the merged LDT theorem gives the exact capped error

\[
 \boxed{
 \Lambda_h(t)=\min\!\left\{1,
 400000h^{5/4}d^{1/4}
 \left[(3t)^\tau+(d/q)^\tau+\exp(-4hd)\right]\right\}.}
\]

The factor follows from the equality
\(N^{1/4}=40h^{3/4}d^{1/4}\), not from padding that root to \(40hd\).
The compatibility branch weakens \(\Lambda_h(t)\) to the printed
common form \(\delta_{\mathrm{LD}}(30,\tau)\) before constructing and rounding
the polynomial measurements. The merged native route carries
\(\Lambda_h(t)\) through the direct-coordinate theorem, singleton transport,
arbitrary-strategy compression, and the rounded polynomial-pair construction
for the same measurements. The common \(\delta_{\mathrm{LD}}\) theorem remains
as a paper-shaped corollary. The exact scalar identity and its source-form
weakening are proved in
[`QuantitativeDirectScalars.lean`][qpbt-native-direct-scalars].

For a supplied native error \(\lambda\), put

\[
 \eta(\lambda)=\lambda+\sqrt{220}\lambda^{1/8}
   +2\sqrt2\lambda^{1/2}.
\]

The existing rounded-measurement calculation then supports the concrete error

\[
 \boxed{
 G(\lambda,Q)=\min\!\left\{1,
 32\eta(\lambda)+64Q+\frac{12n+4d+14}{q}\right\}.}
\]

The theorem
[`exists_quantitative_global_pair_witness_native`][qpbt-native-global]
constructs the witness with
\(g=G(\Lambda_{2m+2}(T_{\mathrm{pass}}),Q)\) under the sole scalar premise
\(e\ge0\). It does not assume \(e\le1\) or \(r\le1\). The older
`exists_quantitative_global_pair_witness_at_native_error` packages the same
equality together with the compatibility comparison
\(g\le10^7n^4E_{2b}\) on the restricted scalar branch; that bundled comparison
is not the construction interface.

The merged proof also exports the separated scalar route. For \(0\le s\le1\),
let

\[
\begin{aligned}
 U_s={}&h^{5s/4}d^{s/4}\Bigl[800000^s\bigl(
 e^{\tau s/16}+m^{\tau s/2}e^{\tau s/512}
 +m^{\tau s/2}r^{\tau s/32}+r^{\tau s}\bigr)\\
 &\hspace{8em}+400000^s\bigl((d/q)^{\tau s}
 +\exp(-4hds)\bigr)\Bigr],\qquad L_s=\min\{1,U_s\}.
\end{aligned}
\]

Then \(\lambda^s\le L_s\). With
\(c=(12n+4d+14)/q\), define

\[
 B_G=\min\{1,32L_1+32\sqrt{220}L_{1/8}
       +64\sqrt2L_{1/2}+64Q+c\}.
\]

The exact pair error satisfies \(G\le B_G\). The separated extraction
certificates are

\[
 Y_{\mathrm{sep}}=2800(B_G+\sqrt e+r)
\]

and

\[
\begin{aligned}
 Z_{\mathrm{sep}}=\sqrt{2800}\bigl(&\sqrt{32}L_{1/2}
 +\sqrt{32\sqrt{220}}L_{1/16}
 +\sqrt{64\sqrt2}L_{1/4}\\
 &+8\sqrt Q+\sqrt c+e^{1/4}+\sqrt r\bigr).
\end{aligned}
\]

The merged theorems retain the two conclusions separately:
\(X_{\mathrm{native}}\le Y_{\mathrm{sep}}\) and
\(\sqrt{X_{\mathrm{native}}}\le Z_{\mathrm{sep}}\). These symbols are distinct
from the earlier extraction identity
\(Y_{\mathrm{old}}=48g+2752e+4r\).

The distinction from other nearby theorems is important. The general direct
transport and the seed-indexed theorem are valid, but they are off the Pauli
headline route. Similarly, the full Magic Square rigidity theorem with
coefficient \(2\cdot10^{12}\) is not the quantitative input used by Pauli
commutation. The live path uses the direct original-state anticommutator bound
\(1183680\varepsilon\). The combined-point construction also uses a
field-valued sandwich measurement and projective rounding, rather than the
separately proved quantum-linearity theorem.

#### Retaining the existing stronger estimates

At the extended dimension \(h=2m+2\le4m\), the existing passing calculation in
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

Even if the coefficient-30 low-degree function is retained, fractional-power
subadditivity supports the mixed estimate

\[
 \begin{aligned}
 L_{\mathrm{mix}}=30(hd)^{30}\bigl[&(10^8m)^\tau
   (e^u+r^{\tau/32})\\
   &+q^{-\tau}+2^{-\tau hd}\bigr].
 \end{aligned}
\]

This keeps the factor \(m^\tau\), the field power \(r^{\tau/32}\), the direct
\(q^{-\tau}\) term, and the exact tail separate. The earlier published scalar
interface instead pads that stage to

\[
 \delta\le10^{30}n^{32}E_u,
 \qquad
 g\le10^7n^4E_v.
\]

The native-error route is more informative than \(L_{\mathrm{mix}}\): it carries
\(\Lambda_h(T_{\mathrm{pass}})\) itself into \(G\). The coefficient-30
expression remains a separate source-shaped weakening rather than the native
construction interface.

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

The merged proof keeps these estimates attached to the same auxiliary state
instead of enlarging them immediately to a common fourth-root error. The
transfer inequalities then give

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
already make the common envelope at least four. Zero error is supported, and
no divisibility condition on \(2m+2\) is introduced.

The merged headlines retain the source-facing **raw prescribed-answer
effects**, not only the internally completed Pauli measurements. They also
retain the range projections used by the existing isometry and Naimark
arguments.

### Proved native mixed component envelope

Before its common-envelope comparison, the merged proof keeps the different
state and operator orders visible. With

\[
 h=2m+2,\qquad
 T_{\mathrm{pass}}=3\left(\sqrt{Q+L_{\mathrm{ext}}}+r\right),\qquad
 \lambda=\Lambda_h(T_{\mathrm{pass}}),
\]

put

\[
 G=G(\lambda,Q),\qquad
 X_{\mathrm{native}}=2800\left(G+\sqrt e+r\right).
\]

The full-domain theorem
[`pauli_soundness_quantitative_mixed_components`][qpbt-quantitative-proved]
constructs one witness satisfying

\[
 \boxed{
 s^2\le\min\{4,16X_{\mathrm{native}}\},\qquad
 D_{\mathrm{raw}}^{A},D_{\mathrm{raw}}^{B}
 \le\min\{4,472X_{\mathrm{native}}+24r
   +192\sqrt{X_{\mathrm{native}}}+344e\}.}
\]

The same range projections and raw prescribed-answer effects occur in all three
estimates, and
[`pauli_soundness_qubit_quantitative_mixed_components`][qpbt-qubit-proved]
transports them exactly. No scalar ordering between this native mixed function
and \(F\), \(I\), or \(C\) is asserted.

### Retained degree-two envelope

The merged implementation, building on the accepted
[bound-strength audit][bound-audit] and earlier
[quadratic-candidate calculation][qpbt-quadratic-candidate], retains the
degree-two factor that the historical published #729 headline enlarges to
degree four. With the same

\[
 b=\frac1{67108864},\qquad
 I_{\mathrm{raw}}=10^9n^2E_b,
\]

it proves

\[
 \boxed{I=\min\{4,I_{\mathrm{raw}}\}.}
\]

The theorem
[`pauli_soundness_quantitative_degree_two`][qpbt-quantitative-proved] is now a
weakening of `pauli_soundness_quantitative_fractional`. It obtains one witness
at the fractional error \(H\), then composes the state estimate and both raw
operator estimates with the proved scalar comparison \(H\le I\). Thus the
auxiliary state, raw prescribed-answer effects, range projections, and exact
field-coordinate metrics are inherited from the fractional theorem. The
degree-two qubit sibling then transports those metrics exactly; neither theorem
rebuilds a witness at \(I\).

For provenance, an earlier direct degree-two derivation followed the actual
global-pair and component constructors. This is a historical alternative
calculation, not the proof of the current theorem. Its inputs give

\[
 g\le10^7n^4E_{2b},\qquad
 x=2800(g+\sqrt e+r)\le10^{11}n^4E_{2b},
\]

and therefore

\[
 \sqrt{x}\le10^6n^2E_b.
\]

Its nonsaturated branch is the condition \(I_{\mathrm{raw}}<4\). If \(n=1\), then
\(E_b\ge2^{-b}\ge1/2\), contradicting \(I_{\mathrm{raw}}<4\). Hence \(n\ge2\).
It also gives

\[
 r\le nE_b\le n^2E_b<4\cdot10^{-9}<1,
 \qquad \sqrt{x}<0.004,
 \qquad x<0.000016<1.
\]

On that historical branch, the global-pair and component constructors return
one witness satisfying

\[
 \begin{aligned}
 D_{\mathrm{raw}}
 &\le472x+24r+192\sqrt{x}+344e\\
 &\le664\sqrt{x}+24r+344e\\
 &\le664000368\,n^2E_b<I_{\mathrm{raw}},
 \end{aligned}
\]

while the state error satisfies
\(s\le4\sqrt{x}\le4\cdot10^6n^2E_b<I_{\mathrm{raw}}\).
For \(I_{\mathrm{raw}}\ge4\), it used an existing fixed-baseline witness and the
universal state/operator caps \(2,4,4\). That alternative also covered the full
nonnegative-error domain without division by \(e\). The merged declaration no
longer uses this branch construction: its full-domain and witness guarantees
come from the sharper fractional theorem followed by \(H\le I\).

For comparison, put

\[
 C=\min\{4,10^{14}n^4E_b\},\qquad
 F=\min\{4,10^{10}n^pE_{64b}\},\qquad
 p=\frac{15}{4}+\frac{5}{262144}.
\]

The capped scalar functions satisfy

\[
 \boxed{F\le I\le C.}
\]

Lean proves \(I\le C\), with strict inequality exactly when
\(I_{\mathrm{raw}}<4\). Separately, the accepted fixed-numerical-LDT source
argument gives \(F\le I\). For that calculation,
\(E_{64b}\le E_b^{64}\), and in the new small branch

\[
 \frac{F_{\mathrm{raw}}}{I_{\mathrm{raw}}}
 \le10n^{p-2}E_b^{63}
 <10(4\cdot10^{-9})^{63}n^{p-128}<1.
\]

Saturation completes the source-argument comparison, and \(F<I\) holds exactly
when \(F_{\mathrm{raw}}<4\). These are capped comparisons; no uncapped uniform
domination is asserted. The function \(I\) is the retained #729 compatibility
bound proved in the merged source. It sharpens the earlier formalization
envelope by retaining existing component information, rather than adding a new
source-paper measurement argument. The comparison with \(F\) ranks those
fixed-numerical-LDT candidates; it does not compare \(F\) with the native mixed
route, and it does not imply \(F\le H\) for the merged fractional headline below.

### Deferred structural fixed-LDT candidate

The complete issue #733 [author report][survey-733-author] and independent
[referee report][survey-733-referee] support a higher-exponent QPBT-only
candidate with LDT frozen. It remains unimplemented only because the owner
reinstated the two-improvement stopping rule after #729. Put

\[
 p=\frac{15}{4}+\frac{5}{262144}<4.
\]

The accepted deferred target is

\[
 \boxed{
 B_{\mathrm{QPBT}}^{\mathrm{struct}}
 =\min\!\left\{4,10^{10}n^pE_{1/1048576}\right\}.}
\]

It implies the simpler
\(\min\{4,10^{10}n^4E_{1/1048576}\}\) bound and the canonical
\(\Delta_{100,1/1048576}\) form. The complete #735 scope consists of these
three statements and the exact qubit counterpart of each. This target is
**MATHEMATICALLY CHECKED, NOT LEAN-IMPLEMENTED**. Issue [#735][issue-735]
tracks the deferred implementation; neither theorem names nor final code links
should be fixed before that implementation exists.

Both sides of the comparison use exactly the same native-LDT theorem, constants,
dimension, and sample:

\[
 \mathcal L(t)
 =\delta_{\mathrm{LD}}(30,1/8192,t,q,2m+2,d,1),
 \qquad N=2560000(2m+2)^3d.
\]

The QPBT improvement changes the passing error supplied as the argument \(t\)
and changes how the returned consistency error is propagated. It does not
change the LDT function, hypotheses, constants, or sample parameters.

The coherent mechanism is complete-measurement consistency together with
squared failure amplitudes. Its central new estimate is

\[
 \boxed{
 C\bigl(A,\operatorname{paste}(G_1,G_2)\bigr)
 \le307\delta+16\eta,}
\]

under the additional premise that both codeword measurements \(G_1,G_2\) are
projective. Both measurements are projective in the actual QPBT line-measurement
consumer. The general pasting theorem, which assumes projectivity only of the
outer measurement, remains unchanged. The proof retains the conditional
collision term, discarded mass, every directed placement, and the same sandwich
measurement; it does not infer a reversed comparison from symmetry.

The end-to-end power comparison is:

| Stage | Historical #729 calculation | Deferred #735 calculation |
|---|---|---|
| Squared twisted commutation | \(O(e^{1/2})\) | \(O(e)\) |
| Joint points | \(O(e^{1/8})\) | \(O(e^{1/4})\) |
| Paired lines | \(O(e^{1/64}+r^{1/4})\) | \(O(e^{1/4}+r)\) |
| Extended lines | \(O(m(e^{1/256}+r^{1/16}))\) | \(O(m(e^{1/16}+r^{1/4}))\) |
| Direct-game passing | \(O(m(e^{1/512}+r^{1/32}))\) | \(O(m(e^{1/16}+r^{1/4}))\) |
| LDT application | \(\mathcal L(t_{729})\) | the same \(\mathcal L(t_{735})\) |
| Global projective pairs, dominant LDT term | \(O(\lambda^{1/8})\) | \(O(\lambda^{1/4})\) |
| Final common error from pair error \(g\) | \(O(g^{1/2})\) | \(O(g^{1/2})\), unchanged |
| Final exponent for LDT power \(\tau\) | \(\tau/8192\) | \(\tau/128\) |

Thus the pre-LDT processing improves the exponent by a factor of 32 and the
post-LDT processing by a factor of two. The resulting 64-fold gain changes
\(1/67108864\) to \(1/1048576\). The extraction gain selected for #729 appears
on both sides and receives no additional credit.

This complete projective calculation has the largest accepted exponent gain
among the fixed-LDT source-argument alternatives in that survey. Keeping only
the existing Schmidt-mirror estimate gives a twofold gain. Using only one of
the commutation, passing, or rounding improvements also gives at most a
twofold gain. The projective squared-failure pasting estimate gives an
eightfold gain by itself, and its coherent propagation through commutation,
passing, and rounding gives the largest justified exponent gain within that
survey. The smaller coefficient and the fractional dimension power are
secondary. Its deferral is a scope decision, not a claim that the gain is less
significant than #729.

### Merged fractional headline and exact comparison with the deferred candidate

The fractional common envelope proved by #736 is

\[
 \boxed{
 H=\min\!\left\{4,
 10769120\,m^{20481/262144}d^{1/64}E_b\right\},
 \qquad b=\frac1{67108864}=2^{-26}.}
\]

The field-coordinate theorem
[`MIPStarRE.QPBT.pauli_soundness_quantitative_fractional`][qpbt-fractional-proved]
and its [exact qubit transport][qpbt-qubit-fractional-proved] prove this bound
for the same common auxiliary state and isometries. They are derived from the
six-term native scalar certificates and the mixed component theorem, while the
separate squared-state and raw-operator estimates remain available. The
incomparability calculation below is independent accepted mathematics,
recorded in the [fractional comparison report][fractional-comparison-report];
it is not needed by the Lean proof of \(H\).

For the terminal scalar conversion, put

\[
 M=m^{20481/262144}d^{1/64},\qquad K=M^2.
\]

On \(0\le e\le1\), the merged source proves

\[
 \lambda^{1/16}\le12ME_b,\qquad
 \sqrt G\le304ME_b.
\]

The extraction certificate additionally assumes \(r\le1\) and gives

\[
 \sqrt{X_{\mathrm{native}}}\le16218ME_b.
\]

Squaring the checked global-pair root estimate yields

\[
 \boxed{G\le277248K E_{2b}}
\]

for \(0\le e\le1\), with no ratio assumption. The preserved
\(10^7n^4E_{2b}\) comparison follows from this sharper result and does not use
the coefficient-30 `deltaLd` interface. The separately derived coefficient
14596 is an unimplemented coefficient-only refinement, not the proved
coefficient. The exact witness construction itself is more general than these
scalar estimates: it needs only \(e\ge0\). The fractional headline clips the
source error to \(e=\min(\varepsilon,1)\), derives \(r<1\) on its nonsaturated
branch, and uses the universal state/operator caps on the complementary branch.

The actual admissible domain for this comparison is

\[
 q=2^\ell\quad(\ell\text{ a positive odd integer}),\qquad
 m,d\in\mathbb N,\quad d\ge1,\quad m\mid q,\quad \varepsilon\ge0.
\]

Thus \(m\ge1\) and \(n=md\ge1\); there is no additional assumption
\(d\le q\). Put

\[
 A=10769120,\qquad B=10^{10},\qquad
 M=m^{20481/262144}d^{1/64},\qquad
 p=\frac{15}{4}+\frac5{262144},
\]

and write

\[
 H_{\mathrm{raw}}=AME_b,\qquad F_{\mathrm{raw}}=Bn^pE_{64b},\qquad
 H=\min\{4,H_{\mathrm{raw}}\},\qquad F=\min\{4,F_{\mathrm{raw}}\}.
\]

Since \(E_b>0\), the exact uncapped ratio is

\[
 R=\frac{F_{\mathrm{raw}}}{H_{\mathrm{raw}}}
 =\frac BA\frac{n^p}{M}\frac{E_{64b}}{E_b}.
\]

The cap-sensitive strictness criteria are

\[
 \boxed{F<H\iff F_{\mathrm{raw}}<4\ \text{and}\ R<1},\qquad
 \boxed{H<F\iff H_{\mathrm{raw}}<4\ \text{and}\ R>1}.
\]

Equality holds exactly when \(F_{\mathrm{raw}}=H_{\mathrm{raw}}\), or when both
raw bounds are at least four. If \(x=e^b\), \(y=q^{-b}\), and \(z=2^{-bn}\),
then

\[
 \frac{E_{64b}}{E_b}
 =\frac{x^{64}+y^{64}+z^{64}}{x+y+z}.
\]

The larger exponent in \(F\) therefore competes with the much larger factor
\(Bn^p/(AM)\); neither feature alone determines the order.

The easy global comparison is different. Since \(m,d\ge1\),

\[
 M\le m^2d^2=n^2,
 \qquad A<10^9,
\]

and hence

\[
 0<H_{\mathrm{raw}}<10^9n^2E_b<10^{14}n^4E_b.
\]

Taking caps gives

\[
 \boxed{H\le I\le C.}
\]

Moreover, \(H<I\) exactly when \(H_{\mathrm{raw}}<4\), and \(I<C\) exactly when
\(10^9n^2E_b<4\). The separately accepted comparison \(F\le I\) therefore
places both \(F\) and \(H\) below \(I\), but it does not imply \(F\le H\).
Clipping omits no boundary case: if \(\varepsilon\ge1\), all four capped
functions equal four, while at \(\varepsilon=0\) the field and tail terms keep
the ratio well-defined.

Two infinite admissible families prove that \(F\) and \(H\) are incomparable
even with both caps inactive. For any integer \(k\ge1\), choose

\[
 m=1,\qquad d=n=2^{2048k},\qquad
 \varepsilon=2^{-2^{26}Lk},\qquad
 q=2^{\,2^{26}Lk+1},
\]

where \(L\in\{121,128\}\). The extension degree is positive and odd,
\(m\mid q\), \(0<\varepsilon<1\), and in fact \(d<q\). With
\(x=2^{-Lk}\),

\[
 e^b=x,\qquad q^{-b}=2^{-b}x<x,\qquad
 2^{-bn}=2^{-2^{2048k-26}}<x,
\]

so

\[
 x<E_b<3x,
 \qquad x^{64}<E_{64b}<3x^{64}.
\]

Here \(M=2^{32k}\) and
\(n^p=2^{(7680+5/128)k}\). Consequently,

\[
 A2^{(32-L)k}<H_{\mathrm{raw}}<3A2^{(32-L)k},
\]

and

\[
 B2^{(7680+5/128-64L)k}
 <F_{\mathrm{raw}}<3B2^{(7680+5/128-64L)k}.
\]

Both caps are inactive throughout both families. Indeed,
\(3A<2^{25}\) and \(3B<2^{35}\) give the uniform certificates

\[
 H_{\mathrm{raw}}<2^{25-89k}<4,
 \qquad F_{\mathrm{raw}}<2^{35-63k}<4.
\]

For \(L=121\),

\[
 \frac{F_{\mathrm{raw}}}{H_{\mathrm{raw}}}
 >\frac{B}{3A}\,2^{(25+5/128)k}>1,
 \qquad\text{so}\qquad \boxed{H<F<4}.
\]

For \(L=128\),

\[
 \frac{F_{\mathrm{raw}}}{H_{\mathrm{raw}}}
 <\frac{3B}{A}\,2^{(-416+5/128)k}
 <2^{12-415k}<1,
 \qquad\text{so}\qquad \boxed{F<H<4}.
\]

These are exact power inequalities, not floating-point evaluations. In plain
terms, the 64-fold larger error exponent can make \(F\) smaller when the error
and inverse field size decay sufficiently quickly, while the much slower
dimension growth can make \(H\) smaller in another admissible regime. This is
only a comparison of common scalar guarantees. It is neither an ordering of
errors attained by strategies nor a comparison with the exact native mixed
state and operator bounds.

### Source argument and checked realization

The primary source theorem prints only the existence of universal constants
\(a,b\). The numerical exponents \(1/5242880000\), \(1/67108864\), and
\(1/1048576\) are derived explicit envelopes; none is a printed source
exponent.

Three parts of the accepted #735 calculation strengthen or make explicit the
source argument itself: the linear complete-measurement triangle is an
alternative to the printed square-root triangle, the twisted-commutation
estimate improves from \(O(\sqrt e)\) to \(O(e)\), and the projective subcase of
pasting receives the explicit linear bound \(307\delta+16\eta\). By contrast,
removing the direct-game passing root and improving same-space
projective-rounding transport concern the checked Lean realization. The paper
invokes the constructed low-degree strategy and an ancillary Naimark route
rather than printing those two extra losses.

At a fixed numerical LDT output \(\lambda\), the implemented checked route has
dominant common dependence \(\lambda^{1/16}\), while the deferred structural
route has \(\lambda^{1/8}\). This does **not** beat the literal source Naimark
route, whose displayed dependence is \(\lambda^{1/4}\). The 64-fold statement
compares two fully specified checked calculations with the same LDT black box;
it is not a comparison with a printed numerical paper exponent.

The common headline on every route remains an unsquared state norm together
with raw, unaveraged sums of squared operator-action errors for both players and
bases, all for one witness. The final root from a squared state estimate is not
removed. The implementation must retain the isometry range projections, raw
prescribed-answer effects, conditional-collision law, discarded probability
mass, and full-domain fallback. Complete-measurement identities must not be
applied to arbitrary submeasurements, where the missing-mass term obstructs the
same estimate.

### QPBT candidate inventory

| Candidate and source | Baseline to calculated target | Headline effect | Cost and risk | Status and decision |
|---|---|---|---|---|
| Explicit fixed witnesses, from [`deltaQld`][delta-qld] and [`pauli_soundness`][pauli-soundness] | Existential \((a,b)\) to exact \((a_0,1/5242880000)\), with \(a_0=346\cdot21^3\operatorname{pauliBaselineProjectiveConstant}^4\); \(a_{\mathrm{base}}\) remains a padded scalar comparison | Establishes the numerical raw/qubit baseline, including the enormous polynomial degree | High formal plumbing through opaque existential interfaces | **IMPLEMENTED (proved and merged)** by [`pauli_soundness_explicit_baseline`][qpbt-baseline-proved] and its [exact qubit form][qpbt-qubit-baseline-proved] |
| Historical degree-four #729 composition, using the improved one-coordinate LDT import and separate state/operator estimates from [`StateExtraction.lean`][state-extraction] through [`RawOperatorTransferCore.lean`][raw-transfer] | \(\Delta_{a_0,1/5242880000}\to C=\min(4,10^{14}n^4E_{1/67108864})\), then canonical \(\Delta_{100,1/67108864}\) | Exponent multiplied by \(78.125\), but a common fourth-degree envelope discards the sharper extraction scaling; raw effects and qubit form retained | High interface work; same witnesses must survive every estimate | **IMPLEMENTED (retained compatibility result)**. The degree-four declarations remain available beside the sharper siblings; their loss is recorded as deferred #727 |
| **Carry the native LDT error through QPBT** | Replace the early `deltaLd` absorption by \(\Lambda_h(t)\), then use \(g=G(\Lambda_{2m+2}(T_{\mathrm{pass}}),Q)\) | Retains the exact tail, dimension factor, and distinct error orders through direct transport, compression, rounding, and global-pair construction | High cross-stage interface work; every sibling must preserve the same measurements and quantifier order | **IMPLEMENTED (proved and merged)** through the native direct, rounding, separation, and global-witness declarations recorded in the [QPBT bound ledger](bound-ledger-qpbt.md) |
| **Expose the mixed state/operator headline** | Replace the one common fourth-degree bound by \(s^2\le\min(4,16X_{\mathrm{native}})\) and raw errors \(\le\min(4,472X_{\mathrm{native}}+24r+192\sqrt{X_{\mathrm{native}}}+344e)\) | Keeps the squared state order separate from both raw summed-squared operator errors for one witness and transports all three exactly to qubits | Medium interface work; full-domain caps, range projections, and raw wrong-answer terms remain attached to the same witness | **IMPLEMENTED (proved and merged)** by the field and exact qubit mixed-component theorems; this remains separate from the common headline |
| **Fractional common headline and retained degree-two/four comparisons** | \(C=\min(4,10^{14}n^4E_b)\) and \(I=\min(4,10^9n^2E_b)\) to \(H=\min(4,10769120m^{20481/262144}d^{1/64}E_b)\), with the same \(b=1/67108864\) | Replaces degree two by separate fractional powers of \(m\) and \(d\), while keeping the six-term native scalar and exact mixed bounds distinct | Bounded but load-bearing scalar and branch proof; preserve the witness, full domain, raw effects, range projections, and separate state/operator estimates | **IMPLEMENTED (selected; proved and merged in [PR #736][pr-736])**. Lean proves \(H\le I\le C\); independent accepted algebra shows \(H\) and deferred \(F\) are incomparable |
| Superseded pre-selection quantitative envelopes from the same mechanisms | Earlier calculations included \(\Delta_{100,1/2621440000}\), then \(\Delta_{100,1/327680000}\); extraction alone gave exponent \(1/655360000\), and an earlier joint LDT/extraction estimate gave \((a,b)=(10^{740},1/268435456)\) | Each improved the traced baseline, but all are weaker than the proved degree-two result | Similar or greater plumbing, with worse retained constants | **NOT IMPLEMENTED (superseded)**. Recorded to preserve the survey history; not separate scopes |
| **Deferred complete-measurement and squared-failure calculus** | #729 target to \(F=\min(4,10^{10}n^{15/4+5/262144}E_{1/1048576})\), then the \(n^4\) bound, canonical-100 form, and the exact qubit counterpart of each | Additional 64-fold exponent gain with the same LDT function and sample | Medium/high end-to-end QPBT work; preserve completeness hypotheses, placements, collision terms, witnesses, range projections, and raw effects | **MATHEMATICALLY CHECKED, NOT LEAN-IMPLEMENTED** under [#735][issue-735]; accepted by the [author][survey-733-author] and [referee][survey-733-referee] reports, and deferred solely by the two-improvement stopping rule |
| Linear consistency calculus in commutation, starting from [`consistencyDefect_trans_le`][consistency-calculus] and [`CommutingObs.lean`][point-commutation] | Squared twisted-commutator error \(O(\sqrt e)\to O(e)\); joint-point error \(O(e^{1/8})\to O(e^{1/4})\) | Twofold final exponent gain by itself | Medium/broad; completeness is load-bearing and every directed comparison must survive | **Deferred component of #735; mathematically checked, not Lean-implemented** |
| Retain the Schmidt-mirror estimate in [`Pasting/Assembly.lean`][qpbt-pasting] | Pasting \(115(\eta^{1/4}+\delta^{1/8})\to12(\eta^{1/4}+\delta^{1/4})\) | Twofold headline exponent gain by itself | Medium; localized proof needs a sharper parameterization | **NOT IMPLEMENTED (comparison only)**. This is weaker than the deferred projective squared-failure estimate |
| Projective pasting by squared failure amplitudes | Same sandwich bound improves to \(307\delta+16\eta\) when both codeword measurements are projective | Eightfold headline exponent gain by itself; improves field-error power as well | Medium/high; finite-sum identities, post-measurement collision weights, and heterogeneous placements are load-bearing | **Deferred central estimate of #735; mathematically checked, not Lean-implemented**. Both actual QPBT codeword families are projective; the general pasting theorem remains unchanged |
| Linear complete-POVM triangle in direct-game passing, at [`EvaluatedLineComparison.lean`][passing-comparison] | \(O(\sqrt{Q+L_{\mathrm{ext}}}+r)\to O(Q+L_{\mathrm{ext}}+r)\) across both completed axis and diagonal readouts | Twofold final exponent gain by itself | Medium; both orientations, both line types, and all seven rejection branches must be propagated | **Deferred component of #735; mathematically checked, not Lean-implemented** |
| Linear rounding transport in [`RoundingTransport.lean`][rounding-transport] | Global-pair dependence \(\lambda^{1/8}\to\lambda^{1/4}\) before the unchanged final state root | Twofold final exponent gain at fixed \(\lambda\) | Medium; choose roundings before postprocessing maps and preserve quantifier order | **Deferred component of #735; mathematically checked, not Lean-implemented** |
| Earlier combination of four local root-removal projections | Prospective sixteenfold exponent gain | Historical indication that a combined change could dominate any local tweak | High, multi-construction; complete constants were not then established | **SUPERSEDED as a projection** by the independently accepted 64-fold projective calculation; retained to preserve survey history |
| Positive-failure state transfer | For a positive failure effect, improve the operator component from \(O(\sqrt x+r)\) to \(O(x+r)\) | Stronger operator conclusion, but no improvement to the common state-limited headline | Medium; positivity and range terms must remain explicit | **NOT IMPLEMENTED (deferred)**. It does not improve the state-limited common headline selected for #729 |
| Keep an enlarged projective construction instead of compressing and rounding | Potentially remove the entire same-space global-rounding loss | Potential eightfold gain by itself | High; requires a compatible enlarged QPBT setting, canonical reference action, and final isometry composition | **NOT IMPLEMENTED (research direction)**. No verified end-to-end construction was found |
| Avoid joint-point orthonormalization loss | Would require a projective joint measurement with substantially better state-dependent distance | Potentially substantial | High; all local-space and directed-comparison obligations remain open | **NOT IMPLEMENTED (research direction)**. Quantum linearity alone does not supply the missing construction |
| Sharper combined-point coefficient in [`Points.lean`][combined-points] | About \(3.10\cdot10^{14}\to2.35\cdot10^{11}\) | Coefficient only | Low scalar change | **NOT IMPLEMENTED (deferred)** |
| Retain \(\sqrt m\) in extended lines, beginning at [`Estimates.lean`][extended-lines] | Avoid weakening \(\sqrt m\) to \(m\) | Better intermediate dimension dependence | Medium propagation | **NOT IMPLEMENTED (deferred)**. Smaller effect than removing final degree inflation |
| Weighted projective-rounding triangle in [`ProjectiveRounding.lean`][projective-rounding] | Small-branch coefficient \(220\to(\sqrt{84}+\sqrt{26})^2\) | Coefficient only | Low locally; global threshold still requires checking | **NOT IMPLEMENTED (deferred)** |
| Actual-rounding arithmetic in [`ActualErrorBounds.lean`][actual-rounding] | Safe inspected coefficient \(1024\to734\) | Coefficient only | Low | **NOT IMPLEMENTED (deferred)**. More aggressive rounding was not supported by the inspected calculation |
| Smaller auxiliary LDT sample in [`Transport/Error.lean`][direct-parameter] | \(2560000m^3d\to400m^3d\) | Large raw coefficient reduction, no exponent gain | Medium transport work | **NOT IMPLEMENTED (deferred)**. It changes the LDT instantiation and receives no credit in the fixed-input #735 comparison |
| Off-route seed-indexed triangle in [`LowDegreeGameTheorems.lean`][seed-indexed] | Remove the seed-compression exponent halving | Improves `exists_ld_soundness`, but not the live one-coordinate Pauli route | Medium | **NOT IMPLEMENTED (deferred, off route)** |
| Off-route general simultaneous transport in [`Combining/Error.lean`][general-transport] | Retain \(1/40000\) instead of weakening to \(1/80000\) | Improves a general theorem, but not the live one-coordinate Pauli route | Medium | **NOT IMPLEMENTED (deferred, off route)** |
| EPR normalization geometry in [`EPRState.lean`][epr-state] | Squared-state coefficient \(16\to8\) | Coefficient only | Low/medium; preserve the zero-projection branch | **NOT IMPLEMENTED (deferred)** |
| Full Magic Square rigidity in [`MagicSquareTheorems.lean`][ms-rigidity] | \(2\cdot10^{12}\to1788904972224\), about a \(10.6\%\) reduction | No current Pauli headline effect: the live route uses [`msVarObs_anticommutator_le`][ms-anticommutator] with coefficient \(1183680\). A separate optimization could keep the operator conclusions quadratic in \(\sqrt\varepsilon+\sqrt\delta\) while the state conclusion remains linear | Low arithmetic, but agreement hypotheses remain load-bearing | **NOT IMPLEMENTED (deferred, off route)** |
| Aggregate malformed-answer incidences in [`RawOperatorTransferCore.lean`][malformed-transfer] | \(86\varepsilon\to43\varepsilon\) before raw transfer | Coefficient only | Needs a new edge-sum proof | **NOT IMPLEMENTED (deferred)** |
| Replace the field-valued combined-point construction by quantum linearity | No established quantitative gain for the current proof | None in the live construction | Would change the construction rather than sharpen its present bound | **NOT IMPLEMENTED (deferred, off route)** |
| Condition a collision estimate on a good event in the [source Pauli composition][qpbt-paper-composition] | No valid target without the actual conditional law and restoration of the discarded probability mass | None from the proposed inference | The conditioning changes the distribution and cannot be omitted from the estimate | **REJECTED** |
| Remove symmetrization attainment slack by scalar optimization | No valid target: symmetrization already preserves a supplied strategy's value exactly | None | Supremum attainment is not an arithmetic loss | **REJECTED** |
| Hide the extended-line dimension factor inside the printed polynomial error | No valid target; [`not_exists_combining_quarter_power_bound`][dimension-obstruction] gives a scalar obstruction to that absorption | None | Contradicts the inspected scalar route | **REJECTED** |
| Use the literal multiplicative pasting-error contract | No valid target; the [pasting error note][pasting-product-gap] gives a counterexample and retains the additive correction | None | The product contract is false | **REJECTED** |

Further rejected shortcuts are applying the complete-measurement triangle to
arbitrary submeasurements, assuming a reversed comparison from register
symmetry, dropping conditional-collision or discarded-mass terms,
postprocessing an arbitrary squared operator distance without a contraction
argument, identifying an isometry range projection with the identity, replacing
raw effects by completed effects in the headline, treating a squared-state
estimate as an unsquared norm estimate, removing the remaining extended-line
quarter power without a new proof, or crediting a changed LDT sample as a
fixed-input gain.

## Comparison with the pinned public `qldErr`

### Source, domain, and conclusion metric

The benchmark is Thomas Vidick's public `MIPRE-formalization` at exact commit
[`286b3ca44f811fa6e37517c04981bc2f164ee6b5`][public-commit]. The inspected
mirror contained 398 manifested source files, all of whose hashes matched its
provenance record. The pinned repository license is
[Apache-2.0][public-license]. The accepted exact-function analysis and its
certificates are recorded in the [published comparison report][benchmark-report].
This remains a public-only, source-inspected comparison: no benchmark code was
copied, and no benchmark build was run for this report.

The mathematical source is [Theorem `thm:pauli`][qpbt-paper-pauli-metric]. One
extraction witness controls an unsquared state norm and both summed squared
operator-action errors. The public theorem [`qld_soundness`][public-soundness]
covers arbitrary POVM strategies. The mirror witness is constructed in
[`MirrorExists.lean`][public-mirror], and [`Regime.lean`][public-regime] derives
the divisibility \(4m\mid q\) used inside the small-error regime. An earlier
concern that either ingredient was missing is superseded. A suspected
square-root mismatch in `deltaLegs_comp` was also a parsing error; the proof and
definition agree.

The common admissible domain used below is

\[
 \varepsilon\ge0,\qquad m,d\ge1,\qquad m\mid q,\qquad
 q=2^k\text{ with }k\text{ positive and odd}.
\]

The public theorem additionally permits general finite fields of characteristic
two. The local theorem uses its fixed field model and odd extension degree.

Both conclusions use an unsquared state norm and, for each party and basis, a
sum of squared operator-action norms on the ideal extracted state. Neither uses
answer averaging or a factor \(1/2\). Comparing the encodings also requires the
correspondence between their register orders and the equivalent placement of an
ideal Pauli projector on either half of an EPR pair.

### The actual capped composition

The public error is an explicit composed function, not either of the
existential envelopes discussed below. Set

\[
 A=2\cdot10^{11},\qquad \beta=\frac1{40000},\qquad
 z=\frac{n+1}{q}.
\]

Direct expansion of the pinned definitions gives

\[
 \begin{aligned}
 Q_V&=2\sqrt{57676416e}+\sqrt{86e}+86e,\\
 D_V&=80Q_V+9228227936e,\\
 P_V&=D_V/2+\sqrt{D_V/2}+\sqrt{32D_V+4\sqrt{172e}+2z},\\
 T_V&=5m^2P_V+4Q_V+z,\\
 L_V&=A(4n)^A\left(T_V^\beta+q^{-\beta}+2^{-4\beta n}\right),\\
 U_V&=2L_V+115352832e,\\
 S_V&=2\sqrt{U_V}+2/q+8U_V,\\
 X_V&=72(10S_V+860e+2\sqrt{172e}+r),\\
 H_V&=2\sqrt{X_V}+2X_V,\\
 \eta_V&=2-2\sqrt{1-H_V},\\
 J_V&=66S_V+44\sqrt{688e}+46r+1892e+13\sqrt{\eta_V}.
 \end{aligned}
\]

Here \(\eta_V\) is used only in the indicated small-error regime. The actual
definition is

\[
 \boxed{
 f:=\operatorname{qldErr}(e,m,d,q)=
 \begin{cases}
 \min(J_V,4),&48n\le q\text{ and }H_V<1,\\
 4,&\text{otherwise}.
 \end{cases}}
\]

The exact source locators are as follows; every path is relative to the pinned
public commit.

| Quantity | Public declaration | Exact locator |
|---|---|---|
| \(Q_V\) | [`MIPRE.QLD.deltaQ`][public-deltaq] | `MIPRE/Background/QLD/Combined.lean:350` |
| \(D_V,P_V\) | [`MIPRE.QLD.deltaPairsD`, `MIPRE.QLD.deltaPairs`][public-pairs] | `MIPRE/Background/QLD/Lines.lean:1027,1033` |
| \(T_V,L_V\) | [`MIPRE.QLD.deltaGS`, `MIPRE.QLD.deltaLD`][public-gs-ld] | `MIPRE/Background/QLD/PaddedLIDT.lean:168,174` |
| \(A,\beta\) and the LDT formula | [`MIPRE.LIDT.clA`, `MIPRE.LIDT.clB`, `MIPRE.LIDT.deltaCL`][public-lidt-constants] | `MIPRE/Background/LIDT/Adapter/Parameters.lean:48,45,54` |
| \(U_V,S_V\) | [`MIPRE.QLD.deltaProd`, `MIPRE.QLD.deltaS`][public-prod-s] | `MIPRE/Background/QLD/PaddedLIDT.lean:552,560` |
| \(X_V\) | [`MIPRE.QLD.deltaSelfCons`][public-self-cons] | `MIPRE/Background/QLD/SwapItemOne.lean:146` |
| \(H_V,J_V,\eta_V\) | [`MIPRE.QLD.deltaLegs`, `MIPRE.QLD.deltaItemTwo`, `MIPRE.QLD.etaItemOne`][public-final-expansion] | `MIPRE/Background/QLD/SwapItemTwo.lean:300,305,309` |
| Regime and cap | [`MIPRE.QLD.qldHlt`, `MIPRE.QLD.qldBound`, `MIPRE.QLD.qldErr`][public-qlderr] | `MIPRE/Background/QLD/QLDError.lean:84,93,99` |

The public named-error theorem
[`MIPRE.QLD.exists_le_qldErr`][public-named-error] supplies its witness at this
actual function.

### Answer normalization

The public operators use [`MIPRE.QLD.rdPauliVec`][public-rd-pauli-vec], which
sends malformed answers to zero. The local headline uses raw
prescribed-answer effects. These families coincide on legally supported
strategies, but they are not definitionally equal for arbitrary strategies.

On a common encoding, if the state norm and completed-family operator distance
are both at most \(f\), the local raw-transfer calculation gives

\[
 D_{\mathrm{raw}}\le2f+4f^2+344e\le104f,
 \qquad f_{\mathrm{raw}}:=\min(4,104f),
\]

using \(4e\le f\le4\). The function \(f_{\mathrm{raw}}\) is a conservative
scalar normalization for this report. It is not a proved transport theorem
between the two repositories.

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
calculation. Neither existential envelope replaces the actual function \(f\)
for numerical comparison.

### Local bounds and their uniform ordering

For this comparison, write \(C=B_{\mathrm{QPBT}}\) for the historical
degree-four #729 bound, let

\[
 I=\min\{4,10^9n^2E_{1/67108864}\}
\]

be the retained degree-two #729 result, let

\[
 H=\min\!\left\{4,
 10769120m^{20481/262144}d^{1/64}E_{1/67108864}\right\}
\]

be the merged #736 fractional headline, write
\(F=B_{\mathrm{QPBT}}^{\mathrm{struct}}\) for the accepted but deferred #735
fractional-power bound already displayed above, and set

\[
 F_4=\min\!\left\{4,10^{10}n^4E_{1/1048576}\right\}.
\]

On the entire common domain,

\[
 \boxed{H\le I\le C,\qquad F\le I\le C,\qquad F\le F_4\le C.}
\]

The first chain is Lean-proved in the merged #736 source. The second is the
capped comparison in the accepted quadratic-candidate calculation. For the
third, \(n\ge1\), the exponent
\(p=15/4+5/262144\) is smaller than four, and every base in \(E_b\) lies in
\([0,1]\). Increasing the common exponent therefore decreases each summand,
and the coefficient also decreases from \(10^{14}\) to \(10^{10}\). The
native LDT theorem remains merged and frozen. The retained \(C,I\) route and
the deferred \(F\) calculation use the fixed numerical input described above;
the proved \(H\) route preserves the native error longer. These are
only capped common-envelope comparisons. In particular, \(F\le I\) does not
imply \(F\le H\): the exact families above prove both \(H<F\) and \(F<H\).
No scalar ordering is asserted between any of \(F,H,I,C\) and the exact native
mixed-component bounds through \(\Lambda_h\) and \(G\).

The status and role of the quantities are distinct.

| Object | Mathematical role | Evidence and qualification |
|---|---|---|
| \(C\) and its canonical-100 and exact qubit forms | Historical degree-four #729 result | **IMPLEMENTED (retained compatibility result)** in the merged source; its degree-four loss is deferred #727 |
| \(I\) and its exact qubit transport | Historical degree-two #729 correction | **IMPLEMENTED (retained compatibility result)**. Lean proves \(H\le I\le C\); the accepted fixed-LDT calculation separately proves \(F\le I\) |
| \(H\) | Selected #736 fractional common envelope | **IMPLEMENTED (proved and merged)** in field and exact-qubit coordinates, with one common witness and full-domain cap |
| \(F,F_4\), canonical \(\Delta_{100,1/1048576}\), and the exact qubit counterpart of each | Deferred #735 structural target | **MATHEMATICALLY CHECKED, NOT LEAN-IMPLEMENTED** with the same frozen LDT input; deferred by the two-improvement stopping rule |
| Native mixed route through \(\Lambda_h\) and \(G\) | Exact construction before common-envelope absorption | **IMPLEMENTED (proved and merged)**; its distinct state/operator orders remain available, and no ordering with \(F\), \(H\), \(I\), or \(C\) is claimed |
| \(f\) | Actual public named error | Defined and used by the pinned public theorem; source-inspected, not built here |
| \(f_{\mathrm{raw}}\) | Conservative completed-to-raw scalar conversion | Unformalized common-encoding calculation; no cross-repository transport theorem |
| \((a_V,1/2560000)\) | Public existential error-shape witness | Reconstructed witness arithmetic; not the actual composed function |
| \((10^{12},1/1280000)\) | Sharper public scalar envelope | Unformalized calculation; not the actual composed function |

The larger common exponent of \(F\) does not imply that \(F\) uniformly
dominates \(f\): the actual public composition retains faster field and tail
rates than its common-envelope exponent records.

### No uniform ordering with the actual public function

Take

\[
 e=0,\qquad m=1,\qquad d=n,\qquad q=2^{n+1}.
\]

For \(n=2^{50}\) or \(n=2^{80}\), the extension degree \(n+1\) is odd, so
these parameters are admissible on both sides. Exact inequalities give

| Parameters | Verified inequalities |
|---|---|
| \(n=2^{50}\) | \(H\le I\le C<2^{-16776968}<4=f=f_{\mathrm{raw}}\), and \(F\le F_4<2^{-1073741589}\) |
| \(n=2^{80}\) | \(f\le f_{\mathrm{raw}}<2^{-2^{60}}<2^{-2^{54}}\le H\), while also \(f_{\mathrm{raw}}<F\le F_4\le C\) |

The same zero-error benchmark therefore proves that \(H\) and the actual public
function are not uniformly ordered. At \(n=2^{50}\), this follows immediately
from \(H\le I\le C\). At \(n=2^{80}\), the coefficient and dimension factor in
\(H_{\mathrm{raw}}\) are at least one and \(E_b\) retains the term \(2^{-bn}\), while the
cap four is also larger than that term. Hence

\[
 H\ge2^{-bn}=2^{-2^{54}},
\]

so \(f_{\mathrm{raw}}<H\). Thus none of \(C\), \(F\), \(F_4\), or \(H\) is
uniformly ordered with \(f\), and the same counterexamples apply to
\(f_{\mathrm{raw}}\). These are analytic comparisons of scalar guarantees, not
an ordering of errors attained by actual strategies.

The estimates can be certified without expanding the field cardinalities or
evaluating underflow-prone floating-point expressions. When \(e=0\),

\[
 T_V=5m^2\sqrt{2z}+z.
\]

If \(48n\le q\) and \(L_V\le2^{-40}\), then

\[
 r,q^{-1}\le\sqrt{L_V},\qquad
 S_V\le21\sqrt{L_V},\qquad X_V<2^{14}\sqrt{L_V}.
\]

It follows that \(H_V<9/32<1\),
\(\sqrt{\eta_V}\le32L_V^{1/8}\), and

\[
 \boxed{f\le2^{11}L_V^{1/8}},
\]

where the final coefficient is
\(66\cdot21+46+13\cdot32=1848<2^{11}\).

For \(n=2^k\), \(m=1\), and \(q=2^{n+1}\), one has

\[
 T_V\le16\sqrt z,\qquad z\le2^{k-n},\qquad
 L_V<2^{\ell_k},
\]

where

\[
 \ell_k=40+A(k+2)+\frac{4+k/2-n/2}{40000}.
\]

At \(k=80\), exact rational arithmetic gives

\[
 \ell_{80}<-40,
 \qquad 18+\ell_{80}/8<-2^{60}.
\]

Together with \(104<2^7\), this proves the second row of the table. At
\(k=50\), the retained public tail instead gives

\[
 L_V>A(4n)^A2^{-n/10000}
 >2^{52A-2^{50}/10000}>1.
\]

Hence \(H_V>1\) and the public definition returns four. The local inequalities
in the first row follow from \(E_b<2\cdot2^{-bn}\).

The mechanism by which the public function wins at \(n=2^{80}\) is its
retained field and tail decay, not its common existential exponent. In the
preceding small-\(L_V\), zero-error regime, root subadditivity gives

\[
 f\le2^{11}[A(4n)^A]^{1/8}
 \left(
 9^{\beta/8}m^{\beta/4}z^{\beta/16}
 +q^{-\beta/8}+2^{-\beta n/2}
 \right).
\]

The surviving field and tail powers include

\[
 z^{1/640000},\qquad 2^{-n/80000},
\]

both faster than the common power \(1/1048576\) in \(F\). A separate example
isolates the tail advantage: for
\(e=0\), \(m=1\), \(d=n=2^{60}\), and \(q=2^{16n+1}\),

\[
 L_V<2^{40+62A-n/10000},
 \qquad f_{\mathrm{raw}}<2^{-2^{40}}<F.
\]

The larger local error exponent also has a genuine effect in the opposite
direction. The actual public composition satisfies

\[
 f\ge e^{1/1280000}
\]

throughout the common domain. Inside the small-error regime this follows from
\(T_V\ge e^{1/4}\), \(L_V\ge e^{\beta/4}\), \(\eta_V\ge H_V\), and
\(J_V\ge L_V^{1/8}\); outside it, \(f=4\). At the same
\(m=1,d=n=2^{80},q=2^{n+1}\) as above, changing only the error to
\(e=2^{-n}\) reverses the zero-error ordering:

\[
 F\le F_4<2^{355-2^{60}}<2^{-n/1280000}\le f.
\]

This positive-error example concerns \(F\) and \(F_4\) only. No comparison with
\(H\) is inferred from it.

These examples are asymptotic certificates, not practical parameter
recommendations. At every fixed finite \(n\), each displayed common envelope
also retains a positive tail floor. No part of this comparison is a benchmark
build, a cross-repository theorem, a proof of actual strategy-error ordering,
or evidence that #735 has been implemented or merged.

## Implementation evidence and remaining scope

### Merged LDT evidence

The proved before/after pair is now public in the local formalization.

1. [`MIPStarRE.LDT.Test.main_formal_explicit_baseline`][ldt-baseline-proved]
   proves the three final consistency conclusions at
   \(B_{\mathrm{LDT}}\).
2. [`MIPStarRE.LDT.Test.main_formal_linear_triangle_bound`][ldt-improved-proved]
   proves the same three conclusions at \(B_\triangle\).

Both declarations retain the heterogeneous projective strategy, passing
hypothesis, field model, \(k\ge400md\), \(k>0\), one common witness pair, and
all three conclusions. They add no \(\varepsilon\le1\), \(d\le q\), or
\(k\le q\) hypothesis, so \(d=0\) and \(k>q\) remain in scope. The merged
[axiom-audit entries][ldt-axiom-audit] cover both headlines and the non-strict
and strict comparison theorems.

The implementation is [PR #731][pr-731] for issue [#728][issue-728]. Canonical
CI tested exact head [`df8f6bc9255e7aa524ceebff3bffc0087dfc1ee2`][ldt-tested-head]
for 475 seconds and passed the summary plus all eight steps. Its build passed
both `MIPStarRE.LDT.Test.AxiomAudit` and
`MIPStarRE.QPBT.Test.AxiomAudit`; Python discovery passed 876 tests with 9
skipped. The [supplementary proof-closure check][ldt-supplementary-evidence]
audited 1,932 tagged declarations across 381 modules with zero failures and no
proof-level `sorryAx` dependency. Independent review
[#5345643236][ldt-independent-review] approved both code and prose with no
findings. The normal merge gate was verified without an override, producing
merge commit [`fac99fdf22bbdbb83a2376ca48cd679dc7d13750`][ldt-merge]. The CI
and review receipts are dated September 28 in UTC, corresponding to September
29 in Asia/Tokyo. The
[merged implementation audit][ldt-implementation-audit] records the
corresponding statement-integrity and construction details.

### Merged QPBT evidence

The authoritative proof source is final #736 head
[`6ea9f96bd86aaaad613130dea49eefdf6e80c5a9`][qpbt-final-head], merged as
[`0b847308c30769be983bbd05c297e1014db76590`][qpbt-merge]. It contains the fixed
field and qubit baselines, the native direct-LDT and exact global-pair route,
the separated six-term and fractional scalar certificates, the mixed field and
qubit component theorems, the fractional headline \(H\), the degree-two and
degree-four compatibility results, the canonical corollaries, and the baseline
comparisons. The native LDT dependency remains frozen at tree
`ddd92480c55bbabba5a96af96064fc792a5eb68c`.

The final source includes the scalar-reuse modules
[`Combining/QuantitativeScalarBase.lean`][qpbt-scalar-base],
[`Combining/QuantitativeNativeScalars/Core.lean`][qpbt-native-core], and
[`Combining/QuantitativeNativeFractionalScalars.lean`][qpbt-native-fractional].
The previous public import modules remain available. The checked root
certificate proves
\(G\le277248K E_{2b}\) without a field-ratio assumption; the older
\(10^7n^4E_{2b}\) comparison follows without the coefficient-30 `deltaLd`
route. The separately derived coefficient 14596 remains an unimplemented
coefficient-only refinement.

Exact-head CI passed all eight steps and all nine contexts in 567 summed
step-seconds. It included the full build, blueprint render and synchronization,
paper-gap, file-length, proof-debt, proof-evasion, and statement-origin checks.
The canonical declaration check resolved 2,198 Lean references. The blueprint
axiom closure checked 2,187 declarations across 407 modules with zero failures,
including 403 statement-only and 1,784 proof-level placements. The committed
QPBT axiom audit contains 53 commands; the quantitative declarations used here
close only over `propext`, `Classical.choice`, and `Quot.sound`.

Review [#5372229944][qpbt-mathematical-review] approved the final mathematics
and identified three prose/dependency repairs. Review
[#5372895844][qpbt-final-review] then approved only that final editorial patch,
after independently checking that the Lean code and formulas were unchanged.
It would be inaccurate to describe these as five full mathematical reviews.
The normal merge completed all seven gates with no override and closed issue
[#729][issue-729].

The native and common-envelope conclusions have different purposes. The
native theorem constructs at the exact \(G\) and defines
\(X_{\mathrm{native}}=2800(G+\sqrt e+r)\). The same witness also satisfies the
coarse consequence \(G\le10^7n^4E_{2b}\), which supports the degree-two common
headline. That consequence does not replace the native construction interface.
The source-argument candidate \(F\) fixes the numerical LDT input and changes
later QPBT reasoning; it remains separate from both of these proved routes.
The proved \(H\) headline is a terminal common-bound corollary. It does not
replace the native mixed construction or merge the squared-state and raw
operator estimates at their construction interface.

### Remaining quantitative scope

The general seed-indexed theorem `exists_ld_soundness` still lacks its public
explicit-constant sibling. Source inspection gives witnesses
\((10^{24},1/160000)\), with its first two errors retained at \(E\) and its
third at \(E+2\sqrt{9\varepsilon+E}+md/q\). This inherited item remains tracked
under [#727][issue-727].

The complete-measurement and squared-failure improvements grouped under
[#735][issue-735] remain mathematically checked but unimplemented. They are
deferred solely by the two-improvement stopping rule. Neither this report nor
the static C8 `DELEGATED` ledger-shape result claims completion of the whole
QPBT track.

This report and the reconciled ledger are authored and awaiting their own
normal CI, `review.sh`, and separate independent mathematical review. That
future review concerns these documents, not the already merged #736 proof.

[baseline-commit]: https://github.com/Dengnifer/MIPStarRE-QPBT/commit/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9
[issue-728]: https://github.com/Dengnifer/MIPStarRE-QPBT/issues/728
[issue-729]: https://github.com/Dengnifer/MIPStarRE-QPBT/issues/729
[issue-727]: https://github.com/Dengnifer/MIPStarRE-QPBT/issues/727
[issue-733]: https://github.com/Dengnifer/MIPStarRE-QPBT/issues/733
[issue-733-adoption]: https://github.com/Dengnifer/MIPStarRE-QPBT/issues/733#issuecomment-5882105555
[issue-734]: https://github.com/Dengnifer/MIPStarRE-QPBT/issues/734
[issue-735]: https://github.com/Dengnifer/MIPStarRE-QPBT/issues/735
[pr-736]: https://github.com/Dengnifer/MIPStarRE-QPBT/pull/736
[qpbt-final-head]: https://github.com/Dengnifer/MIPStarRE-QPBT/commit/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9
[qpbt-merge]: https://github.com/Dengnifer/MIPStarRE-QPBT/commit/0b847308c30769be983bbd05c297e1014db76590
[qpbt-mathematical-review]: https://github.com/Dengnifer/MIPStarRE-QPBT/pull/736#pullrequestreview-5372229944
[qpbt-final-review]: https://github.com/Dengnifer/MIPStarRE-QPBT/pull/736#pullrequestreview-5372895844
[qpbt-baseline-proved]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Test/Soundness.lean#L51-L108
[qpbt-qubit-baseline-proved]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Test/QubitForm.lean#L421-L459
[qpbt-native-direct-scalars]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Combining/QuantitativeDirectScalars.lean#L27-L598
[qpbt-native-global]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Combining/Quantitative.lean#L27-L144
[qpbt-scalar-base]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Combining/QuantitativeScalarBase.lean#L1-L85
[qpbt-native-core]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Combining/QuantitativeNativeScalars/Core.lean#L1-L549
[qpbt-native-fractional]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Combining/QuantitativeNativeFractionalScalars.lean#L1-L973
[qpbt-quantitative-proved]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Test/QuantitativeSoundness.lean#L40-L440
[qpbt-qubit-proved]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Test/QuantitativeQubitForm.lean#L29-L160
[qpbt-fractional-proved]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Test/QuantitativeSoundness.lean#L178-L360
[qpbt-qubit-fractional-proved]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Test/QuantitativeQubitForm.lean#L63-L84
[bound-audit]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/f39cd66b0c5ee49df0e7a723e72107ea5907ba91/results/telemetry/sessions/scout-730-20260930-01.last.md
[bound-backlog]: https://github.com/Dengnifer/MIPStarRE-QPBT/issues/727#issuecomment-5902387427
[qpbt-quadratic-candidate]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/acfd20f07f30e71aedcc77846261c27ce4e1979a/results/telemetry/sessions/scout-730-20260929-02.last.md
[fractional-comparison-report]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/cdc7a3c9b2f2a6bd1f284c0e2d3f0d2e199c9715/results/telemetry/sessions/scout-730-20261001-01.last.md
[survey-733-author]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/2814d000e9c6127bc4d5d30a2ee3f5fe4eb6edc9/results/telemetry/sessions/scout-733-20260929-01.last.md
[survey-733-referee]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/ac0e8ed88fb5400acee65d0a1eaa8a73bf862a8b/results/telemetry/sessions/scout-733-20260929-02.last.md
[benchmark-report]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/2a3db5b923e240d1a54c50ae25ab54108ac2e2c4/results/telemetry/sessions/scout-730-20260929-01.last.md
[pr-731]: https://github.com/Dengnifer/MIPStarRE-QPBT/pull/731
[ldt-tested-head]: https://github.com/Dengnifer/MIPStarRE-QPBT/commit/df8f6bc9255e7aa524ceebff3bffc0087dfc1ee2
[ldt-merge]: https://github.com/Dengnifer/MIPStarRE-QPBT/commit/fac99fdf22bbdbb83a2376ca48cd679dc7d13750
[ldt-baseline-proved]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/fac99fdf22bbdbb83a2376ca48cd679dc7d13750/MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean#L329-L384
[ldt-improved-proved]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/fac99fdf22bbdbb83a2376ca48cd679dc7d13750/MIPStarRE/LDT/Test/MainTheorem/LinearTriangle/MainFormal.lean#L180-L236
[ldt-comparison-le]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/fac99fdf22bbdbb83a2376ca48cd679dc7d13750/MIPStarRE/LDT/Test/MainTheorem/LinearTriangle/MainFormal.lean#L299-L315
[ldt-comparison-lt]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/fac99fdf22bbdbb83a2376ca48cd679dc7d13750/MIPStarRE/LDT/Test/MainTheorem/LinearTriangle/MainFormal.lean#L317-L358
[ldt-triangle-proved]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/fac99fdf22bbdbb83a2376ca48cd679dc7d13750/MIPStarRE/LDT/Preliminaries/Triangles/CompleteMeasurements.lean#L28-L203
[ldt-axiom-audit]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/fac99fdf22bbdbb83a2376ca48cd679dc7d13750/MIPStarRE/LDT/Test/AxiomAudit.lean#L313-L327
[ldt-implementation-audit]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/fac99fdf22bbdbb83a2376ca48cd679dc7d13750/audits/issue-728-ldt-linear-error-bounds.md
[ldt-supplementary-evidence]: https://github.com/Dengnifer/MIPStarRE-QPBT/pull/731#issuecomment-5880259798
[ldt-independent-review]: https://github.com/Dengnifer/MIPStarRE-QPBT/pull/731#pullrequestreview-5345643236
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
[qpbt-paper-pauli-metric]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex#L1431-L1444
[qpbt-paper-composition]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex#L1267-L1404
[qpbt-paper-unitary]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9/references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex#L1666-L1876
[delta-qld]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Test/SoundnessDefs.lean#L30-L38
[pauli-soundness]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Test/Soundness.lean#L110-L122
[direct-one-coordinate]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Combining/DirectLowDegree/AnyStrategySoundness.lean#L360-L400
[state-extraction]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Extraction/StateExtraction.lean#L97-L130
[raw-transfer]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Test/Soundness/RawOperatorTransferCore.lean#L568-L683
[malformed-transfer]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Test/Soundness/RawOperatorTransferCore.lean#L93-L216
[consistency-calculus]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Games/DistanceTheorems/Calculus.lean#L300-L345
[point-commutation]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Observables/WinImplications/CommutingObs.lean#L450-L500
[qpbt-pasting]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Games/Sandwich/Pasting/Assembly.lean#L714-L790
[passing-comparison]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Combining/ExtendedLineGame/EvaluatedLineComparison.lean#L245-L285
[rounding-transport]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Games/DistanceTheorems/RoundingTransport.lean#L120-L175
[combined-points]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Combining/Points.lean#L55-L90
[extended-lines]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Combining/ExtendedLines/Estimates.lean#L235-L315
[projective-rounding]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Games/DistanceTheorems/ProjectiveRounding.lean#L475-L525
[actual-rounding]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Combining/ActualErrorBounds.lean#L20-L63
[direct-parameter]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Error.lean#L65-L95
[seed-indexed]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean#L70-L115
[general-transport]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/Error.lean#L215-L255
[epr-state]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Extraction/EPRState.lean#L135-L173
[ms-rigidity]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Test/MagicSquareTheorems.lean#L640-L675
[ms-anticommutator]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Observables/WinImplications/AnticommutingObs.lean#L131-L155
[dimension-obstruction]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/6ea9f96bd86aaaad613130dea49eefdf6e80c5a9/MIPStarRE/QPBT/Combining/ErrorObstruction.lean#L24-L50
[pasting-product-gap]: paper-gaps/qpbt_pasting-product-error.tex
[public-commit]: https://github.com/vidick/MIPRE-formalization/tree/286b3ca44f811fa6e37517c04981bc2f164ee6b5
[public-license]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/LICENSE
[public-deltaq]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/Combined.lean#L350
[public-pairs]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/Lines.lean#L1027-L1033
[public-gs-ld]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/PaddedLIDT.lean#L168-L174
[public-lidt-constants]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/LIDT/Adapter/Parameters.lean#L45-L54
[public-prod-s]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/PaddedLIDT.lean#L552-L560
[public-self-cons]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/SwapItemOne.lean#L146
[public-final-expansion]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/SwapItemTwo.lean#L300-L309
[public-qlderr]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/QLDError.lean#L84-L99
[public-qlderr-witness]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/QLDError.lean#L297-L305
[public-named-error]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/Soundness.lean#L470
[public-soundness]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/Soundness.lean#L525-L574
[public-mirror]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/MirrorExists.lean#L180-L207
[public-regime]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/Regime.lean#L45-L72
[public-rd-pauli-vec]: https://github.com/vidick/MIPRE-formalization/blob/286b3ca44f811fa6e37517c04981bc2f164ee6b5/MIPRE/Background/QLD/PauliBasis.lean#L190
