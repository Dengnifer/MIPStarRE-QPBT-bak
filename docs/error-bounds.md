# Error bounds in the low individual degree and Pauli basis tests

> **Interim implementation status, 2026-09-29 (Asia/Tokyo).** The survey and
> source-baseline references remain pinned to repository commit
> [`7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9`][baseline-commit]. The selected
> LDT improvement is proved and merged by [PR #731][pr-731]: canonical evidence
> was collected on exact head
> [`df8f6bc9255e7aa524ceebff3bffc0087dfc1ee2`][ldt-tested-head], which was
> merged as [`fac99fdf22bbdbb83a2376ca48cd679dc7d13750`][ldt-merge], and issue
> [#728][issue-728] is closed. The fixed-witness QPBT raw and qubit baselines
> are **PROVED LOCALLY, NOT MERGED** at
> `35ad17dcd89de235373d5c1c5b10050f631144c9`; the published
> [proof receipt][qpbt-baseline-receipt] records their validation. The current
> issue [#729][issue-729] target
>
> \[
>  \min\{4,10^{14}(md)^4E_{1/67108864}\}
> \]
>
> together with its canonical-100 and two qubit forms is still **IN PROGRESS**.
> The local A/B component and global-pair proof layers are complete at the
> recorded checkpoints `dee02c251105` and `88436c45`, while the integrated C
> checkpoint is `388bfa7c`; none of these checkpoints is a merged final
> headline. Survey [#733][issue-733] is closed after the independently checked
> plan was adopted in [comment 5882105555][issue-733-adoption]. The selected
> follow-up [#735][issue-735] is open and records dependencies on #729 and the
> adopted #733 survey. The owner-facing overview [#734][issue-734] is pinned
> and records mathematical acceptance. The final report now depends on both
> #729 and #735 being proved and merged. Neither the QPBT track nor the whole
> project is claimed complete.

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
- **PROVED LOCALLY, NOT MERGED** means that dedicated declarations with the
  displayed constants passed local exact-head checks, but have not completed
  publication, canonical CI, independent review, and merge.
- **Proved explicit baseline** means that a dedicated declaration with the
  displayed constants has passed exact-head validation. The report states
  separately whether that declaration is local or merged.
- **IMPLEMENTED (selected; proved and merged)** means that the selected stronger
  declaration, its baseline, and its comparison evidence are present on the
  merged branch.
- **IN PROGRESS (selected)** means that Lean implementation has started, but no
  completed and merged headline declaration is evidence for the target yet.
- **MATHEMATICALLY CHECKED, NOT LEAN-IMPLEMENTED** means that an author derived
  the complete mathematical target and an independent referee accepted it, but
  the required Lean declarations do not yet exist.
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

### Locally proved explicit baseline

The [source theorem `thm:pauli`][qpbt-paper-pauli] and Lean theorem
`pauli_soundness` assert the existence of universal \(a,b\) for the error
\(\Delta_{a,b}\). The source prints no numerical exponent. At the original
pinned baseline commit, tracing the proof gives the following constants:

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

The later local fixed-witness proof keeps the enormous projective-setting
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
`pauli_soundness_explicit_baseline` and
`pauli_soundness_qubit_explicit_baseline` are **PROVED LOCALLY, NOT MERGED** at
`35ad17dcd89de235373d5c1c5b10050f631144c9`. Their public assumptions match the
source strategy and nonnegative-error domain, and each produces one common
normalized auxiliary state with the unsquared state estimate and both raw
prescribed-answer summed-squared operator estimates. The
[published receipt][qpbt-baseline-receipt] records focused builds, axiom audits,
and proof-hole scans. It is evidence for local proof status, not publication or
merge. The padded \(a_{\mathrm{base}}\) remains a scalar comparison only, and
the source-facing `pauli_soundness` theorem remains existential.

### Current issue #729 target

The selected quantitative calculation is

\[
 \boxed{
 B_{\mathrm{QPBT}}
 =\min\{4,10^{14}(md)^4E_b\},
 \qquad b=\frac1{67108864}.}
\]

This headline remains **IN PROGRESS (selected)** under issue
[#729][issue-729]. The local A/B component and global-pair proof layers are
complete at `dee02c251105` and `88436c45`, and C has an integrated checkpoint at
`388bfa7c`. The unconditional final headline is not yet complete or merged.
The merged native-LDT result is one input to this route; it does not by itself
prove the QPBT propagation or the improved Pauli soundness declaration.

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

This is the current issue #729 implementation scope. It has three inseparable
ingredients:

1. import the selected LDT theorem into the live one-coordinate direct
   low-degree theorem without the current extra square root;
2. keep numerical coefficients separate from polynomial degrees through the
   point, line, rounding, and global-pair estimates;
3. retain the stronger state estimate separately from the squared operator
   estimates through extraction, Naimark reduction, and raw-answer transfer.

The additional accepted QPBT mechanism under issue #735 is separate and must be
implemented only after the actual #729 result is complete. Its comparison uses
the #729 extraction improvement on both sides, so that gain is not counted
twice.

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

### Additional selected target after issue #729

The complete issue #733 [author report][survey-733-author] and independent
[referee report][survey-733-referee] support exactly one additional QPBT-only
implementation with LDT frozen. Put

\[
 p=\frac{15}{4}+\frac{5}{262144}<4.
\]

The accepted target is

\[
 \boxed{
 B_{\mathrm{QPBT}}^{\mathrm{struct}}
 =\min\!\left\{4,10^{10}n^pE_{1/1048576}\right\}.}
\]

It implies the simpler
\(\min\{4,10^{10}n^4E_{1/1048576}\}\) bound, the canonical
\(\Delta_{100,1/1048576}\) form, and exact qubit counterparts. This target is
**MATHEMATICALLY CHECKED, NOT LEAN-IMPLEMENTED**. Issue [#735][issue-735]
tracks its implementation after #729; neither the theorem names nor the final
code links should be fixed before that implementation exists.

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

| Stage | Current #729 calculation | Selected #735 calculation |
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
\(1/67108864\) to \(1/1048576\). The extraction gain already selected in #729
appears on both sides and receives no additional credit.

This complete projective calculation is selected over the weaker alternatives.
Keeping only the existing Schmidt-mirror estimate gives a twofold gain. Using
only one of the commutation, passing, or rounding improvements also gives at
most a twofold gain. The projective squared-failure pasting estimate gives an
eightfold gain by itself, and its coherent propagation through commutation,
passing, and rounding gives the largest justified common-headline improvement.
The smaller coefficient and the fractional dimension power are secondary.

### Source argument and checked realization

The primary source theorem prints only the existence of universal constants
\(a,b\). The numerical exponents \(1/5242880000\), \(1/67108864\), and
\(1/1048576\) are derived explicit envelopes; none is a printed source
exponent.

Three parts of the accepted plan strengthen or make explicit the source
argument itself: the linear complete-measurement triangle is an alternative to
the printed square-root triangle, the twisted-commutation estimate improves
from \(O(\sqrt e)\) to \(O(e)\), and the projective subcase of pasting receives
the explicit linear bound \(307\delta+16\eta\). By contrast, removing the
direct-game passing root and improving same-space projective-rounding transport
concern the checked Lean realization. The paper invokes the constructed
low-degree strategy and an ancillary Naimark route rather than printing those
two extra losses.

At a fixed numerical LDT output \(\lambda\), the current checked route has
dominant common dependence \(\lambda^{1/16}\), while the proposed checked route
has \(\lambda^{1/8}\). This does **not** beat the literal source Naimark route,
whose displayed dependence is \(\lambda^{1/4}\). The 64-fold statement compares
two fully specified checked calculations with the same LDT black box; it is not
a comparison with a printed numerical paper exponent.

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
| Explicit fixed witnesses, from [`deltaQld`][delta-qld] and [`pauli_soundness`][pauli-soundness] | Existential \((a,b)\) to exact \((a_0,1/5242880000)\), with \(a_0=346\cdot21^3\operatorname{pauliBaselineProjectiveConstant}^4\); \(a_{\mathrm{base}}\) remains a padded scalar comparison | Establishes the numerical raw/qubit baseline, including the enormous polynomial degree | High formal plumbing through opaque existential interfaces | **PROVED LOCALLY, NOT MERGED** by `pauli_soundness_explicit_baseline` and `pauli_soundness_qubit_explicit_baseline` at `35ad17dcd89de235373d5c1c5b10050f631144c9`; see the [receipt][qpbt-baseline-receipt] |
| **Current #729 quantitative composition**, using the improved one-coordinate LDT import, separate coefficient/degree bounds, and separate state/operator estimates from [`StateExtraction.lean`][state-extraction] through [`RawOperatorTransfer.lean`][raw-transfer] | \(\Delta_{a_0,1/5242880000}\to\min(4,10^{14}n^4E_{1/67108864})\), then canonical \(\Delta_{100,1/67108864}\) | Exponent multiplied by \(78.125\); sharp quantitative degree becomes four; raw effects and qubit form retained | High interface work; same witnesses must survive every estimate | **IN PROGRESS (selected)** under [#729][issue-729]. A/B local layers are complete and C is integrated, but the unconditional headline and all four required forms are not yet merged |
| Superseded pre-selection quantitative envelopes from the same mechanisms | Earlier calculations included \(\Delta_{100,1/2621440000}\), then \(\Delta_{100,1/327680000}\); extraction alone gave exponent \(1/655360000\), and an earlier joint LDT/extraction estimate gave \((a,b)=(10^{740},1/268435456)\) | Each improved the traced baseline, but all are weaker than the final selected calculation | Similar or greater plumbing, with worse retained constants | **NOT IMPLEMENTED (superseded)**. Recorded to preserve the survey history; not separate scopes |
| **Selected complete-measurement and squared-failure calculus** | #729 target to \(\min(4,10^{10}n^{15/4+5/262144}E_{1/1048576})\), then \(n^4\), canonical-100, and qubit consequences | Additional 64-fold exponent gain with the same LDT function and sample | Medium/high end-to-end QPBT work; preserve completeness hypotheses, placements, collision terms, witnesses, range projections, and raw effects | **MATHEMATICALLY CHECKED, NOT LEAN-IMPLEMENTED** under [#735][issue-735]; accepted by the [author][survey-733-author] and [referee][survey-733-referee] reports |
| Linear consistency calculus in commutation, starting from [`consistencyDefect_trans_le`][consistency-calculus] and [`CommutingObs.lean`][point-commutation] | Squared twisted-commutator error \(O(\sqrt e)\to O(e)\); joint-point error \(O(e^{1/8})\to O(e^{1/4})\) | Twofold final exponent gain by itself | Medium/broad; completeness is load-bearing and every directed comparison must survive | **Selected as one component of #735; mathematically checked, not Lean-implemented** |
| Retain the Schmidt-mirror estimate in [`Pasting/Assembly.lean`][qpbt-pasting] | Pasting \(115(\eta^{1/4}+\delta^{1/8})\to12(\eta^{1/4}+\delta^{1/4})\) | Twofold headline exponent gain by itself | Medium; localized proof needs a sharper parameterization | **NOT IMPLEMENTED (comparison only)**. This is weaker than the selected projective squared-failure estimate |
| Projective pasting by squared failure amplitudes | Same sandwich bound improves to \(307\delta+16\eta\) when both codeword measurements are projective | Eightfold headline exponent gain by itself; improves field-error power as well | Medium/high; finite-sum identities, post-measurement collision weights, and heterogeneous placements are load-bearing | **Selected as the central new #735 estimate; mathematically checked, not Lean-implemented**. Both actual QPBT codeword families are projective; the general pasting theorem remains unchanged |
| Linear complete-POVM triangle in direct-game passing, at [`EvaluatedLineComparison.lean`][passing-comparison] | \(O(\sqrt{Q+L}+r)\to O(Q+L+r)\) across both completed axis and diagonal readouts | Twofold final exponent gain by itself | Medium; both orientations, both line types, and all seven rejection branches must be propagated | **Selected as one component of #735; mathematically checked, not Lean-implemented** |
| Linear rounding transport in [`RoundingTransport.lean`][rounding-transport] | Global-pair dependence \(\lambda^{1/8}\to\lambda^{1/4}\) before the unchanged final state root | Twofold final exponent gain at fixed \(\lambda\) | Medium; choose roundings before postprocessing maps and preserve quantifier order | **Selected as one component of #735; mathematically checked, not Lean-implemented** |
| Earlier combination of four local root-removal projections | Prospective sixteenfold exponent gain | Historical indication that a combined change could dominate any local tweak | High, multi-construction; complete constants were not then established | **SUPERSEDED as a projection** by the independently accepted 64-fold projective calculation; retained to preserve survey history |
| Positive-failure state transfer | For a positive failure effect, improve the operator component from \(O(\sqrt x+r)\) to \(O(x+r)\) | Stronger operator conclusion, but no improvement to the common state-limited headline | Medium; positivity and range terms must remain explicit | **NOT IMPLEMENTED (deferred)**. It does not beat the selected common-headline mechanism |
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
| Aggregate malformed-answer incidences in [`RawOperatorTransfer.lean`][raw-transfer] | \(86\varepsilon\to43\varepsilon\) before raw transfer | Coefficient only | Needs a new edge-sum proof | **NOT IMPLEMENTED (deferred)** |
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

### Source and domain

The benchmark is Thomas Vidick's public `MIPRE-formalization` at exact commit
[`286b3ca44f811fa6e37517c04981bc2f164ee6b5`][public-commit]. The inspected
mirror contained 398 manifested source files, all of whose hashes matched its
provenance record. The pinned repository license is
[Apache-2.0][public-license]. This is a public-only, source-inspected
comparison. No benchmark code was copied, and no benchmark build was run for
this report.

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
| Current #729 canonical target | \(100\) | \(1/67108864\) | **IN PROGRESS (selected)** under [#729][issue-729]; raw prescribed-answer effects and fixed odd-extension field model |
| Proposed #735 canonical consequence | \(100\) | \(1/1048576\) | **MATHEMATICALLY CHECKED, NOT LEAN-IMPLEMENTED**; same frozen LDT input, raw prescribed-answer effects, and fixed odd-extension field model |
| Public reconstructed proof witness | \(a_V\) above | \(1/2560000\) | Witness used by the public existential error-shape proof |
| Public sharper calculated envelope | \(10^{12}\) | \(1/1280000\) | Unformalized scalar calculation from the public definitions |

For the current #729 target, the public calculated exponent is \(52.4288\)
times the local exponent, while the local polynomial dependence is far smaller.
That comparison does not carry over to the proposed #735 exponent:

\[
 \frac{1/1048576}{1/1280000}=1.220703125.
\]

Thus the proposed numerical exponent is larger than the public calculated
exponent, and its canonical polynomial parameter is smaller. This arithmetic
does not prove cross-repository dominance. The domains, answer normalization,
raw/completed conversion, coefficients, caps, and actual composed functions
still differ, and no transport theorem connects them. The exact comparison and
regimes must be recomputed after the #735 Lean proofs establish their final
constants.

### Current-#729 regimes in which each side is smaller

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
parameter recommendations. They compare the current #729 expression with the
public expressions; they are not claims about the proposed #735 target. At
fixed \(md\), reducing \(\varepsilon\) and increasing \(q\) cannot remove the
positive tail term \(2^{-bmd}\). Every finite-\(md\) envelope therefore has a
nonzero floor.

## Implementation evidence and remaining work

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
and review receipts are dated September 28 in UTC; this report uses the local
Asia/Tokyo date September 29. The
[merged implementation audit][ldt-implementation-audit] records the
corresponding statement-integrity and construction details.

### Local QPBT baseline evidence

The fixed numerical baseline now has local Lean evidence. At
`35ad17dcd89de235373d5c1c5b10050f631144c9`,
`pauli_soundness_explicit_baseline` and
`pauli_soundness_qubit_explicit_baseline` prove the raw and qubit forms at

\[
 a_0=346\cdot21^3\operatorname{pauliBaselineProjectiveConstant}^4,
 \qquad b_0=1/5242880000.
\]

The [published receipt][qpbt-baseline-receipt] reports focused builds, both
headline axiom audits, and clean proof-hole and forbidden-token scans. This is
not merged evidence: canonical CI, independent review, publication of the code
commit, and merge remain part of issue #729's integration work.

### Final-report checklist

- [x] Record the proved LDT baseline, improved headline, comparison regimes,
  declaration names, PR, tested head, merge commit, axiom audits, CI, and
  independent review.
- [x] Keep the LDT source theorem unchanged and describe the stronger result as
  a separate Lean-only quantitative theorem on the existing corrected domain.
- [x] Record the locally proved fixed-witness raw/qubit QPBT baseline, its exact
  symbolic \(a_0\), exponent \(b_0\), local commit, and published proof receipt.
- [ ] Merge and record that fixed-witness baseline for issue #729. The exact
  theorem constant \(a_0\) and padded scalar bound \(a_{\mathrm{base}}\) must
  not be conflated.
- [ ] Merge and record both the structured QPBT declaration proving
  \(\min(4,10^{14}(md)^4E_{1/67108864})\) and the canonical `deltaQld`
  corollary with \(a=100\) and \(b=1/67108864\), together with the exact qubit
  counterpart of each. Verify arbitrary strategies, the nonnegative error
  domain, raw prescribed-answer effects, isometry range projections, and one
  common auxiliary state.
- [ ] Change the QPBT selected status to **IMPLEMENTED** only after merged
  theorems establish all four required forms: the structured bound, the
  canonical \(a=100\) form, and their exact qubit counterparts. A precisely
  documented stronger result is acceptable only if it implies all four forms.
  The native LDT merge alone is not evidence of QPBT propagation.
- [x] Record the adopted issue #733 mathematical survey and independent check,
  its closure after comment 5882105555, and the pinned issue #734 overview.
- [ ] After #729, implement and merge issue #735's fractional-power structured
  bound, its \(n^4\) consequence, canonical \(a=100\) form, and both exact qubit
  counterparts. Keep \(\delta_{\mathrm{LD}}(30,1/8192)\), dimension \(2m+2\),
  and sample \(2560000(2m+2)^3d\) fixed, and leave the general pasting theorem
  unchanged.
- [ ] Record exact-head QPBT axiom-audit, focused-check, full-CI, review, and
  merge evidence for both #729 and #735 before finalizing this report.
- [ ] Preserve the benchmark qualifications: commit
  `286b3ca44f811fa6e37517c04981bc2f164ee6b5` was source-inspected but not
  built; the public \((10^{12},1/1280000)\) envelope and the factor-104 raw
  conversion are unformalized calculations; the existing regime examples apply
  to #729, not automatically to #735; no cross-repository transport theorem has
  been proved.

The remaining report blockers are completion and merge of the #729 headline,
followed by implementation and merge of #735 with exact evidence. The final
report must preserve the same measurements, auxiliary state, isometries, range
projections, raw effects, and full-domain fallbacks through both results. The
merged native-LDT theorem and the accepted issue #733 mathematics do not by
themselves discharge those Lean obligations or complete the QPBT track.

[baseline-commit]: https://github.com/Dengnifer/MIPStarRE-QPBT/commit/7bdfa416b7ff1f4a19de98b915efb3ca940f6fd9
[issue-728]: https://github.com/Dengnifer/MIPStarRE-QPBT/issues/728
[issue-729]: https://github.com/Dengnifer/MIPStarRE-QPBT/issues/729
[issue-733]: https://github.com/Dengnifer/MIPStarRE-QPBT/issues/733
[issue-733-adoption]: https://github.com/Dengnifer/MIPStarRE-QPBT/issues/733#issuecomment-5882105555
[issue-734]: https://github.com/Dengnifer/MIPStarRE-QPBT/issues/734
[issue-735]: https://github.com/Dengnifer/MIPStarRE-QPBT/issues/735
[qpbt-baseline-receipt]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/8da61804dc034d3f7bd4d1e701891bb54eb9bce6/results/telemetry/sessions/prover-729-20260929-03.last.md
[survey-733-author]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/2814d000e9c6127bc4d5d30a2ee3f5fe4eb6edc9/results/telemetry/sessions/scout-733-20260929-01.last.md
[survey-733-referee]: https://github.com/Dengnifer/MIPStarRE-QPBT/blob/ac0e8ed88fb5400acee65d0a1eaa8a73bf862a8b/results/telemetry/sessions/scout-733-20260929-02.last.md
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
