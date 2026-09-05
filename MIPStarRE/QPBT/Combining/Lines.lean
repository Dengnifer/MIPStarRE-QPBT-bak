import MIPStarRE.QPBT.Combining.Lines.ConsistencyPositivity
import MIPStarRE.QPBT.Combining.Lines.RestrictedAverage
import MIPStarRE.QPBT.Combining.Lines.SubLineBind
import MIPStarRE.QPBT.Combining.Lines.SubLineBlocks
import MIPStarRE.QPBT.Combining.Lines.SubLineBranch
import MIPStarRE.QPBT.Combining.Lines.SubLineConstruct
import MIPStarRE.QPBT.Combining.Lines.SubLineExtended
import MIPStarRE.QPBT.Combining.Lines.SubLineMixture
import MIPStarRE.QPBT.Combining.Lines.SubLinePrefix
import MIPStarRE.QPBT.Combining.Lines.SubLineProduct
import MIPStarRE.QPBT.Combining.Lines.SubLineSeed
import MIPStarRE.QPBT.Combining.Lines.SubLineShuffle
import MIPStarRE.QPBT.Combining.Lines.SubLineSource
import MIPStarRE.QPBT.Combining.Lines.SubLineSupport
import MIPStarRE.QPBT.Combining.Lines.SubLineTransport
import MIPStarRE.QPBT.Combining.Lines.SubLineUniform
import MIPStarRE.QPBT.Combining.Points
import MIPStarRE.QPBT.Combining.Witnesses
import MIPStarRE.QPBT.Games.Sandwich
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Combined lines and restricted line distributions

This module states the construction of the joint X/Z line measurements, the
mixture and error-inflation estimates for restricted line distributions, and
the sub-line distribution used to combine the two bases.  The extended line
in the sub-line construction uses the directly indexed carrier, so the
sub-line statement is a formalization auxiliary assertion and carries no
divisibility hypothesis at dimension `2 * m + 2`.

The mixture identity, the two inflation estimates, and their instance for the
evaluated line measurement are proved in the submodules
`Combining.Lines.RestrictedMixture` (the uniform coordinate-index mixture),
`Combining.Lines.RestrictedAverage` (the `2 m` and `4 m ^ 2` inflation
factors), and `Combining.Lines.ConsistencyPositivity` (nonnegativity of the
consistency defect on opposite placements).

## References

The declarations formalize `lem:qld-xz-lines` and
`lem:restricted-line-mixture-bounds` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`; `exists_subLineWitness`
instead supports `lem:qld-sublines` through the directly indexed extended-line
carrier and probability law.  Their paper sources
are `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-894`
and `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1069`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum
open scoped Matrix MatrixOrder

noncomputable section

/-- On a nonzero direction, completed evaluation agrees with polynomial evaluation at
the unique affine parameter. This proof-only restriction is used in the collision
step of `lem:qld-xz-lines`, paper `14_analysis_of_the_pauli_basis_test.tex:950-955`. -/
theorem evalOpt_affine_parameter_of_direction_ne_zero {L : LdParams} {bound : ℕ} (line : LineDesc L)
    (hdir : line.direction ≠ 0) (poly : DegPoly L bound) (param : ScalarQ L) :
    evalOpt line (line.base + param • line.direction) poly =
      some (evalCoefficient poly param) := by
  apply (evalOpt_eq_some_iff _ _ _ _).mpr
  refine ⟨⟨param, rfl⟩, ?_⟩
  intro other heq
  have hsmul : param • line.direction = other • line.direction := add_left_cancel heq
  have hsub : (param - other) • line.direction = 0 := by
    rw [sub_smul, hsmul, sub_self]
  have hparam : param = other := sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hdir)
  rw [hparam]

/-- The Mathlib polynomial associated to a coefficient tuple has the specified
evaluation. This formalization-only identity connects the coefficient convention
to the root bound invoked at paper `14_analysis_of_the_pauli_basis_test.tex:955`. -/
theorem polynomial_ofFn_eval_eq_evalCoefficient {K : Type*} [CommSemiring K]
    [DecidableEq K] {size : ℕ}
    (coeffs : Fin size → K) (param : K) :
    (Polynomial.ofFn size coeffs).eval param = evalCoefficient coeffs param := by
  simp [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, evalCoefficient]

/-- Distinct coefficient polynomials of degree at most `bound` agree at no more
than `bound` field elements. This is the univariate root bound underlying the
Schwartz--Zippel step at paper `14_analysis_of_the_pauli_basis_test.tex:955`.
No restriction of the degree relative to the field size is required. -/
theorem evalCoefficient_collision_card_le {L : LdParams} {bound : ℕ}
    (first second : DegPoly L bound) (hne : first ≠ second) :
    (Finset.univ.filter fun param => evalCoefficient first param =
      evalCoefficient second param).card ≤ bound := by
  classical
  by_contra hcard
  have hdeg (poly : DegPoly L bound) :
      (Polynomial.ofFn (bound + 1) poly).natDegree ≤ bound :=
    Nat.lt_succ_iff.mp (Polynomial.ofFn_natDegree_lt (by omega) poly)
  have heq := Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (Polynomial.ofFn (bound + 1) first) (Polynomial.ofFn (bound + 1) second)
    (f := fun param : {param : ScalarQ L // evalCoefficient first param =
      evalCoefficient second param} => param.val) Subtype.val_injective
    (fun param => by simpa only [polynomial_ofFn_eval_eq_evalCoefficient] using param.property)
    (by simpa only [Fintype.card_subtype] using
      lt_of_le_of_lt (max_le (hdeg first) (hdeg second)) (Nat.lt_of_not_ge hcard))
  exact hne (Polynomial.injective_ofFn _ heq)

/-- On a nondegenerate line, completed evaluations of distinct degree-bounded
polynomials collide with probability at most the degree bound divided by the field
size under a uniform affine parameter. This is a proof-only restriction of the
collision step at paper `14_analysis_of_the_pauli_basis_test.tex:950-955`. -/
theorem evalOpt_uniform_parameter_collision_le {L : LdParams} {bound : ℕ} (line : LineDesc L)
    (hdir : line.direction ≠ 0) (first second : DegPoly L bound)
    (hne : first ≠ second) :
    avgOver (uniformDistribution (ScalarQ L)) (fun param =>
      if evalOpt line (line.base + param • line.direction) first =
        evalOpt line (line.base + param • line.direction) second then 1 else 0) ≤
      (bound : ℝ) / Fintype.card (ScalarQ L) := by
  classical
  simp_rw [evalOpt_affine_parameter_of_direction_ne_zero line hdir, Option.some.injEq]
  have hcard := evalCoefficient_collision_card_le first second hne
  unfold avgOver
  simp only [uniformDistribution_support, uniformDistribution_weight_apply,
    mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

/-- Multiplying a normalized restricted average by its retained mass gives the
unnormalized restricted sum. This formalization-only identity supports proof-only
conditioning in `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`; it changes no game distribution. -/
theorem avgOver_restrict_mul_mass {Sample : Type*} [DecidableEq Sample]
    (dist : Distribution Sample) (good : Sample → Prop) [DecidablePred good]
    (hpos : 0 < ∑ sample ∈ dist.support.filter good, dist.weight sample)
    (value : Sample → ℝ) :
    (∑ sample ∈ dist.support.filter good, dist.weight sample) *
      avgOver (Distribution.restrict dist good hpos) value =
      ∑ sample ∈ dist.support.filter good, dist.weight sample * value sample := by
  unfold avgOver Distribution.restrict
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sample hsample
  simp only [if_pos (Finset.mem_filter.mp hsample).2]
  field_simp

/-- An average of a function bounded above by one is at most the retained mass
times its conditional average, plus the discarded probability mass. This
formalization-only estimate restores the original distribution after proof-only
conditioning in `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`. No discarded mass is omitted. -/
theorem avgOver_le_restrict_add_discarded_mass {Sample : Type*} [DecidableEq Sample]
    (dist : Distribution Sample) (good : Sample → Prop) [DecidablePred good]
    (hpos : 0 < ∑ sample ∈ dist.support.filter good, dist.weight sample)
    (defect : Sample → ℝ) (hunit : ∀ sample, defect sample ≤ 1) :
    avgOver dist defect ≤
      (∑ sample ∈ dist.support.filter good, dist.weight sample) *
        avgOver (Distribution.restrict dist good hpos) defect +
      ∑ sample ∈ dist.support.filter (fun sample => ¬ good sample), dist.weight sample := by
  classical
  rw [avgOver_restrict_mul_mass]
  unfold avgOver
  rw [← Finset.sum_filter_add_sum_filter_not dist.support good
    (fun sample => dist.weight sample * defect sample)]
  exact add_le_add_right (Finset.sum_le_sum fun sample _ =>
    mul_le_of_le_one_right (dist.nonnegative sample) (hunit sample)) _

/-- Under the unchanged diagonal line-point law, zero projected directions have
probability at most the inverse field size: the last raw direction coordinate must
vanish and is uniform. Source: `def:line-point-dist`, paper
`08_classical_and_quantum_low_degree_tests.tex:274-287`. This proof-only bound
supports the collision restriction in issue #118. -/
theorem dLinePointDist_zero_direction_mass_le (L : LdParams) :
    avgOver (dLinePointDist L) (fun sample =>
      if sample.1.direction = 0 then 1 else 0) ≤
      1 / Fintype.card (ScalarQ L) := by
  classical
  let last : Fin L.m := ⟨L.m - 1, by have := L.hm; omega⟩
  let coord : LdIndex L := .inr last
  have hmap : (uniformDistribution (LdSpace L)).map (fun raw => raw coord) =
      uniformDistribution (ScalarQ L) := by
    change (uniformDistribution (LdSpace L)).map
      (fun raw => (Equiv.funSplitAt coord (ScalarQ L) raw).1) = _
    rw [← Distribution.map_map, uniformDistribution_map_equiv,
      uniformDistribution_map_fst]
  have hzero : avgOver (uniformDistribution (LdSpace L))
      (fun raw => if raw coord = 0 then (1 : ℝ) else 0) =
      1 / Fintype.card (ScalarQ L) := by
    rw [← Distribution.avgOver_map (uniformDistribution (LdSpace L))
      (fun raw => raw coord) (fun value => if value = 0 then (1 : ℝ) else 0), hmap]
    simp [avgOver, uniformDistribution_weight_apply, mul_ite]
  unfold dLinePointDist clDistribution
  rw [Distribution.avgOver_map, Distribution.avgOver_map]
  refine le_trans (avgOver_mono _ _ _ ?_) hzero.le
  intro raw
  dsimp only
  rw [dLineDescOf_ldDLineCL]
  split_ifs with hdir hcoord hcoord
  · exact le_rfl
  · exfalso
    apply hcoord
    have hlast := congrFun hdir last
    change prefixProjection (chiIndex L (LdSpace.seed raw))
      (LdSpace.direction raw) last = 0 at hlast
    have hindex : ¬ last.val < (chiIndex L (LdSpace.seed raw)).val := by
      have := (chiIndex L (LdSpace.seed raw)).isLt
      dsimp [last]
      omega
    simpa [prefixProjection, hindex, LdSpace.direction, coord] using hlast
  · norm_num
  · exact le_rfl

/-- Axis-line sampling gives zero mass to zero directions, since a coordinate
direction is nonzero. This is a formalization-only consequence of
`def:line-point-dist`, paper `08_classical_and_quantum_low_degree_tests.tex:274-287`. -/
theorem aLinePointDist_zero_direction_mass (L : LdParams) :
    avgOver (aLinePointDist L) (fun sample =>
      if sample.1.direction = 0 then 1 else 0) = 0 := by
  classical
  unfold aLinePointDist
  rw [Distribution.avgOver_map]
  have hdir (raw : LdSpace L) : (aLineDescOf L raw).direction ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero (chiIndex L raw.seed)
    simp [aLineDescOf, LineDesc.direction, coordinateDirection] at hcoord
  simp [avgOver, hdir]

/-- The equal mixture of axis and diagonal line-point laws gives zero directions
mass at most `1 / (2q)`. This proof-only estimate preserves the source sampler of
`def:line-point-dist`, paper `08_classical_and_quantum_low_degree_tests.tex:274-287`,
including its degenerate fibers. -/
theorem linePointDist_zero_direction_mass_le (L : LdParams) :
    avgOver (linePointDist L) (fun sample =>
      if sample.1.direction = 0 then 1 else 0) ≤
      1 / (2 * Fintype.card (ScalarQ L)) := by
  rw [linePointDist, avgOver_mix, aLinePointDist_zero_direction_mass]
  have hdiag := dLinePointDist_zero_direction_mass_le L
  calc
    _ = (1 / 2 : ℝ) * avgOver (dLinePointDist L)
        (fun sample => if sample.1.direction = 0 then 1 else 0) := by ring
    _ ≤ (1 / 2 : ℝ) * (1 / Fintype.card (ScalarQ L)) :=
      mul_le_mul_of_nonneg_left hdiag (by norm_num)
    _ = _ := by rw [one_div_mul_one_div]

/-- A uniform point may be replaced by a uniform affine parameter on its
canonical line, while preserving the canonical representative jointly with the
point. This formalization-only identity, including zero directions, supports the
conditional sampling step at paper `14_analysis_of_the_pauli_basis_test.tex:955`. -/
theorem avgOver_lineRepMap_resample_parameter {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {dimension : ℕ} (direction : Fin dimension → K)
    (value : (Fin dimension → K) → (Fin dimension → K) → ℝ) :
    avgOver (uniformDistribution (Fin dimension → K))
      (fun point => value (lineRepMap direction point) point) =
    avgOver (uniformDistribution (Fin dimension → K)) (fun point =>
      avgOver (uniformDistribution K) (fun param =>
        value (lineRepMap direction point) (lineRepMap direction point + param • direction))) := by
  have hmap := uniformDistribution_map_lineRepMap_add_smul direction
  have havg := congrArg (fun dist => avgOver dist
    (fun point => value (lineRepMap direction point) point)) hmap
  rw [Distribution.avgOver_map, uniformDistribution_prod, avgOver_prod] at havg
  simpa only [lineRepMap_add_smul, lineRepMap_apply_self] using havg.symm

/-- Resampling a uniform parameter on the sampled axis line preserves the joint
line-point law. This formalization-only identity derives the conditional sampling
used at paper `14_analysis_of_the_pauli_basis_test.tex:955` from
`def:line-point-dist`, paper `08_classical_and_quantum_low_degree_tests.tex:274-287`. -/
theorem avgOver_aLinePointDist_resample_parameter (L : LdParams)
    (value : (LineDesc L × (Fin L.m → ScalarQ L)) → ℝ) :
    avgOver (aLinePointDist L) value =
    avgOver (aLinePointDist L) (fun sample => avgOver (uniformDistribution (ScalarQ L))
      (fun param => value (sample.1, sample.1.base + param • sample.1.direction))) := by
  classical
  unfold aLinePointDist clDistribution
  simp only [Distribution.avgOver_map, aLineDescOf_ldALineCL]
  have hblock := uniformDistribution_map_equiv (ldSpaceBlockEquiv L).symm
  rw [← hblock]
  simp only [Distribution.avgOver_map]
  rw [uniformDistribution_prod]
  simp only [avgOver_prod]
  rw [avgOver_comm, avgOver_comm (uniformDistribution (Fin L.m → ScalarQ L))]
  apply congrArg
  funext block
  have hresample := avgOver_lineRepMap_resample_parameter (coordinateDirection (chiIndex L block.1))
      (fun base point => value (LineDesc.axis
        (lineRepMap (coordinateDirection (chiIndex L block.1)) base) block.1
        (lineRepMap_apply_self _ _), point))
  simp only [lineRepMap_apply_self] at hresample
  exact hresample

/-- Resampling a uniform parameter on the sampled diagonal line preserves the
joint line-point law, including the zero-direction fibers. This formalization-only
identity derives the conditional sampling used at paper
`14_analysis_of_the_pauli_basis_test.tex:955` from `def:line-point-dist`. -/
theorem avgOver_dLinePointDist_resample_parameter (L : LdParams)
    (value : (LineDesc L × (Fin L.m → ScalarQ L)) → ℝ) :
    avgOver (dLinePointDist L) value =
    avgOver (dLinePointDist L) (fun sample => avgOver (uniformDistribution (ScalarQ L))
      (fun param => value (sample.1, sample.1.base + param • sample.1.direction))) := by
  classical
  unfold dLinePointDist clDistribution
  simp only [Distribution.avgOver_map, dLineDescOf_ldDLineCL]
  have hblock := uniformDistribution_map_equiv (ldSpaceBlockEquiv L).symm
  rw [← hblock]
  simp only [Distribution.avgOver_map]
  rw [uniformDistribution_prod]
  simp only [avgOver_prod]
  rw [avgOver_comm, avgOver_comm (uniformDistribution (Fin L.m → ScalarQ L))]
  apply congrArg
  funext block
  have hprefix : ∀ index : Fin L.m, index.val < (chiIndex L block.1).val →
      prefixProjection (chiIndex L block.1) block.2 index = 0 := by
    intro index hindex
    simp [prefixProjection, hindex]
  have hresample := avgOver_lineRepMap_resample_parameter
    (prefixProjection (chiIndex L block.1) block.2)
    (fun base point => value (LineDesc.diagonal
      (lineRepMap (prefixProjection (chiIndex L block.1) block.2) base) block.1
      (prefixProjection (chiIndex L block.1) block.2)
      (lineRepMap_apply_self _ _) hprefix, point))
  simp only [lineRepMap_apply_self] at hresample
  exact hresample

/-- Uniform parameter resampling preserves the mixed line-point law exactly,
without excluding zero directions. This formalization-only identity justifies
conditioning on the line in the collision step of `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-955`. -/
theorem avgOver_linePointDist_resample_parameter (L : LdParams)
    (value : (LineDesc L × (Fin L.m → ScalarQ L)) → ℝ) :
    avgOver (linePointDist L) value =
    avgOver (linePointDist L) (fun sample => avgOver (uniformDistribution (ScalarQ L))
      (fun param => value (sample.1, sample.1.base + param • sample.1.direction))) := by
  rw [linePointDist, avgOver_mix, avgOver_mix]
  rw [avgOver_aLinePointDist_resample_parameter L value,
    avgOver_dLinePointDist_resample_parameter L value]

/-- The collision bound remains valid with any nonnegative weight depending only
on the line, after restricting to nonzero directions. This proof-only estimate
is the conditional form of the root argument in `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-955`; it is not the false
unrestricted collision claim on zero-direction coefficient presentations. -/
theorem linePointDist_nondegenerate_weighted_collision_le {L : LdParams} {bound : ℕ}
    (weight : LineDesc L → ℝ) (hweight : ∀ line, 0 ≤ weight line)
    (first second : DegPoly L bound) (hne : first ≠ second) :
    avgOver (linePointDist L) (fun sample =>
      if sample.1.direction ≠ 0 then weight sample.1 *
        (if evalOpt sample.1 sample.2 first = evalOpt sample.1 sample.2 second
          then 1 else 0) else 0) ≤
      (bound : ℝ) / Fintype.card (ScalarQ L) *
        avgOver (linePointDist L) (fun sample =>
          if sample.1.direction ≠ 0 then weight sample.1 else 0) := by
  classical
  rw [avgOver_linePointDist_resample_parameter]
  rw [← avgOver_const_mul]
  apply avgOver_mono
  intro sample
  by_cases hdir : sample.1.direction ≠ 0
  · simp only [if_pos hdir]
    rw [avgOver_const_mul]
    exact (mul_le_mul_of_nonneg_left
      (evalOpt_uniform_parameter_collision_le sample.1 hdir first second hne)
      (hweight sample.1)).trans_eq
      (mul_comm _ _)
  · simp [hdir, avgOver]

/-- On each nonzero-direction line fiber the collision mass is at most the
degree-to-field-size ratio times the fiber mass. Thus division by any positive
fiber mass gives the conditional probability required by `lem:pasting`. This
proof-only estimate supports paper `14_analysis_of_the_pauli_basis_test.tex:955`;
transport to the product law and the pasting register presentation is separate. -/
theorem linePointDist_nondegenerate_fiber_collision_le {L : LdParams} {bound : ℕ}
    (line : LineDesc L) (hdir : line.direction ≠ 0)
    (first second : DegPoly L bound) (hne : first ≠ second) :
    avgOver (linePointDist L) (fun sample =>
      if sample.1 = line then
        (if evalOpt sample.1 sample.2 first = evalOpt sample.1 sample.2 second
          then 1 else 0) else 0) ≤
      (bound : ℝ) / Fintype.card (ScalarQ L) *
        avgOver (linePointDist L) (fun sample => if sample.1 = line then 1 else 0) := by
  classical
  have hweight (other : LineDesc L) : (0 : ℝ) ≤ if other = line then 1 else 0 := by
    split_ifs <;> norm_num
  have hbound := linePointDist_nondegenerate_weighted_collision_le
    (fun other => if other = line then 1 else 0)
    hweight first second hne
  have hleft (sample : LineDesc L × (Fin L.m → ScalarQ L)) :
      (if sample.1.direction ≠ 0 then (if sample.1 = line then (1 : ℝ) else 0) *
        (if evalOpt sample.1 sample.2 first = evalOpt sample.1 sample.2 second
          then 1 else 0) else 0) =
      (if sample.1 = line then
        (if evalOpt sample.1 sample.2 first = evalOpt sample.1 sample.2 second
          then 1 else 0) else 0) := by
    by_cases heq : sample.1 = line <;> simp [heq, hdir]
  have hright (sample : LineDesc L × (Fin L.m → ScalarQ L)) :
      (if sample.1.direction ≠ 0 then (if sample.1 = line then (1 : ℝ) else 0) else 0) =
        (if sample.1 = line then 1 else 0) := by
    by_cases heq : sample.1 = line <;> simp [heq, hdir]
  simpa only [hleft, hright] using hbound

/-- Nondegenerate line fibers have total mass at least three quarters in the
unchanged line-point law. This follows from the zero-direction mass bound and
the fact that a field has at least two elements. This proof-only positivity bound
supports conditioning at paper `14_analysis_of_the_pauli_basis_test.tex:950-963`. -/
theorem linePointDist_nondegenerate_mass_ge (L : LdParams) :
    (3 / 4 : ℝ) ≤ ∑ sample ∈ (linePointDist L).support.filter
      (fun sample => sample.1.direction ≠ 0), (linePointDist L).weight sample := by
  classical
  have hsplit : (∑ sample ∈ (linePointDist L).support.filter
        (fun sample => sample.1.direction ≠ 0), (linePointDist L).weight sample) +
      avgOver (linePointDist L) (fun sample => if sample.1.direction = 0 then 1 else 0) = 1 := by
    simp only [avgOver, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    rw [add_comm, Finset.sum_filter_add_sum_filter_not]
    exact (linePointDist_isProbability L).weight_sum_eq_one
  have hmass := linePointDist_zero_direction_mass_le L
  have hcard : (2 : ℝ) ≤ Fintype.card (ScalarQ L) := by
    exact_mod_cast Fintype.one_lt_card (α := ScalarQ L)
  have hquarter : 1 / (2 * (Fintype.card (ScalarQ L) : ℝ)) ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  linarith

/-- For two independent line-point samples, excluding only zero X directions
costs at most `1 / (2q)`. Only X requires the collision estimate when the
X-outer sandwich is instantiated with `G2 = X`. This is a proof-only bound for
paper `14_analysis_of_the_pauli_basis_test.tex:943-963`. -/
theorem prod_linePointDist_zero_X_direction_mass_le (L : LdParams) :
    avgOver (Distribution.prod (linePointDist L) (linePointDist L))
      (fun samples => if samples.1.1.direction = 0 then 1 else 0) ≤
      1 / (2 * Fintype.card (ScalarQ L)) := by
  rw [avgOver_prod]
  change avgOver (linePointDist L) (fun sample => avgOver (linePointDist L)
    (fun _ => if sample.1.direction = 0 then 1 else 0)) ≤ _
  simp_rw [avgOver_const_of_isProbability _ (linePointDist_isProbability L)]
  exact linePointDist_zero_direction_mass_le L

/-- Conditioning a nonnegative average inflates its bound by at most the inverse
retained mass. This formalization-only estimate preserves both point and strategy
errors when applying `lem:pasting` after proof-only conditioning; source context:
paper `14_analysis_of_the_pauli_basis_test.tex:950-963`. -/
theorem avgOver_restrict_le_div_mass {Sample : Type*} [DecidableEq Sample]
    (dist : Distribution Sample) (good : Sample → Prop) [DecidablePred good]
    (hpos : 0 < ∑ sample ∈ dist.support.filter good, dist.weight sample)
    (value : Sample → ℝ) (hnonneg : ∀ sample, 0 ≤ value sample) :
    avgOver (Distribution.restrict dist good hpos) value ≤
      avgOver dist value / (∑ sample ∈ dist.support.filter good, dist.weight sample) := by
  apply (le_div_iff₀ hpos).mpr
  rw [mul_comm, avgOver_restrict_mul_mass]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun sample _ _ => mul_nonneg (dist.nonnegative sample) (hnonneg sample))

/-! ## Combined line measurements -/

/-- Removing the component outside a projective effect is a contraction.
This is the projection step preceding `eq:qqm`, paper
`14_analysis_of_the_pauli_basis_test.tex:902-915`. No commutation of the
two operators being compared is required. -/
theorem norm_sub_projective_mul_sq_le {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (M : Quantum.Measurement α ι)
    (hM : Measurement.IsProjective M) (a : α) (A D : Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (A - M.effect a * A) ψ‖ ^ 2 ≤
      ‖applyOperatorToState (A - M.effect a * D) ψ‖ ^ 2 := by
  have hidem := (hM a).isIdempotentElem.eq
  have hgram : (1 - M.effect a)ᴴ * (1 - M.effect a) ≤ 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      (hM a).isSelfAdjoint.isHermitian.eq]
    calc
      (1 - M.effect a) * (1 - M.effect a) = 1 - M.effect a := by
        simp only [sub_mul, mul_sub, one_mul, mul_one, hidem]
        abel
      _ ≤ 1 := sub_le_self _ (M.pos a)
  have heq : A - M.effect a * A =
      (1 - M.effect a) * (A - M.effect a * D) := by
    simp only [sub_mul, mul_sub, one_mul, ← mul_assoc, hidem]
    abel
  rw [heq, DistanceCalculus.applyOperatorToState_mul]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (MagicSquareRigidity.norm_applyOperatorToState_le hgram _) 2

/-- Summing a projective refinement close to `B_b D` recovers `D` with
four times the squared-distance error. This is the calculation from
`eq:qqm` to `eq:qld-qxz-close-to-point`, paper lines 912--932. Completeness
is required of `B`, not of the fixed marginal fiber `Q`. -/
theorem norm_marginal_sub_sq_le {β ι : Type*} [Fintype β]
    [Fintype ι] [DecidableEq ι] (Q : β → Op ι)
    (hQ : ∀ b, IsProj (Q b))
    (horth : ∀ {b c}, b ≠ c → Q b * Q c = 0)
    (B : Quantum.Measurement β ι) (hB : Measurement.IsProjective B)
    (hcomm : ∀ b, Q b * B.effect b = B.effect b * Q b)
    (D : Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState ((∑ b, Q b) - D) ψ‖ ^ 2 ≤
      4 * ∑ b, ‖applyOperatorToState (Q b - B.effect b * D) ψ‖ ^ 2 := by
  classical
  let U : Op ι := ∑ b, Q b * (Q b - B.effect b * Q b)
  let V : Op ι := ∑ b, B.effect b * (Q b - B.effect b * D)
  have hU : ‖applyOperatorToState U ψ‖ ^ 2 ≤
      ∑ b, ‖applyOperatorToState (Q b - B.effect b * D) ψ‖ ^ 2 := by
    refine le_trans (DistanceCalculus.norm_finset_sum_projector_mul_sq_le
      Q (fun b => Q b - B.effect b * Q b) hQ horth Finset.univ ψ) ?_
    exact Finset.sum_le_sum fun b _ => norm_sub_projective_mul_sq_le B hB b (Q b) D ψ
  have hV : ‖applyOperatorToState V ψ‖ ^ 2 ≤
      ∑ b, ‖applyOperatorToState (Q b - B.effect b * D) ψ‖ ^ 2 :=
    DistanceCalculus.norm_finset_sum_projector_mul_sq_le B.effect
      (fun b => Q b - B.effect b * D) hB
      (fun hbc => DistanceCalculus.projective_effect_mul_effect_eq_zero B hB hbc)
      Finset.univ ψ
  have hsum : (∑ b, Q b) - D = U + V := by
    have hfirst : U = ∑ b, (Q b - B.effect b * Q b) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [mul_sub, ← mul_assoc, hcomm b, mul_assoc,
        (hQ b).isIdempotentElem.eq]
    have hsecond : V = (∑ b, B.effect b * Q b) - D := by
      dsimp [V]
      simp only [mul_sub, ← mul_assoc, (hB _).isIdempotentElem.eq,
        Finset.sum_sub_distrib, ← Finset.sum_mul, B.sum_eq_one, one_mul]
    rw [hfirst, hsecond, Finset.sum_sub_distrib]
    abel
  rw [hsum]
  have htriangle : ‖applyOperatorToState (U + V) ψ‖ ≤
      ‖applyOperatorToState U ψ‖ + ‖applyOperatorToState V ψ‖ := by
    simpa only [applyOperatorToState, map_add, LinearMap.add_apply] using
      norm_add_le (applyOperatorToState U ψ) (applyOperatorToState V ψ)
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  nlinarith [sq_nonneg (‖applyOperatorToState U ψ‖ - ‖applyOperatorToState V ψ‖)]

/-- The joint point witness absorbs the opposite X point projector with
error at most its actual parameter. This is the X counterpart of the first
projection step of `lem:qld-xz-lines`, paper lines 902--915, obtained from
`consistent_XZ` rather than from an assumed marginal identity. -/
theorem CombinedPointsWitness.absorb_X_le {P : AdmissibleParams} {ε δQ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz ab => S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab))
      (fun xz ab => S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect ab.1) *
        S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab)) S.psiHat ≤ δQ := by
  refine le_trans ?_ (points.consistent_XZ p1 p2 hopp)
  unfold opFamilyDistSq
  apply avgOver_mono
  intro xz
  apply Finset.sum_le_sum
  intro ab _
  simpa only [ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul]
    using norm_sub_projective_mul_sq_le
      (S.placedMeasurement p2 (S.pointMeasExp p2.side .X xz.1))
      (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
      ab.1 (S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab))
      (S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect ab.2)) S.psiHat

/-- The joint point witness absorbs the opposite Z point projector with
error at most its actual parameter. This is the first projection step in
`lem:qld-xz-lines`, paper lines 902--915, derived from `consistent_ZX`. -/
theorem CombinedPointsWitness.absorb_Z_le {P : AdmissibleParams} {ε δQ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz ab => S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab))
      (fun xz ab => S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect ab.2) *
        S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab)) S.psiHat ≤ δQ := by
  refine le_trans ?_ (points.consistent_ZX p1 p2 hopp)
  unfold opFamilyDistSq
  apply avgOver_mono
  intro xz
  apply Finset.sum_le_sum
  intro ab _
  simpa only [ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul]
    using norm_sub_projective_mul_sq_le
      (S.placedMeasurement p2 (S.pointMeasExp p2.side .Z xz.2))
      (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
      ab.2 (S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab))
      (S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect ab.1)) S.psiHat

set_option maxHeartbeats 800000 in
/-- The X marginal of any joint point witness is within squared distance
`4 * δQ` of the opposite X point measurement. This is
`eq:qld-qxz-close-to-point`, paper lines 917--932, with the supplied witness
error retained; the source later specializes to its constructed points. -/
theorem CombinedPointsWitness.marginal_X_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz a => ∑ b, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
      (fun xz a => S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect a))
      S.psiHat ≤ 4 * δQ := by
  classical
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (points.consistent_ZX p1 p2 hopp)
    (by norm_num : (0 : ℝ) ≤ 4))
  unfold opFamilyDistSq
  rw [← avgOver_const_mul]
  apply avgOver_mono
  intro xz
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  simpa only [ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul] using
    norm_marginal_sub_sq_le
    (fun b => S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
    (fun b => S.placedMeasurement_isProjective p1 _ (points.projective _ _ _) (a, b))
    (fun hbc => DistanceCalculus.projective_effect_mul_effect_eq_zero
      (S.placedMeasurement p1 (points.Q p1.side xz.1 xz.2))
      (S.placedMeasurement_isProjective p1 _ (points.projective _ _ _))
      (fun hpair => hbc (congrArg Prod.snd hpair)))
    (S.placedMeasurement p2 (S.pointMeasExp p2.side .Z xz.2))
    (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
    (fun b => S.place_comm p1 p2 hopp _ _)
    (S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect a)) S.psiHat

set_option maxHeartbeats 800000 in
/-- The Z marginal of any joint point witness is within squared distance
`4 * δQ` of the opposite Z point measurement. This is the symmetric
calculation `eq:qld-qxz-close-to-point-2`, paper lines 933--935. -/
theorem CombinedPointsWitness.marginal_Z_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz b => ∑ a, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
      (fun xz b => S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect b))
      S.psiHat ≤ 4 * δQ := by
  classical
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (points.consistent_XZ p1 p2 hopp)
    (by norm_num : (0 : ℝ) ≤ 4))
  unfold opFamilyDistSq
  rw [← avgOver_const_mul]
  apply avgOver_mono
  intro xz
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  simpa only [ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul] using
    norm_marginal_sub_sq_le
    (fun a => S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
    (fun a => S.placedMeasurement_isProjective p1 _ (points.projective _ _ _) (a, b))
    (fun hac => DistanceCalculus.projective_effect_mul_effect_eq_zero
      (S.placedMeasurement p1 (points.Q p1.side xz.1 xz.2))
      (S.placedMeasurement_isProjective p1 _ (points.projective _ _ _))
      (fun hpair => hac (congrArg Prod.fst hpair)))
    (S.placedMeasurement p2 (S.pointMeasExp p2.side .X xz.1))
    (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
    (fun a => S.place_comm p1 p2 hopp _ _)
    (S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect b)) S.psiHat

/-- Joint self-consistency in the consistency-defect convention required by
`lem:pasting`, retaining the point witness error. This establishes the
uniform-point estimate; transporting it to line-point samples is separate.
Source: `eq:qld-q-self-cons` and paper lines 955--960. -/
theorem CombinedPointsWitness.self_consistency_defect_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    consistencyDefect
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz ab => S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab))
      (fun xz ab => S.place p2 ((points.Q p2.side xz.1 xz.2).effect ab))
      S.psiHat ≤ δQ := by
  exact le_trans (consistencyDefect_le_opFamilyDistSq_of_projective _
    (fun xz : (Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P) =>
      S.placedMeasurement p1 (points.Q p1.side xz.1 xz.2))
    (fun xz : (Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P) =>
      S.placedMeasurement p2 (points.Q p2.side xz.1 xz.2)) S.psiHat
    (fun xz => S.placedMeasurement_isProjective p1 _ (points.projective _ xz.1 xz.2))
    (fun xz => S.placedMeasurement_isProjective p2 _ (points.projective _ xz.1 xz.2)))
    (points.self_consistent p1 p2 hopp)

/-- The point marginal of the line-point law is uniform. This is the
formalization-only averaging step in `eq:pasting-q1`, paper
`14_analysis_of_the_pauli_basis_test.tex:936-941`, using `lem:alnf` and `lem:dlnf`. -/
theorem avgOver_linePointDist_point (L : LdParams)
    (value : (Fin L.m → ScalarQ L) → ℝ) :
    avgOver (linePointDist L) (fun sample => value sample.2) =
      avgOver (uniformDistribution (Fin L.m → ScalarQ L)) value := by
  rw [linePointDist, avgOver_mix]
  rw [← Distribution.avgOver_map (aLinePointDist L) Prod.snd value,
    ← Distribution.avgOver_map (dLinePointDist L) Prod.snd value,
    (aLinePointDist_point_marginal_uniform L).1,
    (dLinePointDist_point_marginal_uniform L).1]
  ring

/-- Independent line-point samples have independent uniform point marginals.
This formalization-only identity transports the point estimates in
`eq:pasting-q1`, paper `14_analysis_of_the_pauli_basis_test.tex:936-941`. -/
theorem avgOver_prod_linePointDist_points (L : LdParams)
    (value : (Fin L.m → ScalarQ L) × (Fin L.m → ScalarQ L) → ℝ) :
    avgOver (Distribution.prod (linePointDist L) (linePointDist L))
      (fun sample => value (sample.1.2, sample.2.2)) =
      avgOver (uniformDistribution
        ((Fin L.m → ScalarQ L) × (Fin L.m → ScalarQ L))) value := by
  rw [uniformDistribution_prod, avgOver_prod, avgOver_prod]
  conv_lhs =>
    arg 2
    ext sample
    rw [avgOver_linePointDist_point L (fun point => value (sample.2, point))]
  exact avgOver_linePointDist_point L
    (fun point => avgOver (uniformDistribution _) (fun other => value (point, other)))

/-- The first postprocessed joint-point effect is its X marginal sum.
This is the definition preceding `eq:qld-qxz-close-to-point`, paper
`14_analysis_of_the_pauli_basis_test.tex:917-932`, not a witness assumption. -/
theorem CombinedPointsWitness.postprocess_fst_effect
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ) (side : PlayerSide)
    (x z : Fin P.m → PauliScalar P) (a : PauliScalar P) :
    ((points.Q side x z).postprocess Prod.fst).effect a =
      ∑ b, (points.Q side x z).effect (a, b) := by
  classical
  change (∑ pair ∈ Finset.univ.filter (fun pair => pair.1 = a),
    (points.Q side x z).effect pair) = _
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

/-- The second postprocessed joint-point effect is its Z marginal sum.
Source: `eq:qld-qxz-close-to-point-2`, paper
`14_analysis_of_the_pauli_basis_test.tex:933-935`. -/
theorem CombinedPointsWitness.postprocess_snd_effect
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ) (side : PlayerSide)
    (x z : Fin P.m → PauliScalar P) (b : PauliScalar P) :
    ((points.Q side x z).postprocess Prod.snd).effect b =
      ∑ a, (points.Q side x z).effect (a, b) := by
  classical
  change (∑ pair ∈ Finset.univ.filter (fun pair => pair.2 = b),
    (points.Q side x z).effect pair) = _
  simp [Finset.sum_filter, Fintype.sum_prod_type]

/-- X marginal distance on the product line-point law, retaining the supplied
point error. This is the first transport step of `eq:pasting-q1`, paper
`14_analysis_of_the_pauli_basis_test.tex:936-941`; no line comparison is assumed. -/
theorem CombinedPointsWitness.marginal_X_linePoint_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample a => S.place p1
        (((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.fst).effect a))
      (fun sample a => S.place p2 ((S.pointMeasExp p2.side .X sample.1.2).effect a))
      S.psiHat ≤ 4 * δQ := by
  classical
  simp_rw [points.postprocess_fst_effect, S.place_finset_sum]
  unfold opFamilyDistSq
  rw [avgOver_prod_linePointDist_points P.toLdParams (fun xz =>
    ∑ a, ‖applyOperatorToState
      ((∑ b, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b))) -
        S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect a)) S.psiHat‖ ^ 2)]
  exact points.marginal_X_distance_le p1 p2 hopp

/-- Z marginal distance on the product line-point law, with the same error as
the uniform-point estimate. Source: `eq:pasting-q1`, paper
`14_analysis_of_the_pauli_basis_test.tex:936-941`. -/
theorem CombinedPointsWitness.marginal_Z_linePoint_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample b => S.place p1
        (((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.snd).effect b))
      (fun sample b => S.place p2 ((S.pointMeasExp p2.side .Z sample.2.2).effect b))
      S.psiHat ≤ 4 * δQ := by
  classical
  simp_rw [points.postprocess_snd_effect, S.place_finset_sum]
  unfold opFamilyDistSq
  rw [avgOver_prod_linePointDist_points P.toLdParams (fun xz =>
    ∑ b, ‖applyOperatorToState
      ((∑ a, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b))) -
        S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect b)) S.psiHat‖ ^ 2)]
  exact points.marginal_Z_distance_le p1 p2 hopp

/-- Joint self-consistency on independent line-point samples. This supplies
the sampling step for `eq:pasting-2` in the application at paper
`14_analysis_of_the_pauli_basis_test.tex:955-963`. -/
theorem CombinedPointsWitness.self_consistency_linePoint_defect_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    consistencyDefect (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample ab => S.place p1 ((points.Q p1.side sample.1.2 sample.2.2).effect ab))
      (fun sample ab => S.place p2 ((points.Q p2.side sample.1.2 sample.2.2).effect ab))
      S.psiHat ≤ δQ := by
  classical
  unfold consistencyDefect
  rw [avgOver_prod_linePointDist_points P.toLdParams (fun xz =>
    ∑ ab, ∑ cd, if ab = cd then 0 else
      (inner ℂ S.psiHat ((EuclideanSpace.equiv _ ℂ).symm
        ((S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab) *
          S.place p2 ((points.Q p2.side xz.1 xz.2).effect cd)) *ᵥ S.psiHat.ofLp))).re)]
  exact points.self_consistency_defect_le p1 p2 hopp

/-- Completing both answer alphabets with a zero outcome preserves placed
squared distance. This formalization-only identity reconciles `eq:pasting-q1`
with the completed evaluation convention of `lem:qld-comm-line-cons`. -/
theorem ProjectiveSetting.opFamilyDistSq_postprocess_some
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    {Sample Answer : Type*} [Fintype Answer] [DecidableEq Answer]
    (law : Distribution Sample) (p1 p2 : Placement)
    (first : Sample → MIPStarRE.Quantum.Measurement Answer (S.ExpandedLocalSpace p1.side))
    (second : Sample → MIPStarRE.Quantum.Measurement Answer (S.ExpandedLocalSpace p2.side)) :
    opFamilyDistSq law
      (fun sample answer => S.place p1 (((first sample).postprocess some).effect answer))
      (fun sample answer => S.place p2 (((second sample).postprocess some).effect answer))
      S.psiHat =
    opFamilyDistSq law (fun sample answer => S.place p1 ((first sample).effect answer))
      (fun sample answer => S.place p2 ((second sample).effect answer)) S.psiHat := by
  classical
  unfold opFamilyDistSq
  congr 1
  funext sample
  rw [Fintype.sum_option]
  simp [MIPStarRE.Quantum.Measurement.postprocess,
    MIPStarRE.Quantum.Submeasurement.postprocess, Finset.sum_filter,
    S.place_zero, applyOperatorToState]

/-- The completed X marginal has the same `4 * δQ` bound on line-point
samples. Source: the first comparison of `eq:pasting-q1`, paper
`14_analysis_of_the_pauli_basis_test.tex:936-941`, before inserting the line. -/
theorem CombinedPointsWitness.marginal_X_option_linePoint_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p1
        ((((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.fst).postprocess
          some).effect answer))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side .X sample.1.2).effect answer))
      S.psiHat ≤ 4 * δQ := by
  unfold ProjectiveSetting.pointMeasExpOption
  erw [S.opFamilyDistSq_postprocess_some]
  exact points.marginal_X_linePoint_distance_le p1 p2 hopp

/-- The completed Z marginal has the same `4 * δQ` bound on line-point
samples. Source: the second comparison of `eq:pasting-q1`, paper
`14_analysis_of_the_pauli_basis_test.tex:936-941`, before inserting the line. -/
theorem CombinedPointsWitness.marginal_Z_option_linePoint_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p1
        ((((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.snd).postprocess
          some).effect answer))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side .Z sample.2.2).effect answer))
      S.psiHat ≤ 4 * δQ := by
  unfold ProjectiveSetting.pointMeasExpOption
  erw [S.opFamilyDistSq_postprocess_some]
  exact points.marginal_Z_linePoint_distance_le p1 p2 hopp

/-- On either placement the evaluated line is close to the completed point
measurement. This formalization-only version of the intermediate comparison
in `eq:pasting-q1` retains the strategy error. It follows from
`lem:qld-comm-line-cons` item 3 and `lem:qld-comm-cons` item 1, rather than
identifying measurements on different placements. -/
theorem exists_expLine_point_same_placement_distance_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (p1 p2 : Placement), p1.IsOpposite p2 → ∀ W : PauliKind,
        opFamilyDistSq (linePointDist P.toLdParams)
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side W sample.1 sample.2).effect answer))
          (fun sample answer => S.place p2
            ((S.pointMeasExpOption p2.side W sample.2).effect answer))
          S.psiHat ≤ C * (ε + deltaLine ε) := by
  obtain ⟨Cp, hCp, hp⟩ := expPoint_self_cons
  obtain ⟨Cl, hCl, hl⟩ := expLine_point_cons'
  refine ⟨2 * (Cp + Cl), by linarith, ?_⟩
  intro P ε S p1 p2 hopp W
  classical
  have hreverse : p2.IsOpposite p1 := by
    cases p1 <;> cases p2 <;> simp_all [Placement.IsOpposite]
  have hpoint : opFamilyDistSq (linePointDist P.toLdParams)
      (fun sample answer => S.place p1
        ((S.pointMeasExpOption p1.side W sample.2).effect answer))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side W sample.2).effect answer)) S.psiHat ≤ Cp * ε := by
    unfold ProjectiveSetting.pointMeasExpOption
    erw [S.opFamilyDistSq_postprocess_some]
    unfold opFamilyDistSq
    rw [avgOver_linePointDist_point P.toLdParams (fun point =>
      ∑ answer, ‖applyOperatorToState
        (S.place p1 ((S.pointMeasExp p1.side W point).effect answer) -
          S.place p2 ((S.pointMeasExp p2.side W point).effect answer)) S.psiHat‖ ^ 2)]
    exact hp P ε S p1 p2 hopp W
  have htri := opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _
    (hl P ε S p2 p1 hreverse W) hpoint
  refine htri.trans ?_
  have hε := S.eps_nonneg
  have hline : 0 ≤ deltaLine ε := Real.sqrt_nonneg ε
  nlinarith

/-- Both genuine line--point marginal comparisons needed for pasting, in
squared distance, follow from the supplied point witness and the expanded
line comparisons. The `8 * δQ` term is not absorbed into the strategy error.
Source: `eq:pasting-q1`, paper `14_analysis_of_the_pauli_basis_test.tex:936-941`. -/
theorem exists_combinedPoints_line_marginal_distance_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε δQ : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ)
        (p1 p2 : Placement), p1.IsOpposite p2 →
        opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
          (linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            ((((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.fst).postprocess
              some).effect answer))
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side .X sample.1.1 sample.1.2).effect answer))
          S.psiHat ≤ 8 * δQ + C * (ε + deltaLine ε) ∧
        opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
          (linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            ((((points.Q p1.side sample.1.2 sample.2.2).postprocess Prod.snd).postprocess
              some).effect answer))
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side .Z sample.2.1 sample.2.2).effect answer))
          S.psiHat ≤ 8 * δQ + C * (ε + deltaLine ε) := by
  obtain ⟨C, hC, hbound⟩ := exists_expLine_point_same_placement_distance_le
  refine ⟨2 * C, by linarith, ?_⟩
  intro P ε δQ S points p1 p2 hopp
  classical
  have hX : opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side .X sample.1.2).effect answer))
      (fun sample answer => S.place p2
        ((S.lineEvalMeasExp p2.side .X sample.1.1 sample.1.2).effect answer))
      S.psiHat ≤ C * (ε + deltaLine ε) := by
    rw [DistanceCalculus.opFamilyDistSq_symm]
    unfold opFamilyDistSq
    rw [avgOver_prod]
    simp_rw [avgOver_const_of_isProbability _ (linePointDist_isProbability P.toLdParams)]
    exact hbound P ε S p1 p2 hopp .X
  have hZ : opFamilyDistSq (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p2
        ((S.pointMeasExpOption p2.side .Z sample.2.2).effect answer))
      (fun sample answer => S.place p2
        ((S.lineEvalMeasExp p2.side .Z sample.2.1 sample.2.2).effect answer))
      S.psiHat ≤ C * (ε + deltaLine ε) := by
    rw [DistanceCalculus.opFamilyDistSq_symm]
    unfold opFamilyDistSq
    rw [avgOver_prod]
    erw [avgOver_const_of_isProbability _ (linePointDist_isProbability P.toLdParams)
      (opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample answer => S.place p2
          ((S.lineEvalMeasExp p2.side .Z sample.1 sample.2).effect answer))
        (fun sample answer => S.place p2
          ((S.pointMeasExpOption p2.side .Z sample.2).effect answer)) S.psiHat)]
    exact hbound P ε S p1 p2 hopp .Z
  constructor
  · convert opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _
      (points.marginal_X_option_linePoint_distance_le p1 p2 hopp) hX using 1
    ring
  · convert opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _
      (points.marginal_Z_option_linePoint_distance_le p1 p2 hopp) hZ using 1
    ring

/-- Completing a joint answer and then taking its X marginal agrees with
completing the X marginal. This is a formalization-only postprocessing
identity for `eq:pasting-q1`; it is not an extra marginal hypothesis. -/
theorem CombinedPointsWitness.completed_fst_effect
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ) (side : PlayerSide)
    (x z : Fin P.m → PauliScalar P) (answer : Option (PauliScalar P)) :
    (((points.Q side x z).postprocess (fun pair => (some pair.1, some pair.2))).postprocess
      Prod.fst).effect answer =
      (((points.Q side x z).postprocess Prod.fst).postprocess some).effect answer := by
  classical
  exact congrArg (fun meas => meas.effect answer)
    ((MIPStarRE.Quantum.Measurement.postprocess_comp (points.Q side x z)
      (fun pair => (some pair.1, some pair.2)) Prod.fst).trans
      (MIPStarRE.Quantum.Measurement.postprocess_comp (points.Q side x z) Prod.fst some).symm)

/-- Completing a joint answer and then taking its Z marginal agrees with
completing the Z marginal. Source: `eq:pasting-q1`, with the existing
completed evaluation convention. -/
theorem CombinedPointsWitness.completed_snd_effect
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ) (side : PlayerSide)
    (x z : Fin P.m → PauliScalar P) (answer : Option (PauliScalar P)) :
    (((points.Q side x z).postprocess (fun pair => (some pair.1, some pair.2))).postprocess
      Prod.snd).effect answer =
      (((points.Q side x z).postprocess Prod.snd).postprocess some).effect answer := by
  classical
  exact congrArg (fun meas => meas.effect answer)
    ((MIPStarRE.Quantum.Measurement.postprocess_comp (points.Q side x z)
      (fun pair => (some pair.1, some pair.2)) Prod.snd).trans
      (MIPStarRE.Quantum.Measurement.postprocess_comp (points.Q side x z) Prod.snd some).symm)

/-- The two forward marginal hypotheses for pasting hold in the consistency
convention, with explicit dependence on both errors. Source: `eq:pasting-q1`,
paper `14_analysis_of_the_pauli_basis_test.tex:936-941`. Projectivity is
derived from the existing measurements and their postprocessings. -/
theorem exists_combinedPoints_line_marginal_defect_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε δQ : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ)
        (p1 p2 : Placement), p1.IsOpposite p2 →
        consistencyDefect (Distribution.prod (linePointDist P.toLdParams)
          (linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            ((((points.Q p1.side sample.1.2 sample.2.2).postprocess
              (fun pair => (some pair.1, some pair.2))).postprocess Prod.fst).effect answer))
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side .X sample.1.1 sample.1.2).effect answer))
          S.psiHat ≤ 8 * δQ + C * (ε + deltaLine ε) ∧
        consistencyDefect (Distribution.prod (linePointDist P.toLdParams)
          (linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            ((((points.Q p1.side sample.1.2 sample.2.2).postprocess
              (fun pair => (some pair.1, some pair.2))).postprocess Prod.snd).effect answer))
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side .Z sample.2.1 sample.2.2).effect answer))
          S.psiHat ≤ 8 * δQ + C * (ε + deltaLine ε) := by
  obtain ⟨C, hC, hbound⟩ := exists_combinedPoints_line_marginal_distance_le
  refine ⟨C, hC, ?_⟩
  intro P ε δQ S points p1 p2 hopp
  classical
  simp_rw [points.completed_fst_effect, points.completed_snd_effect]
  have hcompare (coordinate : PauliScalar P × PauliScalar P → PauliScalar P)
      (sampleLine : (LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
        (LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) →
        LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) (W : PauliKind) :=
    consistencyDefect_le_opFamilyDistSq_of_projective
      (Distribution.prod (linePointDist P.toLdParams) (linePointDist P.toLdParams))
      (fun sample => S.placedMeasurement p1
        (((points.Q p1.side sample.1.2 sample.2.2).postprocess coordinate).postprocess some))
      (fun sample => S.placedMeasurement p2
        (S.lineEvalMeasExp p2.side W (sampleLine sample).1 (sampleLine sample).2)) S.psiHat
      (fun sample => S.placedMeasurement_isProjective p1 _
        (WinImplications.postprocess_isProjective _
          (WinImplications.postprocess_isProjective _ (points.projective _ _ _) _) _))
      (fun sample => S.placedMeasurement_isProjective p2 _
        (WinImplications.postprocess_isProjective _ (S.lineMeasExp_isProjective _ _ _) _))
  exact ⟨(hcompare Prod.fst Prod.fst .X).trans (hbound P ε δQ S points p1 p2 hopp).1,
    (hcompare Prod.snd Prod.snd .Z).trans (hbound P ε δQ S points p1 p2 hopp).2⟩

/-- Completing both coordinates of a pair answer preserves placed squared
distance. This formalization-only identity supports the completed
self-consistency hypothesis in the application of `lem:pasting`. -/
theorem ProjectiveSetting.opFamilyDistSq_postprocess_some_pair
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    {Sample : Type*} (law : Distribution Sample) (p1 p2 : Placement)
    (first : Sample → MIPStarRE.Quantum.Measurement
      (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace p1.side))
    (second : Sample → MIPStarRE.Quantum.Measurement
      (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace p2.side)) :
    opFamilyDistSq law
      (fun sample answer => S.place p1
        (((first sample).postprocess (fun pair => (some pair.1, some pair.2))).effect answer))
      (fun sample answer => S.place p2
        (((second sample).postprocess (fun pair => (some pair.1, some pair.2))).effect answer))
      S.psiHat =
    opFamilyDistSq law (fun sample answer => S.place p1 ((first sample).effect answer))
      (fun sample answer => S.place p2 ((second sample).effect answer)) S.psiHat := by
  classical
  unfold opFamilyDistSq
  congr 1
  funext sample
  simp [Fintype.sum_prod_type, Fintype.sum_option,
    MIPStarRE.Quantum.Measurement.postprocess,
    MIPStarRE.Quantum.Submeasurement.postprocess, Finset.sum_filter,
    Prod.ext_iff, ite_and, S.place_zero, applyOperatorToState]

/-- Zero-completion of both answer coordinates also preserves consistency
defect exactly. This formalization-only identity handles the completed
answer convention in `eq:pasting-2` without a new consistency assumption. -/
theorem ProjectiveSetting.consistencyDefect_postprocess_some_pair
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    {Sample : Type*} [Fintype Sample] [DecidableEq Sample]
    (law : Distribution Sample) (p1 p2 : Placement)
    (first : Sample → MIPStarRE.Quantum.Measurement
      (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace p1.side))
    (second : Sample → MIPStarRE.Quantum.Measurement
      (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace p2.side)) :
    consistencyDefect law
      (fun sample answer => S.place p1
        (((first sample).postprocess (fun pair => (some pair.1, some pair.2))).effect answer))
      (fun sample answer => S.place p2
        (((second sample).postprocess (fun pair => (some pair.1, some pair.2))).effect answer))
      S.psiHat =
    consistencyDefect law (fun sample answer => S.place p1 ((first sample).effect answer))
      (fun sample answer => S.place p2 ((second sample).effect answer)) S.psiHat := by
  classical
  unfold consistencyDefect
  congr 1
  funext sample
  simp [Fintype.sum_prod_type, Fintype.sum_option,
    MIPStarRE.Quantum.Measurement.postprocess,
    MIPStarRE.Quantum.Submeasurement.postprocess, Finset.sum_filter,
    Prod.ext_iff, ite_and, S.place_zero]

/-- The completed joint measurement is self-consistent on product line-point
samples with defect at most `δQ`. This is the third actual hypothesis of
`lem:pasting`, as used at paper `14_analysis_of_the_pauli_basis_test.tex:955-963`. -/
theorem CombinedPointsWitness.self_consistency_completed_linePoint_defect_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    consistencyDefect (Distribution.prod (linePointDist P.toLdParams)
      (linePointDist P.toLdParams))
      (fun sample answer => S.place p1
        (((points.Q p1.side sample.1.2 sample.2.2).postprocess
          (fun pair => (some pair.1, some pair.2))).effect answer))
      (fun sample answer => S.place p2
        (((points.Q p2.side sample.1.2 sample.2.2).postprocess
          (fun pair => (some pair.1, some pair.2))).effect answer)) S.psiHat ≤ δQ := by
  erw [S.consistencyDefect_postprocess_some_pair]
  exact points.self_consistency_linePoint_defect_le p1 p2 hopp

/-- The paired-line POVM in the proof of `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:942-949`. The X effect is the outer
projector. This construction does not assert consistency with a point witness. -/
def ProjectiveSetting.combinedLineMeasurement {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide)
    (lineX lineZ : LineDesc P.toLdParams) :
    Quantum.Measurement (DegPoly P.toLdParams (P.m * P.d) ×
      DegPoly P.toLdParams (P.m * P.d)) (S.ExpandedLocalSpace side) :=
  Measurement.ofSumEqOne
    (fun fs => (S.lineMeasExp side .X lineX).effect fs.1 *
      (S.lineMeasExp side .Z lineZ).effect fs.2 *
      (S.lineMeasExp side .X lineX).effect fs.1)
    (fun fs => (pastedMeasurement_isMeasurement
      (S.lineMeasExp side .Z lineZ) (S.lineMeasExp side .X lineX)
      (S.lineMeasExp_isProjective side .X lineX)).1 (fs.2, fs.1))
    (by
      classical
      have hsum := (pastedMeasurement_isMeasurement
        (S.lineMeasExp side .Z lineZ) (S.lineMeasExp side .X lineX)
        (S.lineMeasExp_isProjective side .X lineX)).2
      simp only [pastedMeasurement, Fintype.sum_prod_type] at hsum ⊢
      rw [Finset.sum_comm]
      exact hsum)

/-- The effects of the paired-line POVM are the source's X-Z-X sandwiches. -/
@[simp] theorem ProjectiveSetting.combinedLineMeasurement_effect
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (side : PlayerSide)
    (lineX lineZ : LineDesc P.toLdParams)
    (fX fZ : DegPoly P.toLdParams (P.m * P.d)) :
    (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) =
      (S.lineMeasExp side .X lineX).effect fX *
        (S.lineMeasExp side .Z lineZ).effect fZ *
        (S.lineMeasExp side .X lineX).effect fX := rfl

/-- The constructed X-outer sandwich is the one-sided pasting output with
`G1 = Z`, `G2 = X`, and the polynomial answers exchanged. This identity fixes
the orientation in paper `14_analysis_of_the_pauli_basis_test.tex:943-961`;
it asserts no unproved consistency relation. -/
theorem ProjectiveSetting.combinedLineMeasurement_effect_eq_pastedMeasurement
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (side : PlayerSide)
    (lineX lineZ : LineDesc P.toLdParams)
    (fX fZ : DegPoly P.toLdParams (P.m * P.d)) :
    (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) =
      pastedMeasurement (S.lineMeasExp side .Z lineZ).effect
        (S.lineMeasExp side .X lineX).effect fZ fX := rfl

/-- The X-axis degree bound for the constructed POVM, from the support
argument at paper `14_analysis_of_the_pauli_basis_test.tex:949`. -/
theorem ProjectiveSetting.combinedLineMeasurement_axis_degree_X
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (side : PlayerSide)
    (lineX lineZ : LineDesc P.toLdParams)
    (fX fZ : DegPoly P.toLdParams (P.m * P.d))
    (haxis : lineX.kind = .axis) (hf : ¬ fX.FitsDegree P.d) :
    (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) = 0 := by
  simp only [S.combinedLineMeasurement_effect, S.lineMeasExp_effect,
    S.expLineOp_zero_of_not_deg_d side .X lineX haxis fX hf, zero_mul]

/-- The Z-axis degree bound for the constructed POVM, from the support
argument at paper `14_analysis_of_the_pauli_basis_test.tex:949`. -/
theorem ProjectiveSetting.combinedLineMeasurement_axis_degree_Z
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (side : PlayerSide)
    (lineX lineZ : LineDesc P.toLdParams)
    (fX fZ : DegPoly P.toLdParams (P.m * P.d))
    (haxis : lineZ.kind = .axis) (hf : ¬ fZ.FitsDegree P.d) :
    (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) = 0 := by
  simp only [S.combinedLineMeasurement_effect, S.lineMeasExp_effect,
    S.expLineOp_zero_of_not_deg_d side .Z lineZ haxis fZ hf, mul_zero, zero_mul]

/-- Summing out Z recovers the X line effect exactly for the constructed
sandwich. This identity is not assumed of an arbitrary `CombinedLinesWitness`. -/
theorem ProjectiveSetting.combinedLineMeasurement_sum_Z
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (side : PlayerSide)
    (lineX lineZ : LineDesc P.toLdParams)
    (fX : DegPoly P.toLdParams (P.m * P.d)) :
    ∑ fZ, (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) =
      (S.lineMeasExp side .X lineX).effect fX := by
  simp only [S.combinedLineMeasurement_effect, ← Finset.sum_mul, ← Finset.mul_sum,
    (S.lineMeasExp side .Z lineZ).sum_eq_one, mul_one]
  exact (S.lineMeasExp_isProjective side .X lineX fX).1

/-- Conditional joint X/Z line measurements for `lem:qld-xz-lines`.

**Source statement:** `lem:qld-xz-lines` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:345-443`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-894`.
The error depends polynomially on `ε` and `md/q`, and the witness retains all
directed opposite-placement comparisons.  This is the formalization-only form
with an already constructed point witness; the source-facing theorem below
supplies that witness existentially.  The proof is tracked by issue #18.
Discharge: formalize the sandwich measurement and the pasting argument in the
cited proof.

**Quantitative gap (issue #118):** This unproved internal interface still
omits dependence on the unrestricted supplied point error `δQ`. The proved
`marginal_X_distance_le` and `marginal_Z_distance_le` retain the bound `4 * δQ`;
`self_consistency_defect_le` retains `δQ`. The completed line-point marginal
defects are bounded by `8 * δQ + C * (ε + Real.sqrt ε)` above. The sandwich,
its degree bounds, nondegenerate single-line collision bounds, and discarded-mass
estimates are proved. The product-question and register reindexings, pasting,
and specialization to the constructed point error remain to be proved. See
`audits/2026-09-06-issue118-point-error-dependency.md`, attempt 4, and
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`. No corrected quantitative
interface is adopted by these partial results.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(ε, md/q)` is read in that sense. -/
theorem exists_combinedLinesWitness_ofPointsWitness :
    ∃ deltaP : ℝ -> ℝ -> ℝ, IsPolyErr₂ deltaP ∧
      ∀ (P : AdmissibleParams) (ε δQ : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ),
        Nonempty (CombinedLinesWitness S points
          (deltaP ε (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)))) := by
  sorry

/-! The source-facing declaration below supplies the point witness produced by
`lem:qld-4-10` existentially.  The `_ofPointsWitness` companion above is the
conditional form used by downstream calculations. -/

/-- The source-facing joint X/Z line measurement construction of
`lem:qld-xz-lines`, paper lines 882--894.

Unlike the formalization-only `_ofPointsWitness` companion, this declaration
does not assume a `CombinedPointsWitness` as an external bridge input.  It
quantifies the point error function and witness construction together with the
line construction, as the preceding source lemma supplies those points.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(ε, md/q)` is read in that sense. -/
theorem exists_combinedLinesWitness :
    ∃ deltaQ : ℝ -> ℝ, IsPolyErr deltaQ ∧
      ∃ deltaP : ℝ -> ℝ -> ℝ, IsPolyErr₂ deltaP ∧
        ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
          ∃ points : CombinedPointsWitness S (deltaQ ε),
            Nonempty (CombinedLinesWitness S points
              (deltaP ε (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)))) := by
  obtain ⟨deltaQ, hdeltaQ, hpoints⟩ := exists_combinedPointsWitness
  obtain ⟨deltaP, hdeltaP, hlines⟩ := exists_combinedLinesWitness_ofPointsWitness
  refine ⟨deltaQ, hdeltaQ, deltaP, hdeltaP, fun P ε S => ?_⟩
  obtain ⟨points⟩ := hpoints P ε S
  exact ⟨points, hlines P ε (deltaQ ε) S points⟩

/-! ## Restricted line distributions -/

/-- The axis and diagonal line-point laws are uniform mixtures of their
coordinate-index restrictions.

**Source statement:** `lem:restricted-line-mixture-bounds` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:595-646`, formalizing the
unlabelled observation at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`.
`Distribution.bind` is the finite uniform-mixture operation.  The two halves
are proved in `Combining.Lines.RestrictedMixture` from the equal-fiber
decomposition of `chiIndex` and the fact that every line conditioning map
retains the shared scalar seed. -/
theorem linePointDist_eq_mixture_restricted (L : LdParams) :
    aLinePointDist L =
        Distribution.bind (uniformDistribution (Fin L.m))
          (restrictedALineDist L) ∧
      dLinePointDist L =
        Distribution.bind (uniformDistribution (Fin L.m))
          (restrictedDLineDist L) :=
  ⟨aLinePointDist_eq_bind_restricted L, dLinePointDist_eq_bind_restricted L⟩

/-- Restricting a nonnegative average from the line-point distribution to one
fixed line kind and coordinate inflates its bound by at most `2m`.

**Source statement:** item 1 of `lem:restricted-line-mixture-bounds` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:595-646`, from the unlabelled
estimate at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1056`.
The restricted component carries mixture weight `1 / (2 m)`, so a nonnegative
average bounded by `δ` bounds it by `2 m δ`. -/
theorem avg_restricted_le {P : AdmissibleParams}
    (f : (LineDesc P.toLdParams × (Fin P.m -> PauliScalar P)) -> ℝ)
    (hf : ∀ sample, 0 ≤ f sample) {δ : ℝ}
    (havg : avgOver (linePointDist P.toLdParams) f ≤ δ)
    (kind : LineKind) (i : Fin P.m) :
    avgOver (restrictedLinePointDist P kind i) f ≤
      2 * (P.m : ℝ) * δ := by
  refine (avgOver_restrictedLinePointDist_le f hf kind i).trans ?_
  exact mul_le_mul_of_nonneg_left havg (by positivity)

/-- Restricting both variables of a nonnegative average over two independent
line-point samples inflates its bound by at most `4m^2`.

**Source statement:** item 2 of `lem:restricted-line-mixture-bounds` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:595-646`, from the unlabelled
estimate at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1056-1058`.
The one-variable estimate is applied successively to the two product
coordinates. -/
theorem avg_restricted_prod_le {P : AdmissibleParams}
    (f : ((LineDesc P.toLdParams × (Fin P.m -> PauliScalar P)) ×
      (LineDesc P.toLdParams × (Fin P.m -> PauliScalar P))) -> ℝ)
    (hf : ∀ sample, 0 ≤ f sample) {δ : ℝ}
    (havg : avgOver
      (Distribution.prod (linePointDist P.toLdParams)
        (linePointDist P.toLdParams)) f ≤ δ)
    (kindX kindZ : LineKind) (i j : Fin P.m) :
    avgOver
      (Distribution.prod (restrictedLinePointDist P kindX i)
        (restrictedLinePointDist P kindZ j)) f ≤
      4 * (P.m : ℝ) ^ 2 * δ := by
  refine (avgOver_prod_restrictedLinePointDist_le f hf kindX kindZ i j).trans ?_
  exact mul_le_mul_of_nonneg_left havg (by positivity)

/-- Formalization-only auxiliary for item 3 of
`lem:restricted-line-mixture-bounds`: a consistency defect of two complete
measurements placed on opposite registers inflates by at most `4 m ^ 2` when
both line-point coordinates are restricted.  Blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:595-646`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1058-1061`. -/
theorem consistencyDefect_restricted_prod_le {P : AdmissibleParams}
    {ε δ : ℝ} {α : Type*} [Fintype α] [DecidableEq α]
    (S : ProjectiveSetting P ε) (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂)
    (M₁ : ((LineDesc P.toLdParams × (Fin P.m -> PauliScalar P)) ×
        (LineDesc P.toLdParams × (Fin P.m -> PauliScalar P))) ->
      MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p₁.side))
    (M₂ : ((LineDesc P.toLdParams × (Fin P.m -> PauliScalar P)) ×
        (LineDesc P.toLdParams × (Fin P.m -> PauliScalar P))) ->
      MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p₂.side))
    (hbound : consistencyDefect
      (Distribution.prod (linePointDist P.toLdParams)
        (linePointDist P.toLdParams))
      (fun sample answer => S.place p₁ ((M₁ sample).effect answer))
      (fun sample answer => S.place p₂ ((M₂ sample).effect answer))
      S.psiHat ≤ δ)
    (kindX kindZ : LineKind) (i j : Fin P.m) :
    consistencyDefect
      (Distribution.prod (restrictedLinePointDist P kindX i)
        (restrictedLinePointDist P kindZ j))
      (fun sample answer => S.place p₁ ((M₁ sample).effect answer))
      (fun sample answer => S.place p₂ ((M₂ sample).effect answer))
      S.psiHat ≤ 4 * (P.m : ℝ) ^ 2 * δ := by
  unfold consistencyDefect at hbound ⊢
  refine le_trans
    (avgOver_prod_restrictedLinePointDist_le _ ?_ kindX kindZ i j) ?_
  · intro sample
    exact consistencyDefect_integrand_nonneg S p₁ p₂ hopp (M₁ sample)
      (M₂ sample)
  · exact mul_le_mul_of_nonneg_left hbound (by positivity)

/-- The evaluated joint line measurement remains consistent with the joint
point measurement on every product of restricted line distributions.

**Source statement:** item 3 and Equation `eq:qld-xz-lines-restricted` of
`lem:restricted-line-mixture-bounds` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:595-646`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1058-1061`.
Here `consistencyDefect` is the finite POVM form of the displayed expectation
against `Id - Q` after both measurements are postprocessed by evaluation.
The universal constant is outside all strategy and parameter quantifiers, and
is the exact inflation factor `4` of `avg_restricted_prod_le`. -/
theorem restricted_lines_consistency_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : AdmissibleParams} {ε δQ δP : ℝ}
        (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ)
        (lines : CombinedLinesWitness S points δP)
        (p1 p2 : Placement), p1.IsOpposite p2 ->
        ∀ (kindX kindZ : LineKind) (i j : Fin P.m),
          consistencyDefect
            (Distribution.prod (restrictedLinePointDist P kindX i)
              (restrictedLinePointDist P kindZ j))
            (fun sample answer => S.place p1
              (((lines.T p1.side sample.1.1 sample.2.1).postprocess fun fs =>
                (evalOpt sample.1.1 sample.1.2 fs.1,
                  evalOpt sample.2.1 sample.2.2 fs.2)).effect answer))
            (fun sample answer => S.place p2
              (((points.Q p2.side sample.1.2 sample.2.2).postprocess fun ab =>
                (some ab.1, some ab.2)).effect answer))
            S.psiHat ≤ C * (P.m : ℝ) ^ 2 * δP := by
  refine ⟨4, by norm_num, ?_⟩
  intro P ε δQ δP S points lines p1 p2 hopp kindX kindZ i j
  exact consistencyDefect_restricted_prod_le S p1 p2 hopp
    (fun sample => (lines.T p1.side sample.1.1 sample.2.1).postprocess fun fs =>
      (evalOpt sample.1.1 sample.1.2 fs.1, evalOpt sample.2.1 sample.2.2 fs.2))
    (fun sample => (points.Q p2.side sample.1.2 sample.2.2).postprocess fun ab =>
      (some ab.1, some ab.2))
    (lines.consistent p1 p2 hopp) kindX kindZ i j

/-! ## The sub-line distribution -/

/-- Existence of the directly indexed sub-line distribution with its two
separate projected point marginals and axis-line closure.  It supports
`lem:qld-sublines` and `rem:qld-sublines-property-three` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1069` with
its proof at lines 1071--1116.

This is a formalization auxiliary assertion, not the source-labelled
`lem:qld-sublines`.  The extended line uses the directly indexed carrier and
line-point law of `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` in
place of the seed-indexed line-point distribution over `F_q^(2m+2)` of the
source statement, so the statement carries no divisibility hypothesis and its
transport to the source carrier remains open.  Its `source_mixture` field
asserts only the separate X and Z marginal mixtures, not a stronger joint
conditional law.

The witness is the sub-line law `subLineDist` of the sampling procedure: a
line kind and an extended coordinate are drawn uniformly, an extended point
and an extended direction are drawn uniformly and independently, and two
scalar seeds are drawn independently in the coordinate-index fibers of the two
source indices of that coordinate; the triple is the canonical line of the
drawn kind through the extended point together with the two source lines of
the same kind decoded from the two coordinate blocks and from the two seeds.
Its pointwise fields are `subLineTripleOf_incidence`,
`subLineTripleOf_compatibility` and `subLineTripleOf_axis_closure`, applied to
the auxiliary randomness supplied by `exists_raw_of_mem_subLineDist_support`;
its extended-line marginal is `subLineDist_map_fst`; and its two projected
point marginals are the mixtures of `subLineDist_source_mixture`. -/
theorem exists_subLineWitness (P : AdmissibleParams) :
    Nonempty (SubLineWitness P) := by
  refine ⟨{ D := subLineDist P
            isProbability := subLineDist_isProbability P
            extended_marginal := subLineDist_map_fst P
            incidence := ?_
            compatibility := ?_
            source_mixture := subLineDist_source_mixture P
            axis_closure := ?_ }⟩
  · intro sample hsample u hu
    obtain ⟨kind, k, w, hx, hz, rfl⟩ :=
      exists_raw_of_mem_subLineDist_support P hsample
    exact subLineTripleOf_incidence P kind k w hx hz hu
  · intro sample hsample
    obtain ⟨kind, k, w, hx, hz, rfl⟩ :=
      exists_raw_of_mem_subLineDist_support P hsample
    exact subLineTripleOf_compatibility P kind k w hx hz
  · intro sample hsample haxis
    obtain ⟨kind, k, w, hx, hz, rfl⟩ :=
      exists_raw_of_mem_subLineDist_support P hsample
    exact subLineTripleOf_axis_closure P kind k w haxis

end

end MIPStarRE.QPBT
