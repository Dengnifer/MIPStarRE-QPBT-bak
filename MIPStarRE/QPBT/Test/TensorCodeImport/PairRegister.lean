import MIPStarRE.QPBT.Test.TensorCodeImport.PairGeometry

/-!
# A finite register for hidden subcube samples

Each visible ordered pair has a nonempty finite fiber of compatible diagonal
samples. A register stores one sample for each possible pair. Uniform sampling
of this register gives the uniform conditional law at each pair. Both provers
can therefore share the same register without being told the hidden subcube.

## References

- Ji et al., arXiv:2111.08131v3, Figures 1 and 2 and Definition 4.5.
- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:443-458`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, import obligations (#704).
-/

namespace MIPStarRE.QPBT.TensorCodeImport

open MIPStarRE.LDT

noncomputable section

/-- The visible ordered pair of field points in the tensor-code test. -/
abbrev PairQuestion (D : DirectLdParams) :=
  (Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)

/-- The fiber of source diagonal samples compatible with one visible pair.
The index is retained in this fiber, not in the visible question. -/
abbrev PairSample (D : DirectLdParams) (pair : PairQuestion D) :=
  {sample : DirectLdSpace D // diagonalPair D sample = pair}

/-- Every ordered pair has a compatible sample in the full subcube (index
zero). This also covers a repeated point, by using the zero direction. -/
def fullCubePairSample (D : DirectLdParams) (pair : PairQuestion D) : PairSample D pair :=
  ⟨⟨fun j => pair.1 j.rev, D.firstIndex,
      fun j => pair.2 j.rev - pair.1 j.rev⟩, by
    apply Prod.ext <;> funext j
    · simp [diagonalPair]
    · simp [diagonalPair, directPrefixProjection, DirectLdParams.firstIndex]⟩

instance (D : DirectLdParams) (pair : PairQuestion D) : Nonempty (PairSample D pair) :=
  ⟨fullCubePairSample D pair⟩

noncomputable instance (D : DirectLdParams) (pair : PairQuestion D) :
    Fintype (PairSample D pair) := Fintype.ofFinite _

noncomputable instance (D : DirectLdParams) (pair : PairQuestion D) :
    DecidableEq (PairSample D pair) := Classical.decEq _

/-- A common random register assigns a compatible sample to every possible
ordered pair. Sharing this entire finite register lets the players agree on
the conditional choice while their questions reveal only the pair. -/
abbrev PairRegister (D : DirectLdParams) := (pair : PairQuestion D) → PairSample D pair

instance (D : DirectLdParams) : Nonempty (PairRegister D) :=
  ⟨fullCubePairSample D⟩

noncomputable instance (D : DirectLdParams) : DecidableEq (PairRegister D) :=
  Classical.decEq _

/-- Reading the shared register at a fixed pair gives the uniform law on
that pair's fiber, including the correct posterior weights on hidden indices.
This is a sampling identity, not yet a statement about a game's value. -/
theorem pairRegister_marginal (D : DirectLdParams) (pair : PairQuestion D) :
    (uniformDistribution (PairRegister D)).map (fun register => register pair) =
      uniformDistribution (PairSample D pair) := by
  exact uniformDistribution_map_fst_of_equiv
    (Equiv.piSplitAt pair (PairSample D)) (fun register => register pair) (fun _ => rfl)

end

end MIPStarRE.QPBT.TensorCodeImport
