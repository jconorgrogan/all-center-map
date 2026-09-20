import GuthMaynardJIterationCanonicalSigmaII

open scoped BigOperators Real

noncomputable section
namespace GuthMaynardJIteration

/-- A uniform bound for every finite affine branch passes to the canonical
finite `J` supremum.  Finiteness supplies boundedness separately; nonemptiness
is witnessed by the empty affine configuration. -/
theorem sourceAffineJ_le_of_forall_config
    (mUniverse jUniverse : Finset ℤ) (f : ℝ → ℝ) (B : ℝ)
    (hbranch : ∀ cfg ∈ sourceAffineConfigs mUniverse jUniverse,
      sourceFiniteAffineEnergy cfg.1 cfg.2.1 cfg.2.2 f ≤ B) :
    sourceAffineJ (sourceAffineConfigs mUniverse jUniverse) f ≤ B := by
  unfold sourceAffineJ
  apply csSup_le
  · refine ⟨sourceFiniteAffineEnergy ∅ ∅ ∅ f, ?_⟩
    refine ⟨(∅, ∅, ∅), ?_, rfl⟩
    rw [mem_sourceAffineConfigs_iff]
    exact ⟨Finset.empty_subset _, Finset.empty_subset _, Finset.empty_subset _⟩
  · intro x hx
    rcases hx with ⟨cfg, hcfg, rfl⟩
    exact hbranch cfg hcfg

/-- Exact finite-branch characterization of the canonical `J` upper bound.
The reverse direction uses the already certified selected-branch inequality. -/
theorem sourceAffineJ_le_iff_forall_config
    (mUniverse jUniverse : Finset ℤ) (f : ℝ → ℝ) (B : ℝ) :
    sourceAffineJ (sourceAffineConfigs mUniverse jUniverse) f ≤ B ↔
      ∀ cfg ∈ sourceAffineConfigs mUniverse jUniverse,
        sourceFiniteAffineEnergy cfg.1 cfg.2.1 cfg.2.2 f ≤ B := by
  constructor
  · intro hJ cfg hcfg
    exact (sourceFiniteAffineEnergy_le_sourceAffineJ
      (sourceAffineConfigs mUniverse jUniverse) f
      (bddAbove_sourceAffineConfigEnergies mUniverse jUniverse f)
      hcfg).trans hJ
  · exact sourceAffineJ_le_of_forall_config mUniverse jUniverse f B

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourceAffineJ_le_of_forall_config
#print axioms GuthMaynardJIteration.sourceAffineJ_le_iff_forall_config
