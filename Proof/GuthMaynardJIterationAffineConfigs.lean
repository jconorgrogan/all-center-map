import GuthMaynardJIterationSigmaIIAffineJ

open scoped BigOperators Real

noncomputable section
namespace GuthMaynardJIteration

/-- The finite family of all affine branches inside fixed integer universes.
It is the literal finite substitute for the source's bounded dyadic ranges. -/
def sourceAffineConfigFinset (mUniverse jUniverse : Finset ℤ) :
    Finset (Finset ℤ × Finset ℤ × Finset ℤ) :=
  mUniverse.powerset.product
    (mUniverse.powerset.product jUniverse.powerset)

def sourceAffineConfigs (mUniverse jUniverse : Finset ℤ) :
    Set (Finset ℤ × Finset ℤ × Finset ℤ) :=
  sourceAffineConfigFinset mUniverse jUniverse

theorem mem_sourceAffineConfigs_iff
    {mUniverse jUniverse : Finset ℤ}
    {cfg : Finset ℤ × Finset ℤ × Finset ℤ} :
    cfg ∈ sourceAffineConfigs mUniverse jUniverse ↔
      cfg.1 ⊆ mUniverse ∧ cfg.2.1 ⊆ mUniverse ∧ cfg.2.2 ⊆ jUniverse := by
  simp [sourceAffineConfigs, sourceAffineConfigFinset]

theorem self_mem_sourceAffineConfigs (mRange jRange : Finset ℤ) :
    (mRange, mRange, jRange) ∈ sourceAffineConfigs mRange jRange := by
  rw [mem_sourceAffineConfigs_iff]
  exact ⟨Finset.Subset.rfl, Finset.Subset.rfl, Finset.Subset.rfl⟩

/-- The selected-branch `J` supremum is automatically bounded above for the
finite powerset configuration family.  This removes the last artificial
order premise from the whole-line Cauchy/J identification. -/
theorem bddAbove_sourceAffineConfigEnergies
    (mUniverse jUniverse : Finset ℤ) (f : ℝ → ℝ) :
    BddAbove {x : ℝ | ∃ cfg ∈ sourceAffineConfigs mUniverse jUniverse,
      x = sourceFiniteAffineEnergy cfg.1 cfg.2.1 cfg.2.2 f} := by
  let energy : (Finset ℤ × Finset ℤ × Finset ℤ) → ℝ := fun cfg =>
    sourceFiniteAffineEnergy cfg.1 cfg.2.1 cfg.2.2 f
  have hconfigs : (sourceAffineConfigs mUniverse jUniverse).Finite := by
    exact (sourceAffineConfigFinset mUniverse jUniverse).finite_toSet
  have henergy : (energy '' sourceAffineConfigs mUniverse jUniverse).Finite :=
    hconfigs.image energy
  have htarget : {x : ℝ | ∃ cfg ∈
      sourceAffineConfigs mUniverse jUniverse,
      x = sourceFiniteAffineEnergy cfg.1 cfg.2.1 cfg.2.2 f}.Finite := by
    apply henergy.subset
    intro x hx
    rcases hx with ⟨cfg, hcfg, rfl⟩
    exact ⟨cfg, hcfg, rfl⟩
  exact htarget.bddAbove

/-- Every selected branch in fixed universes is bounded by the corresponding
finite source `J`; no separate `BddAbove` premise is needed. -/
theorem sourceFiniteAffineEnergy_le_canonicalJ
    (mUniverse jUniverse : Finset ℤ) (f : ℝ → ℝ)
    {m1Range m2Range jRange : Finset ℤ}
    (hm1 : m1Range ⊆ mUniverse) (hm2 : m2Range ⊆ mUniverse)
    (hj : jRange ⊆ jUniverse) :
    sourceFiniteAffineEnergy m1Range m2Range jRange f ≤
      sourceAffineJ (sourceAffineConfigs mUniverse jUniverse) f := by
  apply sourceFiniteAffineEnergy_le_sourceAffineJ
    (sourceAffineConfigs mUniverse jUniverse) f
    (bddAbove_sourceAffineConfigEnergies mUniverse jUniverse f)
  rw [mem_sourceAffineConfigs_iff]
  exact ⟨hm1, hm2, hj⟩

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.mem_sourceAffineConfigs_iff
#print axioms GuthMaynardJIteration.bddAbove_sourceAffineConfigEnergies
#print axioms GuthMaynardJIteration.sourceFiniteAffineEnergy_le_canonicalJ
