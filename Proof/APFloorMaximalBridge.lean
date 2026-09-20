import APConditionalShortIntervalConnector

/-!
# Floor-tight finite-modulus bridge

The published polylogarithmic family and equations (2.7), (2.8) use
`floor ((log X)^K)`.  The earlier maximal bridge unnecessarily asked for a
natural cap above the real cutoff, forcing a ceiling and one unmatched level.
This file proves the exact floor-tight version.
-/

namespace MAPAPFloorMaximalBridge

open MeasureTheory Set
open scoped ENNReal
open APFoundation APMaximalExplicitFormulaBridge

noncomputable section

theorem simultaneousAPMax_le_sum_floor_fixedModulusMajorants
    {K epsilon X x : ℝ} (B : ℕ → ℝ≥0∞)
    (hfixed : ∀ (q : ℕ) (hqpos : 1 ≤ q)
        (_hqcap : (q : ℝ) ≤ Real.rpow (Real.log X) K),
      letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
      fixedModulusAPMax q epsilon X x ≤ B q) :
    simultaneousAPMax K epsilon X x ≤
      ∑ q ∈ Finset.Icc 1 ⌊Real.rpow (Real.log X) K⌋₊, B q := by
  unfold simultaneousAPMax
  apply iSup_le
  intro q
  apply iSup_le
  intro hqpos
  apply iSup_le
  intro hqcap
  letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  change fixedModulusAPMax q epsilon X x ≤ _
  have hqfloor : q ≤ ⌊Real.rpow (Real.log X) K⌋₊ :=
    Nat.le_floor hqcap
  exact (hfixed q hqpos hqcap).trans <|
    Finset.single_le_sum (fun _ _ => bot_le)
      (Finset.mem_Icc.mpr ⟨hqpos, hqfloor⟩)

theorem lintegral_simultaneousAPMax_le_sum_floor_majorants
    {K epsilon X : ℝ} (B : ℕ → ℝ → ℝ≥0∞)
    (hmeas : ∀ q ∈ Finset.Icc 1 ⌊Real.rpow (Real.log X) K⌋₊,
      Measurable (B q))
    (hfixed : ∀ (x : ℝ) (q : ℕ) (hqpos : 1 ≤ q)
        (_hqcap : (q : ℝ) ≤ Real.rpow (Real.log X) K),
      letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
      fixedModulusAPMax q epsilon X x ≤ B q x) :
    (∫⁻ x in Set.Icc (X / 2) (4 * X), simultaneousAPMax K epsilon X x) ≤
      ∑ q ∈ Finset.Icc 1 ⌊Real.rpow (Real.log X) K⌋₊,
        ∫⁻ x in Set.Icc (X / 2) (4 * X), B q x := by
  calc
    (∫⁻ x in Set.Icc (X / 2) (4 * X), simultaneousAPMax K epsilon X x) ≤
        ∫⁻ x in Set.Icc (X / 2) (4 * X),
          ∑ q ∈ Finset.Icc 1 ⌊Real.rpow (Real.log X) K⌋₊, B q x := by
      apply lintegral_mono
      intro x
      exact simultaneousAPMax_le_sum_floor_fixedModulusMajorants
        (fun q => B q x) (hfixed x)
    _ = ∑ q ∈ Finset.Icc 1 ⌊Real.rpow (Real.log X) K⌋₊,
        ∫⁻ x in Set.Icc (X / 2) (4 * X), B q x := by
      exact lintegral_finsetSum _ (fun q hq => hmeas q hq)

end
end MAPAPFloorMaximalBridge

#print axioms MAPAPFloorMaximalBridge.simultaneousAPMax_le_sum_floor_fixedModulusMajorants
#print axioms MAPAPFloorMaximalBridge.lintegral_simultaneousAPMax_le_sum_floor_majorants
