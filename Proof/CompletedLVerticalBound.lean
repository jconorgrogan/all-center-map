import StrongFEPairVerticalBound
import Mathlib.NumberTheory.LSeries.DirichletContinuation

open Complex Filter Topology Asymptotics Real Set MeasureTheory
open HurwitzZeta

namespace PLInteriorGrowth

noncomputable section

/-- The pole-removed completed even Hurwitz function is bounded on the fixed
strip needed for Dirichlet L-functions. -/
theorem exists_norm_completedHurwitzZetaEven₀_le_fixedStrip
    (a : UnitAddCircle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 →
      ‖completedHurwitzZetaEven₀ a s‖ ≤ C := by
  let P := (hurwitzEvenFEPair a).toStrongFEPair
  have hP : IsStrongFEPair P :=
    (hurwitzEvenFEPair a).isStrongFEPair_toStrongFEPair
  obtain ⟨C, hC, hbound⟩ :=
    PLInteriorGrowth.IsStrongFEPair.exists_norm_Λ_le_on_re_Icc
      hP (-(1 / 2 : ℝ)) 1 (by norm_num)
  refine ⟨C / 2, div_nonneg hC (by norm_num), ?_⟩
  intro s hlo hhi
  have hlo' : -(1 / 2 : ℝ) ≤ (s / 2).re := by
    rw [div_ofNat_re]
    linarith
  have hhi' : (s / 2).re ≤ 1 := by
    rw [div_ofNat_re]
    linarith
  have h := hbound (s / 2) hlo' hhi'
  have h' : ‖(hurwitzEvenFEPair a).Λ₀ (s / 2)‖ ≤ C := by
    convert h
    rw [hP.Λ_eq]
    rfl
  change ‖((hurwitzEvenFEPair a).Λ₀ (s / 2)) / 2‖ ≤ C / 2
  rw [norm_div, Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right h' (by norm_num)

/-- The completed odd Hurwitz function is bounded on the same fixed strip. -/
theorem exists_norm_completedHurwitzZetaOdd_le_fixedStrip
    (a : UnitAddCircle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 →
      ‖completedHurwitzZetaOdd a s‖ ≤ C := by
  let P := hurwitzOddFEPair a
  have hP : IsStrongFEPair P := isStrong_hurwitzOddFEPair a
  obtain ⟨C, hC, hbound⟩ :=
    PLInteriorGrowth.IsStrongFEPair.exists_norm_Λ_le_on_re_Icc
      hP 0 (3 / 2 : ℝ) (by norm_num)
  refine ⟨C / 2, div_nonneg hC (by norm_num), ?_⟩
  intro s hlo hhi
  have hlo' : 0 ≤ ((s + 1) / 2).re := by
    rw [div_ofNat_re, add_re, one_re]
    linarith
  have hhi' : ((s + 1) / 2).re ≤ 3 / 2 := by
    rw [div_ofNat_re, add_re, one_re]
    linarith
  have h := hbound ((s + 1) / 2) hlo' hhi'
  have h' : ‖(hurwitzOddFEPair a).Λ ((s + 1) / 2)‖ ≤ C := by
    simpa [P] using h
  change ‖(hurwitzOddFEPair a).Λ ((s + 1) / 2) / 2‖ ≤ C / 2
  rw [norm_div, Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right h' (by norm_num)

variable {N : ℕ} [NeZero N]

private lemma norm_level_cpow_neg_le_level (s : ℂ) (hs : -1 ≤ s.re) :
    ‖(N : ℂ) ^ (-s)‖ ≤ (N : ℝ) := by
  have hNnat : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hNnat
  change ‖((N : ℝ) : ℂ) ^ (-s)‖ ≤ (N : ℝ)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast (Nat.zero_lt_of_ne_zero (NeZero.ne N)))]
  have hexp : (-s).re ≤ (1 : ℝ) := by simp; linarith
  exact (Real.rpow_le_rpow_of_exponent_le hN hexp).trans_eq (Real.rpow_one _)

/-- For a fixed finite coefficient function, the pole-removed completed
ZMod L-function is bounded on `-1 ≤ Re(s) ≤ 2` by a constant times the level.
The constant may depend on the coefficient function, which is sufficient for
the crude-growth hypothesis in Phragmen--Lindelof. -/
theorem exists_norm_completedLFunction₀_le_level_fixedStrip
    (Φ : ZMod N → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 →
      ‖ZMod.completedLFunction₀ Φ s‖ ≤ C * (N : ℝ) := by
  classical
  choose Ce hCe hEven using fun j : ZMod N =>
    exists_norm_completedHurwitzZetaEven₀_le_fixedStrip (ZMod.toAddCircle j)
  choose Co hCo hOdd using fun j : ZMod N =>
    exists_norm_completedHurwitzZetaOdd_le_fixedStrip (ZMod.toAddCircle j)
  let C : ℝ :=
    (∑ j : ZMod N, ‖Φ j‖ * Ce j) + (∑ j : ZMod N, ‖Φ j‖ * Co j)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (hCe j))
      (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (hCo j))
  refine ⟨C, hC, ?_⟩
  intro s hlo hhi
  have hpow := norm_level_cpow_neg_le_level (N := N) s hlo
  have heven :
      ‖∑ j : ZMod N, Φ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖ ≤
        ∑ j : ZMod N, ‖Φ j‖ * Ce j := by
    calc
      ‖∑ j : ZMod N, Φ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖ ≤
          ∑ j : ZMod N, ‖Φ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j : ZMod N, ‖Φ j‖ * Ce j := by
        gcongr with j
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hEven j s hlo hhi) (norm_nonneg _)
  have hodd :
      ‖∑ j : ZMod N, Φ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ ≤
        ∑ j : ZMod N, ‖Φ j‖ * Co j := by
    calc
      ‖∑ j : ZMod N, Φ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ ≤
          ∑ j : ZMod N, ‖Φ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j : ZMod N, ‖Φ j‖ * Co j := by
        gcongr with j
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hOdd j s hlo hhi) (norm_nonneg _)
  rw [ZMod.completedLFunction₀]
  calc
    ‖(N : ℂ) ^ (-s) * ∑ j : ZMod N,
        Φ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s +
      (N : ℂ) ^ (-s) * ∑ j : ZMod N,
        Φ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ ≤
      ‖(N : ℂ) ^ (-s) * ∑ j : ZMod N,
        Φ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖ +
      ‖(N : ℂ) ^ (-s) * ∑ j : ZMod N,
        Φ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ := norm_add_le _ _
    _ ≤
      (N : ℝ) * (∑ j : ZMod N, ‖Φ j‖ * Ce j) +
        (N : ℝ) * (∑ j : ZMod N, ‖Φ j‖ * Co j) := by
      simp only [norm_mul]
      exact add_le_add
        (mul_le_mul hpow heven (norm_nonneg _) (by positivity))
        (mul_le_mul hpow hodd (norm_nonneg _) (by positivity))
    _ = C * (N : ℝ) := by dsimp [C]; ring

/-- The actual completed Dirichlet L-function agrees with its entire
pole-removed model for a nontrivial character, and hence inherits the fixed
strip bound. -/
theorem exists_norm_completedDirichletLFunction_le_level_fixedStrip
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 →
      ‖DirichletCharacter.completedLFunction χ s‖ ≤ C * (N : ℝ) := by
  have hN : N ≠ 1 := fun hN => hχ (DirichletCharacter.level_one' χ hN)
  have hzero : χ 0 = 0 := χ.map_zero' hN
  have hsum : ∑ j : ZMod N, χ j = 0 := χ.sum_eq_zero_of_ne_one hχ
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_completedLFunction₀_le_level_fixedStrip (N := N) (fun j => χ j)
  refine ⟨C, hC, ?_⟩
  intro s hlo hhi
  change ‖ZMod.completedLFunction (fun j : ZMod N => χ j) s‖ ≤ C * (N : ℝ)
  rw [ZMod.completedLFunction_eq, hzero, hsum, mul_zero, zero_div, sub_zero]
  simp only [zero_div, sub_zero]
  exact hbound s hlo hhi

end

end PLInteriorGrowth

#print axioms PLInteriorGrowth.exists_norm_completedLFunction₀_le_level_fixedStrip
#print axioms PLInteriorGrowth.exists_norm_completedDirichletLFunction_le_level_fixedStrip
