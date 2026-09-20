import Mathlib.NumberTheory.LSeries.DirichletContinuation

open scoped BigOperators ComplexConjugate
noncomputable section
namespace FordHurwitzLFunctionTransfer

open HurwitzZeta Complex ZMod Finset Set

/-- A uniform finite Hurwitz remainder bound gives a crude bound for every
Dirichlet `L`-function in the strip, with no continuation assumption beyond
Mathlib's finite Hurwitz decomposition. -/
theorem norm_dirichlet_LFunction_le
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 2) (hsim : 0 < s.im)
    {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 →
      ‖hurwitzZeta (u : UnitAddCircle) s - (u : ℂ) ^ (-s)‖ ≤ B) :
    ‖DirichletCharacter.LFunction χ s‖ ≤
      (N : ℝ) * ((N : ℝ) ^ 2 + B) := by
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (NeZero.pos N)
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hsne : s ≠ 0 := by
    intro hs
    rw [hs] at hsim
    simp at hsim
  have hCnonneg : 0 ≤ (N : ℝ) ^ 2 + B := by positivity
  have hhurwitz : ∀ j : ZMod N,
      ‖hurwitzZeta (toAddCircle j) s‖ ≤ (N : ℝ) ^ 2 + B := by
    intro j
    by_cases hj : j = 0
    · subst j
      have hrem := hH 0 (by simp)
      have hzero : (0 : ℂ) ^ (-s) = 0 :=
        Complex.zero_cpow (neg_ne_zero.mpr hsne)
      have hN2 : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
      simpa [hzero, sub_zero] using hrem.trans (by linarith)
    · have hjval : 0 < j.val := ZMod.val_pos.mpr hj
      have hjone : (1 : ℝ) ≤ (j.val : ℝ) := by
        exact_mod_cast (show 1 ≤ j.val by omega)
      have hu_pos : 0 < (j.val : ℝ) / (N : ℝ) := by positivity
      have hu_mem : (j.val : ℝ) / (N : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact hu_pos.le
        · apply (div_le_one hNpos).2
          exact_mod_cast (j.val_lt.le)
      have hrem := hH ((j.val : ℝ) / (N : ℝ)) hu_mem
      have hbase_le : (1 : ℝ) / (N : ℝ) ≤
          (j.val : ℝ) / (N : ℝ) := by
        exact div_le_div_of_nonneg_right hjone hNpos.le
      have hpow_le :
          ((j.val : ℝ) / (N : ℝ)) ^ (-s.re) ≤
            ((1 : ℝ) / (N : ℝ)) ^ (-s.re) := by
        exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase_le
          (neg_nonpos.mpr hs0)
      have honepow :
          ((1 : ℝ) / (N : ℝ)) ^ (-s.re) = (N : ℝ) ^ s.re := by
        rw [Real.rpow_neg_eq_inv_rpow]
        congr 1
        field_simp
      have hNpow : (N : ℝ) ^ s.re ≤ (N : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hNone hs1
      have hcpow :
          ‖((j.val : ℝ) / (N : ℝ) : ℂ) ^ (-s)‖ ≤ (N : ℝ) ^ 2 := by
        rw [← Complex.ofReal_div]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hu_pos]
        calc
          ((j.val : ℝ) / (N : ℝ)) ^ (-s.re) ≤
              ((1 : ℝ) / (N : ℝ)) ^ (-s.re) := hpow_le
          _ = (N : ℝ) ^ s.re := honepow
          _ ≤ (N : ℝ) ^ 2 := by
            calc
              (N : ℝ) ^ s.re ≤ (N : ℝ) ^ (2 : ℝ) := hNpow
              _ = (N : ℝ) ^ 2 := by norm_num
      have hsum :
          hurwitzZeta (toAddCircle j) s =
            (hurwitzZeta (toAddCircle j) s -
              ((j.val : ℝ) / (N : ℝ) : ℂ) ^ (-s)) +
            ((j.val : ℝ) / (N : ℝ) : ℂ) ^ (-s) := by ring
      have hrem' :
          ‖hurwitzZeta (toAddCircle j) s -
              ((j.val : ℝ) / (N : ℝ) : ℂ) ^ (-s)‖ ≤ B := by
        rw [toAddCircle_apply]
        simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using hrem
      rw [hsum]
      calc
        ‖hurwitzZeta (toAddCircle j) s -
              ((j.val : ℝ) / (N : ℝ) : ℂ) ^ (-s) +
              ((j.val : ℝ) / (N : ℝ) : ℂ) ^ (-s)‖ ≤
            ‖hurwitzZeta (toAddCircle j) s -
              ((j.val : ℝ) / (N : ℝ) : ℂ) ^ (-s)‖ +
              ‖((j.val : ℝ) / (N : ℝ) : ℂ) ^ (-s)‖ := norm_add_le _ _
        _ ≤ B + (N : ℝ) ^ 2 := add_le_add hrem' hcpow
        _ = (N : ℝ) ^ 2 + B := by ring
  have hsum :
      ‖∑ j : ZMod N, χ j * hurwitzZeta (toAddCircle j) s‖ ≤
        (N : ℝ) * ((N : ℝ) ^ 2 + B) := by
    calc
      ‖∑ j : ZMod N, χ j * hurwitzZeta (toAddCircle j) s‖ ≤
          ∑ j : ZMod N, ‖χ j * hurwitzZeta (toAddCircle j) s‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j : ZMod N, ((N : ℝ) ^ 2 + B) := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          ‖χ j * hurwitzZeta (toAddCircle j) s‖ =
              ‖χ j‖ * ‖hurwitzZeta (toAddCircle j) s‖ := norm_mul _ _
          _ ≤ 1 * ((N : ℝ) ^ 2 + B) := by
            calc
              ‖χ j‖ * ‖hurwitzZeta (toAddCircle j) s‖ ≤
                  1 * ‖hurwitzZeta (toAddCircle j) s‖ :=
                mul_le_mul_of_nonneg_right (χ.norm_le_one j) (norm_nonneg _)
              _ ≤ 1 * ((N : ℝ) ^ 2 + B) :=
                mul_le_mul_of_nonneg_left (hhurwitz j) zero_le_one
          _ = (N : ℝ) ^ 2 + B := one_mul _
      _ = (N : ℝ) * ((N : ℝ) ^ 2 + B) := by simp; ring
  rw [DirichletCharacter.LFunction, ZMod.LFunction]
  have hNcpow : ‖(N : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    exact Real.rpow_le_one_of_one_le_of_nonpos hNone
      (neg_nonpos.mpr hs0)
  calc
    ‖(N : ℂ) ^ (-s) * ∑ j : ZMod N, χ j * hurwitzZeta (toAddCircle j) s‖ =
        ‖(N : ℂ) ^ (-s)‖ *
          ‖∑ j : ZMod N, χ j * hurwitzZeta (toAddCircle j) s‖ := norm_mul _ _
    _ ≤ 1 * ((N : ℝ) * ((N : ℝ) ^ 2 + B)) := by
      exact mul_le_mul hNcpow hsum (norm_nonneg _) (by positivity)
    _ = (N : ℝ) * ((N : ℝ) ^ 2 + B) := one_mul _

end FordHurwitzLFunctionTransfer

#print axioms FordHurwitzLFunctionTransfer.norm_dirichlet_LFunction_le
