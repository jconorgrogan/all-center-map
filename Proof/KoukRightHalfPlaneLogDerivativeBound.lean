import KoukEndpointLeftVerticalBound
import VonMangoldtPSeriesBound

/-!
# A uniform logarithmic-derivative bound on `Re s ≥ 3/2`

The functional-equation reflection used on the canonical left edge lands in
this fixed absolute-convergence half-plane.  The bound below is a direct
consequence of the certified twisted von Mangoldt series and the elementary
von Mangoldt p-series estimate.
-/

namespace KoukRightHalfPlaneLogDerivativeBound

open scoped BigOperators ArithmeticFunction LSeries.notation
open PrimitiveExplicitFormulaSpine

noncomputable section

/-- Termwise domination of the twisted Mangoldt series on `Re s ≥ 3/2`. -/
theorem norm_twistedMangoldt_LSeries_term_le_threeHalves
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : ℂ)
    (hs : (3 / 2 : ℝ) ≤ s.re) (n : ℕ) :
    ‖LSeries.term (twistedMangoldtCoeff chi) s n‖ ≤
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ) := by
  by_cases hn0 : n = 0
  · subst n
    simp [twistedMangoldtCoeff]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hnOne : 1 ≤ (n : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  rw [LSeries.norm_term_eq, if_neg hn0]
  have hcoeff := norm_twistedMangoldtCoeff_le chi n
  have hpow : (n : ℝ) ^ (3 / 2 : ℝ) ≤ (n : ℝ) ^ s.re :=
    Real.rpow_le_rpow_of_exponent_le hnOne hs
  have hpowPos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hnpos _
  have hpowSPos : 0 < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos hnpos _
  exact div_le_div₀ ArithmeticFunction.vonMangoldt_nonneg hcoeff hpowPos hpow

/-- Character-uniform absolute bound for `L'/L` in the fixed half-plane
`Re s ≥ 3/2`.  The explicit constant `20` comes from the already certified
von Mangoldt p-series estimate at `delta = 1/2`. -/
theorem norm_logDeriv_LFunction_le_twenty
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : (3 / 2 : ℝ) ≤ s.re) :
    ‖logDeriv (DirichletCharacter.LFunction chi) s‖ ≤ 20 := by
  have hsOne : 1 < s.re := lt_of_lt_of_le (by norm_num) hs
  have hseries : Summable fun n : ℕ =>
      LSeries.term (twistedMangoldtCoeff chi) s n :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi hsOne
  let g : ℕ → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ)
  have hg : Summable g := by
    have hbase : Summable fun n : ℕ =>
        ‖LSeries.term (fun k : ℕ =>
          (ArithmeticFunction.vonMangoldt k : ℂ))
          ((3 / 2 : ℝ) : ℂ) n‖ := by
      apply summable_norm_iff.mpr
      exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
    have hpoint (n : ℕ) : g n =
        ‖LSeries.term (fun k : ℕ =>
          (ArithmeticFunction.vonMangoldt k : ℂ))
          ((3 / 2 : ℝ) : ℂ) n‖ := by
      by_cases hn : n = 0
      · subst n
        simp [g]
      · rw [LSeries.norm_term_eq, if_neg hn]
        simp only [g, Complex.ofReal_re, Complex.norm_real,
          Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hfun : g = fun n : ℕ =>
        ‖LSeries.term (fun k : ℕ =>
          (ArithmeticFunction.vonMangoldt k : ℂ))
          ((3 / 2 : ℝ) : ℂ) n‖ := by
      funext n
      exact hpoint n
    rw [hfun]
    exact hbase
  have hterm (n : ℕ) :
      ‖LSeries.term (twistedMangoldtCoeff chi) s n‖ ≤ g n :=
    norm_twistedMangoldt_LSeries_term_le_threeHalves chi s hs n
  have hnormSeries :
      ‖LSeries (twistedMangoldtCoeff chi) s‖ ≤ ∑' n, g n := by
    change ‖∑' n, LSeries.term (twistedMangoldtCoeff chi) s n‖ ≤ _
    calc
      ‖∑' n, LSeries.term (twistedMangoldtCoeff chi) s n‖ ≤
          ∑' n, ‖LSeries.term (twistedMangoldtCoeff chi) s n‖ :=
        norm_tsum_le_tsum_norm hseries.norm
      _ ≤ ∑' n, g n := hseries.norm.tsum_le_tsum hterm hg
  have hsum := VonMangoldtPSeriesBound.tsum_vonMangoldt_div_rpow_le
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hsumTwenty : (∑' n, g n) ≤ 20 := by
    calc
      (∑' n, g n) ≤
          (2 / (1 / 2 : ℝ)) * (1 + ((1 / 2 : ℝ) / 2)⁻¹) := by
        simpa only [g, show (1 + (1 / 2 : ℝ)) = 3 / 2 by norm_num]
          using hsum
      _ = 20 := by norm_num
  rw [LSeries_twistedMangoldtCoeff_eq_neg_logDeriv_LFunction chi hsOne] at hnormSeries
  simpa only [norm_neg] using hnormSeries.trans hsumTwenty

end

end KoukRightHalfPlaneLogDerivativeBound

#print axioms KoukRightHalfPlaneLogDerivativeBound.norm_logDeriv_LFunction_le_twenty
