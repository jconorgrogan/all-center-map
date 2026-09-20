import JutilaP53Lemma2Bridge
import JutilaGenericGammaRightLine

/-!
# The literal selected pseudocharacter pair on the Mellin right line

This applies generic Gamma inversion directly to one selected `r,r'`
component of the p.53 kernel.  The result does not yet continue the finite
Euler correction; it isolates that factorization as the only step between
the exact arithmetic pair and the movable L-function contour.
-/

namespace MAPJutilaP53PairRightLine

open Complex MeasureTheory
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53PseudocharacterSquareExpansion
open MAPJutilaP53PairRExpansion
open MAPJutilaGenericGammaRightLine

noncomputable section

def p53PairCoefficient {q : ℕ}
    (chi : DirichletCharacter ℂ q) (r r' n : ℕ) : ℂ :=
  normalizedP53PseudoAt r n * normalizedP53PseudoAt r' n * chi n

theorem norm_p53PairCoefficient_le_one
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {r r' : ℕ} (hr : 0 < r) (hr' : 0 < r') (n : ℕ) :
    ‖p53PairCoefficient chi r r' n‖ ≤ 1 := by
  unfold p53PairCoefficient
  have ha := norm_normalizedP53PseudoAt_le_one (n := n) hr
  have hb := norm_normalizedP53PseudoAt_le_one (n := n) hr'
  have hc := DirichletCharacter.norm_le_one chi n
  simp only [norm_mul]
  have hab : ‖normalizedP53PseudoAt r n‖ *
      ‖normalizedP53PseudoAt r' n‖ ≤ 1 := by
    nlinarith [norm_nonneg (normalizedP53PseudoAt r n),
      norm_nonneg (normalizedP53PseudoAt r' n)]
  nlinarith [norm_nonneg (chi n)]

theorem pair_LSeries_term_eq
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {r r' n : ℕ} (hn : 0 < n) (s : ℂ) :
    LSeries.term (p53PairCoefficient chi r r') (1 + s) n =
      ((n : ℝ)⁻¹ : ℂ) * normalizedP53PseudoAt r n *
        normalizedP53PseudoAt r' n * chi n * (n : ℂ) ^ (-s) := by
  rw [LSeries.term_of_ne_zero hn.ne']
  unfold p53PairCoefficient
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show -(1 + s) = -1 + -s by ring,
    Complex.cpow_add _ _ hnC]
  rw [Complex.cpow_neg_one (n : ℂ)]
  have hinv : (n : ℂ)⁻¹ = ((n : ℝ)⁻¹ : ℂ) := by
    push_cast
    rfl
  rw [hinv]
  ring

theorem pairRTerm_eq_LSeries_term_mul_difference
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {M N : ℝ} {s : ℂ} {r r' n : ℕ} (hn : 0 < n) :
    jutilaP53PairRTerm M N s chi r r' n =
      LSeries.term (p53PairCoefficient chi r r') (1 + s) n *
        ((Real.exp (-((n : ℝ) / N)) -
          Real.exp (-((n : ℝ) / M))) : ℂ) := by
  rw [pair_LSeries_term_eq chi hn s]
  unfold jutilaP53PairRTerm
  ring

def p53PairOneScaleSmoothed {q : ℕ}
    (chi : DirichletCharacter ℂ q) (r r' : ℕ)
    (s : ℂ) (U : ℝ) : ℂ :=
  ∑' n : ℕ,
    LSeries.term (p53PairCoefficient chi r r') (1 + s) n *
      (Real.exp (-((n : ℝ) / U)) : ℂ)

theorem pairRB_eq_oneScale_sub
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    {s : ℂ} (hs : 0 ≤ s.re) {r r' : ℕ}
    (hr : 0 < r) (hr' : 0 < r') :
    jutilaP53PairRB M N s chi r r' =
      p53PairOneScaleSmoothed chi r r' s N -
        p53PairOneScaleSmoothed chi r r' s M := by
  have hPair := summable_jutilaP53PairRTerm hM hMN hs chi hr hr'
  have hN : 0 < N := hM.trans hMN
  have hOneScale (U : ℝ) (hU : 0 < U) : Summable (fun n : ℕ =>
      LSeries.term (p53PairCoefficient chi r r') (1 + s) n *
        (Real.exp (-((n : ℝ) / U)) : ℂ)) := by
    let a : ℝ := Real.exp (-(1 / U))
    have haPos : 0 < a := by dsimp [a]; positivity
    have haLt : a < 1 := by
      dsimp [a]
      have hneg : -(1 / U) < 0 := by
        have : 0 < 1 / U := one_div_pos.mpr hU
        linarith
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hneg
    have hgeo : Summable (fun n : ℕ => a ^ n) :=
      summable_geometric_of_norm_lt_one
        (show ‖a‖ < 1 by
          simpa [Real.norm_eq_abs, abs_of_pos haPos] using haLt)
    apply Summable.of_norm_bounded hgeo
    intro n
    by_cases hn0 : n = 0
    · subst n
      simp [LSeries.term_zero]
    have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hexp : 0 ≤ (1 + s).re := by simp; linarith
    have hden : 1 ≤ (n : ℝ) ^ (1 + s).re :=
      Real.one_le_rpow hnOne hexp
    have hdenPos : 0 < (n : ℝ) ^ (1 + s).re :=
      zero_lt_one.trans_le hden
    have hterm :
        ‖LSeries.term (p53PairCoefficient chi r r') (1 + s) n‖ ≤ 1 := by
      rw [LSeries.norm_term_eq, if_neg hn0, div_le_one hdenPos]
      exact (norm_p53PairCoefficient_le_one chi hr hr' n).trans hden
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      ‖LSeries.term (p53PairCoefficient chi r r') (1 + s) n‖ *
          Real.exp (-((n : ℝ) / U)) ≤
        1 * Real.exp (-((n : ℝ) / U)) := by gcongr
      _ = a ^ n := by
        dsimp [a]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hsumN := hOneScale N hN
  have hsumM := hOneScale M hM
  unfold jutilaP53PairRB p53PairOneScaleSmoothed
  rw [← hsumN.tsum_sub hsumM]
  apply tsum_congr
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp [jutilaP53PairRTerm, LSeries.term_zero]
  rw [pairRTerm_eq_LSeries_term_mul_difference chi
    (Nat.pos_of_ne_zero hn0)]
  push_cast
  ring

/-- The actual selected pair on the Mellin right line.  The remaining
factorization problem is now exactly the L-series displayed here. -/
theorem pairOneScale_eq_LSeries_gamma_rightLine
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {r r' : ℕ} (hr : 0 < r) (hr' : 0 < r')
    {s : ℂ} (hs : 0 ≤ s.re) {U : ℝ} (hU : 0 < U) :
    p53PairOneScaleSmoothed chi r r' s U =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          LSeries (p53PairCoefficient chi r r')
              ((1 + s) + (((1 : ℝ) : ℂ) + v * I)) *
            Complex.Gamma (((1 : ℝ) : ℂ) + v * I) *
            (U : ℂ) ^ (((1 : ℝ) : ℂ) + v * I)) := by
  have hLS : LSeriesSummable (p53PairCoefficient chi r r')
      ((1 + s) + (1 : ℂ)) :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (m := 1) (fun n _hn => norm_p53PairCoefficient_le_one chi hr hr' n) (by
        simp
        linarith)
  unfold p53PairOneScaleSmoothed
  exact smoothedSeries_eq_LSeries_gamma_rightLine
    (p53PairCoefficient chi r r') (c := 1) (X := U)
      zero_lt_one hU (1 + s) hLS

end

end MAPJutilaP53PairRightLine

#print axioms MAPJutilaP53PairRightLine.pairRB_eq_oneScale_sub
#print axioms MAPJutilaP53PairRightLine.pairOneScale_eq_LSeries_gamma_rightLine
