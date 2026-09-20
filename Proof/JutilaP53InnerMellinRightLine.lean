import JutilaGenericGammaRightLine

/-!
# The inner Mellin line in Jutila p.53

After Lemma 2 and the substitution `n = d*m`, the remaining inner series is
an exponentially smoothed Dirichlet L-series at `1+s`.  This file proves the
exact one-scale and two-scale right-line identities.  No continuation or
contour estimate is used here.
-/

namespace MAPJutilaP53InnerMellinRightLine

open Complex MeasureTheory
open MAPJutilaGenericGammaRightLine

noncomputable section

def p53InnerSmoothed {q : ℕ} (chi : DirichletCharacter ℂ q)
    (s : ℂ) (U : ℝ) : ℂ :=
  ∑' m : ℕ,
    LSeries.term ((chi ·) : ℕ → ℂ) (1 + s) m *
      (Real.exp (-((m : ℝ) / U)) : ℂ)

/-- Exact right-line Mellin inversion for the inner smoothed L-series. -/
theorem p53InnerSmoothed_eq_LFunction_gamma_rightLine
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 ≤ s.re) {U : ℝ} (hU : 0 < U) :
    p53InnerSmoothed chi s U =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          DirichletCharacter.LFunction chi
              (1 + s + ((1 : ℝ) : ℂ) + v * I) *
            Complex.Gamma (((1 : ℝ) : ℂ) + v * I) *
            (U : ℂ) ^ (((1 : ℝ) : ℂ) + v * I)) := by
  have hsum : LSeriesSummable ((chi ·) : ℕ → ℂ)
      ((1 + s) + ((1 : ℝ) : ℂ)) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re chi (by
      simp only [map_add, ofReal_one, add_re, one_re]
      linarith)
  rw [p53InnerSmoothed,
    smoothedSeries_eq_LSeries_gamma_rightLine
      ((chi ·) : ℕ → ℂ) (c := 1) (X := U) zero_lt_one hU
      (1 + s) hsum]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  have hline : 1 <
      (1 + s + (((1 : ℝ) : ℂ) + v * I)).re := by
    simp only [map_add, ofReal_one, add_re, one_re, mul_re, ofReal_re,
      I_re, ofReal_im, I_im, mul_zero, zero_mul, sub_zero]
    linarith
  rw [← DirichletCharacter.LFunction_eq_LSeries chi hline]
  ring

def p53InnerTwoScale {q : ℕ} (chi : DirichletCharacter ℂ q)
    (s : ℂ) (U V : ℝ) : ℂ :=
  ∑' m : ℕ,
    LSeries.term ((chi ·) : ℕ → ℂ) (1 + s) m *
      ((Real.exp (-((m : ℝ) / U)) -
        Real.exp (-((m : ℝ) / V))) : ℂ)

private theorem norm_inner_term_le_geometric
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 ≤ s.re) {U : ℝ} (hU : 0 < U) (m : ℕ) :
    ‖LSeries.term ((chi ·) : ℕ → ℂ) (1 + s) m *
        (Real.exp (-((m : ℝ) / U)) : ℂ)‖ ≤
      (Real.exp (-(1 / U))) ^ m := by
  by_cases hm0 : m = 0
  · subst m
    simp [LSeries.term_zero]
  have hm : 0 < m := Nat.pos_of_ne_zero hm0
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hexp : 0 ≤ (1 + s).re := by simp; linarith
  have hden : 1 ≤ (m : ℝ) ^ (1 + s).re :=
    Real.one_le_rpow hmOne hexp
  have hdenPos : 0 < (m : ℝ) ^ (1 + s).re :=
    lt_of_lt_of_le zero_lt_one hden
  have hterm :
      ‖LSeries.term ((chi ·) : ℕ → ℂ) (1 + s) m‖ ≤ 1 := by
    rw [LSeries.norm_term_eq, if_neg hm0]
    rw [div_le_one hdenPos]
    exact (DirichletCharacter.norm_le_one chi m).trans hden
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    ‖LSeries.term ((chi ·) : ℕ → ℂ) (1 + s) m‖ *
          Real.exp (-((m : ℝ) / U)) ≤
        1 * Real.exp (-((m : ℝ) / U)) := by
      gcongr
    _ = (Real.exp (-(1 / U))) ^ m := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem summable_inner_smoothed
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 ≤ s.re) {U : ℝ} (hU : 0 < U) :
    Summable (fun m : ℕ =>
      LSeries.term ((chi ·) : ℕ → ℂ) (1 + s) m *
        (Real.exp (-((m : ℝ) / U)) : ℂ)) := by
  let a : ℝ := Real.exp (-(1 / U))
  have haPos : 0 < a := by dsimp [a]; positivity
  have haLt : a < 1 := by
    dsimp [a]
    have hneg : -(1 / U) < 0 := by
      have hinv : 0 < 1 / U := one_div_pos.mpr hU
      linarith
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hneg
  have hgeo : Summable (fun m : ℕ => a ^ m) :=
    summable_geometric_of_norm_lt_one
      (show ‖a‖ < 1 by
        simpa [Real.norm_eq_abs, abs_of_pos haPos] using haLt)
  exact Summable.of_norm_bounded hgeo (fun m => by
    simpa [a] using norm_inner_term_le_geometric chi hs hU m)

theorem summable_inner_twoScale
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 ≤ s.re) {U V : ℝ} (hU : 0 < U) (hV : 0 < V) :
    Summable (fun m : ℕ =>
      LSeries.term ((chi ·) : ℕ → ℂ) (1 + s) m *
        ((Real.exp (-((m : ℝ) / U)) -
          Real.exp (-((m : ℝ) / V))) : ℂ)) := by
  have hsumU := summable_inner_smoothed chi hs hU
  have hsumV := summable_inner_smoothed chi hs hV
  convert hsumU.sub hsumV using 1
  funext m
  push_cast
  ring

theorem p53InnerTwoScale_eq_sub
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 ≤ s.re) {U V : ℝ} (hU : 0 < U) (hV : 0 < V) :
    p53InnerTwoScale chi s U V =
      p53InnerSmoothed chi s U - p53InnerSmoothed chi s V := by
  have hsumU := summable_inner_smoothed chi hs hU
  have hsumV := summable_inner_smoothed chi hs hV
  unfold p53InnerTwoScale p53InnerSmoothed
  rw [← hsumU.tsum_sub hsumV]
  apply tsum_congr
  intro m
  push_cast
  ring

/-- Exact two-scale right-line formula used before the contour move. -/
theorem p53InnerTwoScale_eq_LFunction_gamma_rightLine
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 ≤ s.re) {U V : ℝ}
    (hU : 0 < U) (hV : 0 < V) :
    p53InnerTwoScale chi s U V =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ,
            DirichletCharacter.LFunction chi
                (1 + s + ((1 : ℝ) : ℂ) + v * I) *
              Complex.Gamma (((1 : ℝ) : ℂ) + v * I) *
              (U : ℂ) ^ (((1 : ℝ) : ℂ) + v * I)) -
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ,
            DirichletCharacter.LFunction chi
                (1 + s + ((1 : ℝ) : ℂ) + v * I) *
              Complex.Gamma (((1 : ℝ) : ℂ) + v * I) *
              (V : ℂ) ^ (((1 : ℝ) : ℂ) + v * I)) := by
  rw [p53InnerTwoScale_eq_sub chi hs hU hV,
    p53InnerSmoothed_eq_LFunction_gamma_rightLine chi hs hU,
    p53InnerSmoothed_eq_LFunction_gamma_rightLine chi hs hV]

end

end MAPJutilaP53InnerMellinRightLine

#print axioms MAPJutilaP53InnerMellinRightLine.p53InnerSmoothed_eq_LFunction_gamma_rightLine
#print axioms MAPJutilaP53InnerMellinRightLine.p53InnerTwoScale_eq_LFunction_gamma_rightLine
