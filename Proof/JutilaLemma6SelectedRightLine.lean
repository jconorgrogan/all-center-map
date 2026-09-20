import JutilaLemma1OuterSum
import JutilaGenericGammaRightLine

/-!
# Selected-system right line for Jutila Lemma 6

This is the source-faithful starting-line Mellin identity.  The primed
`r`-sum is an explicit finite set `S`; its range, squarefreeness, and
coprimality to the character modulus are visible hypotheses.  No all-integers
surrogate is used.
-/

namespace MAPJutilaLemma6SelectedRightLine

open Complex MeasureTheory
open MAPJutilaMEntire
open MAPJutilaLemma1OuterSum
open MAPJutilaGenericGammaRightLine

noncomputable section

/-- Exact selected-system inverse Mellin identity on any line on which the
coefficient L-series is absolutely convergent. -/
theorem jutilaSelectedSmoothedSeries_eq_gamma_rightLine
    {q R : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    {D S : Finset ℕ}
    (hDpos : ∀ d ∈ D, d ≠ 0)
    (hS : S ⊆ Finset.Icc 1 R)
    (hrsq : ∀ r ∈ S, Squarefree r)
    (hrcop : ∀ r ∈ S, r.Coprime q)
    {c X : ℝ} (hc : 0 < c) (hX : 0 < X)
    (s : ℂ) (hs : 1 < (s + (c : ℂ)).re) :
    (∑' n : ℕ,
      LSeries.term (jutilaEquation22SelectedCoeff chi xi D S) s n *
        (Real.exp (-((n : ℝ) / X)) : ℂ)) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          DirichletCharacter.LFunction chi
              (s + ((c : ℂ) + v * I)) *
            jutilaMWeightedSumComplex chi xi D S
              (s + ((c : ℂ) + v * I)) *
            Complex.Gamma ((c : ℂ) + v * I) *
            (X : ℂ) ^ ((c : ℂ) + v * I)) := by
  have hLS : LSeriesSummable
      (jutilaEquation22SelectedCoeff chi xi D S) (s + (c : ℂ)) :=
    LSeriesSummable_jutilaEquation22SelectedCoeff
      chi xi hDpos hS hrsq hrcop hs
  rw [smoothedSeries_eq_LSeries_gamma_rightLine
    (jutilaEquation22SelectedCoeff chi xi D S) hc hX s hLS]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  have hline : 1 < (s + ((c : ℂ) + v * I)).re := by
    simpa using hs
  rw [← JutilaEquation22SelectedFinite
    chi xi hDpos hS hrsq hrcop hline]

end

end MAPJutilaLemma6SelectedRightLine

#print axioms MAPJutilaLemma6SelectedRightLine.jutilaSelectedSmoothedSeries_eq_gamma_rightLine
