import JutilaLemma6SieveCoefficientBridge
import JutilaPseudocharacterHarmonicLower

/-!
# Main, detector, and tail decomposition in Jutila Lemma 6

The exact selected direct series is split into its `n=1` main term, the
finite detector range `z1<n≤M`, and the infinite tail.  The vanishing of the
intermediate coefficients is the finite Möbius identity already certified in
the Graham-bypass module.
-/

namespace MAPJutilaLemma6PrefixMainTail

open scoped BigOperators
open Complex
open MAPJutilaPseudocharacterMExact
open MAPJutilaPseudocharacterHarmonicLower
open MAPJutilaGappedGrahamBypass
open MAPJutilaLemma6DirectTail

noncomputable section

def jutilaLemmaSixFiniteDetector {q : ℕ}
    (chi : DirichletCharacter ℂ q) (z1 z2 : ℝ)
    (S : Finset ℕ) (rho : ℂ) (X : ℝ) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (M + 1),
    if z1 < (n : ℝ) then
      jutilaLemmaSixDirectTerm chi z1 z2 S rho X n else 0

theorem selbergPseudoAt_one (r : ℕ) :
    selbergPseudoAt r 1 = 1 := by
  simp [selbergPseudoAt, selbergPseudoCoeff]

theorem jutilaWeightedPseudocharacter_one (S : Finset ℕ) :
    jutilaWeightedPseudocharacter S 1 =
      ∑ r ∈ S, (r : ℂ)⁻¹ := by
  unfold jutilaWeightedPseudocharacter
  apply Finset.sum_congr rfl
  intro r hr
  rw [selbergPseudoAt_one]
  simp

theorem jutilaLemmaSixDirectTerm_one
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    (S : Finset ℕ) (rho : ℂ) (X : ℝ) :
    jutilaLemmaSixDirectTerm chi z1 z2 S rho X 1 =
      (Real.exp (-(1 / X)) : ℂ) * ∑ r ∈ S, (r : ℂ)⁻¹ := by
  unfold jutilaLemmaSixDirectTerm
  rw [jutilaDivisorCoefficient_one hz1 hz12,
    jutilaWeightedPseudocharacter_one]
  simp

private theorem directTerm_eq_mainIndicator_add_detectorIndicator
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    (S : Finset ℕ) (rho : ℂ) (X : ℝ) (n : ℕ) :
    jutilaLemmaSixDirectTerm chi z1 z2 S rho X n =
      (if n = 1 then jutilaLemmaSixDirectTerm chi z1 z2 S rho X n else 0) +
      (if z1 < (n : ℝ) then
        jutilaLemmaSixDirectTerm chi z1 z2 S rho X n else 0) := by
  rcases n with _ | n
  · simp [jutilaLemmaSixDirectTerm, jutilaDivisorCoefficient]
  · by_cases hn1 : n + 1 = 1
    · have hn0 : n = 0 := by omega
      subst n
      simp [show ¬ z1 < (1 : ℝ) by linarith]
    · have hn2 : 2 ≤ n + 1 := by omega
      have hn0 : n ≠ 0 := by omega
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
      by_cases hlarge : z1 < ((n + 1 : ℕ) : ℝ)
      · rw [hcast] at hlarge
        simp [hn0, hlarge]
      · have hsmall : ((n + 1 : ℕ) : ℝ) ≤ z1 := le_of_not_gt hlarge
        have hzero := jutilaDivisorCoefficient_zero_of_two_le
          hz1 hz12 hn2 hsmall
        rw [hcast] at hlarge
        simp [hn0, hlarge, jutilaLemmaSixDirectTerm, hzero]

/-- Exact prefix decomposition: the source assertion `a1=1`, `an=0` up to
`z1` leaves only the main term and the finite detector. -/
theorem jutilaLemmaSixPrefix_eq_main_add_detector
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    (S : Finset ℕ) (rho : ℂ) (X : ℝ)
    {M : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Finset.range (M + 1),
      jutilaLemmaSixDirectTerm chi z1 z2 S rho X n) =
      (Real.exp (-(1 / X)) : ℂ) * ∑ r ∈ S, (r : ℂ)⁻¹ +
        jutilaLemmaSixFiniteDetector chi z1 z2 S rho X M := by
  calc
    (∑ n ∈ Finset.range (M + 1),
        jutilaLemmaSixDirectTerm chi z1 z2 S rho X n) =
      ∑ n ∈ Finset.range (M + 1),
        ((if n = 1 then
            jutilaLemmaSixDirectTerm chi z1 z2 S rho X n else 0) +
          (if z1 < (n : ℝ) then
            jutilaLemmaSixDirectTerm chi z1 z2 S rho X n else 0)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact directTerm_eq_mainIndicator_add_detectorIndicator
        chi hz1 hz12 S rho X n
    _ = (∑ n ∈ Finset.range (M + 1),
          if n = 1 then
            jutilaLemmaSixDirectTerm chi z1 z2 S rho X n else 0) +
        jutilaLemmaSixFiniteDetector chi z1 z2 S rho X M := by
      rw [Finset.sum_add_distrib]
      rfl
    _ = jutilaLemmaSixDirectTerm chi z1 z2 S rho X 1 +
        jutilaLemmaSixFiniteDetector chi z1 z2 S rho X M := by
      have hmem : 1 ∈ Finset.range (M + 1) := Finset.mem_range.mpr (by omega)
      simp [Finset.sum_ite_eq', hmem]
    _ = _ := by rw [jutilaLemmaSixDirectTerm_one chi hz1 hz12]

/-- Full exact main + detector + tail identity. -/
theorem jutilaLemmaSixDirectSeries_eq_main_add_detector_add_tail
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    {S : Finset ℕ} {R : ℕ} (hS : S ⊆ Finset.Icc 1 R)
    {rho : ℂ} (hrho : 0 ≤ rho.re) {X : ℝ} (hX : 0 < X)
    {M : ℕ} (hM : 1 ≤ M) :
    (∑' n : ℕ, jutilaLemmaSixDirectTerm chi z1 z2 S rho X n) =
      (Real.exp (-(1 / X)) : ℂ) * ∑ r ∈ S, (r : ℂ)⁻¹ +
        jutilaLemmaSixFiniteDetector chi z1 z2 S rho X M +
      ∑' k : ℕ,
        jutilaLemmaSixDirectTerm chi z1 z2 S rho X (k + (M + 1)) := by
  rw [jutilaLemmaSixDirectSeries_eq_prefix_add_tail
    chi hz1 hz12 hS M hrho hX]
  rw [jutilaLemmaSixPrefix_eq_main_add_detector chi hz1 hz12 S rho X hM]

/-- Canonical source specialization: `S` is exactly the primed set, so the
main term is the harmonic quantity used by the terminal lower weld. -/
theorem jutilaCanonicalDirectSeries_eq_main_add_detector_add_tail
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    (R : ℕ) {rho : ℂ} (hrho : 0 ≤ rho.re)
    {X : ℝ} (hX : 0 < X) {M : ℕ} (hM : 1 ≤ M) :
    (∑' n : ℕ,
      jutilaLemmaSixDirectTerm chi z1 z2 (jutilaPrimedRSet q R) rho X n) =
      (Real.exp (-(1 / X)) : ℂ) * (jutilaPrimedHarmonic q R : ℂ) +
        jutilaLemmaSixFiniteDetector chi z1 z2
          (jutilaPrimedRSet q R) rho X M +
      ∑' k : ℕ,
        jutilaLemmaSixDirectTerm chi z1 z2 (jutilaPrimedRSet q R) rho X
          (k + (M + 1)) := by
  simpa [jutilaPrimedHarmonic] using
    (jutilaLemmaSixDirectSeries_eq_main_add_detector_add_tail
      chi hz1 hz12 (jutilaPrimedRSet_subset_Icc q R) hrho hX hM)

end

end MAPJutilaLemma6PrefixMainTail

#print axioms MAPJutilaLemma6PrefixMainTail.jutilaCanonicalDirectSeries_eq_main_add_detector_add_tail
