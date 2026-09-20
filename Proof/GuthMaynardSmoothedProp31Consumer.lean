import GuthMaynardTwoPlateauSmoothingBridge
import GuthMaynardTwoPlateauThreshold
import GuthMaynardJutilaReflection2941

/-!
# Conditional consumer for the fixed-weight smoothed Proposition 3.1 premise

This module does not replace the source's fixed weight by an arbitrary sharp
polynomial.  It states the local analytic premise for one fixed plateau weight
`w`, with coefficients supported on that plateau, and proves the exact bridge
from the weighted polynomial to the sharp polynomial of the same coefficient.
The two-plateau and threshold modules then supply the finite decomposition
needed by the global reduction.
-/

namespace GuthMaynardSmoothedProp31Consumer

open scoped BigOperators
open CGLProofDAG
open GuthMaynardTwoPlateauSmoothingBridge
open GuthMaynardJutilaReflection2941

noncomputable section

def smoothedPolynomial (w : ℝ → ℝ) (b : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N),
    (w ((n : ℝ) / (N : ℝ)) : ℂ) * b n *
      Complex.exp (Complex.I * (t * Real.log n))

def supportedOnPlateau (N : ℕ) (b : ℕ → ℂ) : Prop :=
  ∀ n, b n ≠ 0 → n ∈ plateau N

def FixedWeightProp31 (w : ℝ → ℝ) : Prop :=
  PlateauWeight w ∧
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (V : ℝ) (b : ℕ → ℂ) (U : Finset ℝ),
        32 ≤ N → 0 < V →
        Real.rpow (N : ℝ) (7 / 10 : ℝ) ≤ V →
        V ≤ Real.rpow (N : ℝ) (8 / 10 : ℝ) →
        (∀ n, ‖b n‖ ≤ 1) → supportedOnPlateau N b →
        TPowerSeparated U (Real.rpow (N : ℝ) (6 / 5 : ℝ)) ε →
        (∀ u ∈ U, 0 ≤ u ∧ u ≤ Real.rpow (N : ℝ) (6 / 5 : ℝ)) →
        (∀ u ∈ U, V ≤ ‖smoothedPolynomial w b N u‖) →
        (U.card : ℝ) ≤ C *
            Real.rpow (Real.rpow (N : ℝ) (6 / 5 : ℝ)) ε *
          (Real.rpow (N : ℝ) (6 / 5) *
            Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4)

theorem smoothed_eq_sharp_of_supported
    {w : ℝ → ℝ} (hw : PlateauWeight w) {N : ℕ}
    (hN : 32 ≤ N) {b : ℕ → ℂ} (hsupp : supportedOnPlateau N b)
    (t : ℝ) :
    smoothedPolynomial w b N t = dirichletPolynomial b N t := by
  unfold smoothedPolynomial dirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hbn : b n = 0
  · simp [hbn]
  · have hp := hsupp n hbn
    have hratio : (6 / 5 : ℝ) ≤ (n : ℝ) / (N : ℝ) ∧
        (n : ℝ) / (N : ℝ) ≤ 9 / 5 := by
      have hm : 0 < (N : ℝ) := by
        have : 1 ≤ N := by omega
        exact_mod_cast this
      have hp' := plateau_mem_iff.mp hp
      constructor
      · apply (le_div_iff₀ hm).2
        have h := (show (6 : ℝ) * N ≤ 5 * n by exact_mod_cast hp'.1)
        nlinarith
      · apply (div_le_iff₀ hm).2
        have h := (show (5 : ℝ) * n ≤ 9 * N by exact_mod_cast hp'.2)
        nlinarith
    rw [hw _ hratio.1 hratio.2]
    simp

theorem fixedWeightProp31_localSharp
    {w : ℝ → ℝ} (hlocal : FixedWeightProp31 w)
    {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 32 ≤ N)
    {V : ℝ} (hV : 0 < V)
    (hVlow : Real.rpow (N : ℝ) (7 / 10 : ℝ) ≤ V)
    (hVhigh : V ≤ Real.rpow (N : ℝ) (8 / 10 : ℝ))
    {b : ℕ → ℂ} (hb : ∀ n, ‖b n‖ ≤ 1)
    (hsupp : supportedOnPlateau N b) {U : Finset ℝ}
    (hsep : TPowerSeparated U (Real.rpow (N : ℝ) (6 / 5 : ℝ)) ε)
    (hheight : ∀ u ∈ U, 0 ≤ u ∧
      u ≤ Real.rpow (N : ℝ) (6 / 5 : ℝ))
    (hlarge : ∀ u ∈ U, V ≤ ‖dirichletPolynomial b N u‖) :
    ∃ C : ℝ, 0 < C ∧
      (U.card : ℝ) ≤ C *
          Real.rpow (Real.rpow (N : ℝ) (6 / 5 : ℝ)) ε *
        (Real.rpow (N : ℝ) (6 / 5) *
          Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4) := by
  rcases hlocal with ⟨hw, hbound⟩
  rcases hbound ε hε with ⟨C, hC, hbound'⟩
  have hsmoothed : ∀ u ∈ U, V ≤ ‖smoothedPolynomial w b N u‖ := by
    intro u hu
    rw [smoothed_eq_sharp_of_supported hw hN hsupp]
    exact hlarge u hu
  exact ⟨C, hC, hbound' N V b U hN hV hVlow hVhigh hb hsupp hsep
    hheight hsmoothed⟩

/- The witness is exposed before any local parameters.  This is the form
needed by the partition and time-subdivision consumer. -/
theorem fixedWeightProp31_localSharp_uniform
    {w : ℝ → ℝ} (hlocal : FixedWeightProp31 w) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ (N : ℕ) (V : ℝ) (b : ℕ → ℂ) (U : Finset ℝ),
          32 ≤ N → 0 < V →
          Real.rpow (N : ℝ) (7 / 10 : ℝ) ≤ V →
          V ≤ Real.rpow (N : ℝ) (8 / 10 : ℝ) →
          (∀ n, ‖b n‖ ≤ 1) → supportedOnPlateau N b →
          TPowerSeparated U (Real.rpow (N : ℝ) (6 / 5 : ℝ)) ε →
          (∀ u ∈ U, 0 ≤ u ∧
            u ≤ Real.rpow (N : ℝ) (6 / 5 : ℝ)) →
          (∀ u ∈ U, V ≤ ‖dirichletPolynomial b N u‖) →
          (U.card : ℝ) ≤ C *
              Real.rpow (Real.rpow (N : ℝ) (6 / 5 : ℝ)) ε *
            (Real.rpow (N : ℝ) (6 / 5) *
              Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4) := by
  intro ε hε
  rcases hlocal with ⟨hw, hbound⟩
  rcases hbound ε hε with ⟨C, hC, hbound'⟩
  refine ⟨C, hC, ?_⟩
  intro N V b U hN hV hVlow hVhigh hb hsupp hsep hheight hlarge
  have hsmoothed : ∀ u ∈ U, V ≤ ‖smoothedPolynomial w b N u‖ := by
    intro u hu
    rw [smoothed_eq_sharp_of_supported hw hN hsupp]
    exact hlarge u hu
  exact hbound' N V b U hN hV hVlow hVhigh hb hsupp hsep hheight hsmoothed

end
end GuthMaynardSmoothedProp31Consumer

#print axioms GuthMaynardSmoothedProp31Consumer.smoothed_eq_sharp_of_supported
