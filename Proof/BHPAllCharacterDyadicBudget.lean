import MRTLemma210DyadicMeanSquare

/-!
# Shared dyadic budget below the BHP/Ramachandra fourth moment

This file contains no fourth-moment source theorem.  It proves the exact
all-character continuous mean-square cost of every dyadic block which occurs
in Ramachandra's formula for `L(1/2+it, chi)^2`.  The Boolean mode records the
two literal halves:

* `false`: `chi(n) n^(-it)`;
* `true`: `conj(chi)(n) n^(+it)`.

The second half has exactly the same all-character cost, by the involution
`chi |-> conj(chi)` and reflection of the symmetric `t` interval.
-/

namespace BHPAllCharacterDyadicBudget

open scoped BigOperators
open MAPMRTLemma210OrthogonalityReduction
open MAPMRTLemma210DyadicMeanSquare
open MontgomeryVaughanFiniteReduction

noncomputable section

/-- One literal dyadic block in the two halves of the squared functional
equation.  The coefficient contains the critical-line factor and divisor
weight, but is independent of the character. -/
def ramachandraDyadicBlock
    (q N : ℕ) [NeZero q] (b : ℕ → ℂ) (dual : Bool)
    (chi : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  if dual then
    twistedFinitePolynomial q (dyadicSupport N) b (star chi) (-t)
  else
    twistedFinitePolynomial q (dyadicSupport N) b chi t

/-- The literal all-character cost obtained from orthogonality and the
same-residue logarithmic Hilbert inequality on an interval of length `2U`. -/
def ramachandraDyadicCost
    (q N : ℕ) (U : ℝ) (b : ℕ → ℂ) : ℝ :=
  ((q : ℝ) * (2 * U) + 8 * Real.pi * (N : ℝ)) * coefficientEnergy b N

theorem continuous_ramachandraDyadicBlock
    (q N : ℕ) [NeZero q] (b : ℕ → ℂ) (dual : Bool)
    (chi : DirichletCharacter ℂ q) :
    Continuous (ramachandraDyadicBlock q N b dual chi) := by
  cases dual
  · change Continuous (fun t => twistedFinitePolynomial q
      (dyadicSupport N) b chi t)
    unfold twistedFinitePolynomial twistedPhase
    fun_prop
  · change Continuous (fun t => twistedFinitePolynomial q
      (dyadicSupport N) b (star chi) (-t))
    unfold twistedFinitePolynomial twistedPhase
    fun_prop

/-- Conjugating every character merely permutes the complete character
family.  No primitivity restriction is present. -/
theorem sum_norm_twisted_star_eq
    (q N : ℕ) [NeZero q] (b : ℕ → ℂ) (t : ℝ) :
    (∑ chi : DirichletCharacter ℂ q,
      ‖twistedFinitePolynomial q (dyadicSupport N) b (star chi) t‖ ^ 2) =
    ∑ chi : DirichletCharacter ℂ q,
      ‖twistedFinitePolynomial q (dyadicSupport N) b chi t‖ ^ 2 := by
  let e : DirichletCharacter ℂ q ≃ DirichletCharacter ℂ q :=
    Equiv.mk star star star_involutive star_involutive
  have h := e.sum_comp (fun chi : DirichletCharacter ℂ q =>
    ‖twistedFinitePolynomial q (dyadicSupport N) b chi t‖ ^ 2)
  simpa [e] using h

/-- Premise-free continuous all-character mean square for either half of the
Ramachandra squared formula, on the exact symmetric interval `[-U,U]`. -/
theorem integral_sum_norm_ramachandraDyadicBlock_sq_le
    (q N : ℕ) [NeZero q] (hN : 1 ≤ N) (b : ℕ → ℂ)
    (dual : Bool) {U : ℝ} (hU : 0 ≤ U) :
    (∫ t in (-U)..U,
      ∑ chi : DirichletCharacter ℂ q,
        ‖ramachandraDyadicBlock q N b dual chi t‖ ^ 2) ≤
      ramachandraDyadicCost q N U b := by
  cases dual with
  | false =>
      simpa [ramachandraDyadicBlock, ramachandraDyadicCost,
        show -U + 2 * U = U by ring] using
        (dyadic_twisted_character_mean_square_interval_le
          (q := q) hN b (-U) (T := 2 * U) (by positivity))
  | true =>
      let F : ℝ → ℝ := fun t => ∑ chi : DirichletCharacter ℂ q,
        ‖twistedFinitePolynomial q (dyadicSupport N) b chi t‖ ^ 2
      have hstar : (fun t : ℝ => ∑ chi : DirichletCharacter ℂ q,
          ‖ramachandraDyadicBlock q N b true chi t‖ ^ 2) =
          (fun t : ℝ => F (-t)) := by
        funext t
        simp only [ramachandraDyadicBlock, if_true]
        exact sum_norm_twisted_star_eq q N b (-t)
      rw [hstar]
      rw [intervalIntegral.integral_comp_neg]
      have h := dyadic_twisted_character_mean_square_interval_le
        (q := q) hN b (-U) (T := 2 * U) (by positivity)
      simpa [F, ramachandraDyadicCost,
        show -U + 2 * U = U by ring] using h

/-- A finite family of literal Ramachandra blocks. -/
def ramachandraDyadicFamily
    {J q : ℕ} [NeZero q]
    (dual : Fin J → Bool) (N : Fin J → ℕ)
    (b : Fin J → ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  ∑ j : Fin J, ‖ramachandraDyadicBlock q (N j) (b j) (dual j) chi t‖ ^ 2

/-- The exact aggregate cost of the finite dyadic family. -/
def ramachandraDyadicFamilyCost
    {J : ℕ} (q : ℕ) (U : ℝ)
    (N : Fin J → ℕ) (b : Fin J → ℕ → ℂ) : ℝ :=
  ∑ j : Fin J, ramachandraDyadicCost q (N j) U (b j)

theorem continuous_ramachandraDyadicFamily
    {J q : ℕ} [NeZero q]
    (dual : Fin J → Bool) (N : Fin J → ℕ)
    (b : Fin J → ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) :
    Continuous (ramachandraDyadicFamily dual N b chi) := by
  unfold ramachandraDyadicFamily
  apply continuous_finsetSum
  intro j hj
  exact (continuous_ramachandraDyadicBlock q (N j) (b j)
    (dual j) chi).norm.pow 2

/-- The complete finite sum/integral and orthogonality weld.  Any nonnegative
continuous family pointwise majorized by `A` times the literal squared-AFE
blocks is bounded by `A` times their exact aggregate length-energy cost. -/
theorem allCharacter_integral_le_ramachandraDyadicFamilyCost
    {J q : ℕ} [NeZero q]
    {U A : ℝ} (hU : 0 ≤ U) (hA : 0 ≤ A)
    (dual : Fin J → Bool) (N : Fin J → ℕ)
    (b : Fin J → ℕ → ℂ)
    (F : DirichletCharacter ℂ q → ℝ → ℝ)
    (hF : ∀ chi, Continuous (F chi))
    (hN : ∀ j, 1 ≤ N j)
    (hmajor : ∀ chi t, |t| ≤ U →
      F chi t ≤ A * ramachandraDyadicFamily dual N b chi t) :
    (∑ chi : DirichletCharacter ℂ q,
      ∫ t in (-U)..U, F chi t) ≤
      A * ramachandraDyadicFamilyCost q U N b := by
  classical
  have hchi (chi : DirichletCharacter ℂ q) :
      (∫ t in (-U)..U, F chi t) ≤
        ∫ t in (-U)..U, A * ramachandraDyadicFamily dual N b chi t := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (hF chi).intervalIntegrable _ _
    · exact (continuous_const.mul
        (continuous_ramachandraDyadicFamily dual N b chi)).intervalIntegrable _ _
    · intro t ht
      exact hmajor chi t ((abs_le).2 ⟨by linarith [ht.1], ht.2⟩)
  calc
    (∑ chi : DirichletCharacter ℂ q,
        ∫ t in (-U)..U, F chi t) ≤
        ∑ chi : DirichletCharacter ℂ q,
          ∫ t in (-U)..U,
            A * ramachandraDyadicFamily dual N b chi t := by
      exact Finset.sum_le_sum fun chi hchiMem => hchi chi
    _ = A * ∑ j : Fin J,
          ∫ t in (-U)..U,
            ∑ chi : DirichletCharacter ℂ q,
              ‖ramachandraDyadicBlock q (N j) (b j) (dual j) chi t‖ ^ 2 := by
      simp_rw [intervalIntegral.integral_const_mul]
      rw [← Finset.mul_sum]
      congr 1
      unfold ramachandraDyadicFamily
      calc
        (∑ chi : DirichletCharacter ℂ q,
            ∫ t in (-U)..U,
              ∑ j : Fin J,
                ‖ramachandraDyadicBlock q (N j) (b j) (dual j) chi t‖ ^ 2) =
            ∑ chi : DirichletCharacter ℂ q,
              ∑ j : Fin J,
                ∫ t in (-U)..U,
                  ‖ramachandraDyadicBlock q (N j) (b j) (dual j) chi t‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro chi hchiMem
          rw [intervalIntegral.integral_finsetSum]
          intro j hj
          exact ((continuous_ramachandraDyadicBlock q (N j) (b j)
            (dual j) chi).norm.pow 2).intervalIntegrable _ _
        _ = ∑ j : Fin J,
              ∑ chi : DirichletCharacter ℂ q,
                ∫ t in (-U)..U,
                  ‖ramachandraDyadicBlock q (N j) (b j) (dual j) chi t‖ ^ 2 := by
          rw [Finset.sum_comm]
        _ = ∑ j : Fin J,
              ∫ t in (-U)..U,
                ∑ chi : DirichletCharacter ℂ q,
                  ‖ramachandraDyadicBlock q (N j) (b j) (dual j) chi t‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [intervalIntegral.integral_finsetSum]
          intro chi hchiMem
          exact ((continuous_ramachandraDyadicBlock q (N j) (b j)
            (dual j) chi).norm.pow 2).intervalIntegrable _ _
    _ ≤ A * ∑ j : Fin J, ramachandraDyadicCost q (N j) U (b j) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact Finset.sum_le_sum fun j hj =>
        integral_sum_norm_ramachandraDyadicBlock_sq_le
          q (N j) (hN j) (b j) (dual j) hU
    _ = A * ramachandraDyadicFamilyCost q U N b := rfl

end
end BHPAllCharacterDyadicBudget

#print axioms BHPAllCharacterDyadicBudget.sum_norm_twisted_star_eq
#print axioms BHPAllCharacterDyadicBudget.integral_sum_norm_ramachandraDyadicBlock_sq_le
#print axioms BHPAllCharacterDyadicBudget.allCharacter_integral_le_ramachandraDyadicFamilyCost
