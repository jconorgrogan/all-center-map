import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# MRT Lemma 2.10: character-orthogonality reduction

This file descends the mean-value theorem with characters to its exact finite
orthogonality layer.  It does not assume Lemma 2.10 or Theorem 9.12.
-/

namespace MAPMRTLemma210OrthogonalityReduction

open scoped BigOperators ComplexConjugate
noncomputable section

/-- Exact orthogonality kernel for the product appearing after expansion of a
character-twisted square.  The nonunit case is retained explicitly. -/
theorem sum_character_mul_star_character
    {q : ℕ} [NeZero q] (n m : ℕ) :
    (∑ chi : DirichletCharacter ℂ q,
        chi n * star (chi m)) =
      if IsUnit (m : ZMod q) then
        if (m : ZMod q) = (n : ZMod q) then (q.totient : ℂ) else 0
      else 0 := by
  by_cases hm : IsUnit (m : ZMod q)
  · rw [if_pos hm]
    have horth :=
      DirichletCharacter.sum_char_inv_mul_char_eq ℂ hm (n : ZMod q)
    calc
      (∑ chi : DirichletCharacter ℂ q, chi n * star (chi m)) =
          ∑ chi : DirichletCharacter ℂ q,
            chi (Ring.inverse (m : ZMod q)) * chi n := by
        apply Finset.sum_congr rfl
        intro chi hchi
        rw [MulChar.star_apply', MulChar.inv_apply]
        ring
      _ = if (m : ZMod q) = (n : ZMod q) then
          (q.totient : ℂ) else 0 := by
        have hinv : Ring.inverse (m : ZMod q) = (m : ZMod q)⁻¹ := by
          rcases hm with ⟨u, hu⟩
          rw [← hu]
          rw [Ring.inverse_unit, ZMod.inv_coe_unit]
        rw [hinv]
        exact horth
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro chi hchi
    rw [chi.map_nonunit hm, star_zero, mul_zero]

/-- The unit/congruence mask selected by character orthogonality. -/
def characterPairMask (q n m : ℕ) : Prop :=
  IsUnit (m : ZMod q) ∧ (m : ZMod q) = (n : ZMod q)

instance characterPairMaskDecidable (q n m : ℕ) :
    Decidable (characterPairMask q n m) := Classical.propDecidable _

/-- The critical-line oscillatory phase `n^(-it)`. -/
def twistedPhase (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I)

/-- Character-twisted finite Dirichlet polynomial with arbitrary coefficients;
`a n` includes the critical-line factor `f(n)/sqrt n` in the source. -/
def twistedFinitePolynomial
    (q : ℕ) (S : Finset ℕ) (a : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ S, (a n * chi n) * twistedPhase n t

/-- The phase of the finite Dirichlet polynomial has unit norm. -/
theorem norm_twistedPhase (n : ℕ) (t : ℝ) :
    ‖twistedPhase n t‖ = 1 := by
  unfold twistedPhase
  exact Complex.norm_exp_ofReal_mul_I _

/-- Exact square expansion before summing over characters. -/
theorem twistedFinitePolynomial_mul_star
    {q : ℕ} (S : Finset ℕ) (a : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    twistedFinitePolynomial q S a chi t *
        star (twistedFinitePolynomial q S a chi t) =
      ∑ n ∈ S, ∑ m ∈ S,
        ((a n *
            twistedPhase n t) *
          star (a m *
            twistedPhase m t)) *
          (chi n * star (chi m)) := by
  unfold twistedFinitePolynomial
  rw [star_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp_rw [star_mul]
  ring

/-- Reassociate the three finite sums without invoking a recursive simplifier
on the symmetric `Finset.sum_comm` rule. -/
theorem sum_character_two_finsets_comm
    {q : ℕ} (S : Finset ℕ)
    (F : DirichletCharacter ℂ q → ℕ → ℕ → ℂ) :
    (∑ chi : DirichletCharacter ℂ q,
        ∑ n ∈ S, ∑ m ∈ S, F chi n m) =
      ∑ n ∈ S, ∑ m ∈ S,
        ∑ chi : DirichletCharacter ℂ q, F chi n m := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]

/-- Exact character-summed square: only unit pairs in the same residue class
survive, with multiplicity `phi(q)`. -/
theorem sum_twistedFinitePolynomial_norm_sq
    {q : ℕ} [NeZero q] (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ((∑ chi : DirichletCharacter ℂ q,
        ‖twistedFinitePolynomial q S a chi t‖ ^ 2 : ℝ) : ℂ) =
      (q.totient : ℂ) *
        ∑ n ∈ S, ∑ m ∈ S,
          if characterPairMask q n m then
            (a n *
                twistedPhase n t) *
              star (a m *
                twistedPhase m t)
          else 0 := by
  classical
  push_cast
  simp_rw [show ∀ chi : DirichletCharacter ℂ q,
      ((‖twistedFinitePolynomial q S a chi t‖ : ℝ) : ℂ) ^ 2 =
        twistedFinitePolynomial q S a chi t *
          star (twistedFinitePolynomial q S a chi t) by
    intro chi
    simpa only [Complex.ofReal_pow] using
      (RCLike.mul_conj (twistedFinitePolynomial q S a chi t)).symm]
  simp_rw [twistedFinitePolynomial_mul_star]
  rw [sum_character_two_finsets_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  let c : ℂ :=
    (a n * twistedPhase n t) *
      star (a m * twistedPhase m t)
  change (∑ chi : DirichletCharacter ℂ q,
      c * (chi n * star (chi m))) =
    (q.totient : ℂ) * (if characterPairMask q n m then c else 0)
  rw [← Finset.mul_sum, sum_character_mul_star_character]
  unfold characterPairMask
  by_cases hunit : IsUnit (m : ZMod q)
  · rw [if_pos hunit]
    by_cases heq : (m : ZMod q) = (n : ZMod q)
    · have hunitn : IsUnit (n : ZMod q) := heq ▸ hunit
      simp [heq, hunitn, mul_comm]
    · simp [heq, hunit]
  · simp [hunit]

end
end MAPMRTLemma210OrthogonalityReduction

#print axioms MAPMRTLemma210OrthogonalityReduction.sum_character_mul_star_character
#print axioms MAPMRTLemma210OrthogonalityReduction.twistedFinitePolynomial_mul_star
#print axioms MAPMRTLemma210OrthogonalityReduction.sum_twistedFinitePolynomial_norm_sq
