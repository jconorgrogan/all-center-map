import FordP16FiniteFourierBridge

open scoped BigOperators ZMod ComplexConjugate
set_option maxHeartbeats 5000000

namespace MAPFordBoundaryCrossFourier
noncomputable section
open MAPFordP16FiniteFourierBridge
open MAPFordFiniteFourierCharacterSum

/-- The finite Fourier block attached to an integer vector frequency family. -/
def fordBoundaryBlock {L k : ℕ} [NeZero L] {A : Type*} [Fintype A]
    (f : A → Fin k → ℤ) (alpha : Fin k → ZMod L) : ℂ :=
  ∑ a : A, fordIntegerCharTerm alpha (f a)

/-- Exact cross correlation: finite characters count the literal equal-frequency
pairs, provided the integer differences lie strictly inside the modulus. -/
theorem cross_count
    {L k : ℕ} [NeZero L] {A B : Type*} [Fintype A] [Fintype B]
    (f : A → Fin k → ℤ) (g : B → Fin k → ℤ)
    (hbound : ∀ a b j, |f a j - g b j| < (L : ℤ)) :
    (∑ alpha : Fin k → ZMod L,
      fordBoundaryBlock f alpha * star (fordBoundaryBlock g alpha)) =
      (L : ℂ) ^ k * Fintype.card {r : A × B // ∀ j, f r.1 j = g r.2 j} := by
  classical
  have hα : ∀ alpha : Fin k → ZMod L,
      fordBoundaryBlock f alpha * star (fordBoundaryBlock g alpha) =
        ∑ r : A × B, fordIntegerCharTerm alpha (fun j => f r.1 j - g r.2 j) := by
    intro alpha
    simp only [fordBoundaryBlock, star_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Fintype.sum_prod_type']
    apply Finset.sum_congr rfl
    intro r hr
    rw [char_term_neg]
    have hadd := char_term_add alpha
      (fun j => f r.1 j) (fun j => -g r.2 j)
    rw [hadd]
    rfl
  calc
    (∑ alpha : Fin k → ZMod L,
      fordBoundaryBlock f alpha * star (fordBoundaryBlock g alpha)) =
        ∑ alpha : Fin k → ZMod L,
          ∑ r : A × B, fordIntegerCharTerm alpha (fun j => f r.1 j - g r.2 j) := by
      apply Finset.sum_congr rfl
      intro alpha ha
      exact hα alpha
    _ = _ := by
      simpa only [sub_eq_zero] using (finite_masked_integer_character_count
        (freq := fun (r : A × B) (j : Fin k) => f r.1 j - g r.2 j) (by
          intro r j
          exact hbound r.1 r.2 j))


/-- The same identity in real form, bounded by the Fourier absolute values. -/
theorem cross_count_le
    {L k : ℕ} [NeZero L] {A B : Type*} [Fintype A] [Fintype B]
    (f : A → Fin k → ℤ) (g : B → Fin k → ℤ)
    (hbound : ∀ a b j, |f a j - g b j| < (L : ℤ)) :
    (Fintype.card {r : A × B // ∀ j, f r.1 j = g r.2 j} : ℝ) ≤
      (∑ alpha : Fin k → ZMod L,
        ‖fordBoundaryBlock f alpha‖ * ‖fordBoundaryBlock g alpha‖) /
        (L : ℝ) ^ k := by
  classical
  have hcount := cross_count f g hbound
  have hL : 0 < (L : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne L))
  have hden : 0 < (L : ℝ) ^ k := pow_pos hL _
  have hterm : ∀ alpha : Fin k → ZMod L,
      ‖fordBoundaryBlock f alpha * star (fordBoundaryBlock g alpha)‖ =
        ‖fordBoundaryBlock f alpha‖ * ‖fordBoundaryBlock g alpha‖ := by
    intro alpha
    rw [norm_mul, norm_star]
  have hnorm :
      ‖∑ alpha : Fin k → ZMod L,
          fordBoundaryBlock f alpha * star (fordBoundaryBlock g alpha)‖ ≤
        ∑ alpha : Fin k → ZMod L,
          ‖fordBoundaryBlock f alpha‖ * ‖fordBoundaryBlock g alpha‖ := by
    calc
      _ ≤ ∑ alpha : Fin k → ZMod L,
          ‖fordBoundaryBlock f alpha * star (fordBoundaryBlock g alpha)‖ :=
        (by simpa using (norm_sum_le (Finset.univ : Finset (Fin k → ZMod L))
          (fun alpha : Fin k → ZMod L =>
            fordBoundaryBlock f alpha * star (fordBoundaryBlock g alpha))))
      _ = _ := by apply Finset.sum_congr rfl; intro alpha ha; exact hterm alpha
  have hleft :
      ‖(L : ℂ) ^ k * Fintype.card {r : A × B // ∀ j, f r.1 j = g r.2 j}‖ =
        (L : ℝ) ^ k * Fintype.card {r : A × B // ∀ j, f r.1 j = g r.2 j} := by
    rw [norm_mul, norm_pow, norm_natCast]
    simp [abs_of_nonneg (le_of_lt hL)]
  rw [hcount] at hnorm
  rw [hleft] at hnorm
  apply (le_div_iff₀ hden).2
  simpa [mul_comm] using hnorm

/-- The energy specialization is obtained from `cross_count` with `g := f`;
this declaration records the exact complex identity used downstream. -/
theorem energy_count_complex
    {L k : ℕ} [NeZero L] {A : Type*} [Fintype A]
    (f : A → Fin k → ℤ)
    (hbound : ∀ a a' j, |f a j - f a' j| < (L : ℤ)) :
    (∑ alpha : Fin k → ZMod L,
      fordBoundaryBlock f alpha * star (fordBoundaryBlock f alpha)) =
      (L : ℂ) ^ k * Fintype.card {r : A × A // ∀ j, f r.1 j = f r.2 j} :=
  cross_count f f hbound

end
end MAPFordBoundaryCrossFourier

#print axioms MAPFordBoundaryCrossFourier.cross_count
#print axioms MAPFordBoundaryCrossFourier.cross_count_le
#print axioms MAPFordBoundaryCrossFourier.energy_count_complex

namespace MAPFordBoundaryCrossFourier
noncomputable section
open MAPFordP16FiniteFourierBridge

/-- Word block factorization: adding a fixed source frequency to the sum of
`s` independent word frequencies factors into one source block and `s` word
blocks. -/
theorem block_product_word
    {L k s : ℕ} [NeZero L] {A U : Type*} [Fintype A] [Fintype U]
    (f : A → Fin k → ℤ) (h : U → Fin k → ℤ)
    (alpha : Fin k → ZMod L) :
    (∑ r : A × (Fin s → U),
      fordIntegerCharTerm alpha
        (fun j => f r.1 j + ∑ i : Fin s, h (r.2 i) j)) =
      fordBoundaryBlock f alpha * (fordBoundaryBlock h alpha) ^ s := by
  classical
  rw [fordBoundaryBlock, fordBoundaryBlock]
  rw [Fintype.sum_pow]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Fintype.sum_prod_type']
  apply Finset.sum_congr rfl
  intro r hr
  rw [char_prod_term_sum]
  rw [← char_term_add]

end
end MAPFordBoundaryCrossFourier

#print axioms MAPFordBoundaryCrossFourier.block_product_word
