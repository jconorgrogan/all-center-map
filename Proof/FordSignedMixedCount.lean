import FordBoundaryAlias
import FordBoundaryCrossFourier

set_option maxHeartbeats 5000000

open scoped BigOperators ZMod ComplexConjugate
open MAPFordBoundaryCrossFourier MAPFordP16FiniteFourierBridge
open MAPFordFiniteFourierCharacterSum

noncomputable section
namespace FordSignedMixedCount

abbrev SignedState (A U : Type*) (n : ℕ) :=
  (A × A) × (Fin n → U)

def signedFrequency
    {A U H : Type*} {d n : ℕ}
    (f : A → Fin d → ℤ) (g : H → U → Fin d → ℤ)
    (hs : Fin n → H) (sign : Fin n → Bool)
    (r : SignedState A U n) : Fin d → ℤ :=
  fun j => f r.1.1 j - f r.1.2 j +
    ∑ i : Fin n, if sign i then g (hs i) (r.2 i) j else -g (hs i) (r.2 i) j

abbrev SignedZero
    {A U H : Type*} {d n : ℕ}
    (f : A → Fin d → ℤ) (g : H → U → Fin d → ℤ)
    (hs : Fin n → H) (sign : Fin n → Bool) :=
  {r : SignedState A U n // ∀ j, signedFrequency f g hs sign r j = 0}

instance signedStateFintype
    {A U : Type*} [Fintype A] [Fintype U] (n : ℕ) :
    Fintype (SignedState A U n) := by
  classical
  unfold SignedState
  infer_instance

instance signedZeroFintype
    {A U H : Type*} [Fintype A] [Fintype U] [Fintype H]
    {d n : ℕ} (f : A → Fin d → ℤ) (g : H → U → Fin d → ℤ)
    (hs : Fin n → H) (sign : Fin n → Bool) :
    Fintype (SignedZero f g hs sign) := by
  classical
  unfold SignedZero
  infer_instance

def signedSourceBlock
    {U H : Type*} [Fintype U] {d n L : ℕ} [NeZero L]
    (g : H → U → Fin d → ℤ) (hs : Fin n → H) (sign : Fin n → Bool)
    (alpha : Fin d → ZMod L) (i : Fin n) : ℂ :=
  if sign i then fordBoundaryBlock (g (hs i)) alpha
  else star (fordBoundaryBlock (g (hs i)) alpha)

private lemma signedSourceBlock_expand
    {U H : Type*} [Fintype U] {d n L : ℕ} [NeZero L]
    (g : H → U → Fin d → ℤ) (hs : Fin n → H) (sign : Fin n → Bool)
    (alpha : Fin d → ZMod L) (i : Fin n) :
    signedSourceBlock g hs sign alpha i =
      ∑ u : U, fordIntegerCharTerm alpha
        (fun j => if sign i then g (hs i) u j else -g (hs i) u j) := by
  by_cases hi : sign i
  · simp [signedSourceBlock, hi, fordBoundaryBlock]
  · simp only [signedSourceBlock, hi, Bool.false_eq_true, if_false,
      fordBoundaryBlock, star_sum]
    apply Finset.sum_congr rfl
    intro u hu
    exact char_term_neg alpha (fun j => g (hs i) u j)

def signedSourceBlockProduct
    {U H : Type*} [Fintype U] {d n L : ℕ} [NeZero L]
    (g : H → U → Fin d → ℤ) (hs : Fin n → H) (sign : Fin n → Bool)
    (alpha : Fin d → ZMod L) : ℂ :=
  ∏ i : Fin n, signedSourceBlock g hs sign alpha i

private lemma signedSourceBlockProduct_expand
    {U H : Type*} [Fintype U] {d n L : ℕ} [NeZero L]
    (g : H → U → Fin d → ℤ) (hs : Fin n → H) (sign : Fin n → Bool)
    (alpha : Fin d → ZMod L) :
    signedSourceBlockProduct g hs sign alpha =
      ∑ v : Fin n → U, fordIntegerCharTerm alpha
        (fun j => ∑ i : Fin n,
          if sign i then g (hs i) (v i) j else -g (hs i) (v i) j) := by
  unfold signedSourceBlockProduct
  simp_rw [signedSourceBlock_expand]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact char_prod_term_sum alpha
    (fun i => fun j => if sign i then g (hs i) (v i) j else -g (hs i) (v i) j)

private lemma baseEnergy_expand
    {A : Type*} [Fintype A] {d L : ℕ} [NeZero L]
    (f : A → Fin d → ℤ) (alpha : Fin d → ZMod L) :
    ((‖fordBoundaryBlock f alpha‖ ^ 2 : ℝ) : ℂ) =
      ∑ r : A × A, fordIntegerCharTerm alpha
        (fun j => f r.1 j - f r.2 j) := by
  unfold fordBoundaryBlock
  rw [norm_sum_expand]
  simp_rw [char_term_neg]
  simp_rw [char_term_add]
  rw [← Fintype.sum_prod_type']
  simp [sub_eq_add_neg]

theorem signed_zero_fourier_identity
    {A U H : Type*} [Fintype A] [Fintype U] [Fintype H]
    {d n L : ℕ} [NeZero L]
    (f : A → Fin d → ℤ) (g : H → U → Fin d → ℤ)
    (hs : Fin n → H) (sign : Fin n → Bool)
    (hbound : ∀ r j, |signedFrequency f g hs sign r j| < (L : ℤ)) :
    (∑ alpha : Fin d → ZMod L,
      ((‖fordBoundaryBlock f alpha‖ ^ 2 : ℝ) : ℂ) *
        signedSourceBlockProduct g hs sign alpha) =
      (L : ℂ) ^ d * Fintype.card (SignedZero f g hs sign) := by
  classical
  have hα : ∀ alpha : Fin d → ZMod L,
      ((‖fordBoundaryBlock f alpha‖ ^ 2 : ℝ) : ℂ) *
          signedSourceBlockProduct g hs sign alpha =
        ∑ r : SignedState A U n,
          fordIntegerCharTerm alpha (signedFrequency f g hs sign r) := by
    intro alpha
    rw [baseEnergy_expand, signedSourceBlockProduct_expand]
    simp_rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    simp_rw [char_term_add]
    rw [← Fintype.sum_prod_type']
    apply Finset.sum_congr rfl
    intro r hr
    rfl
  calc
    (∑ alpha : Fin d → ZMod L,
        ((‖fordBoundaryBlock f alpha‖ ^ 2 : ℝ) : ℂ) *
          signedSourceBlockProduct g hs sign alpha) =
      ∑ alpha : Fin d → ZMod L,
        ∑ r : SignedState A U n,
          fordIntegerCharTerm alpha (signedFrequency f g hs sign r) := by
      apply Finset.sum_congr rfl
      intro alpha halpha
      exact hα alpha
    _ = (L : ℂ) ^ d * Fintype.card (SignedZero f g hs sign) := by
      exact finite_masked_integer_character_count (freq := signedFrequency f g hs sign) hbound

private lemma signedSourceBlock_norm
    {U H : Type*} [Fintype U] {d n L : ℕ} [NeZero L]
    (g : H → U → Fin d → ℤ) (hs : Fin n → H) (sign : Fin n → Bool)
    (alpha : Fin d → ZMod L) (i : Fin n) :
    ‖signedSourceBlock g hs sign alpha i‖ =
      ‖fordBoundaryBlock (g (hs i)) alpha‖ := by
  by_cases hi : sign i <;> simp [signedSourceBlock, hi]

theorem signed_zero_card_le
    {A U H : Type*} [Fintype A] [Fintype U] [Fintype H]
    {d n L : ℕ} [NeZero L]
    (f : A → Fin d → ℤ) (g : H → U → Fin d → ℤ)
    (hs : Fin n → H) (sign : Fin n → Bool)
    (hbound : ∀ r j, |signedFrequency f g hs sign r j| < (L : ℤ)) :
    (Fintype.card (SignedZero f g hs sign) : ℝ) ≤
      (∑ alpha : Fin d → ZMod L,
        (‖fordBoundaryBlock f alpha‖ ^ 2) *
          ∏ i : Fin n, ‖fordBoundaryBlock (g (hs i)) alpha‖) /
        (L : ℝ) ^ d := by
  classical
  have hcount := signed_zero_fourier_identity f g hs sign hbound
  have hterm : ∀ alpha : Fin d → ZMod L,
      ‖((‖fordBoundaryBlock f alpha‖ ^ 2 : ℝ) : ℂ) *
          signedSourceBlockProduct g hs sign alpha‖ =
        (‖fordBoundaryBlock f alpha‖ ^ 2) *
          ∏ i : Fin n, ‖fordBoundaryBlock (g (hs i)) alpha‖ := by
    intro alpha
    rw [norm_mul, Complex.norm_real, signedSourceBlockProduct]
    rw [norm_prod]
    simp_rw [signedSourceBlock_norm]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hnorm :
      ‖∑ alpha : Fin d → ZMod L,
        ((‖fordBoundaryBlock f alpha‖ ^ 2 : ℝ) : ℂ) *
          signedSourceBlockProduct g hs sign alpha‖ ≤
        ∑ alpha : Fin d → ZMod L,
          (‖fordBoundaryBlock f alpha‖ ^ 2) *
            ∏ i : Fin n, ‖fordBoundaryBlock (g (hs i)) alpha‖ := by
    calc
      _ ≤ ∑ alpha : Fin d → ZMod L,
          ‖((‖fordBoundaryBlock f alpha‖ ^ 2 : ℝ) : ℂ) *
            signedSourceBlockProduct g hs sign alpha‖ := by
        exact (norm_sum_le (Finset.univ : Finset (Fin d → ZMod L))
          (fun alpha : Fin d → ZMod L =>
            ((‖fordBoundaryBlock f alpha‖ ^ 2 : ℝ) : ℂ) *
              signedSourceBlockProduct g hs sign alpha))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro alpha halpha
        exact hterm alpha
  have hleft :
      ‖(L : ℂ) ^ d * Fintype.card (SignedZero f g hs sign)‖ =
        (L : ℝ) ^ d * Fintype.card (SignedZero f g hs sign) := by
    rw [norm_mul, norm_pow, norm_natCast]
    simp
  rw [hcount, hleft] at hnorm
  have hL : 0 < (L : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne L))
  apply (le_div_iff₀ (pow_pos hL d)).2
  simpa [mul_comm] using hnorm

end FordSignedMixedCount

#print axioms FordSignedMixedCount.signed_zero_fourier_identity
#print axioms FordSignedMixedCount.signed_zero_card_le
