import FordBoundaryWeightedHolder
import FordBoundaryCountGeometry
import FordBoundaryCrossFourier
import FordBoundaryPinnedCross

open scoped BigOperators ZMod ComplexConjugate

namespace FordBoundaryEnergyMoments

open FordBoundaryCountGeometry
open FordBoundaryWeightedHolder
open MAPFordBoundaryCrossFourier

noncomputable section

private theorem complex_self_cross_re (z : ℂ) :
    (z * star z).re = ‖z‖ ^ 2 := by
  have hz : z * star z = (Complex.normSq z : ℂ) := by
    simpa [Complex.star_def] using Complex.mul_conj z
  rw [hz]
  change Complex.normSq z = ‖z‖ ^ 2
  exact Complex.normSq_eq_norm_sq z

private theorem complex_nat_pow_re (L k : ℕ) :
    ((L : ℂ) ^ k).re = (L : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Complex.mul_re]
      simpa [pow_succ, ih, Nat.succ_eq_add_one]

private theorem complex_nat_pow_im (L k : ℕ) :
    ((L : ℂ) ^ k).im = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Complex.mul_im]
      simpa [pow_succ, ih, Nat.succ_eq_add_one]

private def base_equiv
    {k : ℕ} {A : Type*} [Fintype A]
    (f : A → Fin k → ℤ) :
    {r : A × A // ∀ j, f r.1 j = f r.2 j} ≃ BaseZero f :=
  { toFun := fun r => ⟨r.1, funext r.2⟩
    invFun := fun r => ⟨r.1, fun j => congrFun r.2 j⟩
    left_inv := by intro r; rfl
    right_inv := by intro r; rfl }

private theorem base_fourier_sum
    {L k : ℕ} [NeZero L] {A : Type*} [Fintype A]
    (f : A → Fin k → ℤ)
    (hbound : ∀ a b j, |f a j - f b j| < (L : ℤ)) :
    (∑ alpha : Fin k → ZMod L, ‖fordBoundaryBlock f alpha‖ ^ 2) =
      (L : ℝ) ^ k * Fintype.card (BaseZero f) := by
  have hc := energy_count_complex f hbound
  have hr := congrArg Complex.re hc
  calc
    (∑ alpha : Fin k → ZMod L, ‖fordBoundaryBlock f alpha‖ ^ 2) =
        ∑ alpha : Fin k → ZMod L,
          (fordBoundaryBlock f alpha *
            star (fordBoundaryBlock f alpha)).re := by
      apply Finset.sum_congr rfl
      intro alpha halpha
      exact (complex_self_cross_re (fordBoundaryBlock f alpha)).symm
    _ = (∑ alpha : Fin k → ZMod L,
        fordBoundaryBlock f alpha * star (fordBoundaryBlock f alpha)).re := by
      symm
      simpa using (map_sum Complex.reCLM
        (fun alpha : Fin k → ZMod L =>
          fordBoundaryBlock f alpha * star (fordBoundaryBlock f alpha))
        Finset.univ)
    _ = ((L : ℂ) ^ k *
        Fintype.card {r : A × A // ∀ j, f r.1 j = f r.2 j}).re := hr
    _ = ((L : ℂ) ^ k * Fintype.card (BaseZero f)).re := by
      rw [Fintype.card_congr (base_equiv f)]
    _ = (L : ℝ) ^ k * Fintype.card (BaseZero f) := by
      rw [Complex.mul_re, complex_nat_pow_re, complex_nat_pow_im]
      simp

theorem base_card_eq_fordB
    {L k : ℕ} [NeZero L] {A : Type*} [Fintype A]
    (f : A → Fin k → ℤ)
    (hbound : ∀ a b j, |f a j - f b j| < (L : ℤ)) :
    (Fintype.card (BaseZero f) : ℝ) =
      fordAvg (fun alpha : Fin k → ZMod L =>
        ‖fordBoundaryBlock f alpha‖ ^ 2) := by
  have hsum := base_fourier_sum f hbound
  have hcardBase :
      Fintype.card {r : A × A // ∀ j, f r.1 j = f r.2 j} =
        Fintype.card (BaseZero f) := Fintype.card_congr (base_equiv f)
  have hcard : Fintype.card (Fin k → ZMod L) = L ^ k := by
    simp
  have hL : (L : ℝ) ^ k ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast (NeZero.ne L))
  have hden : (L ^ k : ℕ) ≠ 0 := pow_ne_zero _ (NeZero.ne L)
  rw [fordAvg, Finset.expect_eq_sum_div_card, Finset.card_univ, hcard]
  rw [hsum]
  have hcast : ((L ^ k : ℕ) : ℝ) = (L : ℝ) ^ k := by
    norm_num
  rw [hcast]
  field_simp [hden]

private theorem wordFreq_block_eq
    {L k s : ℕ} [NeZero L] {A U : Type*} [Fintype A] [Fintype U]
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (alpha : Fin k → ZMod L) :
    fordBoundaryBlock (FordBoundaryPinnedCross.wordFreq f g s) alpha =
      fordBoundaryBlock f alpha * (fordBoundaryBlock g alpha) ^ s := by
  simpa only [fordBoundaryBlock, FordBoundaryPinnedCross.wordFreq] using!
    block_product_word f g alpha

private def energy_equiv
    {k s : ℕ} {A U : Type*} [Fintype A] [Fintype U]
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) :
    {r : (A × (Fin s → U)) × (A × (Fin s → U)) //
        ∀ j, FordBoundaryPinnedCross.wordFreq f g s r.1 j =
          FordBoundaryPinnedCross.wordFreq f g s r.2 j} ≃
      EnergyZero f g s := by
  let E := {r : (A × (Fin s → U)) × (A × (Fin s → U)) //
      ∀ j, FordBoundaryPinnedCross.wordFreq f g s r.1 j =
        FordBoundaryPinnedCross.wordFreq f g s r.2 j}
  let T := EnergyZero f g s
  let toT : E → T := fun r =>
    ⟨r.1, by
      apply funext
      intro j
      simpa [FordBoundaryPinnedCross.wordFreq, Finset.sum_apply] using r.2 j⟩
  let toE : T → E := fun r =>
    ⟨r.1, by
      intro j
      simpa [FordBoundaryPinnedCross.wordFreq, Finset.sum_apply] using congrFun r.2 j⟩
  have hleft : Function.LeftInverse toE toT := by
    intro r
    apply Subtype.ext
    rfl
  have hright : Function.RightInverse toE toT := by
    intro r
    apply Subtype.ext
    rfl
  exact Equiv.ofBijective toT ⟨hleft.injective, hright.surjective⟩

theorem energy_card_eq_fordA
    {L k s : ℕ} [NeZero L] {A U : Type*} [Fintype A] [Fintype U]
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (hbound : ∀ r r' j,
      |FordBoundaryPinnedCross.wordFreq f g s r j -
        FordBoundaryPinnedCross.wordFreq f g s r' j| < (L : ℤ)) :
    (Fintype.card (EnergyZero f g s) : ℝ) =
      fordA (fun alpha : Fin k → ZMod L =>
        ‖fordBoundaryBlock f alpha‖ ^ 2)
        (fun alpha : Fin k → ZMod L =>
          ‖fordBoundaryBlock g alpha‖) s := by
  let F : (A × (Fin s → U)) → Fin k → ℤ :=
    FordBoundaryPinnedCross.wordFreq f g s
  have hc := energy_count_complex F hbound
  have hr := congrArg Complex.re hc
  have hcardEq :
      Fintype.card {r : (A × (Fin s → U)) × (A × (Fin s → U)) //
        ∀ j, F r.1 j = F r.2 j} = Fintype.card (EnergyZero f g s) := by
    exact Fintype.card_congr (energy_equiv f g)
  have hsum :
      (∑ alpha : Fin k → ZMod L,
        ‖fordBoundaryBlock f alpha‖ ^ 2 *
          ‖fordBoundaryBlock g alpha‖ ^ (2 * s)) =
        (L : ℝ) ^ k * Fintype.card (EnergyZero f g s) := by
    calc
      (∑ alpha : Fin k → ZMod L,
        ‖fordBoundaryBlock f alpha‖ ^ 2 *
          ‖fordBoundaryBlock g alpha‖ ^ (2 * s)) =
          ∑ alpha : Fin k → ZMod L,
            ‖fordBoundaryBlock F alpha‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro alpha halpha
        rw [wordFreq_block_eq f g alpha]
        rw [norm_mul, norm_pow]
        ring
      _ = ∑ alpha : Fin k → ZMod L,
          (fordBoundaryBlock F alpha *
            star (fordBoundaryBlock F alpha)).re := by
        apply Finset.sum_congr rfl
        intro alpha halpha
        exact (complex_self_cross_re (fordBoundaryBlock F alpha)).symm
      _ = (∑ alpha : Fin k → ZMod L,
          fordBoundaryBlock F alpha * star (fordBoundaryBlock F alpha)).re := by
        symm
        simpa using (map_sum Complex.reCLM
          (fun alpha : Fin k → ZMod L =>
            fordBoundaryBlock F alpha * star (fordBoundaryBlock F alpha))
          Finset.univ)
      _ = ((L : ℂ) ^ k *
          Fintype.card {r : (A × (Fin s → U)) × (A × (Fin s → U)) //
            ∀ j, F r.1 j = F r.2 j}).re := hr
      _ = (L : ℝ) ^ k * Fintype.card (EnergyZero f g s) := by
        rw [hcardEq]
        rw [Complex.mul_re, complex_nat_pow_re, complex_nat_pow_im]
        simp
  have hcard : Fintype.card (Fin k → ZMod L) = L ^ k := by
    simp
  have hL : (L : ℝ) ^ k ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast (NeZero.ne L))
  have hden : (L ^ k : ℕ) ≠ 0 := pow_ne_zero _ (NeZero.ne L)
  rw [fordA, fordAvg, Finset.expect_eq_sum_div_card, Finset.card_univ, hcard]
  rw [hsum]
  have hcast : ((L ^ k : ℕ) : ℝ) = (L : ℝ) ^ k := by
    norm_num
  rw [hcast]
  field_simp [hden]

end
end FordBoundaryEnergyMoments

#print axioms FordBoundaryEnergyMoments.base_card_eq_fordB
#print axioms FordBoundaryEnergyMoments.energy_card_eq_fordA
