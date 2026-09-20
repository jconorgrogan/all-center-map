import FordPolynomialPhase

open scoped BigOperators ComplexConjugate
noncomputable section
namespace FordPhaseMoment
open FordPolynomialPhase

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma conj_e (x : ℝ) : conj (e x) = e (-x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma prod_e {A : Type*} [Fintype A] (f : A → ℝ) :
    (∏ a, e (f a)) = e (∑ a, f a) := by
  unfold e
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]

lemma norm_sum_even_pow {B : Type*} [Fintype B] (Z : B → ℂ) (s : ℕ) :
    ((‖∑ b, Z b‖ ^ (2 * s) : ℝ) : ℂ) =
      ∑ x : Fin s → B, ∑ y : Fin s → B,
        (∏ i, Z (x i)) * conj (∏ i, Z (y i)) := by
  have h : ‖∑ b, Z b‖ ^ (2 * s) = ‖(∑ b, Z b) ^ s‖ ^ 2 := by
    rw [norm_pow, ← pow_mul]
    congr 1
    omega
  rw [h, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj,
    Fintype.sum_pow, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]

/-- Finite even moment after cancelling all unit weights outside the frequency sum. -/
theorem unit_weight_moment_bound {B C : Type*} [Fintype B] [Fintype C]
    (a : B → ℂ) (ha : ∀ b, ‖a b‖ = 1) (phase : C → B → ℝ) (s : ℕ) :
    (∑ c, ‖∑ b, a b * e (phase c b)‖ ^ (2 * s)) ≤
      ∑ x : Fin s → B, ∑ y : Fin s → B,
        ‖∑ c, e ((∑ i, phase c (x i)) - (∑ i, phase c (y i)))‖ := by
  classical
  let w : (Fin s → B) → ℂ := fun x => ∏ i, a (x i)
  have hw : ∀ x, ‖w x‖ = 1 := by
    intro x
    simp [w, norm_prod, ha]
  have hterm (c : C) (x y : Fin s → B) :
      (∏ i, a (x i) * e (phase c (x i))) *
        conj (∏ i, a (y i) * e (phase c (y i))) =
      (w x * conj (w y)) * e ((∑ i, phase c (x i)) - (∑ i, phase c (y i))) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, prod_e, prod_e, map_mul,
      conj_e, sub_eq_add_neg, e_add]
    dsimp [w]
    ring
  have heq : ((∑ c, ‖∑ b, a b * e (phase c b)‖ ^ (2 * s) : ℝ) : ℂ) =
      ∑ x : Fin s → B, ∑ y : Fin s → B,
        (w x * conj (w y)) *
          (∑ c, e ((∑ i, phase c (x i)) - (∑ i, phase c (y i)))) := by
    rw [Complex.ofReal_sum]
    simp_rw [norm_sum_even_pow, hterm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.mul_sum]
  have hnonneg : 0 ≤ ∑ c, ‖∑ b, a b * e (phase c b)‖ ^ (2 * s) := by
    positivity
  have hn := congrArg norm heq
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hn
  rw [hn]
  calc
    _ ≤ ∑ x : Fin s → B, ‖∑ y : Fin s → B, (w x * conj (w y)) *
        (∑ c, e ((∑ i, phase c (x i)) - (∑ i, phase c (y i))))‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x hx
      have htri := norm_sum_le (Finset.univ : Finset (Fin s → B))
        (fun y => (w x * conj (w y)) *
          (∑ c, e ((∑ i, phase c (x i)) - (∑ i, phase c (y i)))))
      simpa only [norm_mul, Complex.norm_conj, hw, one_mul, mul_one] using htri

end FordPhaseMoment
#print axioms FordPhaseMoment.unit_weight_moment_bound
