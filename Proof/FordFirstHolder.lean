import Mathlib

open scoped BigOperators
noncomputable section
namespace FordFirstHolder

theorem exists_unit_phase_holder {B : Type*} [Fintype B]
    (Z : B → ℂ) (r : ℕ) (hr : 1 ≤ r) :
    ∃ eps : B → ℂ, (∀ b, ‖eps b‖ = 1) ∧
      ‖∑ b, Z b‖ ^ r ≤ (Fintype.card B : ℝ) ^ (r - 1) *
        ‖∑ b, eps b * (Z b) ^ r‖ := by
  classical
  choose eps heps hphase using fun b => Complex.exists_norm_eq_mul_self ((Z b) ^ r)
  refine ⟨eps, heps, ?_⟩
  have hsum : ∑ b, eps b * (Z b) ^ r =
      ((∑ b, ‖Z b‖ ^ r : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro b hb
    simpa only [norm_pow, Complex.ofReal_pow] using (hphase b).symm
  have hpos : 0 ≤ ∑ b, ‖Z b‖ ^ r :=
    Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _)
  have hnorm : ‖∑ b, eps b * (Z b) ^ r‖ = ∑ b, ‖Z b‖ ^ r := by
    rw [hsum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
  rw [hnorm]
  have hp := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := (Finset.univ : Finset B)) (f := fun b => ‖Z b‖) (p := (r : ℝ))
    (by exact_mod_cast hr) (fun _ _ => norm_nonneg _)
  have hexp : (r : ℝ) - 1 = ((r - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hr]
    norm_num
  simp only [hexp, Real.rpow_natCast, Finset.card_univ] at hp
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) r).trans hp

end FordFirstHolder
#print axioms FordFirstHolder.exists_unit_phase_holder
