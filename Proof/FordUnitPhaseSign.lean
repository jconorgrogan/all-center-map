import FordPhaseDifferencing

open scoped BigOperators ComplexConjugate
noncomputable section
namespace FordUnitPhaseSign
open FordUnitPhaseLipschitz

lemma unitPhase_neg (x : ℝ) : unitPhase (-x) = conj (unitPhase x) := by
  unfold unitPhase
  simpa [unitPhase, mul_neg] using
    (Complex.exp_conj (Complex.I * (x : ℂ)))

theorem norm_sum_unitPhase_sign (s : Finset ℕ) (a : ℕ → ℝ) (r : ℕ) :
    ‖∑ i ∈ s, unitPhase (((-1 : ℝ)^r) * a i)‖ =
      ‖∑ i ∈ s, unitPhase (a i)‖ := by
  rcases Nat.even_or_odd r with hr | hr
  · have hpow : (-1 : ℝ)^r = 1 := by norm_num [hr.neg_one_pow]
    simp [hpow]
  · have hpow : (-1 : ℝ)^r = -1 := by norm_num [hr.neg_one_pow]
    rw [hpow]
    simp only [neg_one_mul]
    have hsum : (∑ i ∈ s, unitPhase (-a i)) =
        conj (∑ i ∈ s, unitPhase (a i)) := by
      simp_rw [unitPhase_neg]
      rw [map_sum]
    rw [hsum, Complex.norm_conj]

end FordUnitPhaseSign
#print axioms FordUnitPhaseSign.unitPhase_neg
#print axioms FordUnitPhaseSign.norm_sum_unitPhase_sign
