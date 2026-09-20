import FordDiscreteCorrelationShift

open scoped BigOperators ComplexConjugate
noncomputable section

namespace FordDiscreteCorrelationNorm

open FordDiscreteShiftIdentity
open FordDiscreteCorrelationShift

/-- The norm of a shifted zero-extended correlation depends only on the
absolute separation of the two shifts. -/
theorem correlation_norm_eq
    {N Q a b : ℕ} (hQ : 1 ≤ Q) (ha : a < Q) (hb : b < Q)
    (f : ℕ → ℂ) :
    ‖∑ r ∈ Finset.range (N + Q - 1),
      zeroExtend N f ((r : ℤ) - a) *
        conj (zeroExtend N f ((r : ℤ) - b))‖ =
      ‖∑ n ∈ Finset.range (N - Nat.dist a b),
        f (n + Nat.dist a b) * conj (f n)‖ := by
  let C : ℕ → ℕ → ℂ := fun x y =>
    ∑ r ∈ Finset.range (N + Q - 1),
      zeroExtend N f ((r : ℤ) - x) *
        conj (zeroExtend N f ((r : ℤ) - y))
  change ‖C a b‖ = _
  rcases le_total a b with hab | hba
  · have h := correlation_shift_identity (N := N) (Q := Q)
        hQ hab hb f
    rw [Nat.dist_eq_sub_of_le hab]
    exact congrArg (fun z : ℂ => ‖z‖) h
  · have h := correlation_shift_identity (N := N) (Q := Q)
        hQ hba ha f
    have hconj : C a b = conj (C b a) := by
      dsimp [C]
      simp [map_sum, map_mul, mul_comm]
    rw [hconj, Complex.norm_conj, Nat.dist_eq_sub_of_le_right hba]
    exact congrArg (fun z : ℂ => ‖z‖) h

/-- The real part of a shifted correlation is bounded by its correlation norm. -/
theorem correlation_real_le_norm
    {N Q a b : ℕ} (hQ : 1 ≤ Q) (ha : a < Q) (hb : b < Q)
    (f : ℕ → ℂ) :
    Complex.re (∑ r ∈ Finset.range (N + Q - 1),
      zeroExtend N f ((r : ℤ) - a) *
        conj (zeroExtend N f ((r : ℤ) - b))) ≤
      ‖∑ r ∈ Finset.range (N + Q - 1),
        zeroExtend N f ((r : ℤ) - a) *
          conj (zeroExtend N f ((r : ℤ) - b))‖ := by
  exact (le_abs_self _).trans (Complex.abs_re_le_norm _)

end FordDiscreteCorrelationNorm

#print axioms FordDiscreteCorrelationNorm.correlation_norm_eq
#print axioms FordDiscreteCorrelationNorm.correlation_real_le_norm
