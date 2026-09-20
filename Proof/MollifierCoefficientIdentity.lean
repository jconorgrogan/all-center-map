import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# The exact truncated Möbius detector coefficient identity

This file formalizes equation (A.3) before any contour shift.  It proves the
literal convolution identity for a Dirichlet character and the vanishing of
the detector coefficients on `1 < n ≤ U`.
-/

namespace MAPMollifierCoefficientIdentity

open scoped ArithmeticFunction.Moebius LSeries.notation BigOperators
open ArithmeticFunction

noncomputable section

/-- The Möbius coefficients cut off at the detector length `U`. -/
def truncatedMoebius (U n : ℕ) : ℂ :=
  if n ≤ U then
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ) n
  else 0

/-- The untwisted coefficient `c_n = sum_{d|n, d≤U} μ(d)`, represented as a
Dirichlet convolution. -/
def mollifierCoeff (U : ℕ) : ℕ → ℂ :=
  (1 : ℕ → ℂ) ⍟ truncatedMoebius U

/-- The finite mollifier, represented by its L-series. -/
def mollifier {q : ℕ} (chi : DirichletCharacter ℂ q) (U : ℕ) (s : ℂ) : ℂ :=
  LSeries (((chi ·) : ℕ → ℂ) * truncatedMoebius U) s

/-- The truncated Möbius sequence is bounded by one. -/
theorem norm_truncatedMoebius_le_one (U n : ℕ) :
    ‖truncatedMoebius U n‖ ≤ 1 := by
  unfold truncatedMoebius
  split_ifs
  · change ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  · simp

/-- Its L-series converges absolutely on `Re s > 1`. -/
theorem LSeriesSummable_truncatedMoebius {U : ℕ} {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (truncatedMoebius U) s := by
  exact LSeriesSummable_of_bounded_of_one_lt_re
    (fun n _ => norm_truncatedMoebius_le_one U n) hs

/-- Exact twisted coefficient factorization. -/
theorem character_convolution_mollifierCoeff {q U : ℕ}
    (chi : DirichletCharacter ℂ q) :
    ((chi ·) : ℕ → ℂ) ⍟ (((chi ·) : ℕ → ℂ) * truncatedMoebius U) =
      ((chi ·) : ℕ → ℂ) * mollifierCoeff U := by
  simpa only [mollifierCoeff, Pi.mul_apply, mul_one] using
    DirichletCharacter.mul_convolution_distrib chi (1 : ℕ → ℂ)
      (truncatedMoebius U)

/-- Equation (A.3): on the absolute-convergence half-plane, multiplying the
Dirichlet L-series by the truncated Möbius mollifier produces the single
Dirichlet series with coefficients `chi(n) * c_n`. -/
theorem LSeries_mul_mollifier_eq {q U : ℕ}
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries ((chi ·) : ℕ → ℂ) s * mollifier chi U s =
      LSeries (((chi ·) : ℕ → ℂ) * mollifierCoeff U) s := by
  have hchi : LSeriesSummable ((chi ·) : ℕ → ℂ) s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re chi hs
  have hmu : LSeriesSummable
      (((chi ·) : ℕ → ℂ) * truncatedMoebius U) s :=
    DirichletCharacter.LSeriesSummable_mul chi
      (LSeriesSummable_truncatedMoebius hs)
  rw [mollifier, ← LSeries_convolution' hchi hmu,
    character_convolution_mollifierCoeff]

/-- The paper-facing version with the analytically continued L-function on the
left. -/
theorem LFunction_mul_mollifier_eq {q U : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction chi s * mollifier chi U s =
      LSeries (((chi ·) : ℕ → ℂ) * mollifierCoeff U) s := by
  rw [DirichletCharacter.LFunction_eq_LSeries chi hs]
  exact LSeries_mul_mollifier_eq chi hs

/-- Expanded divisor-antidiagonal formula for the detector coefficient. -/
theorem mollifierCoeff_apply (U n : ℕ) :
    mollifierCoeff U n =
      ∑ p ∈ n.divisorsAntidiagonal, truncatedMoebius U p.2 := by
  rw [mollifierCoeff, LSeries.convolution_def]
  apply Finset.sum_congr rfl
  intro p hp
  simp

/-- The first detector coefficient is exactly one when `U ≥ 1`. -/
theorem mollifierCoeff_one {U : ℕ} (hU : 1 ≤ U) :
    mollifierCoeff U 1 = 1 := by
  rw [mollifierCoeff_apply]
  simp [truncatedMoebius, hU]

/-- Below the truncation, the truncated coefficient agrees with the full
Möbius coefficient on every divisor. -/
theorem truncatedMoebius_eq_moebius_of_dvd_le
    {U n d : ℕ} (hn : 0 < n) (hnU : n ≤ U) (hd : d ∣ n) :
    truncatedMoebius U d =
      (ArithmeticFunction.moebius : ArithmeticFunction ℂ) d := by
  simp only [truncatedMoebius,
    if_pos (Nat.le_trans (Nat.le_of_dvd hn hd) hnU)]

/-- The detector coefficients vanish throughout `1 < n ≤ U`, exactly as used
in Appendix A. -/
theorem mollifierCoeff_eq_zero_of_one_lt_le
    {U n : ℕ} (hn : 1 < n) (hnU : n ≤ U) :
    mollifierCoeff U n = 0 := by
  rw [mollifierCoeff_apply]
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hn)
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  calc
    (∑ p ∈ n.divisorsAntidiagonal, truncatedMoebius U p.2) =
        ∑ p ∈ n.divisorsAntidiagonal,
          (ArithmeticFunction.moebius : ArithmeticFunction ℂ) p.2 := by
      apply Finset.sum_congr rfl
      intro p hp
      have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
      have hd : p.2 ∣ n :=
        ⟨p.1, by simpa [Nat.mul_comm] using hprod.symm⟩
      exact truncatedMoebius_eq_moebius_of_dvd_le hnpos hnU hd
    _ = ((1 : ℕ → ℂ) ⍟
          (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) n := by
      rw [LSeries.convolution_def]
      apply Finset.sum_congr rfl
      intro p hp
      simp
    _ = 0 := by
      rw [LSeries.one_convolution_eq_zeta_convolution]
      change ((((ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ℕ → ℂ) ⍟
        ((ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ℕ → ℂ)) n) = 0
      rw [ArithmeticFunction.coe_mul]
      rw [ArithmeticFunction.coe_zeta_mul_coe_moebius]
      simp [hn.ne']

end
end MAPMollifierCoefficientIdentity

#print axioms MAPMollifierCoefficientIdentity.LFunction_mul_mollifier_eq
#print axioms MAPMollifierCoefficientIdentity.mollifierCoeff_eq_zero_of_one_lt_le
