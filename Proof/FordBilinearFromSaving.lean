import FordSourceWeakBilinear
import FordPositiveIntervalSum
import FordSourceProductFromSaving
import FordCoarseDyadic

open scoped BigOperators
noncomputable section

namespace FordBilinearFromSaving

open FordPolynomialPhase FordSourceWeakBilinear FordWeakBilinear FordWeakCompleteMoment
open FordWEnvelopeScalar FordSourceWProduct FordSourceWEnvelope FordSourceKernelFactor

/-- The positive interval specialization of the weak source bilinear bound,
with the literal coarse dyadic cost, conditional on the explicit finite envelope saving. -/
theorem source_bilinear_from_saving
    (M1 M2 N k : ℕ) (lam z : ℝ)
    (hk : 2000 ≤ k) (hN : 1 ≤ N)
    (hNlarge : 1024 * (k + 1) ^ 2 ≤ N)
    (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2)
    (hM1N : M1 ≤ N)
    (hzlo : (N : ℝ) ≤ z) (hzhi : z ≤ 2 * (N : ℝ))
    (hlo : (N : ℝ) ^ mu1 / 2 ≤ M1)
    (hhi : (M2 : ℝ) ≤ (N : ℝ) ^ mu2)
    (hlam : 0 < lam)
    (hsave : (k : ℝ)^2/51 ≤ FordUniformEnvelope.rawSaving k lam) :
    ‖∑ b0 : Fin M2, ∑ a : Fin M1,
      e (∑ j : Fin k,
        sourceGamma ((N : ℝ) ^ lam) z j.val *
          (((b0.val + 1 : ℕ) : ℝ) ^ (j.val + 1)) *
          (((a.val + 1 : ℕ) : ℝ) ^ (j.val + 1)))‖ ^
        (order k * (2 * order k)) ≤
      (M2 : ℝ) ^ ((order k - 1) * (2 * order k)) *
        (weakCoefficient k ^ 2 * (order k : ℝ) ^ k *
          (M1 : ℝ) ^ (2 * (order k : ℝ) ^ 2 + (k : ℝ) ^ 2 / 1000) *
          (M2 : ℝ) ^ weakExponent (order k) k *
          ((3 : ℝ) ^ k * prefactor (order k) k *
            (N : ℝ) ^ (mu2 * (k : ℝ) * (k + 1) / 2 -
              eps * (mu1 + mu2) * (k : ℝ) ^ 2 - (k : ℝ) ^ 2 / 100))) := by
  let R := FordWeakBilinear.order k
  let q : Fin k → ℕ := fun _ => N
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hscale : 0 < (N : ℝ) ^ lam := by positivity
  have hR : 1 ≤ R := by
    dsimp [R, FordWeakBilinear.order]
    have hk0 : 0 < k := by omega
    nlinarith
  have hq : ∀ j : Fin k, R * M1 ^ (j.val + 1) < 2 ^ q j := by
    intro j
    dsimp [R, q]
    exact FordCoarseDyadic.fixed_order_frequency_lt hNlarge hM1N j
  have hweak := FordSourceWeakBilinear.weak_bilinear_bound_source
    (B := Finset.Icc 1 M2) k M1 M2 N hk hM1 hM2
    (FordPositiveIntervalSum.interval_bounded M2) hN
    ((N : ℝ) ^ lam) z hscale hzlo hzhi q hq
  have hinterval := FordPositiveIntervalSum.sum_interval_eq M2
    (fun b : ℕ => ∑ a : Fin M1,
      e (∑ j : Fin k,
        sourceGamma ((N : ℝ) ^ lam) z j.val *
          (b : ℝ) ^ (j.val + 1) *
          (((a.val + 1 : ℕ) : ℝ) ^ (j.val + 1))) )
  rw [hinterval] at hweak
  have hq' : (∀ j : Fin k, q j = N) := by intro j; rfl
  simp only [q, FordPositiveIntervalSum.card_interval] at hweak
  have hprod := FordSourceProductFromSaving.product_le_saving
    (R := FordWeakBilinear.order k) (M1 := M1) (M2 := M2) (N := N) (k := k)
    (lam := lam) hN hR hM1 hk hlam hsave hlo hhi
  have hbase0 : 0 ≤
      (M2 : ℝ) ^ ((FordWeakBilinear.order k - 1) *
        (2 * FordWeakBilinear.order k)) *
      (weakCoefficient k ^ 2 * (FordWeakBilinear.order k : ℝ) ^ k *
        (M1 : ℝ) ^ (2 * (FordWeakBilinear.order k : ℝ) ^ 2 +
          (k : ℝ) ^ 2 / 1000) *
        (M2 : ℝ) ^ weakExponent (FordWeakBilinear.order k) k) := by positivity
  calc
    _ ≤ (M2 : ℝ) ^ ((FordWeakBilinear.order k - 1) *
          (2 * FordWeakBilinear.order k)) *
        (weakCoefficient k ^ 2 * (FordWeakBilinear.order k : ℝ) ^ k *
          (M1 : ℝ) ^ (2 * (FordWeakBilinear.order k : ℝ) ^ 2 +
            (k : ℝ) ^ 2 / 1000) *
          (M2 : ℝ) ^ weakExponent (FordWeakBilinear.order k) k *
          ∏ j : Fin k,
            ((2 * (N : ℝ) + 1) *
              sourceW (FordWeakBilinear.order k) (FordWeakBilinear.order k)
                M1 M2 (j.val + 1) N ((N : ℝ) ^ lam))) := by
      simpa [FordWeakBilinear.order, hq', q] using hweak
    _ ≤ _ := by
      simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hprod hbase0)


end FordBilinearFromSaving

#print axioms FordBilinearFromSaving.source_bilinear_from_saving
