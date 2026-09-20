import FordBilinearFromSaving
import FordBilinearNormalization
import FordScaleCancellation
import FordSourceWPrefactor

open scoped BigOperators
open FordSourceWeakBilinear FordWeakBilinear
open FordWeakCompleteMoment FordWEnvelopeScalar FordSourceWPrefactor FordSourceWProduct
  FordPolynomialPhase
open FordScaleCancellation FordBilinearNormalization

namespace FordNormalizedDyadicBilinear
noncomputable section

/-- Scalar form of the normalization step.  This isolates the finite source
bound from the subsequent scale estimate: `q` is the remaining positive
scale factor, `c` is its nonnegative coefficient, and `s` is the desired
post-cancellation majorant. -/
theorem scalar_normalized_bound {R k : ℕ} {x y q c s : ℝ}
    (hR : 1 ≤ R) (hx : 0 < x) (hy : 0 < y)
    (hc : 0 ≤ c)
    (hs : x ^ (eps * (k : ℝ) ^ 2) * y ^ (-deficit k) * q ≤ s) :
    y ^ ((R - 1) * (2 * R)) *
        (c * x ^ (2 * (R : ℝ) ^ 2 + (k : ℝ) ^ 2 / 1000) *
          y ^ weakExponent R k * q) /
          (x * y) ^ (R * (2 * R)) ≤ c * s := by
  have hnorm := normalize_powers (k := k) hR hx hy
  have hden : 0 < (x * y) ^ (R * (2 * R)) := by positivity
  apply (div_le_iff₀ hden).2
  calc
    y ^ ((R - 1) * (2 * R)) *
          (c * x ^ (2 * (R : ℝ) ^ 2 + (k : ℝ) ^ 2 / 1000) *
            y ^ weakExponent R k * q) =
        c * (x ^ (eps * (k : ℝ) ^ 2) * y ^ (-deficit k) * q) *
          (x * y) ^ (R * (2 * R)) := by
      calc
        _ = c * q * (y ^ ((R - 1) * (2 * R)) *
            (x ^ (2 * (R : ℝ) ^ 2 + (k : ℝ) ^ 2 / 1000) *
              y ^ weakExponent R k)) := by ring
        _ = c * q * ((x * y) ^ (R * (2 * R)) *
            (x ^ (eps * (k : ℝ) ^ 2) * y ^ (-deficit k))) := by
          rw [hnorm]
        _ = _ := by ring
    _ ≤ c * s * (x * y) ^ (R * (2 * R)) := by
      gcongr


theorem normalized_bound_from_saving
    (M1 M2 N k : ℕ) (lam z : ℝ)
    (hk : 2000 ≤ k) (hN : 1 ≤ N)
    (hNlarge : 1024 * (k + 1) ^ 2 ≤ N)
    (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2) (hM1N : M1 ≤ N)
    (hM1scale : (M1 : ℝ) ≤ (N : ℝ) ^ mu1)
    (hM2scale : (N : ℝ) ^ mu2 / 2 ≤ (M2 : ℝ))
    (hzlo : (N : ℝ) ≤ z) (hzhi : z ≤ 2 * (N : ℝ))
    (hlo : (N : ℝ) ^ mu1 / 2 ≤ M1)
    (hhi : (M2 : ℝ) ≤ (N : ℝ) ^ mu2)
    (hlam : 0 < lam)
    (hsave : (k : ℝ)^2 / 51 ≤ FordUniformEnvelope.rawSaving k lam) :
    let R := FordWeakBilinear.order k
    let U := ∑ b0 : Fin M2, ∑ a : Fin M1,
      e (∑ j : Fin k,
        FordSourceWeakBilinear.sourceGamma ((N : ℝ) ^ lam) z j.val *
          (((b0.val + 1 : ℕ) : ℝ) ^ (j.val + 1)) *
          (((a.val + 1 : ℕ) : ℝ) ^ (j.val + 1)))
    (‖U‖ / ((M1 : ℝ) * M2)) ^ (R * (2 * R)) ≤
      weakCoefficient k ^ 2 * (R : ℝ) ^ k * (3 : ℝ) ^ k *
        prefactor R k * (2 : ℝ) ^ (deficit k) *
          (N : ℝ) ^ (- (k : ℝ) ^ 2 / 100) := by
  dsimp
  let R := FordWeakBilinear.order k
  have hR : 1 ≤ R := by
    dsimp [R, FordWeakBilinear.order]
    have hk0 : 0 < k := by omega
    nlinarith
  have hsource := FordBilinearFromSaving.source_bilinear_from_saving
    M1 M2 N k lam z hk hN hNlarge hM1 hM2 hM1N hzlo hzhi hlo hhi hlam hsave
  have hden0 : 0 < ((M1 : ℝ) * M2) ^ (R * (2 * R)) := by positivity
  have hdiv := div_le_div_of_nonneg_right hsource (le_of_lt hden0)
  rw [div_pow]
  calc
    ‖∑ b0 : Fin M2, ∑ a : Fin M1,
        e (∑ j : Fin k,
          FordSourceWeakBilinear.sourceGamma ((N : ℝ) ^ lam) z j.val *
            (((b0.val + 1 : ℕ) : ℝ) ^ (j.val + 1)) *
            (((a.val + 1 : ℕ) : ℝ) ^ (j.val + 1)))‖ ^
          (R * (2 * R)) / ((M1 : ℝ) * M2) ^ (R * (2 * R)) ≤ _ := by
            simpa [R] using hdiv
    _ = (weakCoefficient k ^ 2 * (R : ℝ) ^ k * (3 : ℝ) ^ k *
          prefactor R k) *
        ((M1 : ℝ) ^ (eps * (k : ℝ) ^ 2) *
          (M2 : ℝ) ^ (-deficit k) *
          (N : ℝ) ^ (mu2 * (k : ℝ) * (k + 1) / 2 -
            eps * (mu1 + mu2) * (k : ℝ) ^ 2 - (k : ℝ) ^ 2 / 100)) := by
      have hnorm := normalize_powers (k := k) hR (by positivity : 0 < (M1 : ℝ))
        (by positivity : 0 < (M2 : ℝ))
      have hfrac :
          (M2 : ℝ) ^ ((R - 1) * (2 * R)) /
              ((M1 : ℝ) * M2) ^ (R * (2 * R)) *
              ((M1 : ℝ) ^ (2 * (R : ℝ) ^ 2 + (k : ℝ) ^ 2 / 1000) *
                (M2 : ℝ) ^ weakExponent R k) =
            (M1 : ℝ) ^ (eps * (k : ℝ) ^ 2) *
              (M2 : ℝ) ^ (-deficit k) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_iff hden0.ne').2
        simpa [mul_assoc, mul_left_comm, mul_comm] using hnorm
      rw [div_eq_iff hden0.ne']
      calc
        _ = (weakCoefficient k ^ 2 * (R : ℝ) ^ k * (3 : ℝ) ^ k *
              prefactor R k *
              (N : ℝ) ^ (mu2 * (k : ℝ) * (k + 1) / 2 -
                eps * (mu1 + mu2) * (k : ℝ) ^ 2 - (k : ℝ) ^ 2 / 100)) *
            ((M2 : ℝ) ^ ((R - 1) * (2 * R)) *
              ((M1 : ℝ) ^ (2 * (R : ℝ) ^ 2 + (k : ℝ) ^ 2 / 1000) *
                (M2 : ℝ) ^ weakExponent R k)) := by
          simp [R]
          ring
        _ = (weakCoefficient k ^ 2 * (R : ℝ) ^ k * (3 : ℝ) ^ k *
              prefactor R k *
              (N : ℝ) ^ (mu2 * (k : ℝ) * (k + 1) / 2 -
                eps * (mu1 + mu2) * (k : ℝ) ^ 2 - (k : ℝ) ^ 2 / 100)) *
            (((M1 : ℝ) * M2) ^ (R * (2 * R)) *
              ((M1 : ℝ) ^ (eps * (k : ℝ) ^ 2) *
                (M2 : ℝ) ^ (-deficit k))) := by
          rw [hnorm]
        _ = _ := by ring
    _ ≤ (weakCoefficient k ^ 2 * (R : ℝ) ^ k * (3 : ℝ) ^ k *
          prefactor R k) * ((2 : ℝ) ^ (deficit k) *
            (N : ℝ) ^ (- (k : ℝ) ^ 2 / 100)) := by
      apply mul_le_mul_of_nonneg_left
        (FordScaleCancellation.scale_cancellation hN hM1scale hM2scale)
      unfold prefactor FordSourceWEnvelope.coeff
      positivity
    _ = _ := by ring

end
end FordNormalizedDyadicBilinear

#print axioms FordNormalizedDyadicBilinear.normalized_bound_from_saving
