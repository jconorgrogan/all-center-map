import FordSourceWProduct
import FordCoarseDyadic
open scoped BigOperators
open FordSourceKernelFactor FordSourceWEnvelope FordSourceWProduct FordWEnvelopeScalar FordUniformEnvelope
noncomputable section
namespace FordSourceProductFromSaving

theorem product_le_saving {R M1 M2 N k : ℕ} {lam : ℝ}
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hM1 : 1 ≤ M1) (hk : 2000 ≤ k)
    (hlam : 0 < lam) (hsave : (k : ℝ)^2/51 ≤ rawSaving k lam)
    (hlo : (N : ℝ)^mu1/2 ≤ M1) (hhi : (M2 : ℝ) ≤ (N : ℝ)^mu2) :
    (∏ j : Fin k, ((2*(N : ℝ)+1)*sourceW R R M1 M2 (j.val+1) N ((N : ℝ)^lam))) ≤
      (3 : ℝ)^k * prefactor R k * (N : ℝ)^(mu2*(k : ℝ)*(k+1)/2 -
        eps*(mu1+mu2)*(k : ℝ)^2 - (k : ℝ)^2/100) := by
  have hn0 : (0 : ℝ) < N := by positivity
  have hw := FordSourceWProduct.product_le (k := k) hN hR hM1 hlam hlo hhi
  have hq := FordCoarseDyadic.dyadic_cost_le k N hN
  have hp0 : 0 ≤ (∏ j : Fin k, sourceW R R M1 M2 (j.val+1) N ((N : ℝ)^lam)) := by
    apply Finset.prod_nonneg
    intro j hj
    unfold sourceW sourceC
    positivity
  have hc0 : 0 ≤ prefactor R k := by unfold prefactor coeff; positivity
  have hexp : envelopeSum k lam + (k : ℝ) ≤ mu2*(k : ℝ)*(k+1)/2 -
      eps*(mu1+mu2)*(k : ℝ)^2 - (k : ℝ)^2/100 := by
    have hkR : (2000 : ℝ) ≤ k := by exact_mod_cast hk
    have hpay : (k : ℝ)^2/100 + k ≤ (k : ℝ)^2/51 := by
      nlinarith [sq_nonneg ((k : ℝ)-2000)]
    unfold rawSaving at hsave
    linarith only [hsave, hpay]
  rw [Finset.prod_mul_distrib]
  calc
    _ ≤ ((3 : ℝ)^k*(N : ℝ)^k) * (prefactor R k*(N : ℝ)^(envelopeSum k lam)) :=
      mul_le_mul hq hw hp0 (by positivity)
    _ = (3 : ℝ)^k*prefactor R k*(N : ℝ)^(envelopeSum k lam+(k : ℝ)) := by
      rw [Real.rpow_add hn0, Real.rpow_natCast]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hexp) (by positivity)
end FordSourceProductFromSaving
#print axioms FordSourceProductFromSaving.product_le_saving
