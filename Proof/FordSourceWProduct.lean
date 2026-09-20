import FordSourceWEnvelope
import FordEnvelopeRescale
import FordUniformEnvelope
import FordScaleFloor
open scoped BigOperators
open FordSourceKernelFactor FordSourceWEnvelope FordWEnvelopeScalar FordUniformEnvelope
noncomputable section
namespace FordSourceWProduct

def prefactor (R k : ℕ) : ℝ := ∏ j : Fin k, coeff R (j.val+1)

lemma exponent_sum (k : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    (∑ j : Fin k, exponent (j.val+1) lam) = envelopeSum k lam := by
  simp_rw [exponent, FordEnvelopeRescale.min_max_rescale hlam]
  unfold envelopeSum
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => lam * envelope (((j+1 : ℕ) : ℝ)/lam)) k

theorem product_le {R M1 M2 N k : ℕ} {lam : ℝ}
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hM1 : 1 ≤ M1) (hlam : 0 < lam)
    (hlo : (N : ℝ)^mu1/2 ≤ M1) (hhi : (M2 : ℝ) ≤ (N : ℝ)^mu2) :
    (∏ j : Fin k, sourceW R R M1 M2 (j.val+1) N ((N : ℝ)^lam)) ≤
      prefactor R k * (N : ℝ)^(envelopeSum k lam) := by
  have hn0 : (0 : ℝ) < N := by positivity
  calc
    _ ≤ ∏ j : Fin k, (coeff R (j.val+1)*(N : ℝ)^(exponent (j.val+1) lam)) := by
      apply Finset.prod_le_prod
      · intro j hj
        unfold sourceW sourceC
        positivity
      · intro j hj
        exact sourceW_le_power hN (by omega) hR hM1 hlo hhi
    _ = prefactor R k * (∏ j : Fin k, (N : ℝ)^(exponent (j.val+1) lam)) := by
      rw [Finset.prod_mul_distrib]; rfl
    _ = _ := by rw [← Real.rpow_sum_of_pos hn0, exponent_sum k hlam]

theorem product_le_saving {R M1 M2 N k : ℕ} {lam : ℝ}
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hM1 : 1 ≤ M1) (hk : 2000 ≤ k)
    (hlow : b*(k : ℝ) ≤ lam) (hupp : lam ≤ b*(k : ℝ)+1)
    (hlo : (N : ℝ)^mu1/2 ≤ M1) (hhi : (M2 : ℝ) ≤ (N : ℝ)^mu2) :
    (∏ j : Fin k, sourceW R R M1 M2 (j.val+1) N ((N : ℝ)^lam)) ≤
      prefactor R k * (N : ℝ)^(mu2*(k : ℝ)*(k+1)/2 -
        eps*(mu1+mu2)*(k : ℝ)^2 - (k : ℝ)^2/50) := by
  have hlam : 0 < lam := by
    have hkR : (2000 : ℝ) ≤ k := by exact_mod_cast hk
    norm_num [b] at hlow
    linarith
  apply (product_le hN hR hM1 hlam hlo hhi).trans
  apply mul_le_mul_of_nonneg_left _ (by unfold prefactor coeff; positivity)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
  have hs := raw_saving_ge_target hk hlow hupp
  unfold rawSaving at hs
  linarith only [hs]

theorem floor_product_le_saving {R N k : ℕ} {lam : ℝ}
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hk : 2000 ≤ k)
    (hlow : b*(k : ℝ) ≤ lam) (hupp : lam ≤ b*(k : ℝ)+1) :
    (∏ j : Fin k, sourceW R R (FordScaleFloor.scale N mu1)
      (FordScaleFloor.scale N mu2) (j.val+1) N ((N : ℝ)^lam)) ≤
      prefactor R k * (N : ℝ)^(mu2*(k : ℝ)*(k+1)/2 -
        eps*(mu1+mu2)*(k : ℝ)^2 - (k : ℝ)^2/50) := by
  obtain ⟨h1,h2,hlo,hhi,hbase1,hbase2⟩ := FordScaleFloor.ford_scales hN
  exact product_le_saving hN hR h1 hk hlow hupp hlo hhi
end FordSourceWProduct
#print axioms FordSourceWProduct.product_le_saving
#print axioms FordSourceWProduct.floor_product_le_saving
