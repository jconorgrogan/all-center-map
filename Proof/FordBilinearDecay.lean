import FordNormalizedDyadicBilinear
import FordBinaryPrefactorCost
import FordBinaryAbsorption
import FordPowerExtraction
import FordDecayExponent
import FordNextDegreeEnvelope
open scoped BigOperators
noncomputable section
namespace FordBilinearDecay
open FordWEnvelopeScalar FordScaleFloor FordPolynomialPhase FordSourceWeakBilinear
open FordBinaryPrefactorCost FordDecayExponent

/-- Actual source double sum at ordinary floor scales, with all scalar premises discharged. -/
theorem floor_bilinear_decay {N k : ℕ} {lam z : ℝ}
    (hN : 1 ≤ N) (hlam : 2000*b ≤ lam)
    (hdegree : k = Nat.floor (lam/b)+1)
    (hNlarge : 1024*(k+1)^2 ≤ N)
    (hlog : 1000000000000*(k : ℝ)^4 ≤ Real.log N)
    (hzlo : (N : ℝ) ≤ z) (hzhi : z ≤ 2*(N : ℝ)) :
    ‖∑ b0 : Fin (scale N mu2), ∑ a : Fin (scale N mu1),
      e (∑ j : Fin k, sourceGamma ((N : ℝ)^lam) z j.val *
        (((b0.val+1 : ℕ) : ℝ)^(j.val+1)) *
        (((a.val+1 : ℕ) : ℝ)^(j.val+1)))‖ ≤
      ((scale N mu1 : ℝ)*scale N mu2)*(N : ℝ)^(-decay k) := by
  obtain ⟨hk',_,_⟩ := FordNextDegreeEnvelope.floor_next_degree_slab hlam
  have hk : 2000 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hn0 : (0 : ℝ) < N := by positivity
  have hlam0 : 0 < lam := by norm_num [b] at hlam; linarith
  obtain ⟨hM1,hM2,hlo,hhi,hM1N,_⟩ := ford_scales hN
  have hm1 := scale_comparable (mu := mu1) hN (by norm_num)
  have hm2 := scale_comparable (mu := mu2) hN (by norm_num)
  have hs : (k : ℝ)^2/51 ≤ FordUniformEnvelope.rawSaving k lam := by
    rw [hdegree]
    exact FordNextDegreeEnvelope.raw_saving_floor_next_degree hlam
  have hn := FordNormalizedDyadicBilinear.normalized_bound_from_saving
    (scale N mu1) (scale N mu2) N k lam z hk hN hNlarge hM1 hM2 hM1N
    hm1.2.1 hm2.2.2 hzlo hzhi hlo hhi hlam0 hs
  have hc := FordBinaryAbsorption.absorb hn0 hlog (binary_prefactor_cost_le hk)
  have hp := hn.trans hc
  have hm : 0 < FordWeakBilinear.order k*(2*FordWeakBilinear.order k) := by
    unfold FordWeakBilinear.order
    positivity
  have he := FordPowerExtraction.extract (a := (k : ℝ)^2/200) hn0 hm (by
    convert hp using 1 <;> congr 1 <;> ring)
  have hexp : -((k : ℝ)^2/200) /
      ((FordWeakBilinear.order k*(2*FordWeakBilinear.order k) : ℕ) : ℝ) =
      -decay k := by rw [neg_div, FordDecayExponent.root_exponent hk1]
  rw [hexp] at he
  have hD : 0 < (scale N mu1 : ℝ)*scale N mu2 := by positivity
  simpa [mul_comm] using (div_le_iff₀ hD).mp he

end FordBilinearDecay
#print axioms FordBilinearDecay.floor_bilinear_decay
