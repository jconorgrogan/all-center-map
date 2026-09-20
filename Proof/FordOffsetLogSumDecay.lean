import FordBilinearDecay
import FordOffsetMeanTransfer
import FordTaylorScaleError
open scoped BigOperators
noncomputable section
namespace FordOffsetLogSumDecay
open FordWEnvelopeScalar FordScaleFloor FordPolynomialPhase FordSourceWeakBilinear
open FordDecayExponent FordOffsetLogTransfer

/-- Literal logarithmic exponential sum with all finite moment and transfer inputs proved. -/
theorem offset_log_sum_decay {N H k : ℕ} {lam u : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hN : 1 ≤ N) (hH : H ≤ N) (hlam : 2000*b ≤ lam)
    (hdegree : k = Nat.floor (lam/b)+1)
    (hNlarge : 1024*(k+1)^2 ≤ N)
    (hlog : 1000000000000*(k : ℝ)^4 ≤ Real.log N) :
    ‖∑ n ∈ Finset.range H, offsetPhase ((N : ℝ)^lam) u (N+n)‖ ≤
      4*(N : ℝ)^(1-decay k) := by
  have hn0 : (0 : ℝ) < N := by positivity
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hk1 : 1 ≤ k := by omega
  obtain ⟨hM1,hM2,_,_,_,_⟩ := ford_scales hN
  have hm1 := scale_comparable (mu := mu1) hN (by norm_num)
  have hm2 := scale_comparable (mu := mu2) hN (by norm_num)
  have hU : ∀ n ∈ Finset.range H,
      ‖∑ b0 : Fin (scale N mu2), ∑ a : Fin (scale N mu1),
        e (∑ j : Fin k, sourceGamma ((N : ℝ)^lam) (((N+n : ℕ) : ℝ)+u) j.val *
          (((b0.val+1 : ℕ) : ℝ)^(j.val+1)) *
          (((a.val+1 : ℕ) : ℝ)^(j.val+1)))‖ ≤
        ((scale N mu1 : ℝ)*scale N mu2)*(N : ℝ)^(-decay k) := by
    intro n hn
    have hnH : n < H := Finset.mem_range.mp hn
    apply FordBilinearDecay.floor_bilinear_decay hN hlam hdegree hNlarge hlog
    · have hh : (N : ℝ) ≤ ((N+n : ℕ) : ℝ) := by exact_mod_cast (show N ≤ N+n by omega)
      linarith
    · have hh : ((N+n : ℕ) : ℝ)+1 ≤ 2*(N : ℝ) := by
        exact_mod_cast (show N+n+1 ≤ 2*N by omega)
      linarith
  have hmean := FordOffsetMeanTransfer.offset_mean_transfer
    (scale N mu1) (scale N mu2) N H k ((N : ℝ)^lam) u ((N : ℝ)^(-decay k))
    hM1 hM2 hN (by positivity) hu hu1 hU
  have herr := FordTaylorScaleError.taylor_error_le hN hm1.2.1 hm2.2.1 hlam
  have herr' : (N : ℝ)^lam *
      (((scale N mu1*scale N mu2 : ℕ) : ℝ)/(N : ℝ))^(k+1)/(k+1) ≤
      (N : ℝ)^(-b) := by simpa only [hdegree] using herr
  have hprod := FordTaylorScaleError.two_scale_product_le hN hm1.2.1 hm2.2.1
  have hd := decay_le_b hk1
  have hsmall : (N : ℝ)^(-b) ≤ (N : ℝ)^(-decay k) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hscale : (N : ℝ)^(mu1+mu2) ≤ (N : ℝ)^(1-decay k) := by
    apply Real.rpow_le_rpow_of_exponent_le hn1
    have he : mu1+mu2=1-b := by norm_num [mu1,mu2,b]
    rw [he]
    linarith
  have hHreal : (H : ℝ) ≤ N := by exact_mod_cast hH
  have hmain : (H : ℝ)*(N : ℝ)^(-decay k) ≤ (N : ℝ)^(1-decay k) := by
    calc
      _ ≤ (N : ℝ)*(N : ℝ)^(-decay k) :=
        mul_le_mul_of_nonneg_right hHreal (by positivity)
      _ = _ := by rw [sub_eq_add_neg, Real.rpow_add hn0, Real.rpow_one]
  have herrH := mul_le_mul_of_nonneg_left (herr'.trans hsmall) (by positivity : 0 ≤ (H : ℝ))
  have hprod' : 2*((scale N mu1 : ℝ)*scale N mu2) ≤ 2*(N : ℝ)^(1-decay k) := by
    simpa only [Nat.cast_mul] using hprod.trans (mul_le_mul_of_nonneg_left hscale (by norm_num))
  exact hmean.trans ((add_le_add (add_le_add hprod' hmain) (herrH.trans hmain)).trans_eq (by ring))

end FordOffsetLogSumDecay
#print axioms FordOffsetLogSumDecay.offset_log_sum_decay
