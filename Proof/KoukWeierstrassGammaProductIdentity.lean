import KoukWeierstrassGammaFactors
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Pointwise identification of the Weierstrass Gamma product
-/

namespace KoukWeierstrassGammaProductIdentity

open Complex Filter
open scoped BigOperators Topology

noncomputable section

set_option maxHeartbeats 800000

private theorem prod_succ_cast_eq_factorial (N : ℕ) :
    (∏ n ∈ Finset.range N, (((n + 1 : ℕ) : ℂ))) = (N.factorial : ℂ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
      push_cast
      ring

private theorem zero_mul_prod_succ_eq_prod_range_succ
    (z : ℂ) (N : ℕ) :
    z * (∏ n ∈ Finset.range N, (z + ((n + 1 : ℕ) : ℂ))) =
      ∏ j ∈ Finset.range (N + 1), (z + (j : ℂ)) := by
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
  ring

private theorem prod_factor_linear_part
    (z : ℂ) (N : ℕ) :
    ∏ n ∈ Finset.range N, (1 + z / ((n + 1 : ℕ) : ℂ)) =
      (∏ n ∈ Finset.range N, (z + ((n + 1 : ℕ) : ℂ))) /
        (N.factorial : ℂ) := by
  rw [← prod_succ_cast_eq_factorial N]
  have heq :
      (∏ n ∈ Finset.range N, (1 + z / ((n + 1 : ℕ) : ℂ))) =
        ∏ n ∈ Finset.range N,
          ((z + ((n + 1 : ℕ) : ℂ)) / ((n + 1 : ℕ) : ℂ)) := by
    apply Finset.prod_congr rfl
    intro n hn
    have hne : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    field_simp
    ring
  rw [heq]
  rw [Finset.prod_div_distrib]

private theorem prod_factor_exponential_part
    (z : ℂ) (N : ℕ) :
    ∏ n ∈ Finset.range N,
        Complex.exp (-z / ((n + 1 : ℕ) : ℂ)) =
      Complex.exp (-(z * (harmonic N : ℂ))) := by
  rw [← Complex.exp_sum]
  congr 1
  unfold harmonic
  push_cast
  rw [Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  simp [div_eq_mul_inv]

private theorem prod_gammaFactor_eq
    (z : ℂ) (N : ℕ) :
    ∏ n ∈ Finset.range N,
        KoukWeierstrassGammaFactors.gammaFactor n z =
      ((∏ n ∈ Finset.range N, (z + ((n + 1 : ℕ) : ℂ))) /
          (N.factorial : ℂ)) *
        Complex.exp (-(z * (harmonic N : ℂ))) := by
  simp only [KoukWeierstrassGammaFactors.gammaFactor,
    KoukWeierstrassGammaFactors.u]
  rw [Finset.prod_mul_distrib, prod_factor_linear_part]
  have hexp := prod_factor_exponential_part z N
  rw [show (∏ x ∈ Finset.range N, Complex.exp (-(z / ((x + 1 : ℕ) : ℂ)))) =
      Complex.exp (-(z * (harmonic N : ℂ))) by
    simpa [neg_div] using hexp]

/-- Exact finite bridge from Euler's `GammaSeq` to the canonical product. -/
theorem prod_gammaFactor_mul_zGammaSeq
    (z : ℂ) (N : ℕ) (hz : 0 < z.re) (hN : N ≠ 0) :
    (∏ n ∈ Finset.range N,
        KoukWeierstrassGammaFactors.gammaFactor n z) *
      (z * Complex.GammaSeq z N) =
        ((N : ℂ) ^ z) * Complex.exp (-(z * (harmonic N : ℂ))) := by
  rw [prod_gammaFactor_eq, Complex.GammaSeq]
  have hfac : (N.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero N
  have hNcast : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num at hz
  have hPne :
      (∏ n ∈ Finset.range N, (z + ((n + 1 : ℕ) : ℂ))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro n hn
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hprod :
      ∏ j ∈ Finset.range (N + 1), (z + (j : ℂ)) =
        z * ∏ n ∈ Finset.range N, (z + ((n + 1 : ℕ) : ℂ)) := by
    rw [zero_mul_prod_succ_eq_prod_range_succ]
  rw [hprod]
  field_simp [hzne, hPne]

private theorem tendsto_cpow_mul_exp_harmonic (z : ℂ) :
    Tendsto (fun N : ℕ =>
      ((N : ℂ) ^ z) * Complex.exp (-(z * (harmonic N : ℂ))))
      atTop
      (𝓝 (Complex.exp (-(z * (Real.eulerMascheroniConstant : ℂ))))) := by
  have hreal : Tendsto
      (fun N : ℕ => Real.log (N : ℝ) - (harmonic N : ℝ))
      atTop (𝓝 (-Real.eulerMascheroniConstant)) := by
    simpa [sub_eq_add_neg, add_comm] using
      Real.tendsto_harmonic_sub_log.neg
  have hcomplex : Tendsto
      (fun N : ℕ => (Real.log (N : ℝ) - (harmonic N : ℝ) : ℂ))
      atTop (𝓝 ((-Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
    by simpa using hreal.ofReal
  have hexp : Tendsto
      (fun N : ℕ => Complex.exp
        (z * (Real.log (N : ℝ) - (harmonic N : ℝ) : ℂ)))
      atTop
      (𝓝 (Complex.exp (z * ((-Real.eulerMascheroniConstant : ℝ) : ℂ)))) :=
    (hcomplex.const_mul z).cexp
  have heq : ∀ᶠ N : ℕ in atTop,
      ((N : ℂ) ^ z) * Complex.exp (-(z * (harmonic N : ℂ))) =
        Complex.exp
          (z * (Real.log (N : ℝ) - (harmonic N : ℝ) : ℂ)) := by
    filter_upwards [eventually_ne_atTop 0] with N hN
    rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hN)]
    have hlog : Complex.log (N : ℂ) = (Real.log (N : ℝ) : ℂ) :=
      (Complex.ofReal_log (show (0 : ℝ) ≤ N by positivity)).symm
    rw [hlog]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hlimit :
      Complex.exp (z * ((-Real.eulerMascheroniConstant : ℝ) : ℂ)) =
        Complex.exp (-(z * (Real.eulerMascheroniConstant : ℂ))) := by
    congr 1
    push_cast
    ring
  rw [← hlimit]
  exact hexp.congr' (Filter.EventuallyEq.symm heq)

/-- Pointwise Weierstrass product identity, obtained from the certified local
uniform product and Euler's pointwise `GammaSeq` limit. -/
theorem tprod_gammaFactor_eq
    (z : ℂ) (hz : 0 < z.re) :
    (∏' n : ℕ, KoukWeierstrassGammaFactors.gammaFactor n z) =
      Complex.exp (-(z * (Real.eulerMascheroniConstant : ℂ))) /
        (z * Complex.Gamma z) := by
  have hprod : HasProd
      (fun n : ℕ => KoukWeierstrassGammaFactors.gammaFactor n z)
      (∏' n : ℕ, KoukWeierstrassGammaFactors.gammaFactor n z) :=
    KoukWeierstrassGammaFactors.hasProdLocallyUniformlyOn_gammaFactor.hasProd
      (by simp)
  have hleft : Tendsto (fun N : ℕ =>
      (∏ n ∈ Finset.range N,
          KoukWeierstrassGammaFactors.gammaFactor n z) *
        (z * Complex.GammaSeq z N)) atTop
      (𝓝 ((∏' n : ℕ, KoukWeierstrassGammaFactors.gammaFactor n z) *
        (z * Complex.Gamma z))) :=
    hprod.tendsto_prod_nat.mul
      ((Complex.GammaSeq_tendsto_Gamma z).const_mul z)
  have heq : ∀ᶠ N : ℕ in atTop,
      (∏ n ∈ Finset.range N,
          KoukWeierstrassGammaFactors.gammaFactor n z) *
        (z * Complex.GammaSeq z N) =
      ((N : ℂ) ^ z) * Complex.exp (-(z * (harmonic N : ℂ))) := by
    filter_upwards [eventually_ne_atTop 0] with N hN
    exact prod_gammaFactor_mul_zGammaSeq z N hz hN
  have hright := tendsto_cpow_mul_exp_harmonic z
  have hmul :
      (∏' n : ℕ, KoukWeierstrassGammaFactors.gammaFactor n z) *
          (z * Complex.Gamma z) =
        Complex.exp (-(z * (Real.eulerMascheroniConstant : ℂ))) :=
    tendsto_nhds_unique hleft
      (hright.congr' (Filter.EventuallyEq.symm heq))
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num at hz
  have hGamma : Complex.Gamma z ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    linarith
  apply (eq_div_iff (mul_ne_zero hzne hGamma)).2
  exact hmul

end
end KoukWeierstrassGammaProductIdentity

#print axioms KoukWeierstrassGammaProductIdentity.prod_gammaFactor_mul_zGammaSeq
#print axioms KoukWeierstrassGammaProductIdentity.tprod_gammaFactor_eq
