import KoukWeierstrassGammaProductIdentity

/-!
# Gauss' digamma series from the Weierstrass Gamma product
-/

namespace KoukGaussDigammaSeries

open Complex Filter
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 800000

private theorem logDeriv_gammaFactor
    (n : ℕ) (z : ℂ) (hz : 0 < z.re) :
    logDeriv (KoukWeierstrassGammaFactors.gammaFactor n) z =
      (z + ((n + 1 : ℕ) : ℂ))⁻¹ -
        (((n + 1 : ℕ) : ℂ))⁻¹ := by
  let a : ℂ := ((n + 1 : ℕ) : ℂ)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast Nat.succ_ne_zero n
  have hza : z + a ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [a] at hre
    simp at hre
    linarith
  have hu : HasDerivAt (fun w : ℂ => w / a) (1 / a) z :=
    (hasDerivAt_id z).div_const a
  have hlin : HasDerivAt (fun w : ℂ => 1 + w / a) (1 / a) z :=
    hu.const_add 1
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp (-(w / a)))
      (Complex.exp (-(z / a)) * (-(1 / a))) z :=
    hu.neg.cexp
  have hlinne : 1 + z / a ≠ 0 := by
    intro h
    apply hza
    field_simp [ha] at h
    linear_combination h
  have hldlin : logDeriv (fun w : ℂ => 1 + w / a) z =
      (z + a)⁻¹ := by
    rw [logDeriv_apply, hlin.deriv]
    field_simp [ha, hza, hlinne]
    rw [add_comm a z, div_self hza]
  have hldexp : logDeriv (fun w : ℂ => Complex.exp (-(w / a))) z =
      -a⁻¹ := by
    rw [logDeriv_apply, hexp.deriv]
    field_simp [ha, Complex.exp_ne_zero]
  rw [show KoukWeierstrassGammaFactors.gammaFactor n =
      fun w => (1 + w / a) * Complex.exp (-(w / a)) by
    funext w
    simp [KoukWeierstrassGammaFactors.gammaFactor,
      KoukWeierstrassGammaFactors.u, a]]
  rw [logDeriv_mul
    (f := fun w : ℂ => 1 + w / a)
    (g := fun w : ℂ => Complex.exp (-(w / a)))
    z hlinne (Complex.exp_ne_zero _)
    hlin.differentiableAt hexp.differentiableAt]
  rw [hldlin, hldexp]
  simp only [a, Nat.cast_add, Nat.cast_one, sub_eq_add_neg]

private theorem norm_logDeriv_gammaFactor_le
    (n : ℕ) (z : ℂ) (hz : 0 < z.re) :
    ‖logDeriv (KoukWeierstrassGammaFactors.gammaFactor n) z‖ ≤
      ‖z‖ / (((n + 1 : ℕ) : ℝ) ^ 2) := by
  rw [logDeriv_gammaFactor n z hz]
  have hden : ((n + 1 : ℕ) : ℝ) ≤ ‖z + ((n + 1 : ℕ) : ℂ)‖ := by
    calc
      ((n + 1 : ℕ) : ℝ) ≤ (z + ((n + 1 : ℕ) : ℂ)).re := by
        simp
        linarith
      _ ≤ ‖z + ((n + 1 : ℕ) : ℂ)‖ := Complex.re_le_norm _
  have hapos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hza : z + ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hid :
      (z + ((n + 1 : ℕ) : ℂ))⁻¹ - (((n + 1 : ℕ) : ℂ))⁻¹ =
        -z * ((((n + 1 : ℕ) : ℂ) *
          (z + ((n + 1 : ℕ) : ℂ)))⁻¹) := by
    have ha : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    field_simp
    ring
  rw [hid, norm_mul, norm_inv, norm_mul, Complex.norm_natCast]
  rw [norm_neg]
  rw [div_eq_mul_inv]
  gcongr
  rw [pow_two]
  exact mul_le_mul_of_nonneg_left hden hapos.le

private theorem summable_logDeriv_gammaFactor
    (z : ℂ) (hz : 0 < z.re) :
    Summable (fun n : ℕ =>
      logDeriv (KoukWeierstrassGammaFactors.gammaFactor n) z) := by
  have hbase : Summable
      (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    have h0 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    simpa using ((summable_nat_add_iff 1).2 h0)
  have hmajor : Summable
      (fun n : ℕ => ‖z‖ / (((n + 1 : ℕ) : ℝ) ^ 2)) :=
    by simpa [div_eq_mul_inv] using hbase.mul_left ‖z‖
  exact hmajor.of_norm_bounded
    (fun n => norm_logDeriv_gammaFactor_le n z hz)

private theorem gammaFactor_ne_zero
    (n : ℕ) (z : ℂ) (hz : 0 < z.re) :
    KoukWeierstrassGammaFactors.gammaFactor n z ≠ 0 := by
  have hlin : 1 + z / (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    intro h
    have ha : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    have hzero : z + ((n + 1 : ℕ) : ℂ) = 0 := by
      field_simp [ha] at h
      linear_combination h
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  exact mul_ne_zero hlin (Complex.exp_ne_zero _)

private theorem tprod_gammaFactor_ne_zero
    (z : ℂ) (hz : 0 < z.re) :
    (∏' n : ℕ, KoukWeierstrassGammaFactors.gammaFactor n z) ≠ 0 := by
  rw [KoukWeierstrassGammaProductIdentity.tprod_gammaFactor_eq z hz]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num at hz
  exact div_ne_zero (Complex.exp_ne_zero _)
    (mul_ne_zero hz0 (Complex.Gamma_ne_zero_of_re_pos hz))

private theorem logDeriv_tprod_gammaFactor_eq_tsum
    (z : ℂ) (hz : 0 < z.re) :
    logDeriv (fun w : ℂ =>
      ∏' n : ℕ, KoukWeierstrassGammaFactors.gammaFactor n w) z =
      ∑' n : ℕ, logDeriv
        (KoukWeierstrassGammaFactors.gammaFactor n) z := by
  apply logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z)
  · exact fun n => gammaFactor_ne_zero n z hz
  · intro n
    unfold KoukWeierstrassGammaFactors.gammaFactor
      KoukWeierstrassGammaFactors.u
    fun_prop
  · exact summable_logDeriv_gammaFactor z hz
  · exact KoukWeierstrassGammaFactors.multipliableLocallyUniformlyOn_gammaFactor
  · exact tprod_gammaFactor_ne_zero z hz

private def gammaProductRhs (z : ℂ) : ℂ :=
  Complex.exp (-(z * (Real.eulerMascheroniConstant : ℂ))) /
    (z * Complex.Gamma z)

private theorem logDeriv_tprod_eq_logDeriv_gammaProductRhs
    (z : ℂ) (hz : 0 < z.re) :
    logDeriv (fun w : ℂ =>
      ∏' n : ℕ, KoukWeierstrassGammaFactors.gammaFactor n w) z =
      logDeriv gammaProductRhs z := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have heq : Filter.EventuallyEq (nhds z)
      (fun w : ℂ => ∏' n : ℕ,
        KoukWeierstrassGammaFactors.gammaFactor n w)
      gammaProductRhs := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact KoukWeierstrassGammaProductIdentity.tprod_gammaFactor_eq w hw
  have hval : (∏' n : ℕ,
      KoukWeierstrassGammaFactors.gammaFactor n z) = gammaProductRhs z :=
    heq.self_of_nhds
  rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, hval]

private theorem logDeriv_gammaProductRhs
    (z : ℂ) (hz : 0 < z.re) :
    logDeriv gammaProductRhs z =
      -(Real.eulerMascheroniConstant : ℂ) -
        (z⁻¹ + Complex.digamma z) := by
  let c : ℂ := (Real.eulerMascheroniConstant : ℂ)
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num at hz
  have hpoles : ∀ m : ℕ, z ≠ -m := by
    intro m h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hGamma0 : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hpoles
  have hGammaDiff : DifferentiableAt ℂ Complex.Gamma z :=
    Complex.differentiableAt_Gamma z hpoles
  have hlin : HasDerivAt (fun w : ℂ => -(w * c)) (-c) z := by
    simpa using ((hasDerivAt_id z).mul_const c).neg
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp (-(w * c)))
      (Complex.exp (-(z * c)) * (-c)) z := hlin.cexp
  have hldexp : logDeriv (fun w : ℂ => Complex.exp (-(w * c))) z = -c := by
    rw [logDeriv_apply, hexp.deriv]
    field_simp [Complex.exp_ne_zero]
  have hldden : logDeriv (fun w : ℂ => w * Complex.Gamma w) z =
      z⁻¹ + Complex.digamma z := by
    rw [logDeriv_mul (f := fun w : ℂ => w) (g := Complex.Gamma) z
      hz0 hGamma0 (by fun_prop) hGammaDiff]
    simp [Complex.digamma_def, logDeriv_id']
  unfold gammaProductRhs
  rw [logDeriv_div
    (f := fun w : ℂ => Complex.exp (-(w * c)))
    (g := fun w : ℂ => w * Complex.Gamma w) z
    (Complex.exp_ne_zero _) (mul_ne_zero hz0 hGamma0)
    hexp.differentiableAt ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w) z).mul hGammaDiff)]
  rw [hldexp, hldden]

private theorem hasSum_shifted_gaussDigammaSeries
    (z : ℂ) (hz : 0 < z.re) :
    HasSum (fun n : ℕ =>
      (((n + 1 : ℕ) : ℂ))⁻¹ -
        (z + ((n + 1 : ℕ) : ℂ))⁻¹)
      (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + z⁻¹) := by
  have hs := (summable_logDeriv_gammaFactor z hz).hasSum.neg
  have htsum :
      ∑' n : ℕ,
          logDeriv (KoukWeierstrassGammaFactors.gammaFactor n) z =
        -(Real.eulerMascheroniConstant : ℂ) -
          (z⁻¹ + Complex.digamma z) := by
    rw [← logDeriv_tprod_gammaFactor_eq_tsum z hz,
      logDeriv_tprod_eq_logDeriv_gammaProductRhs z hz,
      logDeriv_gammaProductRhs z hz]
  convert hs using 1
  · ext n
    rw [logDeriv_gammaFactor n z hz]
    ring
  · rw [htsum]
    ring

private theorem telescopeTerm_eq
    (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    (z + (n : ℂ))⁻¹ - (z + ((n + 1 : ℕ) : ℂ))⁻¹ =
      1 / ((z + (n : ℂ)) * (z + ((n + 1 : ℕ) : ℂ))) := by
  have hzn : z + (n : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hzn1 : z + ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  field_simp [hzn, hzn1]
  push_cast
  ring

private theorem norm_telescopeTerm_succ_le
    (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ‖(z + ((n + 1 : ℕ) : ℂ))⁻¹ -
        (z + ((n + 2 : ℕ) : ℂ))⁻¹‖ ≤
      1 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
  rw [telescopeTerm_eq z hz (n + 1), norm_div, norm_mul, norm_one]
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hfirst : ((n + 1 : ℕ) : ℝ) ≤
      ‖z + ((n + 1 : ℕ) : ℂ)‖ := by
    calc
      ((n + 1 : ℕ) : ℝ) ≤
          (z + ((n + 1 : ℕ) : ℂ)).re := by simp; linarith
      _ ≤ ‖z + ((n + 1 : ℕ) : ℂ)‖ := Complex.re_le_norm _
  have hsecond : ((n + 1 : ℕ) : ℝ) ≤
      ‖z + ((n + 2 : ℕ) : ℂ)‖ := by
    calc
      ((n + 1 : ℕ) : ℝ) ≤
          (z + ((n + 2 : ℕ) : ℂ)).re := by simp; linarith
      _ ≤ ‖z + ((n + 2 : ℕ) : ℂ)‖ := Complex.re_le_norm _
  rw [one_div, one_div]
  gcongr
  rw [pow_two]
  exact mul_le_mul hfirst hsecond (by positivity) (by positivity)

private theorem summable_telescopeTerm
    (z : ℂ) (hz : 0 < z.re) :
    Summable (fun n : ℕ =>
      (z + (n : ℂ))⁻¹ - (z + ((n + 1 : ℕ) : ℂ))⁻¹) := by
  rw [← summable_nat_add_iff 1]
  have hs : Summable
      (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  exact hs.of_norm_bounded (fun n => by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      norm_telescopeTerm_succ_le z hz n)

private theorem tendsto_inv_add_nat_atTop_zero (z : ℂ) :
    Tendsto (fun n : ℕ => (z + n)⁻¹) atTop (nhds 0) := by
  have h := (tendsto_natCast_div_add_atTop z).mul
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ))
  have h' : Tendsto (fun n : ℕ =>
      (n : ℂ) / (n + z) * (n : ℂ)⁻¹) atTop (nhds 0) := by
    simpa only [one_mul] using h
  refine h'.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [div_eq_mul_inv]
  calc
    (n : ℂ) * ((n : ℂ) + z)⁻¹ * (n : ℂ)⁻¹ =
        ((n : ℂ) * (n : ℂ)⁻¹) * ((n : ℂ) + z)⁻¹ := by ring
    _ = ((n : ℂ) + z)⁻¹ := by
      rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]
    _ = (z + (n : ℂ))⁻¹ := by rw [add_comm]

private theorem hasSum_telescopeTerm
    (z : ℂ) (hz : 0 < z.re) :
    HasSum (fun n : ℕ =>
      (z + n)⁻¹ - (z + (n + 1 : ℕ))⁻¹) z⁻¹ := by
  have hs := summable_telescopeTerm z hz
  rw [hasSum_iff_tendsto_nat_of_summable_norm (summable_norm_iff.mpr hs)]
  have ht : Tendsto (fun n : ℕ => z⁻¹ - (z + n)⁻¹)
      atTop (nhds z⁻¹) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub (tendsto_inv_add_nat_atTop_zero z))
  refine ht.congr' ?_
  filter_upwards with n
  rw [Finset.sum_range_sub']
  simp only [Nat.cast_zero, add_zero]

/-- Gauss' complex digamma series on the open right half-plane, derived from
the certified locally uniform Weierstrass product. -/
theorem gaussDigammaSeries :
    KoukGaussSeriesToRightHalfPlane.GaussDigammaSeries := by
  intro z hz
  have hshift := hasSum_shifted_gaussDigammaSeries z hz
  have htel := (hasSum_telescopeTerm z hz).neg
  convert hshift.add htel using 1
  · ext n
    push_cast
    ring
  · ring

/-- The certified Weierstrass-product derivation supplies the right-half-plane
digamma logarithmic bound without any analytic source premise. -/
theorem rightHalfPlaneDigammaLogBound :
    KoukDigammaAwayFromPoles.RightHalfPlaneDigammaLogBound :=
  KoukGaussSeriesToRightHalfPlane.rightHalfPlaneDigammaLogBound_of_gaussSeries
    gaussDigammaSeries

/-- Premise-free fixed-clearance digamma growth used by the Koukoulopoulos
half-strip contour. -/
theorem awayFromPolesDigammaLogBound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      (∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) →
      ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2) :=
  KoukGaussSeriesToRightHalfPlane.awayFromPolesDigammaLogBound_of_gaussSeries
    gaussDigammaSeries

end
end KoukGaussDigammaSeries

#print axioms KoukGaussDigammaSeries.gaussDigammaSeries
#print axioms KoukGaussDigammaSeries.rightHalfPlaneDigammaLogBound
#print axioms KoukGaussDigammaSeries.awayFromPolesDigammaLogBound
