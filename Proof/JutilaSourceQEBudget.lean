import JutilaCollarSourceParameters
import JutilaP53SourceRectangleBudget

/-! Literal source QE absorption, including both floors, all harmonic and
logarithmic factors, and the published +7*delta endpoint. -/
namespace MAPJutilaSourceQEBudget
open Real Filter
open MAPJutilaCollarSourceParameters MAPJutilaLemma6GenericTailAbsorption
open MAPJutilaP53SourceRectangleBudget PostA5HighStripSplitReductionFromFourthMoment
noncomputable section
set_option maxHeartbeats 1000000

def sourceQ (δ D sigma : ℝ) : ℝ :=
  10 * Real.rpow (lemmaSixDirectCutoff δ D) (2-2*sigma) *
    (1+Real.log (lemmaSixDirectCutoff δ D : ℝ))^4

def sourceE (K δ D : ℝ) (q : ℕ) (T : ℝ) : ℝ :=
  K * Real.sqrt ((q : ℝ)*(1+2*T)) *
    (2*Real.exp (-((1-δ)^2)*Real.log (sourceZ1 δ D))) *
    (sourceR δ D : ℝ)^2 * (harmonic (sourceR δ D) : ℝ)^8

theorem cutoff_power_le
    {δ D sigma : ℝ} (hδ0 : 0 ≤ δ) (hδhi : δ ≤ 1/280)
    (hD : 1 ≤ D) (hlog : 1 ≤ Real.log D) (hgeo : SourceGeometry δ D)
    (hsigma : 1-δ ≤ sigma) :
    Real.rpow (lemmaSixDirectCutoff δ D) (2-2*sigma) ≤
      Real.rpow D (2*δ*(1+12*δ)) * Real.log D := by
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hx1 : (1:ℝ) ≤ lemmaSixDirectCutoff δ D := by exact_mod_cast hgeo.x_one
  have hx0 : (0:ℝ) ≤ lemmaSixDirectCutoff δ D := by positivity
  have hfirst := Real.rpow_le_rpow_of_exponent_le hx1
    (show 2-2*sigma ≤ 2*δ by linarith)
  have hsecond := Real.rpow_le_rpow hx0 hgeo.x_upper (show 0 ≤ 2*δ by linarith)
  have hX0 : 0 ≤ lemmaSixSmoothScale δ D := (lemmaSixSmoothScale_pos hDp).le
  have heq : Real.rpow (lemmaSixSmoothScale δ D * (Real.log D)^2) (2*δ) =
      Real.rpow D (2*δ*(1+12*δ)) * Real.rpow (Real.log D) (4*δ) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.mul_rpow hX0 (sq_nonneg _)]
    unfold lemmaSixSmoothScale
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul hDp.le, ← Real.rpow_natCast_mul (show 0 ≤ Real.log D by linarith) 2]
    congr 1 <;> ring
  have hlogpow : Real.rpow (Real.log D) (4*δ) ≤ Real.log D := by
    simpa using Real.rpow_le_rpow_of_exponent_le hlog (show 4*δ ≤ 1 by linarith)
  exact hfirst.trans (hsecond.trans (heq.le.trans
    (mul_le_mul_of_nonneg_left hlogpow (Real.rpow_nonneg hDp.le _))))

theorem sourceQ_le
    {δ D sigma : ℝ} (hδ0 : 0 ≤ δ) (hδhi : δ ≤ 1/280)
    (hD : 1 ≤ D) (hlog : 1 ≤ Real.log D) (hgeo : SourceGeometry δ D)
    (hsigma : 1-δ ≤ sigma) :
    sourceQ δ D sigma ≤ 2560 * Real.rpow D (2*δ*(1+12*δ)) * (Real.log D)^5 := by
  have hx := cutoff_power_le hδ0 hδhi hD hlog hgeo hsigma
  have hx1 : (1:ℝ) ≤ lemmaSixDirectCutoff δ D := by exact_mod_cast hgeo.x_one
  have hlx0 : 0 ≤ 1+Real.log (lemmaSixDirectCutoff δ D : ℝ) := by
    linarith [Real.log_nonneg hx1]
  have hlx : 1+Real.log (lemmaSixDirectCutoff δ D : ℝ) ≤ 4*Real.log D := by
    linarith [hgeo.logx_upper]
  have hp := pow_le_pow_left₀ hlx0 hlx 4
  have hnonneg : 0 ≤ 10*(Real.rpow D (2*δ*(1+12*δ))*Real.log D) :=
    mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg (by linarith) _) (by linarith))
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hx (by norm_num : (0:ℝ)≤10)) hp
    (by positivity) hnonneg
  unfold sourceQ
  convert h using 1 <;> ring

theorem sourceE_le
    {K δ D T : ℝ} {q : ℕ} (hK : 0 ≤ K) (hD : 1 ≤ D)
    (hlog : 1 ≤ Real.log D) (hgeo : SourceGeometry δ D)
    (hT : 1 ≤ T) (hscale : (q : ℝ)*T = D) :
    sourceE K δ D q T ≤ 1024*K *
      (Real.rpow D (1/2) * Real.rpow D (-((1-δ)^2)*(1/2+7*δ)) * Real.rpow D (2*δ)) *
      (Real.log D)^8 := by
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hsqrt := sqrt_pairHeight_le_sqrt_three_scale (q:=(q:ℝ)) (by positivity) hT
  rw [show 3*(q:ℝ)*T=3*D by rw [mul_assoc,hscale]] at hsqrt
  have hsqrt' : Real.sqrt (3*D) ≤ 2*Real.sqrt D := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity,by nlinarith [Real.sq_sqrt hDp.le]⟩
  have hs : Real.sqrt ((q:ℝ)*(1+2*T)) ≤ 2*Real.rpow D (1/2) := by
    simpa only [Real.sqrt_eq_rpow] using! hsqrt.trans hsqrt'
  have he : Real.exp (-((1-δ)^2)*Real.log (sourceZ1 δ D)) =
      Real.rpow D (-((1-δ)^2)*(1/2+7*δ)) := by
    unfold sourceZ1
    simp only [Real.rpow_eq_pow]
    rw [Real.log_rpow hDp,Real.rpow_def_of_pos hDp]
    congr 1; ring
  have hR := pow_le_pow_left₀ (Nat.cast_nonneg (sourceR δ D)) hgeo.R_upper 2
  have hR' : (sourceR δ D : ℝ)^2 ≤ Real.rpow D (2*δ) := by
    have heq := Real.rpow_mul_natCast hDp.le δ 2
    simpa [Real.rpow_eq_pow,mul_comm] using hR.trans_eq heq.symm
  have hh0 : 0 ≤ (harmonic (sourceR δ D) : ℝ) := by unfold harmonic; positivity
  have hh : (harmonic (sourceR δ D) : ℝ) ≤ 2*Real.log D := by linarith [hgeo.harmonic_upper]
  have hh8 := pow_le_pow_left₀ hh0 hh 8
  unfold sourceE
  rw [he]
  calc
    _ ≤ K*(2*Real.rpow D (1/2)) *
        (2*Real.rpow D (-((1-δ)^2)*(1/2+7*δ))) * Real.rpow D (2*δ) * (2*Real.log D)^8 := by
      have hp0 : ∀ a : ℝ, 0 ≤ Real.rpow D a := fun a => Real.rpow_nonneg hDp.le a
      simp only [Real.rpow_eq_pow] at hs hR' hp0 ⊢
      gcongr
    _ = _ := by ring

theorem sourceQE_le_power_log
    {K δ D T sigma : ℝ} {q : ℕ} (hK : 0 ≤ K)
    (hδlo : 1/560 ≤ δ) (hδhi : δ ≤ 1/280)
    (hD : 1 ≤ D) (hlog : 1 ≤ Real.log D) (hgeo : SourceGeometry δ D)
    (hT : 1 ≤ T) (hscale : (q : ℝ)*T = D) (hsigma : 1-δ ≤ sigma) :
    sourceQ δ D sigma * sourceE K δ D q T ≤
      (2621440*K) * Real.rpow D (-(3/2)*δ) * (Real.log D)^13 := by
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hQ := sourceQ_le (by linarith) hδhi hD hlog hgeo hsigma
  have hE := sourceE_le hK hD hlog hgeo hT hscale
  have hE0 : 0 ≤ sourceE K δ D q T := by unfold sourceE; positivity
  have hQbound0 : 0 ≤ 2560*Real.rpow D (2*δ*(1+12*δ))*(Real.log D)^5 := by
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hDp.le _)) (pow_nonneg (by linarith) _)
  have h := mul_le_mul hQ hE hE0 hQbound0
  have heq : Real.rpow D (2*δ*(1+12*δ)) *
      (Real.rpow D (1/2)*Real.rpow D (-((1-δ)^2)*(1/2+7*δ))*Real.rpow D (2*δ)) =
      Real.rpow D ((1/2)+2*δ-(1-δ)^2*(1/2+7*δ)+2*δ*(1+12*δ)) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hDp,← Real.rpow_add hDp,← Real.rpow_add hDp]
    congr 1; ring
  have hledger := source_seven_epsilon_ledger (by linarith : 0 ≤ δ) (by linarith : δ ≤ 1/100)
  have hpow := Real.rpow_le_rpow_of_exponent_le hD hledger
  calc
    _ ≤ (2560*Real.rpow D (2*δ*(1+12*δ))*(Real.log D)^5) *
        (1024*K*(Real.rpow D (1/2)*Real.rpow D (-((1-δ)^2)*(1/2+7*δ))*Real.rpow D (2*δ))*(Real.log D)^8) := h
    _ = (2621440*K) *
        (Real.rpow D (2*δ*(1+12*δ)) *
          (Real.rpow D (1/2)*Real.rpow D (-((1-δ)^2)*(1/2+7*δ))*Real.rpow D (2*δ))) * (Real.log D)^13 := by ring
    _ ≤ _ := by
      rw [heq]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by simpa only [Real.rpow_eq_pow] using hpow) (by positivity))
        (pow_nonneg (by linarith) _)

/-- Fixed source constants precede the scale. This estimates the literal QE
uniformly in q,T and sigma, and therefore supplies an actual absorption input. -/
theorem eventually_sourceQE_le_decay {δ : ℝ}
    (hδlo : 1/560 ≤ δ) (hδhi : δ ≤ 1/280) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ D : ℝ in atTop, ∀ (q : ℕ) (T sigma : ℝ),
      1 ≤ T → (q : ℝ)*T = D → 1-δ ≤ sigma →
      sourceQ δ D sigma * sourceE K δ D q T ≤ Real.rpow D (-δ/2) := by
  have hpoly := eventually_const_mul_polylog_le_rpow (2621440*K) 13 δ (by positivity) (by linarith)
  filter_upwards [eventually_sourceGeometry hδlo hδhi,hpoly,eventually_ge_atTop (Real.exp 1)] with D hgeo hpoly hDe
  intro q T sigma hT hscale hsigma
  have hD : 1 ≤ D := (Real.one_le_exp (by norm_num)).trans hDe
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hlog : 1 ≤ Real.log D := by
    have h := Real.log_le_log (Real.exp_pos 1) hDe
    simpa using h
  have h := sourceQE_le_power_log hK hδlo hδhi hD hlog hgeo hT hscale hsigma
  have hpoly' : (2621440*K)*(Real.log D)^13 ≤ Real.rpow D δ := by
    have he13 : Real.rpow (Real.log D) (13:ℝ) = (Real.log D)^13 := by
      simpa only [Nat.cast_ofNat] using! Real.rpow_natCast (Real.log D) 13
    rwa [he13] at hpoly
  have hp := mul_le_mul_of_nonneg_right hpoly' (Real.rpow_nonneg hDp.le (-(3/2)*δ))
  have heq : Real.rpow D δ * Real.rpow D (-(3/2)*δ) = Real.rpow D (-δ/2) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hDp]
    congr 1; ring
  have hp' : (2621440*K)*(Real.log D)^13*Real.rpow D (-(3/2)*δ) ≤
      Real.rpow D δ * Real.rpow D (-(3/2)*δ) := by
    simpa only [Real.rpow_eq_pow] using hp
  rw [heq] at hp'
  nlinarith only [h,hp']

theorem eventually_sourceQE_le_one {δ : ℝ}
    (hδlo : 1/560 ≤ δ) (hδhi : δ ≤ 1/280) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ D : ℝ in atTop, ∀ (q : ℕ) (T sigma : ℝ),
      1 ≤ T → (q : ℝ)*T = D → 1-δ ≤ sigma →
      sourceQ δ D sigma * sourceE K δ D q T ≤ 1 := by
  filter_upwards [eventually_sourceQE_le_decay hδlo hδhi K hK,eventually_ge_atTop (1:ℝ)] with D h hD
  intro q T sigma hT hscale hsigma
  exact (h q T sigma hT hscale hsigma).trans
    (Real.rpow_le_one_of_one_le_of_nonpos hD (by linarith))
end
end MAPJutilaSourceQEBudget
#print axioms MAPJutilaSourceQEBudget.eventually_sourceQE_le_decay
#print axioms MAPJutilaSourceQEBudget.eventually_sourceQE_le_one
