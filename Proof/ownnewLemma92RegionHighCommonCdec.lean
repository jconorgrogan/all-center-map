import GuthMaynardJIterationSourceHighFrequency
import GuthMaynardHighFrequencyBudget
import GuthMaynardSourceDyadicRanges
import GuthMaynardSourceGGeneralPlancherel
import GuthMaynardWholeFrequencyDyadicStructuralInputs

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-!
  Region III producer for the literal dyadic source.  The decay constant is
  deliberately an explicit parameter before the profile variables.  The
  caller supplies the single-family certificate `hdecayProfile`; this theorem
  does not choose a new constant from `hf.rapidDecay` at the current value of
  `T`.  To use a family uniformly, the same `Cdec` must be reused in each
  instance of this certificate.

  The finite order is `79` on `f̂` and `q = 77` in the integrable envelope.
  The ledger is

    cards `(7T,7T,5T)`, bump `1`, ratio upper `2T`,
    reciprocal ratio `T/Rlo ≤ 2T^5`,
    `K ≤ ((686 Cdec S) 2^79 2^79) T^412`,
    and `412 = 6·27 + 250`.

  The third range is the literal radius-two bump collar
  `sourceIntegerWindow 0 (2*M3)`; the
  actual Jacobian `|m₂/m₁|` and the actual `M3` argument stay in the source
  Fourier theorem.  No desired tail or squared-Fourier integral is assumed.
-/
theorem ownnewLemma92RegionHigh_commonCdec
    (Cdec : ℝ) (hCdec : 0 ≤ Cdec)
    {T S F : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    (hdecayProfile : ∀ {z : ℝ}, z ≠ 0 →
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
        Cdec * T ^ (1 : ℝ) * (T / |z|) ^ (79 : ℕ) * S)
    {M1 M2 M3 M : ℕ}
    (hT : 1 ≤ T)
    (hM1 : 0 < M1) (hM2 : 0 < M2) (hM3 : 0 < M3)
    (hM1M : M1 ≤ M) (hM2M : M2 ≤ M) (hM3M : M3 ≤ M)
    (hMT : (M : ℝ) ≤ T) :
    (∫ xi in highFrequencyRegion (sourceHighFrequencyCutoff T),
      ‖FourierTransform.fourier
        (sourceGFinite (sourceSignedDyadicRange M1)
          (sourcePositiveDyadicRange M2)
          (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (fun u : ℝ => (f u : ℂ)) (M3 : ℝ)) xi‖ ^ 2) ≤
      (((686 * Cdec * S) * 2 ^ 79 * 2 ^ 79) ^ 2 *
        quarticDecayMass) / T ^ 100 := by
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hS : 0 ≤ S := hf.bound_nonneg
  have hM1T : (M1 : ℝ) ≤ T := by
    calc
      (M1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1M
      _ ≤ T := hMT
  have hM2T : (M2 : ℝ) ≤ T := by
    calc
      (M2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2M
      _ ≤ T := hMT
  have hM3T : (M3 : ℝ) ≤ T := by
    calc
      (M3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM3M
      _ ≤ T := hMT
  let Rlo : ℝ := (M2 : ℝ) / (2 * M1 : ℝ)
  have hRlo : 0 < Rlo := by
    dsimp only [Rlo]
    positivity
  have hm1 : ∀ m1 ∈ sourceSignedDyadicRange M1, m1 ≠ 0 :=
    fun _ hm1mem => sourceSignedDyadicRange_ne_zero hM1 hm1mem
  have hm2 : ∀ m2 ∈ sourcePositiveDyadicRange M2, m2 ≠ 0 :=
    fun _ hm2mem => sourcePositiveDyadicRange_ne_zero hM2 hm2mem
  have hN10 : 0 ≤ ((sourceSignedDyadicRange M1).card : ℝ) := by
    positivity
  have hN20 : 0 ≤ ((sourcePositiveDyadicRange M2).card : ℝ) := by
    positivity
  have hN30 : 0 ≤ ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ) := by
    positivity
  have hRhi : 0 ≤ 2 * T := by positivity
  have hpsi : ∀ m3 ∈ sourceIntegerWindow 0 (2 * (M3 : ℝ)),
      ‖(sourceBump 1 zero_lt_one ((m3 : ℝ) / (M3 : ℝ)) : ℂ)‖ ≤ 1 := by
    intro m3 hm3mem
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sourceBump_nonneg 1 zero_lt_one _)]
    exact sourceBump_le_one 1 zero_lt_one _
  have hratioLo : ∀ m1 ∈ sourceSignedDyadicRange M1,
      ∀ m2 ∈ sourcePositiveDyadicRange M2,
        Rlo ≤ |((m2 : ℝ) / (m1 : ℝ))| := by
    intro m1 hm1mem m2 hm2mem
    simpa only [Rlo] using
      (sourceDyadic_ratio_bounds hM1 hM2 hm1mem hm2mem).1
  have hratioHi : ∀ m1 ∈ sourceSignedDyadicRange M1,
      ∀ m2 ∈ sourcePositiveDyadicRange M2,
        |((m2 : ℝ) / (m1 : ℝ))| ≤ 2 * T := by
    intro m1 hm1mem m2 hm2mem
    exact sourceDyadic_ratio_upper_le_two_mul_time hM1 hM2 hM2T
      hm1mem hm2mem
  have hdecay : ∀ {m1 m2 xi : ℝ},
      m1 ≠ 0 → m2 ≠ 0 → xi ≠ 0 →
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
        ((m2 / m1) * xi)‖ ≤
        Cdec * T ^ (1 : ℝ) *
          (T / (|m2 / m1| * |xi|)) ^ (77 + 2 : ℕ) * S := by
    intro m1 m2 xi hm1R hm2R hxi
    have hz : (m2 / m1) * xi ≠ 0 :=
      mul_ne_zero (div_ne_zero hm2R hm1R) hxi
    simpa only [abs_mul] using hdecayProfile hz
  have hghat : Integrable
      (fun xi : ℝ => ‖FourierTransform.fourier
        (sourceGFinite (sourceSignedDyadicRange M1)
          (sourcePositiveDyadicRange M2)
          (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (fun u : ℝ => (f u : ℂ)) (M3 : ℝ)) xi‖ ^ 2) := by
    exact integrable_norm_sq_fourier_sourceGFinite_of_sourceProfile
      (sourceSignedDyadicRange M1) (sourcePositiveDyadicRange M2)
      (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
      hf (by norm_num : (0 : ℝ) < 1) hT0 hRlo hN10 hN20 hN30
      (by norm_num) hRhi (le_rfl) (le_rfl) (le_rfl) hm1 hm2 hpsi
      hratioLo hratioHi
  have hN1scale :
      ((sourceSignedDyadicRange M1).card : ℝ) ≤ 7 * T :=
    card_sourceSignedDyadicRange_cast_le_seven_mul_time hT hM1T
  have hN2scale :
      ((sourcePositiveDyadicRange M2).card : ℝ) ≤ 7 * T :=
    card_sourcePositiveDyadicRange_cast_le_seven_mul_time hT hM2T
  have hN3scale :
      ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ) ≤ 7 * T := by
    have hcard := card_centeredTwoScale_cast_le M3
    nlinarith
  have hprefix :
      ((sourceSignedDyadicRange M1).card : ℝ) *
          ((sourcePositiveDyadicRange M2).card : ℝ) *
          ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ) *
          (1 : ℝ) * (2 * T) * Cdec * S ≤
        (686 * Cdec * S) * T ^ (0 + 16) := by
    calc
      ((sourceSignedDyadicRange M1).card : ℝ) *
            ((sourcePositiveDyadicRange M2).card : ℝ) *
            ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ) *
            (1 : ℝ) * (2 * T) * Cdec * S ≤
          (7 * T) * (7 * T) * (7 * T) * 1 * (2 * T) * Cdec * S := by
            gcongr
      _ = (686 * Cdec * S) * T ^ 4 := by ring
      _ ≤ (686 * Cdec * S) * T ^ 16 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hT (show 4 ≤ 16 by omega))
          (by positivity)
      _ = (686 * Cdec * S) * T ^ (0 + 16) := by norm_num
  have hratioBudget : T / Rlo ≤ 2 * T ^ 5 :=
    sourceDyadic_reciprocal_ratio_le_two_mul_time_pow_five
      hM1 hM2 hT hM1T
  have henv := sourceHighFrequencyEnvelope_polynomialGrowth 0
    (T := T)
    (N1 := ((sourceSignedDyadicRange M1).card : ℝ))
    (N2 := ((sourcePositiveDyadicRange M2).card : ℝ))
    (N3 := ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ))
    (P1 := (1 : ℝ)) (Rhi := 2 * T) (Cdec := Cdec) (S := S)
    (Rlo := Rlo) (C := 686 * Cdec * S) (D := 2)
    hT hN10 hN20 hN30 (by norm_num) hRhi hCdec hS hRlo
    (by positivity) (by norm_num) hprefix hratioBudget
  have hK0 : 0 ≤
      ((sourceSignedDyadicRange M1).card : ℝ) *
        ((sourcePositiveDyadicRange M2).card : ℝ) *
        ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ) * (1 : ℝ) *
        (2 * T) * (Cdec * Real.rpow T 1 * (T / Rlo) ^ 79 * 2 ^ 79 * S) := by
    have hTpow : 0 ≤ Real.rpow T 1 := Real.rpow_nonneg hT0 _
    have hratio0 : 0 ≤ T / Rlo := div_nonneg hT0 hRlo.le
    have hterm : 0 ≤ Cdec * Real.rpow T 1 *
        (T / Rlo) ^ 79 * 2 ^ 79 * S := by
      positivity
    have hcardprod : 0 ≤
        ((sourceSignedDyadicRange M1).card : ℝ) *
          ((sourcePositiveDyadicRange M2).card : ℝ) *
          ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ) *
          (1 : ℝ) * (2 * T) := by
      positivity
    exact mul_nonneg hcardprod hterm
  have hCtail0 : 0 ≤ (686 * Cdec * S) * 2 ^ 79 * 2 ^ 79 := by
    positivity [hS, hCdec]
  have hbudget := sourceHighFrequencyBudget_of_polynomialGrowth 27
    (T := T)
    (K := ((sourceSignedDyadicRange M1).card : ℝ) *
      ((sourcePositiveDyadicRange M2).card : ℝ) *
      ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ) * (1 : ℝ) *
      (2 * T) * (Cdec * Real.rpow T 1 * (T / Rlo) ^ 79 * 2 ^ 79 * S))
    (C := (686 * Cdec * S) * 2 ^ 79 * 2 ^ 79)
    (B := quarticDecayMass)
    hT hK0 hCtail0
    (le_rfl : quarticDecayMass ≤ quarticDecayMass)
    (by simpa only [Nat.zero_add, mul_assoc] using henv)
  apply sourceGFinite_highFrequencyIntegral_le_time_neg100
    (sourceSignedDyadicRange M1) (sourcePositiveDyadicRange M2)
    (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
    (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
    (fun u : ℝ => (f u : ℂ)) hf.integrable.ofReal (M3 : ℝ) 77
    (T := T) (S := S) (eta := (1 : ℝ)) (Cdec := Cdec)
    (Rlo := Rlo)
    (N1 := ((sourceSignedDyadicRange M1).card : ℝ))
    (N2 := ((sourcePositiveDyadicRange M2).card : ℝ))
    (N3 := ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ))
    (P1 := (1 : ℝ)) (Rhi := 2 * T)
    (CIII := ((686 * Cdec * S) * 2 ^ 79 * 2 ^ 79) ^ 2 *
      quarticDecayMass)
    hT hf.bound_nonneg hCdec hRlo hN10 hN20 hN30 (by norm_num) hRhi
    (le_rfl) (le_rfl) (le_rfl) hm1 hm2 hpsi hratioLo hratioHi hdecay
    hghat.integrableOn
  simpa only [Rlo] using! hbudget

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.ownnewLemma92RegionHigh_commonCdec

namespace GuthMaynardJIteration

/-! The next corollary exposes the profile-size dependence instead of hiding
it inside the tail constant.  It is the useful form when a later source
consumer supplies a growth bound for `S`. -/
theorem ownnewLemma92RegionHigh_commonCdec_factored
    (Cdec : ℝ) (hCdec : 0 ≤ Cdec)
    {T S F : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    (hdecayProfile : ∀ {z : ℝ}, z ≠ 0 →
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
        Cdec * T ^ (1 : ℝ) * (T / |z|) ^ (79 : ℕ) * S)
    {M1 M2 M3 M : ℕ}
    (hT : 1 ≤ T)
    (hM1 : 0 < M1) (hM2 : 0 < M2) (hM3 : 0 < M3)
    (hM1M : M1 ≤ M) (hM2M : M2 ≤ M) (hM3M : M3 ≤ M)
    (hMT : (M : ℝ) ≤ T) :
    (∫ xi in highFrequencyRegion (sourceHighFrequencyCutoff T),
      ‖FourierTransform.fourier
        (sourceGFinite (sourceSignedDyadicRange M1)
          (sourcePositiveDyadicRange M2)
          (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (fun u : ℝ => (f u : ℂ)) (M3 : ℝ)) xi‖ ^ 2) ≤
      (((686 * Cdec) * 2 ^ 79 * 2 ^ 79) ^ 2 * quarticDecayMass * S ^ 2) /
        T ^ 100 := by
  have hraw := ownnewLemma92RegionHigh_commonCdec Cdec hCdec hf
    hdecayProfile hT hM1 hM2 hM3 hM1M hM2M hM3M hMT
  convert hraw using 1 <;> ring

/-! The S3 whole-frequency consumer already carries `S ≤ 1`; this removes
the explicit `S²` factor and gives an absolute `C/T^100` tail. -/
theorem ownnewLemma92RegionHigh_commonCdec_of_le_one
    (Cdec : ℝ) (hCdec : 0 ≤ Cdec)
    {T S F : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    (hdecayProfile : ∀ {z : ℝ}, z ≠ 0 →
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
        Cdec * T ^ (1 : ℝ) * (T / |z|) ^ (79 : ℕ) * S)
    (hS1 : S ≤ 1)
    {M1 M2 M3 M : ℕ}
    (hT : 1 ≤ T)
    (hM1 : 0 < M1) (hM2 : 0 < M2) (hM3 : 0 < M3)
    (hM1M : M1 ≤ M) (hM2M : M2 ≤ M) (hM3M : M3 ≤ M)
    (hMT : (M : ℝ) ≤ T) :
    (∫ xi in highFrequencyRegion (sourceHighFrequencyCutoff T),
      ‖FourierTransform.fourier
        (sourceGFinite (sourceSignedDyadicRange M1)
          (sourcePositiveDyadicRange M2)
          (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (fun u : ℝ => (f u : ℂ)) (M3 : ℝ)) xi‖ ^ 2) ≤
      ((686 * Cdec) * 2 ^ 79 * 2 ^ 79) ^ 2 * quarticDecayMass /
        T ^ 100 := by
  have hfact := ownnewLemma92RegionHigh_commonCdec_factored Cdec hCdec hf
    hdecayProfile hT hM1 hM2 hM3 hM1M hM2M hM3M hMT
  have hS0 : 0 ≤ S := hf.bound_nonneg
  have hSsq0 : S ^ 2 ≤ (1 : ℝ) ^ 2 :=
    (sq_le_sq₀ hS0 (by norm_num)).2 hS1
  have hSsq : S ^ 2 ≤ (1 : ℝ) := by simpa using hSsq0
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hmass0 : 0 ≤ quarticDecayMass := by
    unfold quarticDecayMass
    exact integral_nonneg (fun xi => by
      unfold quarticDecayEnvelope
      positivity)
  have hbase0 : 0 ≤ ((686 * Cdec) * 2 ^ 79 * 2 ^ 79) ^ 2 *
      quarticDecayMass := by
    positivity
  calc
    _ ≤ (((686 * Cdec) * 2 ^ 79 * 2 ^ 79) ^ 2 * quarticDecayMass * S ^ 2) /
        T ^ 100 := hfact
    _ ≤ (((686 * Cdec) * 2 ^ 79 * 2 ^ 79) ^ 2 * quarticDecayMass * 1) /
        T ^ 100 := by
      gcongr
    _ = ((686 * Cdec) * 2 ^ 79 * 2 ^ 79) ^ 2 * quarticDecayMass /
        T ^ 100 := by ring

#print axioms GuthMaynardJIteration.ownnewLemma92RegionHigh_commonCdec_factored
#print axioms GuthMaynardJIteration.ownnewLemma92RegionHigh_commonCdec_of_le_one

/-! A growth-aware ledger: if `S ≤ T^a`, use profile order `a+79` and
envelope order `a+77`.  This proves the absolute scalar `T^-100` budget; the
actual source call is kept separate so its `M₃` collar and Jacobian remain
visible at the consumer. -/
theorem ownnewLemma92RegionHigh_growth_budget
    (a : ℕ) (Cdec : ℝ) (hCdec : 0 ≤ Cdec)
    {T S : ℝ} (hT : 1 ≤ T) (hS : 0 ≤ S) (hSgrowth : S ≤ T ^ a)
    {M1 M2 M3 M : ℕ}
    (hM1 : 0 < M1) (hM2 : 0 < M2) (hM3 : 0 < M3)
    (hM1M : M1 ≤ M) (hM2M : M2 ≤ M) (hM3M : M3 ≤ M)
    (hMT : (M : ℝ) ≤ T) :
    (((((sourceSignedDyadicRange M1).card : ℝ) *
      ((sourcePositiveDyadicRange M2).card : ℝ) *
      ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ) * (1 : ℝ) *
      (2 * T) * (Cdec * Real.rpow T 1 *
        (T / ((M2 : ℝ) / (2 * M1 : ℝ))) ^ (a + 79) *
        2 ^ (a + 79) * S)) /
      (sourceHighFrequencyCutoff T) ^ (a + 77)) ^ 2 *
      quarticDecayMass * T ^ 100) ≤
      ((686 * Cdec) * 2 ^ (a + 79) * 2 ^ (a + 79)) ^ 2 *
        quarticDecayMass := by
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hM1T : (M1 : ℝ) ≤ T := by
    calc (M1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1M
      _ ≤ T := hMT
  have hM2T : (M2 : ℝ) ≤ T := by
    calc (M2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2M
      _ ≤ T := hMT
  have hM3T : (M3 : ℝ) ≤ T := by
    calc (M3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM3M
      _ ≤ T := hMT
  let Rlo : ℝ := (M2 : ℝ) / (2 * M1 : ℝ)
  have hRlo : 0 < Rlo := by dsimp only [Rlo]; positivity
  have hN10 : 0 ≤ ((sourceSignedDyadicRange M1).card : ℝ) := by positivity
  have hN20 : 0 ≤ ((sourcePositiveDyadicRange M2).card : ℝ) := by positivity
  have hN30 : 0 ≤ ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ) := by positivity
  have hN1scale : ((sourceSignedDyadicRange M1).card : ℝ) ≤ 7 * T :=
    card_sourceSignedDyadicRange_cast_le_seven_mul_time hT hM1T
  have hN2scale : ((sourcePositiveDyadicRange M2).card : ℝ) ≤ 7 * T :=
    card_sourcePositiveDyadicRange_cast_le_seven_mul_time hT hM2T
  have hN3scale : ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ) ≤ 7 * T := by
    have hcard := card_centeredTwoScale_cast_le M3
    nlinarith
  have hratioBudget : T / Rlo ≤ 2 * T ^ 5 :=
    sourceDyadic_reciprocal_ratio_le_two_mul_time_pow_five hM1 hM2 hT hM1T
  have hprefix :
      ((sourceSignedDyadicRange M1).card : ℝ) *
          ((sourcePositiveDyadicRange M2).card : ℝ) *
          ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ) *
          (1 : ℝ) * (2 * T) * Cdec * S ≤
        (686 * Cdec) * T ^ (a + 16) := by
    have hprod0 : 0 ≤
        ((sourceSignedDyadicRange M1).card : ℝ) *
          ((sourcePositiveDyadicRange M2).card : ℝ) *
          ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ) *
          (1 : ℝ) * (2 * T) * Cdec := by positivity
    calc
      _ ≤ ((sourceSignedDyadicRange M1).card : ℝ) *
          ((sourcePositiveDyadicRange M2).card : ℝ) *
          ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ) *
          (1 : ℝ) * (2 * T) * Cdec * T ^ a :=
            mul_le_mul_of_nonneg_left hSgrowth hprod0
      _ ≤ (7 * T) * (7 * T) * (7 * T) * 1 * (2 * T) * Cdec * T ^ a := by
            gcongr
      _ = (686 * Cdec) * T ^ (a + 4) := by ring
      _ ≤ (686 * Cdec) * T ^ (a + 16) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hT (by omega)) (by positivity)
  have henv := sourceHighFrequencyEnvelope_polynomialGrowth a
    (T := T) (N1 := ((sourceSignedDyadicRange M1).card : ℝ))
    (N2 := ((sourcePositiveDyadicRange M2).card : ℝ))
    (N3 := ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ))
    (P1 := (1 : ℝ)) (Rhi := 2 * T) (Cdec := Cdec) (S := S)
    (Rlo := Rlo) (C := 686 * Cdec) (D := 2)
    hT hN10 hN20 hN30 (by norm_num) (by positivity) hCdec hS hRlo
    (by positivity) (by norm_num) hprefix hratioBudget
  have hK0 : 0 ≤
      ((sourceSignedDyadicRange M1).card : ℝ) *
        ((sourcePositiveDyadicRange M2).card : ℝ) *
        ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ) * (1 : ℝ) *
        (2 * T) * (Cdec * Real.rpow T 1 * (T / Rlo) ^ (a + 79) *
          2 ^ (a + 79) * S) := by
    have hTpow : 0 ≤ Real.rpow T 1 := Real.rpow_nonneg hT0 _
    have hratio0 : 0 ≤ T / Rlo := div_nonneg hT0 hRlo.le
    have hterm : 0 ≤ Cdec * Real.rpow T 1 * (T / Rlo) ^ (a + 79) *
        2 ^ (a + 79) * S := by positivity
    have hfront : 0 ≤
        ((sourceSignedDyadicRange M1).card : ℝ) *
          ((sourcePositiveDyadicRange M2).card : ℝ) *
          ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ) *
          (1 : ℝ) * (2 * T) := by positivity
    exact mul_nonneg hfront hterm
  have hbudget := sourceHighFrequencyBudget_of_polynomialGrowth (a + 27)
    (T := T)
    (K := ((sourceSignedDyadicRange M1).card : ℝ) *
      ((sourcePositiveDyadicRange M2).card : ℝ) *
      ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ) * (1 : ℝ) *
      (2 * T) * (Cdec * Real.rpow T 1 * (T / Rlo) ^ (a + 79) *
        2 ^ (a + 79) * S))
    (C := (686 * Cdec) * 2 ^ (a + 79) * 2 ^ (a + 79))
    (B := quarticDecayMass)
    hT hK0 (by positivity) (le_rfl : quarticDecayMass ≤ quarticDecayMass)
    (by simpa [Nat.add_assoc, mul_assoc] using henv)
  simpa [Rlo, Nat.add_assoc, mul_assoc] using hbudget

#print axioms GuthMaynardJIteration.ownnewLemma92RegionHigh_growth_budget

end GuthMaynardJIteration
