import GuthMaynardS3LiteralProfileFourier
import GuthMaynardS3LiteralLemma84Outer
import GuthMaynardJIterationSigmaII
import GuthMaynardS3MediumActualUnequalSplit
import GuthMaynardS3WideProfile

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardS3WideTail

open GuthMaynardJIteration
open GuthMaynardS3LiteralLemma84Outer
open GuthMaynardS3LiteralProfileFourier
open GuthMaynardS3MediumActualUnequalSplit
open GuthMaynardS3WideProfile

theorem wideProfile_fourier_decay_explicit
    {B T eta : ℝ} (hB : 0 < B) (hT : 1 ≤ T) (hBT : B ≤ T)
    (W : Finset ℝ) (q : ℕ) (heta : 0 < eta) :
    ∀ z : ℝ, z ≠ 0 →
      ‖FourierTransform.fourier
        (fun u : ℝ => (wideProfile B W u : ℂ)) z‖ ≤
      lemma84SmoothingFourierConstant q * T ^ eta *
        (T / |z|) ^ q * (4 * (W.card : ℝ) ^ 2) := by
  intro z hz
  have hdec := smoothedRatioSquare_fourier_le_timePow_mul_card
    hB hT hBT W q hz
  have hTeta : 1 ≤ T ^ eta := Real.one_le_rpow hT heta.le
  have hC : 0 ≤ lemma84SmoothingFourierConstant q :=
    lemma84SmoothingFourierConstant_nonneg q
  have hpow : 0 ≤ (T / |z|) ^ q := by positivity
  have hcard : 0 ≤ (W.card : ℝ) ^ 2 := sq_nonneg _
  dsimp [wideProfile]
  calc
    ‖FourierTransform.fourier
        (fun u : ℝ =>
          (GuthMaynardS3LiteralProfile.smoothedRatioSquare B W u : ℂ)) z‖ ≤
        lemma84SmoothingFourierConstant q * (W.card : ℝ) ^ 2 *
          (T / |z|) ^ q := hdec
    _ ≤ lemma84SmoothingFourierConstant q * T ^ eta *
        (T / |z|) ^ q * (4 * (W.card : ℝ) ^ 2) := by
      have h1 := mul_le_mul_of_nonneg_left hTeta hC
      have h2 := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (show (W.card : ℝ)^2 ≤
          4 * (W.card : ℝ)^2 by nlinarith [hcard]) (by positivity)) hpow
      nlinarith [h1, h2]

theorem wide_profile_decay_budget
    {T eta S C : ℝ} {q : ℕ} (hT : (1 : ℝ) ≤ T)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hS : 0 ≤ S)
    (hSgrowth : S ≤ T ^ (4 : ℝ)) (hC : 0 ≤ C)
    (hq : (300 : ℝ) ≤ eta * q) :
    C * T ^ eta * (1 / T ^ eta) ^ q * S ≤ C * T ^ (-295 : ℝ) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hpow : (1 / T ^ eta) ^ q = T ^ (-(eta * q)) := by
    rw [div_pow, one_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul (le_trans zero_le_one hT),
      one_div]
    exact (Real.rpow_neg (le_trans zero_le_one hT) _).symm
  have hcombine : T ^ eta * (1 / T ^ eta) ^ q = T ^ (eta - eta * q) := by
    rw [hpow, ← Real.rpow_add hTpos]
    congr 1 <;> ring
  have hexp : eta - eta * q + 4 ≤ (-295 : ℝ) := by nlinarith
  calc
    C * T ^ eta * (1 / T ^ eta) ^ q * S =
        C * (T ^ eta * (1 / T ^ eta) ^ q) * S := by ring
    _ = C * (T ^ (eta - eta * q)) * S := by rw [hcombine]
    _ ≤ C * (T ^ (eta - eta * q)) * T ^ (4 : ℝ) := by gcongr
    _ = C * T ^ (eta - eta * q + 4) := by
      have h := (Real.rpow_add hTpos (eta - eta * q) (4 : ℝ)).symm
      calc
        C * T ^ (eta - eta * q) * T ^ (4 : ℝ) =
            C * (T ^ (eta - eta * q) * T ^ (4 : ℝ)) := by ring
        _ = _ := by rw [h]
    _ ≤ C * T ^ (-295 : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT hexp) hC

theorem wide_m2_tail_polynomial_budget
    {T M2 C : ℝ} (hT : (1 : ℝ) ≤ T)
    (hM2 : M2 ≤ T ^ (4 : ℝ)) (hC : 0 ≤ C) :
    T ^ (4 : ℝ) * (2 * M2) * (C * T ^ (-295 : ℝ)) ≤
      2 * C * T ^ (-120 : ℝ) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hleft := show T ^ (4 : ℝ) * (2 * M2) * (C * T ^ (-295 : ℝ)) ≤
      T ^ (4 : ℝ) * (2 * T ^ (4 : ℝ)) * (C * T ^ (-295 : ℝ)) by gcongr
  have h1 : T ^ (4 : ℝ) * T ^ (4 : ℝ) = T ^ (8 : ℝ) := by
    rw [← Real.rpow_add hTpos]; norm_num
  have h2 : T ^ (8 : ℝ) * T ^ (-295 : ℝ) = T ^ (-287 : ℝ) := by
    rw [← Real.rpow_add hTpos]; norm_num
  calc
    _ ≤ T ^ (4 : ℝ) * (2 * T ^ (4 : ℝ)) * (C * T ^ (-295 : ℝ)) := hleft
    _ = 2 * C * T ^ (-287 : ℝ) := by
      calc
        T ^ (4 : ℝ) * (2 * T ^ (4 : ℝ)) *
            (C * T ^ (-295 : ℝ)) =
            2 * C * (T ^ (4 : ℝ) * T ^ (4 : ℝ) * T ^ (-295 : ℝ)) := by ring
        _ = 2 * C * T ^ (-287 : ℝ) := by rw [h1, h2]
    _ ≤ 2 * C * T ^ (-120 : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT (by norm_num)) (by positivity)

theorem wide_tail_square_card_budget
    {T C : ℝ} (hT : (1 : ℝ) ≤ T) (hC : 0 ≤ C) :
    T ^ (11 : ℝ) * (2 * C * T ^ (-120 : ℝ)) ^ 2 ≤
      4 * C ^ 2 * T ^ (-229 : ℝ) := by
  apply le_of_eq
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hpow : (T ^ (-120 : ℝ)) ^ (2 : ℕ) = T ^ (-240 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]; norm_num
  have hadd : T ^ (11 : ℝ) * T ^ (-240 : ℝ) = T ^ (-229 : ℝ) := by
    rw [← Real.rpow_add hTpos]; norm_num
  calc
    T ^ (11 : ℝ) * (2 * C * T ^ (-120 : ℝ)) ^ 2 =
        4 * C ^ 2 * (T ^ (11 : ℝ) * (T ^ (-120 : ℝ)) ^ 2) := by ring
    _ = 4 * C ^ 2 * T ^ (-229 : ℝ) := by rw [hpow, hadd]

/-! Scalar affine-tail kernel.  The profile is abstract here so the same
finite tail proof can be used with the uncut wide profile. -/
theorem wide_sum_norm_sq_sigmaII_affine_tail_le
    {T S eta M2 M3 C : ℝ} (hT : (1 : ℝ) ≤ T)
    (hM2pos : 0 < M2) (hM2M3 : M2 ≤ M3) (hM3pos : 0 < M3)
    (hM2growth : M2 ≤ T ^ (4 : ℝ))
    (ellRange m2Range : Finset ℤ)
    (hell : ∀ ell ∈ ellRange,
      4 * T ^ (1 + eta) / M2 < |(ell : ℝ)|)
    (hEllCard : (ellRange.card : ℝ) ≤ T ^ (11 : ℝ))
    (hm2lo : ∀ m2 ∈ m2Range, M2 ≤ |(m2 : ℝ)|)
    (hm2hi : ∀ m2 ∈ m2Range, |(m2 : ℝ)| ≤ 2 * M2)
    (hcard : (m2Range.card : ℝ) ≤ T ^ (4 : ℝ))
    (hSgrowth : S ≤ T ^ (4 : ℝ))
    (fhat : ℝ → ℂ) {q : ℕ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hq : (300 : ℝ) ≤ eta * q)
    (tau : ℝ) (htau : |tau| ≤ T ^ eta)
    (hdecay : ∀ z : ℝ, z ≠ 0 →
      ‖fhat z‖ ≤ C * T ^ eta * (T / |z|) ^ q * S)
    (hC : 0 ≤ C) (hS : 0 ≤ S) :
    ∑ ell ∈ ellRange,
      ‖∑ m2 ∈ m2Range,
        (m2 : ℂ) * fhat (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2 ≤
      4 * C ^ 2 * T ^ (-229 : ℝ) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hT0 : 0 ≤ T := hTpos.le
  have hTe : 0 ≤ T ^ eta := Real.rpow_nonneg hT0 eta
  have hTe1 : T ^ eta ≤ T ^ (1 + eta) := by
    have hadd : T ^ (1 + eta) = T * T ^ eta := by
      calc
        T ^ (1 + eta) = T ^ 1 * T ^ eta := Real.rpow_add hTpos 1 eta
        _ = T * T ^ eta := by
          exact congrArg (fun x : ℝ => x * T ^ eta) (Real.rpow_one T)
    rw [hadd]
    nlinarith
  have hpoint : ∀ ell ∈ ellRange, ∀ tau, |tau| ≤ T ^ eta →
      ‖∑ m2 ∈ m2Range, (m2 : ℂ) *
        fhat (sigmaIIAffineFrequency M3 ell m2 tau)‖ ≤
        2 * C * T ^ (-120 : ℝ) := by
    intro ell hellmem tau htau
    have hmain : 4 * T ^ (1 + eta) < |(ell : ℝ)| * M2 :=
      (div_lt_iff₀ hM2pos).mp (hell ell hellmem)
    have hfreq : ∀ m2 ∈ m2Range,
        2 * T ^ (1 + eta) <
          |sigmaIIAffineFrequency M3 ell m2 tau| := by
      intro m2 hm2
      have hmain' : 4 * T ^ (1 + eta) <
          |(ell : ℝ)| * |(m2 : ℝ)| := by
        have hmul := mul_le_mul_of_nonneg_left (hm2lo m2 hm2)
          (abs_nonneg (ell : ℝ))
        nlinarith [hmain]
      have hshift : |((m2 : ℝ) / M3) * tau| ≤ 2 * T ^ eta := by
        rw [abs_mul, abs_div, abs_of_pos hM3pos]
        have hr : |(m2 : ℝ)| / M3 ≤ 2 := by
          apply (div_le_iff₀ hM3pos).2
          nlinarith [hm2hi m2 hm2, hM2M3]
        exact mul_le_mul hr htau (abs_nonneg tau) (by positivity)
      have hshift' := hshift.trans
        (mul_le_mul_of_nonneg_left hTe1 (by norm_num : (0 : ℝ) ≤ 2))
      have hsum : |(ell : ℝ) * (m2 : ℝ)| ≤
          |sigmaIIAffineFrequency M3 ell m2 tau| +
            |((m2 : ℝ) / M3) * tau| := by
        calc
          |(ell : ℝ) * (m2 : ℝ)| =
              |sigmaIIAffineFrequency M3 ell m2 tau -
                ((m2 : ℝ) / M3) * tau| := by
                  congr 1
                  unfold sigmaIIAffineFrequency
                  ring
          _ ≤ _ := abs_sub _ _
      rw [abs_mul] at hsum
      nlinarith [hmain', hshift']
    have hterm : ∀ m2 ∈ m2Range,
        ‖fhat (sigmaIIAffineFrequency M3 ell m2 tau)‖ ≤ C * T ^ (-295 : ℝ) := by
      intro m2 hm2
      have hz := hfreq m2 hm2
      have hz0 : sigmaIIAffineFrequency M3 ell m2 tau ≠ 0 := by
        exact (abs_pos.mp (lt_of_lt_of_le (by positivity) hz.le))
      have hf := hdecay _ hz0
      have hfrac : T / |sigmaIIAffineFrequency M3 ell m2 tau| ≤ 1 / T ^ eta := by
        have hpowadd : T ^ (1 + eta) = T * T ^ eta := by
          calc
            T ^ (1 + eta) = T ^ 1 * T ^ eta := Real.rpow_add hTpos 1 eta
            _ = T * T ^ eta := by
              exact congrArg (fun x : ℝ => x * T ^ eta) (Real.rpow_one T)
        have h1 := div_le_div_of_nonneg_left hT0 (by positivity) hz.le
        have heq : T / (2 * T ^ (1 + eta)) = 1 / (2 * T ^ eta) := by
          rw [hpowadd]
          field_simp
        have hden : T ^ eta ≤ 2 * T ^ eta := by nlinarith [hTe]
        have h2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
          (Real.rpow_pos_of_pos hTpos eta) hden
        exact h1.trans_eq heq |>.trans h2
      have hp := pow_le_pow_left₀ (by positivity) hfrac q
      have hbudget : C * T ^ eta * (1 / T ^ eta) ^ q * S ≤
          C * T ^ (-295 : ℝ) := wide_profile_decay_budget
            hT heta heta1 hS hSgrowth hC hq
      calc
        ‖fhat (sigmaIIAffineFrequency M3 ell m2 tau)‖ ≤
            C * T ^ eta * (T / |sigmaIIAffineFrequency M3 ell m2 tau|) ^ q * S := hf
        _ ≤ C * T ^ eta * (1 / T ^ eta) ^ q * S := by gcongr
        _ ≤ C * T ^ (-295 : ℝ) := hbudget
    calc
      ‖∑ m2 ∈ m2Range, (m2 : ℂ) *
          fhat (sigmaIIAffineFrequency M3 ell m2 tau)‖ ≤
        ∑ m2 ∈ m2Range, ‖(m2 : ℂ) *
          fhat (sigmaIIAffineFrequency M3 ell m2 tau)‖ := norm_sum_le _ _
      _ ≤ ∑ _m2 ∈ m2Range, (2 * M2) * (C * T ^ (-295 : ℝ)) := by
        apply Finset.sum_le_sum
        intro m2 hm2
        rw [norm_mul, Complex.norm_intCast]
        exact mul_le_mul (hm2hi m2 hm2) (hterm m2 hm2)
          (norm_nonneg _) (by positivity)
      _ ≤ T ^ (4 : ℝ) * (2 * M2) * (C * T ^ (-295 : ℝ)) := by
        have hsum : (∑ _m2 ∈ m2Range,
            (2 * M2) * (C * T ^ (-295 : ℝ))) =
            (m2Range.card : ℝ) * ((2 * M2) *
              (C * T ^ (-295 : ℝ))) := by simp
        rw [hsum]
        have hfactor : 0 ≤ (2 * M2) * (C * T ^ (-295 : ℝ)) := by positivity
        calc
          (m2Range.card : ℝ) * ((2 * M2) * (C * T ^ (-295 : ℝ))) ≤
              T ^ (4 : ℝ) * ((2 * M2) * (C * T ^ (-295 : ℝ))) :=
            mul_le_mul_of_nonneg_right hcard hfactor
          _ = T ^ (4 : ℝ) * (2 * M2) * (C * T ^ (-295 : ℝ)) := by ring
      _ ≤ 2 * C * T ^ (-120 : ℝ) := by
        exact wide_m2_tail_polynomial_budget hT hM2growth hC
  have hsum := Finset.sum_le_sum (fun ell hell =>
    pow_le_pow_left₀ (norm_nonneg _) (hpoint ell hell tau htau) 2)
  calc
    ∑ ell ∈ ellRange,
        ‖∑ m2 ∈ m2Range,
          (m2 : ℂ) * fhat (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2 ≤
      ∑ _ell ∈ ellRange, (2 * C * T ^ (-120 : ℝ)) ^ 2 := hsum
    _ = (ellRange.card : ℝ) * (2 * C * T ^ (-120 : ℝ)) ^ 2 := by simp
    _ ≤ T ^ (11 : ℝ) * (2 * C * T ^ (-120 : ℝ)) ^ 2 := by
      gcongr
    _ ≤ 4 * C ^ 2 * T ^ (-229 : ℝ) := wide_tail_square_card_budget hT hC

theorem wideProfile_sum_norm_sq_sigmaII_affine_tail_le
    {B T eta : ℝ} (hB4 : (4 : ℝ) ≤ B) (hT : (1 : ℝ) ≤ T)
    (hBT : B ≤ T) (W : Finset ℝ)
    {M2 M3 : ℝ} (hM2pos : 0 < M2) (hM2M3 : M2 ≤ M3)
    (hM3pos : 0 < M3) (hM2growth : M2 ≤ T ^ (4 : ℝ))
    (ellRange m2Range : Finset ℤ)
    (hell : ∀ ell ∈ ellRange,
      4 * T ^ (1 + eta) / M2 < |(ell : ℝ)|)
    (hEllCard : (ellRange.card : ℝ) ≤ T ^ (11 : ℝ))
    (hm2lo : ∀ m2 ∈ m2Range, M2 ≤ |(m2 : ℝ)|)
    (hm2hi : ∀ m2 ∈ m2Range, |(m2 : ℝ)| ≤ 2 * M2)
    (hcard : (m2Range.card : ℝ) ≤ T ^ (4 : ℝ))
    (hSgrowth : 4 * (W.card : ℝ)^2 ≤ T ^ (4 : ℝ))
    {q : ℕ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hq : (300 : ℝ) ≤ eta * q) (tau : ℝ)
    (htau : |tau| ≤ T ^ eta) :
    ∑ ell ∈ ellRange,
      ‖∑ m2 ∈ m2Range,
        (m2 : ℂ) * FourierTransform.fourier
          (fun u : ℝ => (wideProfile B W u : ℂ))
          (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2 ≤
      4 * lemma84SmoothingFourierConstant q ^ 2 * T ^ (-229 : ℝ) := by
  have hS : 0 ≤ 4 * (W.card : ℝ)^2 := by positivity
  apply wide_sum_norm_sq_sigmaII_affine_tail_le hT hM2pos hM2M3 hM3pos
    hM2growth ellRange m2Range hell hEllCard hm2lo hm2hi hcard
    hSgrowth
      (fun z : ℝ => FourierTransform.fourier
        (fun u : ℝ => (wideProfile B W u : ℂ)) z)
      heta heta1 hq tau htau
    (wideProfile_fourier_decay_explicit (lt_of_lt_of_le (by norm_num) hB4)
      hT hBT W q heta) (lemma84SmoothingFourierConstant_nonneg q) hS

/-! Integrated finite-interval tail wrapper.  The only profile-specific input
is the concrete affine-tail sum bound above; the finite sum/interchange and
interval integration are handled in this module. -/
theorem wideProfile_sigmaIIEllTailFiniteLE
    {B T eta M2 M3 : ℝ} (hB4 : 4 ≤ B) (hT : 1 ≤ T)
    (hBT : B ≤ T) (W : Finset ℝ)
    (hSgrowth : 4 * (W.card : ℝ)^2 ≤ T ^ (4 : ℝ))
    (hM2pos : 0 < M2) (hM2M3 : M2 ≤ M3) (hM3pos : 0 < M3)
    (hM2growth : M2 ≤ T ^ (4 : ℝ))
    (ellRange m2Range : Finset ℤ)
    (hEllCard :
      ((ellRange.filter (fun ell : ℤ =>
        ¬ |(ell : ℝ)| ≤ 4 * Real.rpow T (1 + eta) / M2)).card : ℝ) ≤
        T ^ (11 : ℝ))
    (hm2lo : ∀ m2' ∈ m2Range, M2 ≤ |(m2' : ℝ)|)
    (hm2hi : ∀ m2' ∈ m2Range, |(m2' : ℝ)| ≤ 2 * M2)
    (hcard : (m2Range.card : ℝ) ≤ T ^ (4 : ℝ))
    {q : ℕ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hq : (300 : ℝ) ≤ eta * q)
    (hfhat : Continuous
      (FourierTransform.fourier
        (fun u : ℝ => (wideProfile B W u : ℂ)))) :
    sigmaIIEllTailFiniteLE ellRange m2Range
        ((4 * Real.rpow T eta) * T / M2) (fun _ => 1)
        (FourierTransform.fourier
          (fun u : ℝ => (wideProfile B W u : ℂ)))
        M2 T M3 (Real.rpow T eta) ≤
      (2 * Real.rpow T eta) *
        (4 * lemma84SmoothingFourierConstant q ^ 2 *
          Real.rpow T (-229 : ℝ)) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTeta0 : 0 ≤ Real.rpow T eta := Real.rpow_nonneg hTpos.le eta
  have hL : (4 * Real.rpow T eta) * T / M2 =
      4 * Real.rpow T (1 + eta) / M2 := by
    have hpowadd : Real.rpow T (1 + eta) = T * Real.rpow T eta := by
      calc
        Real.rpow T (1 + eta) = Real.rpow T 1 * Real.rpow T eta :=
          Real.rpow_add hTpos 1 eta
        _ = T * Real.rpow T eta := by norm_num
    rw [hpowadd]
    ring
  let tailRange : Finset ℤ := ellRange.filter (fun ell : ℤ =>
    ¬ |(ell : ℝ)| ≤ 4 * Real.rpow T (1 + eta) / M2)
  have htail := wideProfile_sum_norm_sq_sigmaII_affine_tail_le
    hB4 hT hBT W hM2pos hM2M3 hM3pos hM2growth
    tailRange m2Range
    (fun ell hell => lt_of_not_ge (Finset.mem_filter.mp hell).2)
    (by simpa only [tailRange] using hEllCard) hm2lo hm2hi hcard hSgrowth
    heta heta1 hq
  have htermInt : ∀ ell ∈ tailRange,
      IntervalIntegrable
        (fun tau : ℝ =>
          ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) *
              FourierTransform.fourier
                (fun u : ℝ => (wideProfile B W u : ℂ))
                (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2)
        volume (-Real.rpow T eta) (Real.rpow T eta) := by
    intro ell hell
    apply Continuous.intervalIntegrable
    unfold sigmaIIAffineFrequency
    fun_prop
  have hswap :
      (∑ ell ∈ tailRange,
        ∫ tau in -Real.rpow T eta..Real.rpow T eta,
          ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) *
              FourierTransform.fourier
                (fun u : ℝ => (wideProfile B W u : ℂ))
                (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2) =
      ∫ tau in -Real.rpow T eta..Real.rpow T eta,
        ∑ ell ∈ tailRange,
          ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) *
              FourierTransform.fourier
                (fun u : ℝ => (wideProfile B W u : ℂ))
                (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2 := by
    symm
    exact intervalIntegral.integral_finsetSum htermInt
  have hpoint : ∀ tau ∈ Set.Icc (-Real.rpow T eta) (Real.rpow T eta),
      ∑ ell ∈ tailRange,
          ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) *
              FourierTransform.fourier
                (fun u : ℝ => (wideProfile B W u : ℂ))
                (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2 ≤
        4 * lemma84SmoothingFourierConstant q ^ 2 *
          Real.rpow T (-229 : ℝ) := by
    intro tau htau
    exact htail tau (abs_le.2 ⟨htau.1, htau.2⟩)
  have hsumInt :
      IntervalIntegrable
        (fun tau : ℝ =>
          ∑ ell ∈ tailRange,
            ‖∑ m2 ∈ m2Range,
              (m2 : ℂ) *
                FourierTransform.fourier
                  (fun u : ℝ => (wideProfile B W u : ℂ))
                  (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2)
        volume (-Real.rpow T eta) (Real.rpow T eta) := by
    apply Continuous.intervalIntegrable
    unfold sigmaIIAffineFrequency
    fun_prop
  have hconstInt :
      IntervalIntegrable
        (fun _ : ℝ => 4 * lemma84SmoothingFourierConstant q ^ 2 *
          Real.rpow T (-229 : ℝ))
        volume (-Real.rpow T eta) (Real.rpow T eta) :=
    Continuous.intervalIntegrable continuous_const _ _
  have hmono := intervalIntegral.integral_mono_on
    (by linarith [hTeta0]) hsumInt hconstInt hpoint
  unfold sigmaIIEllTailFiniteLE sigmaIIFinite
  rw [hL]
  simp only [one_mul]
  calc
    (∑ x ∈ ellRange.filter (fun ell : ℤ =>
        ¬ |(ell : ℝ)| ≤ 4 * Real.rpow T (1 + eta) / M2),
        ∫ tau in -Real.rpow T eta..Real.rpow T eta,
          ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) *
              FourierTransform.fourier
                (fun u : ℝ => (wideProfile B W u : ℂ))
                (sigmaIIAffineFrequency M3 x m2 tau)‖ ^ 2) =
      ∫ tau in -Real.rpow T eta..Real.rpow T eta,
        ∑ ell ∈ tailRange,
          ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) *
              FourierTransform.fourier
                (fun u : ℝ => (wideProfile B W u : ℂ))
                (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2 := by
      simpa only [tailRange] using hswap
    _ ≤ ∫ tau in -Real.rpow T eta..Real.rpow T eta,
        4 * lemma84SmoothingFourierConstant q ^ 2 *
          Real.rpow T (-229 : ℝ) := hmono
    _ = (2 * Real.rpow T eta) *
        (4 * lemma84SmoothingFourierConstant q ^ 2 *
          Real.rpow T (-229 : ℝ)) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

end GuthMaynardS3WideTail

#print axioms GuthMaynardS3WideTail.wide_sum_norm_sq_sigmaII_affine_tail_le
#print axioms GuthMaynardS3WideTail.wideProfile_fourier_decay_explicit
#print axioms GuthMaynardS3WideTail.wideProfile_sum_norm_sq_sigmaII_affine_tail_le
#print axioms GuthMaynardS3WideTail.wideProfile_sigmaIIEllTailFiniteLE
