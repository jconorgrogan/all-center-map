import GuthMaynardS3LiteralLemma84Outer
import GuthMaynardJIterationSigmaII

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardS3LiteralLemma84Outer

open GuthMaynardJIteration
open GuthMaynardS3LiteralProfile
open GuthMaynardS3LiteralProfileFourier
open GuthMaynardHeathBrownInterface

/-! A small arithmetic budget for the literal outer-profile Fourier decay.
The profile theorem supplies `C_q * T^eta * (T/|z|)^q * S`; the hypothesis
`eta*q ≥ 300` pays the four powers of the raw profile height and the finite
`m₂` sum with ample room below `T^-120`. -/
theorem profile_fourier_decay_budget
    {T eta S C : ℝ} {q : ℕ}
    (hT : (1 : ℝ) ≤ T) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hS0 : 0 ≤ S) (hS : S ≤ T ^ (4 : ℝ)) (hC : 0 ≤ C)
    (hq : (300 : ℝ) ≤ eta * q) :
    C * T ^ eta * (1 / T ^ eta) ^ q * S ≤ C * T ^ (-295 : ℝ) := by
  have hT0 : 0 ≤ T := hT.trans' (by norm_num)
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hpow : (1 / T ^ eta) ^ q = T ^ (-(eta * q)) := by
    rw [div_pow, one_pow]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hT0]
    rw [one_div]
    exact (Real.rpow_neg hT0 _).symm
  have hcombine : T ^ eta * (1 / T ^ eta) ^ q =
      T ^ (eta - eta * q) := by
    rw [hpow]
    rw [← Real.rpow_add hTpos]
    congr 1 <;> ring
  have hexp : eta - eta * q + 4 ≤ (-295 : ℝ) := by
    nlinarith
  have hSbound : C * (T ^ (eta - eta * q)) * S ≤
      C * (T ^ (eta - eta * q)) * T ^ (4 : ℝ) := by
    gcongr
  calc
    C * T ^ eta * (1 / T ^ eta) ^ q * S =
        C * (T ^ eta * (1 / T ^ eta) ^ q) * S := by ring
    _ = C * (T ^ (eta - eta * q)) * S := by rw [hcombine]
    _ ≤ C * (T ^ (eta - eta * q)) * T ^ (4 : ℝ) := hSbound
    _ = C * T ^ (eta - eta * q + 4) := by
      have hadd := (Real.rpow_add hTpos (eta - eta * q) (4 : ℝ)).symm
      calc
        C * (T ^ (eta - eta * q)) * T ^ (4 : ℝ) =
            C * (T ^ (eta - eta * q) * T ^ (4 : ℝ)) := by ring
        _ = C * T ^ (eta - eta * q + 4) := by rw [hadd]
    _ ≤ C * T ^ (-295 : ℝ) := by
      apply mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT hexp)
        hC

theorem m2_tail_polynomial_budget
    {T M2 C : ℝ} (hT : (1 : ℝ) ≤ T)
    (hM2 : M2 ≤ T ^ (4 : ℝ)) (hC : 0 ≤ C) :
    T ^ (4 : ℝ) * (2 * M2) * (C * T ^ (-295 : ℝ)) ≤
      2 * C * T ^ (-120 : ℝ) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hleft : T ^ (4 : ℝ) * (2 * M2) * (C * T ^ (-295 : ℝ)) ≤
      T ^ (4 : ℝ) * (2 * T ^ (4 : ℝ)) * (C * T ^ (-295 : ℝ)) := by
    gcongr
  have hadd1 : T ^ (4 : ℝ) * T ^ (4 : ℝ) = T ^ (8 : ℝ) := by
    rw [← Real.rpow_add hTpos]
    norm_num
  have hadd2 : T ^ (8 : ℝ) * T ^ (-295 : ℝ) = T ^ (-287 : ℝ) := by
    rw [← Real.rpow_add hTpos]
    norm_num
  have hpow : T ^ (-287 : ℝ) ≤ T ^ (-120 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hT
    norm_num
  calc
    _ ≤ T ^ (4 : ℝ) * (2 * T ^ (4 : ℝ)) *
        (C * T ^ (-295 : ℝ)) := hleft
    _ = 2 * C * (T ^ (4 : ℝ) * T ^ (4 : ℝ) * T ^ (-295 : ℝ)) := by ring
    _ = 2 * C * T ^ (-287 : ℝ) := by rw [hadd1, hadd2]
    _ ≤ 2 * C * T ^ (-120 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)

theorem tail_square_card_budget
    {T C : ℝ} (hT : (1 : ℝ) ≤ T) (hC : 0 ≤ C) :
    T ^ (11 : ℝ) * (2 * C * T ^ (-120 : ℝ)) ^ 2 ≤
      4 * C ^ 2 * T ^ (-229 : ℝ) := by
  apply le_of_eq
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hpow : (T ^ (-120 : ℝ)) ^ (2 : ℕ) = T ^ (-240 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hTpos.le]
    norm_num
  have hadd : T ^ (11 : ℝ) * T ^ (-240 : ℝ) = T ^ (-229 : ℝ) := by
    rw [← Real.rpow_add hTpos]
    norm_num
  calc
    T ^ (11 : ℝ) * (2 * C * T ^ (-120 : ℝ)) ^ 2 =
        4 * C ^ 2 * (T ^ (11 : ℝ) * (T ^ (-120 : ℝ)) ^ 2) := by ring
    _ = 4 * C ^ 2 * T ^ (-229 : ℝ) := by
      rw [hpow, hadd]

/-! Pointwise tail for the literal Sigma-II coefficient sum.  The range
assumptions are intentionally explicit: this is the exact finite object used
by the later medium weld, with no abstract Fourier-decay premise. -/
theorem norm_sigmaII_affine_sum_tail_le
    {B T S eta : ℝ} (hB : (4 : ℝ) ≤ B) (hT : (1 : ℝ) ≤ T)
    (hBT : B ≤ T) (W : Finset ℝ)
    (hW : ContainedInIntervalOfLength W T)
    (hS0 : 0 ≤ S) (hS : ∀ u, lemma84Profile B W u ≤ S)
    (hSgrowth : S ≤ T ^ (4 : ℝ))
    {M2 M3 : ℝ} (hM2pos : 0 < M2) (hM2M3 : M2 ≤ M3)
    (hM3pos : 0 < M3) (hM2growth : M2 ≤ T ^ (4 : ℝ))
    {ell : ℤ} (hell : 4 * T ^ (1 + eta) / M2 < |(ell : ℝ)|)
    {tau : ℝ} (htau : |tau| ≤ T ^ eta)
    (m2Range : Finset ℤ)
    (hcard : (m2Range.card : ℝ) ≤ T ^ (4 : ℝ))
    (hm2lo : ∀ m2 ∈ m2Range, M2 ≤ |(m2 : ℝ)|)
    (hm2hi : ∀ m2 ∈ m2Range, |(m2 : ℝ)| ≤ 2 * M2)
    {q : ℕ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hq : (300 : ℝ) ≤ eta * q) :
    ‖∑ m2 ∈ m2Range,
      (m2 : ℂ) * FourierTransform.fourier
        (fun u : ℝ => (lemma84Profile B W u : ℂ))
        (sigmaIIAffineFrequency M3 ell m2 tau)‖ ≤
      2 * lemma84OuterSupFourierConstant q * T ^ (-120 : ℝ) := by
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
  have hmain : 4 * T ^ (1 + eta) < |(ell : ℝ)| * M2 :=
    (div_lt_iff₀ hM2pos).mp hell
  have hfreq_lower {m2 : ℤ} (hm2 : m2 ∈ m2Range) :
      2 * T ^ (1 + eta) <
        |sigmaIIAffineFrequency M3 ell m2 tau| := by
    have hmain' : 4 * T ^ (1 + eta) <
        |(ell : ℝ)| * |(m2 : ℝ)| := by
      have hmul := mul_le_mul_of_nonneg_left (hm2lo m2 hm2)
        (abs_nonneg (ell : ℝ))
      nlinarith [hmain]
    have hshift : |((m2 : ℝ) / M3) * tau| ≤ 2 * T ^ eta := by
      rw [abs_mul, abs_div, abs_of_pos hM3pos]
      have hratio : |(m2 : ℝ)| / M3 ≤ 2 := by
        apply (div_le_iff₀ hM3pos).2
        nlinarith [hm2hi m2 hm2, hM2M3]
      exact mul_le_mul (hratio) htau (abs_nonneg tau) (by positivity)
    have hshift' : |((m2 : ℝ) / M3) * tau| ≤
        2 * T ^ (1 + eta) :=
      hshift.trans (mul_le_mul_of_nonneg_left hTe1 (by norm_num))
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
        _ ≤ |sigmaIIAffineFrequency M3 ell m2 tau| +
            |((m2 : ℝ) / M3) * tau| := abs_sub _ _
    have hmainabs : |(ell : ℝ) * (m2 : ℝ)| =
        |(ell : ℝ)| * |(m2 : ℝ)| := by rw [abs_mul]
    rw [hmainabs] at hsum
    nlinarith [hmain', hshift']
  have hC0 : 0 ≤ lemma84OuterSupFourierConstant q :=
    lemma84OuterSupFourierConstant_nonneg q
  have hdecay : ∀ z : ℝ, z ≠ 0 →
      ‖FourierTransform.fourier
          (fun u : ℝ => (lemma84Profile B W u : ℂ)) z‖ ≤
        lemma84OuterSupFourierConstant q * T ^ eta *
          (T / |z|) ^ q * S := by
    intro z hz
    have hraw := lemma84Profile_fourier_le_timePow_mul_sup
      hB hT hBT W hW hS hS0 q hz
    have hTeta : 1 ≤ T ^ eta := Real.one_le_rpow hT heta.le
    calc
      ‖FourierTransform.fourier
          (fun u : ℝ => (lemma84Profile B W u : ℂ)) z‖ ≤
          lemma84OuterSupFourierConstant q * (T / |z|) ^ q * S := by
        simpa only [lemma84ProfileC] using hraw
      _ ≤ lemma84OuterSupFourierConstant q * T ^ eta *
          (T / |z|) ^ q * S := by
        have hmul := mul_le_mul_of_nonneg_left hTeta hC0
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_right hmul
            (mul_nonneg (by positivity) hS0))
  have hterm {m2 : ℤ} (hm2 : m2 ∈ m2Range) :
      ‖FourierTransform.fourier
          (fun u : ℝ => (lemma84Profile B W u : ℂ))
          (sigmaIIAffineFrequency M3 ell m2 tau)‖ ≤
        lemma84OuterSupFourierConstant q * T ^ (-295 : ℝ) := by
    have hfreq := hfreq_lower hm2
    have hfreqpos : 0 < |sigmaIIAffineFrequency M3 ell m2 tau| :=
      lt_of_lt_of_le (by positivity) hfreq.le
    have hfreqne : sigmaIIAffineFrequency M3 ell m2 tau ≠ 0 :=
      (abs_pos.mp hfreqpos)
    have hpowadd : T ^ (1 + eta) = T * T ^ eta := by
      calc
        T ^ (1 + eta) = T ^ 1 * T ^ eta := Real.rpow_add hTpos 1 eta
        _ = T * T ^ eta := by
          exact congrArg (fun x : ℝ => x * T ^ eta) (Real.rpow_one T)
    have hfrac1 : T / |sigmaIIAffineFrequency M3 ell m2 tau| ≤
        T / (2 * T ^ (1 + eta)) := by
      exact div_le_div_of_nonneg_left hT0
        (by positivity) hfreq.le
    have hfrac1eq : T / (2 * T ^ (1 + eta)) =
        1 / (2 * T ^ eta) := by
      rw [hpowadd]
      field_simp
    have hfrac2 : 1 / (2 * T ^ eta) ≤ 1 / T ^ eta := by
      exact div_le_div_of_nonneg_left (by norm_num)
        (by positivity : (0 : ℝ) < T ^ eta) (by nlinarith [hTe])
    have hfrac : T / |sigmaIIAffineFrequency M3 ell m2 tau| ≤
        1 / T ^ eta := hfrac1.trans_eq hfrac1eq |>.trans hfrac2
    have hpowfrac :
        (T / |sigmaIIAffineFrequency M3 ell m2 tau|) ^ q ≤
          (1 / T ^ eta) ^ q := by
      exact pow_le_pow_left₀ (by positivity) hfrac q
    calc
      ‖FourierTransform.fourier
          (fun u : ℝ => (lemma84Profile B W u : ℂ))
          (sigmaIIAffineFrequency M3 ell m2 tau)‖ ≤
        lemma84OuterSupFourierConstant q * T ^ eta *
            (T / |sigmaIIAffineFrequency M3 ell m2 tau|) ^ q * S :=
        hdecay _ hfreqne
      _ ≤ lemma84OuterSupFourierConstant q * T ^ eta *
          (1 / T ^ eta) ^ q * S := by
        gcongr
      _ ≤ lemma84OuterSupFourierConstant q * T ^ (-295 : ℝ) :=
        profile_fourier_decay_budget hT heta heta1 hS0 hSgrowth hC0 hq
  calc
    ‖∑ m2 ∈ m2Range,
        (m2 : ℂ) * FourierTransform.fourier
          (fun u : ℝ => (lemma84Profile B W u : ℂ))
          (sigmaIIAffineFrequency M3 ell m2 tau)‖ ≤
      ∑ m2 ∈ m2Range,
        ‖(m2 : ℂ) * FourierTransform.fourier
          (fun u : ℝ => (lemma84Profile B W u : ℂ))
          (sigmaIIAffineFrequency M3 ell m2 tau)‖ := norm_sum_le _ _
    _ ≤ ∑ _m2 ∈ m2Range,
        (2 * M2) *
          (lemma84OuterSupFourierConstant q * T ^ (-295 : ℝ)) := by
      apply Finset.sum_le_sum
      intro m2 hm2
      rw [norm_mul, Complex.norm_intCast]
      exact mul_le_mul (hm2hi m2 hm2) (hterm hm2)
        (norm_nonneg _) (by positivity)
    _ = (m2Range.card : ℝ) * ((2 * M2) *
          (lemma84OuterSupFourierConstant q * T ^ (-295 : ℝ))) := by
      simp
    _ ≤ T ^ (4 : ℝ) * ((2 * M2) *
          (lemma84OuterSupFourierConstant q * T ^ (-295 : ℝ))) := by
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ 2 * lemma84OuterSupFourierConstant q * T ^ (-120 : ℝ) := by
      simpa [mul_assoc] using m2_tail_polynomial_budget hT hM2growth hC0

/-! Summing the pointwise tail over an explicit large-`ell` set keeps the
profile height squared and records the finite `T^11` cardinality budget. -/
theorem sum_norm_sq_sigmaII_affine_tail_le
    {B T S eta : ℝ} (hB : (4 : ℝ) ≤ B) (hT : (1 : ℝ) ≤ T)
    (hBT : B ≤ T) (W : Finset ℝ)
    (hW : ContainedInIntervalOfLength W T)
    (hS0 : 0 ≤ S) (hS : ∀ u, lemma84Profile B W u ≤ S)
    (hSgrowth : S ≤ T ^ (4 : ℝ))
    {M2 M3 : ℝ} (hM2pos : 0 < M2) (hM2M3 : M2 ≤ M3)
    (hM3pos : 0 < M3) (hM2growth : M2 ≤ T ^ (4 : ℝ))
    (ellRange m2Range : Finset ℤ)
    (hell : ∀ ell ∈ ellRange,
      4 * T ^ (1 + eta) / M2 < |(ell : ℝ)|)
    (hEllCard : (ellRange.card : ℝ) ≤ T ^ (11 : ℝ))
    (hm2lo : ∀ m2 ∈ m2Range, M2 ≤ |(m2 : ℝ)|)
    (hm2hi : ∀ m2 ∈ m2Range, |(m2 : ℝ)| ≤ 2 * M2)
    (hcard : (m2Range.card : ℝ) ≤ T ^ (4 : ℝ))
    {q : ℕ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hq : (300 : ℝ) ≤ eta * q) (tau : ℝ)
    (htau : |tau| ≤ T ^ eta) :
    ∑ ell ∈ ellRange,
      ‖∑ m2 ∈ m2Range,
        (m2 : ℂ) * FourierTransform.fourier
          (fun u : ℝ => (lemma84Profile B W u : ℂ))
          (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2 ≤
      4 * lemma84OuterSupFourierConstant q ^ 2 * T ^ (-229 : ℝ) := by
  let C : ℝ := 2 * lemma84OuterSupFourierConstant q * T ^ (-120 : ℝ)
  have hCq : 0 ≤ lemma84OuterSupFourierConstant q :=
    lemma84OuterSupFourierConstant_nonneg q
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num) hCq)
      (Real.rpow_nonneg (le_trans zero_le_one hT) _)
  have hpoint : ∀ ell ∈ ellRange,
      ‖∑ m2 ∈ m2Range,
          (m2 : ℂ) * FourierTransform.fourier
            (fun u : ℝ => (lemma84Profile B W u : ℂ))
            (sigmaIIAffineFrequency M3 ell m2 tau)‖ ≤ C := by
    intro ell hellmem
    dsimp [C]
    exact norm_sigmaII_affine_sum_tail_le hB hT hBT W hW hS0 hS hSgrowth
      hM2pos hM2M3 hM3pos hM2growth (hell ell hellmem) htau m2Range hcard
      hm2lo hm2hi heta heta1 hq
  have hsum :
      ∑ ell ∈ ellRange,
        ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) * FourierTransform.fourier
              (fun u : ℝ => (lemma84Profile B W u : ℂ))
              (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2 ≤
        (ellRange.card : ℝ) * C ^ 2 := by
    calc
      ∑ ell ∈ ellRange,
          ‖∑ m2 ∈ m2Range,
              (m2 : ℂ) * FourierTransform.fourier
                (fun u : ℝ => (lemma84Profile B W u : ℂ))
                (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2 ≤
        ∑ _ell ∈ ellRange, C ^ 2 := by
          apply Finset.sum_le_sum
          intro ell hellmem
          exact pow_le_pow_left₀ (norm_nonneg _) (hpoint ell hellmem) 2
      _ = (ellRange.card : ℝ) * C ^ 2 := by simp
  have hcardbound : (ellRange.card : ℝ) * C ^ 2 ≤
      T ^ (11 : ℝ) * C ^ 2 :=
    mul_le_mul_of_nonneg_right hEllCard (sq_nonneg C)
  calc
    _ ≤ (ellRange.card : ℝ) * C ^ 2 := hsum
    _ ≤ T ^ (11 : ℝ) * C ^ 2 := hcardbound
    _ ≤ 4 * lemma84OuterSupFourierConstant q ^ 2 * T ^ (-229 : ℝ) := by
      dsimp [C]
      simpa [mul_assoc] using
        tail_square_card_budget hT hCq

end GuthMaynardS3LiteralLemma84Outer

#print axioms GuthMaynardS3LiteralLemma84Outer.norm_sigmaII_affine_sum_tail_le
