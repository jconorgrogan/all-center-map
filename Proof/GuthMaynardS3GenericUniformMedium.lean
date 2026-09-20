import GuthMaynardS3MediumCanonicalInputs
import GuthMaynardS3ActualProfileInputs
import GuthMaynardS3MediumConcreteWeld
import GuthMaynardS3FirstPoissonAbsorption
import GuthMaynardS3FourierTailAbsorption
import GuthMaynardS3MediumActualWeightedTail
import GuthMaynardS3ZeroEllLowAbsorption
import GuthMaynardLemma92EllWindowSupport
import GuthMaynardS3NormalizedMainAbsorption
import GuthMaynardS3GenericConcreteWeld
import GuthMaynardS3WideGenericTail
import GuthMaynardS3AdmissibleProfileInputs

set_option maxHeartbeats 4000000
open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory Metric
noncomputable section
namespace GuthMaynardS3GenericUniformMedium
open MeasureTheory Metric
open GuthMaynardJIteration
open GuthMaynardS3MediumConcreteWeld
open GuthMaynardS3MediumCanonicalInputs
open GuthMaynardS3FirstPoissonAbsorption
open GuthMaynardS3FourierTailAbsorption
open GuthMaynardS3MediumActualWeightedTail
open GuthMaynardS3ZeroEllLowAbsorption
open GuthMaynardS3LiteralLemma84Outer
open GuthMaynardS3LiteralProfile
open GuthMaynardS3LiteralProfileFourier
open GuthMaynardHeathBrownInterface
open GuthMaynardS3NormalizedMainAbsorption
open GuthMaynardS3AdmissibleProfileInputs
open GuthMaynardS3ZeroEllProfile
open GuthMaynardS3GenericConcreteWeld
open GuthMaynardS3WideExtremesGeneric

/-- Elementary finite weighted tail bound used by the concrete weld. -/
theorem concrete_weighted_Q_bound
    {T eta D L1 : ℝ} {M2 N : ℕ}
    (hT : 1 ≤ T) (hD : 0 ≤ D)
    (hN : (N : ℝ) ≤ T ^ (4 : ℕ))
    (hcard : ((sourcePositiveDyadicRange M2).card : ℝ) ≤ N)
    (hL1 : 0 ≤ L1) :
    (∑ m2 ∈ sourcePositiveDyadicRange M2,
      ∑ m2' ∈ sourcePositiveDyadicRange M2,
        |(m2 : ℝ) * (m2' : ℝ)| *
          ((L1 ^ 2 * (2 * Real.rpow T eta)) *
            ((100 * D) / T ^ 100))) ≤
      (800 * D * Real.rpow T eta * (M2 : ℝ) ^ 2 * L1 ^ 2) *
        ((N : ℝ) ^ 2 / T ^ 100) := by
  have hT0 : 0 ≤ T := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hU : 0 ≤ Real.rpow T eta := Real.rpow_nonneg hT0 eta
  have hfactor : 0 ≤ (L1 ^ 2 * (2 * Real.rpow T eta)) *
      ((100 * D) / T ^ 100) := by positivity
  by_cases hM20 : M2 = 0
  · subst M2
    simp [sourcePositiveDyadicRange]
  have hM2pos : 0 < M2 := Nat.pos_of_ne_zero hM20
  have hm2bound : ∀ m2 ∈ sourcePositiveDyadicRange M2,
      |(m2 : ℝ)| ≤ 2 * (M2 : ℝ) := by
    intro m2 hm2
    exact (sourcePositiveDyadicRange_abs_bounds hM2pos hm2).2
  have hterm : ∀ m2 ∈ sourcePositiveDyadicRange M2,
      ∀ m2' ∈ sourcePositiveDyadicRange M2,
      |(m2 : ℝ) * (m2' : ℝ)| *
          ((L1 ^ 2 * (2 * Real.rpow T eta)) *
            ((100 * D) / T ^ 100)) ≤
        (4 * (M2 : ℝ) ^ 2) *
          ((L1 ^ 2 * (2 * Real.rpow T eta)) *
            ((100 * D) / T ^ 100)) := by
    intro m2 hm2 m2' hm2'
    have ha := hm2bound m2 hm2
    have hb := hm2bound m2' hm2'
    have habs : |(m2 : ℝ) * (m2' : ℝ)| ≤ 4 * (M2 : ℝ) ^ 2 := by
      rw [abs_mul]
      nlinarith [abs_nonneg (m2 : ℝ), abs_nonneg (m2' : ℝ)]
    exact mul_le_mul_of_nonneg_right habs hfactor
  calc
    (∑ m2 ∈ sourcePositiveDyadicRange M2,
      ∑ m2' ∈ sourcePositiveDyadicRange M2,
        |(m2 : ℝ) * (m2' : ℝ)| *
          ((L1 ^ 2 * (2 * Real.rpow T eta)) *
            ((100 * D) / T ^ 100))) ≤
      ∑ _m2 ∈ sourcePositiveDyadicRange M2,
        ∑ _m2' ∈ sourcePositiveDyadicRange M2,
          (4 * (M2 : ℝ) ^ 2) *
            ((L1 ^ 2 * (2 * Real.rpow T eta)) *
              ((100 * D) / T ^ 100)) := by
        apply Finset.sum_le_sum
        intro m2 hm2
        apply Finset.sum_le_sum
        intro m2' hm2'
        exact hterm m2 hm2 m2' hm2'
    _ = ((sourcePositiveDyadicRange M2).card : ℝ) ^ 2 *
        ((4 * (M2 : ℝ) ^ 2) *
          ((L1 ^ 2 * (2 * Real.rpow T eta)) *
            ((100 * D) / T ^ 100))) := by simp; ring
    _ ≤ (N : ℝ) ^ 2 *
        ((4 * (M2 : ℝ) ^ 2) *
          ((L1 ^ 2 * (2 * Real.rpow T eta)) *
            ((100 * D) / T ^ 100))) := by
      have hcard0 : 0 ≤ ((sourcePositiveDyadicRange M2).card : ℝ) := by positivity
      have hN0 : 0 ≤ (N : ℝ) := by positivity
      have hsquare : ((sourcePositiveDyadicRange M2).card : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 :=
        (sq_le_sq₀ hcard0 hN0).2 hcard
      gcongr
    _ = (800 * D * Real.rpow T eta * (M2 : ℝ) ^ 2 * L1 ^ 2) *
        ((N : ℝ) ^ 2 / T ^ 100) := by
      field_simp [ne_of_gt hTpos]
      ring


/-- A single decay order meeting both the outer-tail and reserve budgets. -/
theorem exists_decay_order
    {eta delta : ℝ} (heta : 0 < eta) (hdelta : 0 < delta) :
    ∃ q : ℕ, (300 : ℝ) ≤ eta * (q : ℝ) ∧
      eta + 107 ≤ delta * (q : ℝ) := by
  let X : ℝ := max (300 / eta) ((eta + 107) / delta)
  obtain ⟨q, hq⟩ := exists_nat_gt X
  refine ⟨q, ?_, ?_⟩
  · have hX : 300 / eta ≤ (q : ℝ) :=
      le_trans (le_max_left _ _) (le_of_lt hq)
    have hh := (div_le_iff₀ heta).mp hX
    simpa [mul_comm] using hh
  · have hX : (eta + 107) / delta ≤ (q : ℝ) :=
      le_trans (le_max_right _ _) (le_of_lt hq)
    have hh := (div_le_iff₀ hdelta).mp hX
    simpa [mul_comm] using hh

theorem generic_medium_uniform
    (Cdec : ℕ → ℝ) (hCdec_nonneg : ∀ q, 0 ≤ Cdec q)
    {eta delta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) (hdelta : 0 < delta) :
    ∃ Cfinal : ℝ, 0 < Cfinal ∧
      ∀ (T S F : ℝ) (f : ℝ → ℝ) (M M1 M2 M3 : ℕ)
        (hT7 : (7 : ℝ) ≤ T) (hT : 1 ≤ T) (hF0 : 0 ≤ F) (hFT : F ≤ T)
        (hF8 : F ≤ 8) (hS0 : 0 ≤ S) (hSgrowth : S ≤ T ^ (4 : ℝ)),
        1 ≤ (M : ℝ) → 1 ≤ M1 → 1 ≤ M2 → 1 ≤ M3 →
        (M1 : ℝ) ≤ M → (M2 : ℝ) ≤ M → (M3 : ℝ) ≤ M →
        (M : ℝ) ≤ T → M2 ≤ M3 → (M3 : ℝ) ≤ 16 * (M2 : ℝ) →
        SourceAdmissibleProfile T S F f →
        (∀ q : ℕ, (300 : ℝ) ≤ eta * q → ∀ z : ℝ, z ≠ 0 →
          ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
            Cdec q * T ^ eta * (T / |z|) ^ q * S) →
      (∫ xi in mediumFrequencyRegion
          (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
          (sourceHighFrequencyCutoff T),
        ‖FourierTransform.fourier
          (sourceGFinite (sourceSignedDyadicRange M1)
            (sourcePositiveDyadicRange M2) (sourceBumpEllRange 1 (M3 : ℝ) 1)
            (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
            (fun x : ℝ => (f x : ℂ)) (M3 : ℝ)) xi‖ ^ 2) ≤
        Cfinal * (Real.rpow T (3 * eta) * (M : ℝ) ^ 6 *
            (∫ u : ℝ, ‖(f u : ℂ)‖) ^ 2 +
          Real.rpow T (4 * eta + delta) * (M : ℝ) ^ 2 *
            Real.sqrt ((∫ u : ℝ, f u ^ 2) *
              sourceAffineJ
                (sourceAffineConfigs (sourcePositiveDyadicRange M2)
                  (sourceLemma92JRange M2 T F (2 * Real.rpow T delta)))
                (affineSmoothing T
                  (sourceBumpNormalized (Real.rpow T delta)
                    (Real.rpow_pos_of_pos (by linarith [hT7]) delta)) f))) + Cfinal / T ^ 100
  := by
  obtain ⟨q, hqtail, hreserve⟩ := exists_decay_order heta hdelta
  obtain ⟨Ceta, hCeta, hpack⟩ :=
    sourceGFinite_medium_canonical_inputs heta heta1
  let K0 : ℝ := sourceBumpFourierConstant 1 zero_lt_one 0
  let D : ℝ := sourceLemma92Decay q * integerQuadraticMass
  let C : ℝ := 4 * sourceBumpFourierConstant 1 zero_lt_one (q + 2) *
      integerQuadraticMass
  have hpreK : 0 ≤ K0 := sourceBumpFourierConstant_nonneg 1 zero_lt_one 0
  have hpreD : 0 ≤ D := mul_nonneg (sourceLemma92Decay_nonneg q) integerQuadraticMass_nonneg
  let Cfinal : ℝ :=
    8192 * Ceta * K0 ^ 3 +
      (9216 * K0 ^ 2 + 2304 * C ^ 2 + 25600 * Ceta * K0 ^ 2 * D) +
    256 * Ceta * K0 ^ 2 * (Cdec q) ^ 2 + 1
  have hCfinal : 0 < Cfinal := by
    dsimp [Cfinal]
    positivity
  refine ⟨Cfinal, hCfinal, ?_⟩
  intro T S F f M M1 M2 M3 hT7 hT hF0 hFT hF8 hS0 hSgrowthInput hM hM1 hM2 hM3 hM1M hM2M hM3M hMT hM2M3 hM3hi hf hdecay
  have hSgrowth : S ≤ T ^ (4 : ℝ) := hSgrowthInput
  obtain ⟨hcount, hcover, hxi, hEllCard, hbudget⟩ :=
    hpack T M1 M2 M3 q (by linarith) hM1 hM2 hM3 (hM1M.trans hMT) (hM3M.trans hMT) (by linarith [hqtail])
  let ellRange : Finset ℤ :=
    sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T eta)
  let m3Range : Finset ℤ := sourceBumpEllRange 1 (M3 : ℝ) 1
  let L1 : ℝ := ∫ u : ℝ, ‖(f u : ℂ)‖
  let F2 : ℝ := ∫ u : ℝ, (f u) ^ 2
  let J : ℝ := sourceAffineJ
      (sourceAffineConfigs (sourcePositiveDyadicRange M2)
        (sourceLemma92JRange M2 T F (2 * Real.rpow T delta)))
      (affineSmoothing T (sourceBumpNormalized (Real.rpow T delta)
        (Real.rpow_pos_of_pos (by linarith [hT7]) delta))
        (f))
  let Hinner : ℝ := 6 * (M2 : ℝ) ^ 2 / (M1 : ℝ) * L1
  have hT : 1 ≤ T := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hM1pos : 0 < M1 := lt_of_lt_of_le Nat.zero_lt_one hM1
  have hM2pos : 0 < M2 := lt_of_lt_of_le Nat.zero_lt_one hM2
  have hM3pos : 0 < M3 := lt_of_lt_of_le Nat.zero_lt_one hM3
  have hM2posR : 0 < (M2 : ℝ) := by exact_mod_cast hM2pos
  have hM3posR : 0 < (M3 : ℝ) := by exact_mod_cast hM3pos
  have hM1T : (M1 : ℝ) ≤ T := hM1M.trans (hMT)
  have hM3T : (M3 : ℝ) ≤ T := hM3M.trans hMT
  have hM2hiT : (M2 : ℝ) ≤ T ^ (4 : ℝ) := by
    have hM2T : (M2 : ℝ) ≤ T := hM2M.trans hMT
    calc
      (M2 : ℝ) ≤ T := hM2T
      _ ≤ T ^ (4 : ℝ) := by
        calc
          T = T ^ (1 : ℕ) := by simp
          _ ≤ T ^ (4 : ℕ) := pow_le_pow_right₀ hT (by omega)
          _ = T ^ (4 : ℝ) := by norm_num [Real.rpow_natCast]
  have hsupport : ∀ m3 : ℤ, m3 ∉ m3Range →
      (sourceBump 1 zero_lt_one ((m3 : ℝ) / (M3 : ℝ)) : ℂ) = 0 := by
    intro m3 hm3
    have hz := sourceBump_eq_zero_outside_sourceBumpEllRange
      (M := 1) (T := (M3 : ℝ)) (R := (1 : ℝ))
      (by norm_num) (by positivity) (by norm_num) hm3
    norm_num at hz
    simpa using hz
  have hinner : ∀ xi ∈ mediumFrequencyRegion
      (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
      (sourceHighFrequencyCutoff T), ∀ m1 ∈ sourceSignedDyadicRange M1,
      ‖sourceCorrectedM2FourierInner (sourcePositiveDyadicRange M2)
        (FourierTransform.fourier
          (fun u : ℝ => (f u : ℂ))) m1 xi‖ ≤ Hinner := by
    intro xi hxi' m1 hm1
    dsimp [Hinner, L1]
    exact admissible_profile_corrected_inner_le_L1 hT hf
      hM1 hM2 hm1 xi
  have hfullInt := admissible_profile_medium_fourier_integrableOn
    hT hf hM1 hM2 hM3 m3Range hM1T hM3T heta
  have hS : S ≤ T ^ (4 : ℝ) := hSgrowth
  have hdeltaB : 0 < Real.rpow T delta := Real.rpow_pos_of_pos hTpos _
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (sourceBumpFourierConstant_nonneg 1 zero_lt_one (q + 2)))
      integerQuadraticMass_nonneg
  have hL10 : 0 ≤ L1 := by dsimp [L1]; positivity
  have hHinner : 0 ≤ Hinner := by dsimp [Hinner]; positivity
  have hY : 0 ≤ T ^ 6 := by positivity
  have hM2lo : M2 ≤ M3 := hM2M3
  have hM3lo : (M2 : ℝ) ≤ M3 := by exact_mod_cast hM2M3
  have hm2lo : ∀ m2' ∈ sourcePositiveDyadicRange M2,
      (M2 : ℝ) ≤ |(m2' : ℝ)| :=
    fun m2' hm => (sourcePositiveDyadicRange_abs_bounds hM2pos hm).1
  have hm2hi : ∀ m2' ∈ sourcePositiveDyadicRange M2,
      |(m2' : ℝ)| ≤ 2 * (M2 : ℝ) :=
    fun m2' hm => (sourcePositiveDyadicRange_abs_bounds hM2pos hm).2
  have hcard : ((sourcePositiveDyadicRange M2).card : ℝ) ≤ T ^ (4 : ℝ) := by
    have hc := card_sourcePositiveDyadicRange_cast_le_three_mul hM2
    have hM2T : (M2 : ℝ) ≤ T := hM2M.trans hMT
    calc
      _ ≤ 3 * (M2 : ℝ) := hc
      _ ≤ 3 * T := by gcongr
      _ ≤ T ^ (4 : ℝ) := by
        have hT3 : (3 : ℝ) ≤ T ^ (3 : ℕ) := by
          have h6 : (6 : ℝ) ^ (3 : ℕ) ≤ T ^ (3 : ℕ) := by gcongr <;> linarith
          norm_num at h6 ⊢
          linarith
        calc
          3 * T ≤ T ^ 3 * T := by gcongr
          _ = T ^ (4 : ℕ) := by ring
          _ = T ^ (4 : ℝ) := by norm_num [Real.rpow_natCast]
  have htail := profile_sigmaIIEllTailFiniteLE
    (T := T) (S := S) (eta := eta) (M2 := (M2 : ℝ)) (M3 := (M3 : ℝ))
    (C := Cdec q) hT hSgrowth hM2posR hM3lo hM3posR hM2hiT ellRange
    (sourcePositiveDyadicRange M2) hEllCard hm2lo hm2hi hcard
    (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) heta heta1 hqtail
    (hdecay q hqtail) (hCdec_nonneg q) hS0
    (admissible_profile_fourier_continuous hT hf)
  have hbase := sourceGFinite_mediumIntegral_le_Ceta_actualNormalizedSigmaII_genericConcrete
    (Ctail := Cdec q) (T := T) (S := S) (F := F) (f := f) hf hF0 hFT (by linarith) hM1 hM2 hM3
    hM1M hM2M hM3M hT heta heta1 (le_of_lt hdelta) hM1T hM3T hCeta hY hC hHinner
    q ellRange m3Range hsupport hcount hbudget hcover hxi hinner hfullInt
    hM3lo hM3lo hM3hi hM2hiT hEllCard hm2lo hm2hi hcard hSgrowth
    hdeltaB hreserve hqtail htail
    (admissible_profile_fourier_continuous hT hf)
  have hK0 : 0 ≤ K0 := by
    dsimp [K0]
    exact sourceBumpFourierConstant_nonneg 1 zero_lt_one 0
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (sourceLemma92Decay_nonneg q) integerQuadraticMass_nonneg
  have hDouter : 0 ≤ Cdec q := hCdec_nonneg q
  have hL1' : 0 ≤ L1 := hL10
  have hNcard : ((sourcePositiveDyadicRange M2).card : ℝ) ≤ T ^ (4 : ℕ) := by
    exact_mod_cast hcard
  have hQ := concrete_weighted_Q_bound (T := T) (eta := eta) (D := D) (L1 := L1)
    (M2 := M2) (N := (sourcePositiveDyadicRange M2).card) hT hD
    hNcard (by rfl) hL1'
  have hQabs := weightedSigma_tail_le_actualLowMain
    (T := T) (eta := eta) (Ceta := Ceta) (K := K0) (M := (M : ℝ))
    (M1 := (M1 : ℝ)) (M2 := (M2 : ℝ)) (M3 := (M3 : ℝ))
    (D := D) (L := L1) (N := ((sourcePositiveDyadicRange M2).card : ℝ))
    (Q := (∑ m2 ∈ sourcePositiveDyadicRange M2,
      ∑ m2' ∈ sourcePositiveDyadicRange M2,
        |(m2 : ℝ) * (m2' : ℝ)| *
          ((L1 ^ 2 * (2 * Real.rpow T eta)) *
            ((100 * D) / T ^ 100))))
    hT (by positivity) (le_of_lt hCeta) hK0 (by linarith) (by positivity)
    (by positivity) (by positivity) hM1M hM2M hM3M hD hL1'
    (by positivity) (by simpa using hNcard) hQ
  have hmain := normalizedSigma_main_with_radius
    (T := T) (eta := eta) (delta := delta) (Ceta := Ceta) (K := K0)
    (M := (M : ℝ)) (M1 := (M1 : ℝ)) (M2 := (M2 : ℝ)) (M3 := (M3 : ℝ))
    (F2 := F2) (J := J) hT heta (le_of_lt hCeta) hK0 (by positivity)
    (by positivity) (by positivity) (by positivity) hM1M hM2M hM3M
  have hfourier := actualFourierTail_scalar_absorption
    (T := T) (eta := eta) (Ceta := Ceta) (K := K0)
    (D := Cdec q) (M1 := (M1 : ℝ))
    (M3 := (M3 : ℝ)) hT heta1 (le_of_lt hCeta) hK0 hDouter
    (by positivity) (by positivity) hM1T hM3T
  have hvol : volume.real (mediumFrequencyRegion
      (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
      (sourceHighFrequencyCutoff T)) ≤ 2 * T ^ 6 := by
    simpa only [sourceHighFrequencyCutoff] using
      volumeReal_mediumFrequencyRegion_le (by positivity : (0 : ℝ) ≤ T ^ 6)
  have hfirst := firstPoisson_scalar_absorption
    (T := T) (eta := eta) (M := (M : ℝ)) (M1 := (M1 : ℝ))
    (M2 := (M2 : ℝ)) (C := C) (H := Hinner) (L := L1)
    (vol := volume.real (mediumFrequencyRegion
      (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
      (sourceHighFrequencyCutoff T)))
    hT (by positivity) hM (by exact_mod_cast hM1pos) (by positivity) hM2M hC hHinner hL10
    (by positivity) hvol (by dsimp [Hinner]; linarith)
  have hzero :
      9216 * K0 ^ 2 * Real.rpow T eta * (M : ℝ) ^ 6 * L1 ^ 2 +
        2304 * C ^ 2 * Real.rpow T (3 * eta) * (M : ℝ) ^ 6 * L1 ^ 2 ≤
      (9216 * K0 ^ 2 + 2304 * C ^ 2) *
        Real.rpow T (3 * eta) * (M : ℝ) ^ 6 * L1 ^ 2 := by
    have hz := zeroEllTail_le_extendedLowMain (T := T) (eta := eta)
      (M := (M : ℝ)) hT heta (by positivity) L1 K0 hK0 hL10
    nlinarith
  have hbase' := hbase
  dsimp [L1, F2, J, K0, D, C, Hinner, ellRange, m3Range] at hbase'
  have hfourier' := hfourier
  have hneg100 : Real.rpow T (-100 : ℝ) = (T ^ 100)⁻¹ := by
    calc
      Real.rpow T (-100 : ℝ) = (Real.rpow T (100 : ℝ))⁻¹ :=
        Real.rpow_neg hTpos.le _
      _ = (T ^ 100)⁻¹ := by norm_num [Real.rpow_natCast]
  rw [hneg100] at hfourier'
  have hL1eq : L1 = ∫ u : ℝ, |f u| := by
    dsimp [L1]
    apply integral_congr_ae
    filter_upwards with u
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hL1norm : (∫ u : ℝ, ‖(f u : ℂ)‖) = L1 := by
    rfl
  rw [← hL1eq] at hbase'
  have hzero' :
      9216 * K0 ^ 2 * Real.rpow T eta * (M : ℝ) ^ 6 * L1 ^ 2 +
        2 * volume.real (mediumFrequencyRegion
          (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
          (sourceHighFrequencyCutoff T)) *
          (C / T ^ 100 * (4 * (M1 : ℝ) * Hinner)) ^ 2 ≤
      (9216 * K0 ^ 2 + 2304 * C ^ 2) *
        Real.rpow T (3 * eta) * (M : ℝ) ^ 6 * L1 ^ 2 := by
    nlinarith [hzero, hfirst]
  let A : ℝ := 16 * Ceta * Real.rpow T (2 * eta) * K0 ^ 2 *
    ((M1 : ℝ) + (M3 : ℝ))
  let U : ℝ := (2 * Real.rpow T eta * (4 * Real.rpow T eta * K0)) *
    (2 : ℝ) ^ 2 * (M2 : ℝ) *
      Real.sqrt ((∫ u : ℝ, f u ^ 2) *
        ((4 * Real.rpow T delta) ^ 2 * J))
  let V : ℝ := ∑ m2 ∈ sourcePositiveDyadicRange M2,
    ∑ m2' ∈ sourcePositiveDyadicRange M2,
      |(m2 : ℝ) * (m2' : ℝ)| *
        ((L1 ^ 2 * (2 * Real.rpow T eta)) *
          ((25 * 4 * sourceLemma92Decay q * integerQuadraticMass) / T ^ 100))
  let Z : ℝ := 2 * Real.rpow T eta *
    (4 * (Cdec q) ^ 2 *
      Real.rpow T (-229 : ℝ))
  let Z0 : ℝ := 9216 * K0 ^ 2 * Real.rpow T eta *
    (M : ℝ) ^ 6 * L1 ^ 2
  let P : ℝ := 2 * volume.real (mediumFrequencyRegion
    (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
    (sourceHighFrequencyCutoff T)) *
      (C / T ^ 100 * (4 * (M1 : ℝ) * Hinner)) ^ 2
  let Low : ℝ := Real.rpow T (3 * eta) * (M : ℝ) ^ 6 * L1 ^ 2
  let Main : ℝ := Real.rpow T (4 * eta + delta) * (M : ℝ) ^ 2 *
    Real.sqrt ((∫ u : ℝ, f u ^ 2) * J)
  let cmain : ℝ := 8192 * Ceta * K0 ^ 3
  let clow : ℝ := 9216 * K0 ^ 2 + 2304 * C ^ 2
  let cq : ℝ := 25600 * Ceta * K0 ^ 2 * D
  let cf : ℝ := 256 * Ceta * K0 ^ 2 *
    (Cdec q) ^ 2
  have hbase0 := hbase
  rw [← hL1eq] at hbase0
  rw [hL1norm] at hbase0
  have hbase_decomp : (∫ xi in mediumFrequencyRegion
      (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
      (sourceHighFrequencyCutoff T),
      ‖FourierTransform.fourier
        (sourceGFinite (sourceSignedDyadicRange M1)
          (sourcePositiveDyadicRange M2) m3Range
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (fun x : ℝ => (f x : ℂ)) (M3 : ℝ)) xi‖ ^ 2) ≤
      A * U + A * V + A * Z + Z0 + P := by
    calc
      _ ≤ A * (U + V + Z) + Z0 + P := by
        have hb := hbase0
        dsimp [A, U, V, Z, Z0, P, K0, D, C, Hinner] at hb ⊢
        convert hb using 1 <;> simp only [abs_mul] <;> ring
      _ = A * U + A * V + A * Z + Z0 + P := by ring
  have hmain0 : A * U ≤ cmain * Main := by
    have hh := hmain
    dsimp [A, U, cmain, Main, K0] at hh ⊢
    convert hh using 1 <;> ring
  have hq0 : A * V ≤ cq * Low := by
    have hVeq : V = ∑ m2 ∈ sourcePositiveDyadicRange M2,
        ∑ m2' ∈ sourcePositiveDyadicRange M2,
          |(m2 : ℝ) * (m2' : ℝ)| *
            ((L1 ^ 2 * (2 * Real.rpow T eta)) *
              ((100 * D) / T ^ 100)) := by
      dsimp [V, D]
      apply Finset.sum_congr rfl
      intro m2 hm2
      apply Finset.sum_congr rfl
      intro m2' hm2'
      ring
    rw [hVeq]
    have hh := hQabs
    dsimp [A, cq, Low, K0, L1, D] at hh ⊢
    convert hh using 1 <;> ring_nf
  have hf0 : A * Z ≤ cf * (T ^ 100)⁻¹ := by
    have hh := hfourier'
    dsimp [A, Z, cf, K0] at hh ⊢
    convert hh using 1 <;> ring
  have hz0 : Z0 + P ≤ clow * Low := by
    have hh := hzero'
    dsimp [Z0, P, clow, Low, K0, C, Hinner, L1] at hh ⊢
    convert hh using 1 <;> ring
  have hsum :
      A * U + A * V + A * Z + Z0 + P ≤
        cmain * Main + cq * Low + cf * (T ^ 100)⁻¹ + clow * Low := by
    linarith [hmain0, hq0, hf0, hz0]
  have hnonnegMain : 0 ≤ Main := by
    dsimp [Main]
    positivity
  have hnonnegLow : 0 ≤ Low := by
    dsimp [Low]
    positivity
  have hnonnegInv : 0 ≤ (T ^ 100)⁻¹ := by positivity
  have hcmain : 0 ≤ cmain := by dsimp [cmain]; positivity
  have hclow : 0 ≤ clow := by dsimp [clow]; positivity
  have hcq : 0 ≤ cq := by dsimp [cq]; positivity
  have hcf : 0 ≤ cf := by dsimp [cf]; positivity
  have hcfinal' : cmain + clow + cq + cf ≤ Cfinal := by
    dsimp [Cfinal, cmain, clow, cq, cf]
    linarith
  have hcmle : cmain ≤ Cfinal := by
    linarith [hcfinal', hclow, hcq, hcf]
  have hclowcqle : clow + cq ≤ Cfinal := by
    linarith [hcfinal', hcmain, hcf]
  have hcfle : cf ≤ Cfinal := by
    linarith [hcfinal', hcmain, hclow, hcq]
  have hfinal_bound :
      cmain * Main + cq * Low + cf * (T ^ 100)⁻¹ + clow * Low ≤
        Cfinal * (Low + Main) + Cfinal / T ^ 100 := by
    have hmainmono : cmain * Main ≤ Cfinal * Main := by
      exact mul_le_mul_of_nonneg_right hcmle hnonnegMain
    have hlowmono : (clow + cq) * Low ≤ Cfinal * Low := by
      exact mul_le_mul_of_nonneg_right hclowcqle hnonnegLow
    have hfourmono : cf * (T ^ 100)⁻¹ ≤ Cfinal / T ^ 100 := by
      have : cf * (T ^ 100)⁻¹ ≤ Cfinal * (T ^ 100)⁻¹ := by
        exact mul_le_mul_of_nonneg_right hcfle hnonnegInv
      simpa [div_eq_mul_inv] using this
    nlinarith [hmainmono, hlowmono, hfourmono]
  have hcombined :
      (∫ xi in mediumFrequencyRegion
          (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
          (sourceHighFrequencyCutoff T),
        ‖FourierTransform.fourier
          (sourceGFinite (sourceSignedDyadicRange M1)
            (sourcePositiveDyadicRange M2) m3Range
            (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
            (fun x : ℝ => (f x : ℂ)) (M3 : ℝ)) xi‖ ^ 2) ≤
      Cfinal * (Low + Main) + Cfinal / T ^ 100 := by
    exact hbase_decomp.trans (hsum.trans hfinal_bound)
  -- The remaining calculation is the scalar welding of the three central
  -- absorptions into the displayed `Cfinal` target.
  change (∫ xi in mediumFrequencyRegion
      (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
      (sourceHighFrequencyCutoff T),
      ‖FourierTransform.fourier
        (sourceGFinite (sourceSignedDyadicRange M1)
          (sourcePositiveDyadicRange M2) m3Range
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (fun x : ℝ => (f x : ℂ)) (M3 : ℝ)) xi‖ ^ 2) ≤ _
  have hh := hcombined
  dsimp [Low, Main, L1, F2, J] at hh ⊢
  convert hh using 1 <;> ring


end GuthMaynardS3GenericUniformMedium
#print axioms GuthMaynardS3GenericUniformMedium.generic_medium_uniform
