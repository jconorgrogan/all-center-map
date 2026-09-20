import GuthMaynardLemma92ConcreteBump

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory Metric

noncomputable section
namespace GuthMaynardJIteration

/-!
# The literal second-Poisson scalar budget

This file keeps the complete scalar factor in Lemma 9.2 visible.  The source
scale bounds cost `T^107`.  For the source-compatible choice `B=T^δ`, the
reserve is therefore exactly `δ*q-107`; the decay order `q` must be chosen
after `δ`.

The earlier diagnostic `B=T^6`, `q=20` is retained below as a scalar stress
test: it has a thirteen-power reserve.  It is *not* a source Lemma 9.2 iteration
endpoint, because `T^6` is the source's high-frequency `ξ` cutoff, whereas
the affine smoothing bump has support only `T^δ` (up to a fixed constant).
-/

/-- The concrete order-22 Fourier seminorm used when the tail order is
`q = 20`. -/
def sourceLemma92Decay20 : ℝ :=
  sourceBumpFourierConstant 1 zero_lt_one 22

theorem sourceLemma92Decay20_nonneg : 0 ≤ sourceLemma92Decay20 := by
  exact sourceBumpFourierConstant_nonneg 1 zero_lt_one 22

theorem integerQuadraticMass_nonneg : 0 ≤ integerQuadraticMass := by
  unfold integerQuadraticMass
  exact tsum_nonneg fun j => by
    unfold integerQuadraticEnvelope
    split_ifs <;> positivity

/-- The exact radius-one Fourier seminorm at the decay order `q+2`. -/
def sourceLemma92Decay (q : ℕ) : ℝ :=
  sourceBumpFourierConstant 1 zero_lt_one (q + 2)

theorem sourceLemma92Decay_nonneg (q : ℕ) : 0 ≤ sourceLemma92Decay q := by
  exact sourceBumpFourierConstant_nonneg 1 zero_lt_one (q + 2)

/-- The exact scalar chosen to make the displayed second-Poisson budget an
identity at `B = T^6`, `q = 20`. -/
def sourceLemma92SecondPoissonC20 (T F : ℝ) (M : ℕ) : ℝ :=
  (((T / (M : ℝ)) * sourceLemma92Decay20 *
      ((1 + (4 * (M : ℝ) * F) / ((M : ℝ) / T)) ^ 2 *
        max 1 (((M : ℝ) / T) ^ 2) * integerQuadraticMass) * T ^ 100) /
    (T ^ 6) ^ 20)

/-- The determinant-window quotient loses no power of `M`; it is exactly
`4FT`. -/
theorem sourceLemma92_determinantQuotient_eq
    {T F : ℝ} {M : ℕ} (hT : 0 < T) (hM : 0 < M) :
    (4 * (M : ℝ) * F) / ((M : ℝ) / T) = 4 * F * T := by
  have hMr : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  have hTr : T ≠ 0 := hT.ne'
  field_simp [hMr, hTr]

/-- The exact definition of `C` discharges the literal scalar premise. -/
theorem sourceLemma92SecondPoissonC20_budget
    {T F : ℝ} {M : ℕ} (hT : 0 < T) :
    (T / (M : ℝ)) * sourceLemma92Decay20 *
        ((1 + (4 * (M : ℝ) * F) / ((M : ℝ) / T)) ^ 2 *
          max 1 (((M : ℝ) / T) ^ 2) * integerQuadraticMass) * T ^ 100 ≤
      sourceLemma92SecondPoissonC20 T F M * (T ^ 6) ^ 20 := by
  unfold sourceLemma92SecondPoissonC20
  have hden : (T ^ 6) ^ 20 ≠ 0 := by positivity
  rw [div_mul_cancel₀ _ hden]

/-- Under the literal source ranges, the full numerator of `C` costs at most
`T^107`.  The improvement over the separate crude bounds is source-relevant:
`(T/M) * max(1,(M/T)^2) = max(T/M,M/T) ≤ T^3`. -/
theorem sourceLemma92SecondPoissonNumerator_le
    {T F Kdec : ℝ} {M : ℕ}
    (hT : 1 ≤ T) (hM : 0 < M) (hMhi : (M : ℝ) ≤ T ^ 4)
    (hF0 : 0 ≤ F) (hF : F ≤ T) (hKdec : 0 ≤ Kdec) :
    (T / (M : ℝ)) * Kdec *
        ((1 + (4 * (M : ℝ) * F) / ((M : ℝ) / T)) ^ 2 *
          max 1 (((M : ℝ) / T) ^ 2) * integerQuadraticMass) * T ^ 100 ≤
      (25 * Kdec * integerQuadraticMass) * T ^ 107 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hMreal : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hMone : (1 : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hM))
  have hToverM : T / (M : ℝ) ≤ T := by
    rw [div_le_iff₀ hMreal]
    nlinarith [mul_nonneg hTpos.le (sub_nonneg.mpr hMone)]
  have hMoverT : (M : ℝ) / T ≤ T ^ 3 := by
    rw [div_le_iff₀ hTpos]
    simpa [pow_succ] using hMhi
  have hTleT3 : T ≤ T ^ 3 := by
    nlinarith [show (1 : ℝ) ≤ T ^ 2 from one_le_pow₀ hT]
  have hcombined :
      (T / (M : ℝ)) * max 1 (((M : ℝ) / T) ^ 2) ≤ T ^ 3 := by
    by_cases hcase : 1 ≤ ((M : ℝ) / T) ^ 2
    · rw [max_eq_right hcase]
      have heq :
          (T / (M : ℝ)) * ((M : ℝ) / T) ^ 2 = (M : ℝ) / T := by
        field_simp [hTpos.ne', hMreal.ne']
      rw [heq]
      exact hMoverT
    · rw [max_eq_left (le_of_not_ge hcase), mul_one]
      exact hToverM.trans hTleT3
  have hFT : 4 * F * T ≤ 4 * T ^ 2 := by nlinarith
  have hquadBase : 1 + 4 * F * T ≤ 5 * T ^ 2 := by
    nlinarith [show (1 : ℝ) ≤ T ^ 2 from one_le_pow₀ hT]
  have hquadBase0 : 0 ≤ 1 + 4 * F * T := by positivity
  have hquad : (1 + 4 * F * T) ^ 2 ≤ 25 * T ^ 4 := by
    calc
      (1 + 4 * F * T) ^ 2 ≤ (5 * T ^ 2) ^ 2 :=
        pow_le_pow_left₀ hquadBase0 hquadBase 2
      _ = 25 * T ^ 4 := by ring
  have hmass0 : 0 ≤ integerQuadraticMass := integerQuadraticMass_nonneg
  rw [sourceLemma92_determinantQuotient_eq hTpos hM]
  calc
    (T / (M : ℝ)) * Kdec *
          ((1 + 4 * F * T) ^ 2 * max 1 (((M : ℝ) / T) ^ 2) *
            integerQuadraticMass) * T ^ 100 =
        Kdec * integerQuadraticMass *
          ((T / (M : ℝ)) * max 1 (((M : ℝ) / T) ^ 2)) *
          (1 + 4 * F * T) ^ 2 * T ^ 100 := by ring
    _ ≤ Kdec * integerQuadraticMass * (T ^ 3) *
          (25 * T ^ 4) * T ^ 100 := by
      gcongr
    _ = (25 * Kdec * integerQuadraticMass) * T ^ 107 := by
      ring

/-- The fixed `q=20` instance of the general `T^107` numerator bound. -/
theorem sourceLemma92SecondPoissonNumerator20_le
    {T F : ℝ} {M : ℕ}
    (hT : 1 ≤ T) (hM : 0 < M) (hMhi : (M : ℝ) ≤ T ^ 4)
    (hF0 : 0 ≤ F) (hF : F ≤ T) :
    (T / (M : ℝ)) * sourceLemma92Decay20 *
        ((1 + (4 * (M : ℝ) * F) / ((M : ℝ) / T)) ^ 2 *
          max 1 (((M : ℝ) / T) ^ 2) * integerQuadraticMass) * T ^ 100 ≤
      (25 * sourceLemma92Decay20 * integerQuadraticMass) * T ^ 107 := by
  exact sourceLemma92SecondPoissonNumerator_le hT hM hMhi hF0 hF
    sourceLemma92Decay20_nonneg

/-- Exact scalar for a source-compatible cutoff `B=T^δ` at arbitrary
decay order `q`. -/
def sourceLemma92SecondPoissonCDelta
    (T F delta : ℝ) (M q : ℕ) : ℝ :=
  (((T / (M : ℝ)) * sourceLemma92Decay q *
      ((1 + (4 * (M : ℝ) * F) / ((M : ℝ) / T)) ^ 2 *
        max 1 (((M : ℝ) / T) ^ 2) * integerQuadraticMass) * T ^ 100) /
    (T ^ delta) ^ q)

/-- The general `B=T^δ` scalar is chosen so that the exact displayed budget
holds by identity. -/
theorem sourceLemma92SecondPoissonCDelta_budget
    {T F delta : ℝ} {M q : ℕ} (hT : 0 < T) :
    (T / (M : ℝ)) * sourceLemma92Decay q *
        ((1 + (4 * (M : ℝ) * F) / ((M : ℝ) / T)) ^ 2 *
          max 1 (((M : ℝ) / T) ^ 2) * integerQuadraticMass) * T ^ 100 ≤
      sourceLemma92SecondPoissonCDelta T F delta M q *
        (T ^ delta) ^ q := by
  unfold sourceLemma92SecondPoissonCDelta
  have hden : (T ^ delta) ^ q ≠ 0 := by
    exact pow_ne_zero q (ne_of_gt (Real.rpow_pos_of_pos hT delta))
  rw [div_mul_cancel₀ _ hden]

/-- The exact exponent law.  The numerator costs `107` powers, so the
remaining fixed-constant reserve is `δ*q-107`. -/
theorem sourceLemma92SecondPoissonCDelta_le
    {T F delta : ℝ} {M q : ℕ}
    (hT : 1 ≤ T) (hM : 0 < M) (hMhi : (M : ℝ) ≤ T ^ 4)
    (hF0 : 0 ≤ F) (hF : F ≤ T) :
    sourceLemma92SecondPoissonCDelta T F delta M q ≤
      (25 * sourceLemma92Decay q * integerQuadraticMass) /
        T ^ (delta * (q : ℝ) - 107) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hcutoff : (T ^ delta) ^ q = T ^ (delta * (q : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_mul hTpos.le delta (q : ℝ)).symm
  unfold sourceLemma92SecondPoissonCDelta
  calc
    _ ≤ ((25 * sourceLemma92Decay q * integerQuadraticMass) * T ^ 107) /
          (T ^ delta) ^ q := by
      exact div_le_div_of_nonneg_right
        (sourceLemma92SecondPoissonNumerator_le hT hM hMhi hF0 hF
          (sourceLemma92Decay_nonneg q)) (by positivity)
    _ = (25 * sourceLemma92Decay q * integerQuadraticMass) /
          T ^ (delta * (q : ℝ) - 107) := by
      rw [hcutoff, Real.rpow_sub hTpos]
      field_simp
      exact congrArg
        (fun x : ℝ => sourceLemma92Decay q * integerQuadraticMass * x)
        (Real.rpow_natCast T 107).symm

/-- Once the single fixed-constant threshold fits inside the exponent
reserve, the exact scalar tail is at most `T^-100`. -/
theorem sourceLemma92SecondPoissonCDelta_div_time100_le
    {T F delta : ℝ} {M q : ℕ}
    (hT : 1 ≤ T) (hM : 0 < M) (hMhi : (M : ℝ) ≤ T ^ 4)
    (hF0 : 0 ≤ F) (hF : F ≤ T)
    (hthreshold : 25 * sourceLemma92Decay q * integerQuadraticMass ≤
      T ^ (delta * (q : ℝ) - 107)) :
    sourceLemma92SecondPoissonCDelta T F delta M q / T ^ 100 ≤
      T⁻¹ ^ 100 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hreservePos : 0 < T ^ (delta * (q : ℝ) - 107) :=
    Real.rpow_pos_of_pos hTpos _
  have hCone : sourceLemma92SecondPoissonCDelta T F delta M q ≤ 1 := by
    calc
      sourceLemma92SecondPoissonCDelta T F delta M q ≤
          (25 * sourceLemma92Decay q * integerQuadraticMass) /
            T ^ (delta * (q : ℝ) - 107) :=
        sourceLemma92SecondPoissonCDelta_le hT hM hMhi hF0 hF
      _ ≤ 1 := (div_le_one hreservePos).2 hthreshold
  calc
    sourceLemma92SecondPoissonCDelta T F delta M q / T ^ 100 ≤
        1 / T ^ 100 := by
      exact div_le_div_of_nonneg_right hCone (by positivity)
    _ = T⁻¹ ^ 100 := by simp [one_div]

/-- For every positive smoothing exponent `δ`, some finite decay order has
strictly positive reserve. -/
theorem exists_sourceLemma92_decayOrder_reserve_pos
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ q : ℕ, 107 < delta * (q : ℝ) := by
  obtain ⟨q, hq⟩ := exists_nat_gt (107 / delta)
  refine ⟨q, ?_⟩
  have hq' : 107 / delta < (q : ℝ) := by exact_mod_cast hq
  simpa [mul_comm] using (div_lt_iff₀ hdelta).mp hq'

/-- A positive reserve really does absorb the fixed Fourier-seminorm/mass
constant after one explicit threshold. -/
theorem exists_sourceLemma92_fixedConstant_threshold
    {delta : ℝ} {q : ℕ}
    (hreserve : 0 < delta * (q : ℝ) - 107) :
    ∃ T0 : ℝ, 1 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
      25 * sourceLemma92Decay q * integerQuadraticMass ≤
        T ^ (delta * (q : ℝ) - 107) := by
  let K : ℝ := 25 * sourceLemma92Decay q * integerQuadraticMass
  let r : ℝ := delta * (q : ℝ) - 107
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity [sourceLemma92Decay_nonneg q, integerQuadraticMass_nonneg]
  have hr : 0 < r := by simpa only [r] using hreserve
  let root : ℝ := K ^ (1 / r)
  refine ⟨max 1 root, le_max_left _ _, ?_⟩
  intro T hT
  have hrootT : root ≤ T := (le_max_right _ _).trans hT
  have hroot0 : 0 ≤ root := Real.rpow_nonneg hK _
  have hpow : root ^ r ≤ T ^ r :=
    Real.rpow_le_rpow hroot0 hrootT hr.le
  have hrootpow : root ^ r = K := by
    dsimp only [root]
    rw [← Real.rpow_mul hK]
    have hrne : r ≠ 0 := hr.ne'
    field_simp [hrne]
    simp
  simpa only [K, r, hrootpow] using hpow

/-- The thirteen-power reserve after division by `(T^6)^20`. -/
theorem sourceLemma92SecondPoissonC20_le
    {T F : ℝ} {M : ℕ}
    (hT : 1 ≤ T) (hM : 0 < M) (hMhi : (M : ℝ) ≤ T ^ 4)
    (hF0 : 0 ≤ F) (hF : F ≤ T) :
    sourceLemma92SecondPoissonC20 T F M ≤
      (25 * sourceLemma92Decay20 * integerQuadraticMass) / T ^ 13 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  unfold sourceLemma92SecondPoissonC20
  calc
    _ ≤ ((25 * sourceLemma92Decay20 * integerQuadraticMass) * T ^ 107) /
          (T ^ 6) ^ 20 := by
      exact div_le_div_of_nonneg_right
        (sourceLemma92SecondPoissonNumerator20_le hT hM hMhi hF0 hF)
        (by positivity)
    _ = (25 * sourceLemma92Decay20 * integerQuadraticMass) / T ^ 13 := by
      field_simp

/-- One explicit eventual threshold absorbs both fixed constants.  The
resulting scalar tail is at most the advertised `T^-100`. -/
theorem sourceLemma92SecondPoissonC20_div_time100_le
    {T F : ℝ} {M : ℕ}
    (hT : 1 ≤ T) (hM : 0 < M) (hMhi : (M : ℝ) ≤ T ^ 4)
    (hF0 : 0 ≤ F) (hF : F ≤ T)
    (hthreshold : 25 * sourceLemma92Decay20 * integerQuadraticMass ≤ T ^ 13) :
    sourceLemma92SecondPoissonC20 T F M / T ^ 100 ≤ T⁻¹ ^ 100 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hCone : sourceLemma92SecondPoissonC20 T F M ≤ 1 := by
    calc
      sourceLemma92SecondPoissonC20 T F M ≤
          (25 * sourceLemma92Decay20 * integerQuadraticMass) / T ^ 13 :=
        sourceLemma92SecondPoissonC20_le hT hM hMhi hF0 hF
      _ ≤ 1 := (div_le_one (pow_pos hTpos 13)).2 hthreshold
  calc
    sourceLemma92SecondPoissonC20 T F M / T ^ 100 ≤ 1 / T ^ 100 := by
      exact div_le_div_of_nonneg_right hCone (by positivity)
    _ = T⁻¹ ^ 100 := by simp [one_div]

/-- The fixed uniform Fourier constant of the radius-one concrete bump. -/
def sourceLemma92Sup0 : ℝ :=
  sourceBumpFourierConstant 1 zero_lt_one 0

theorem sourceLemma92Sup0_nonneg : 0 ≤ sourceLemma92Sup0 := by
  exact sourceBumpFourierConstant_nonneg 1 zero_lt_one 0

/-- Reusable concrete Fourier package at arbitrary second-Poisson order. -/
theorem sourceLemma92ConcreteFourierPackage (q : ℕ) :
    0 ≤ sourceLemma92Decay q ∧ 0 ≤ sourceLemma92Sup0 ∧
    (∀ xi, ‖FourierTransform.fourier
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) xi‖ ≤
        sourceBumpFourierConstant 1 zero_lt_one 2 / (1 + |xi|) ^ 2) ∧
    (∀ xi, ‖FourierTransform.fourier
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) xi‖ ≤
        sourceLemma92Decay q / (1 + |xi|) ^ (q + 2)) ∧
    (∀ xi, ‖FourierTransform.fourier
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) xi‖ ≤
        sourceLemma92Sup0) := by
  refine ⟨sourceLemma92Decay_nonneg q, sourceLemma92Sup0_nonneg,
    sourceBump_fourier_decay 1 zero_lt_one 2, ?_, ?_⟩
  · simpa [sourceLemma92Decay] using
      (sourceBump_fourier_decay 1 zero_lt_one (q + 2))
  · intro xi
    simpa [sourceLemma92Sup0] using
      (sourceBump_fourier_decay 1 zero_lt_one 0 xi)

/-- Reusable fixed-order Fourier package for the selected-range and full-range
Lemma 9.2 endpoints.  This exposes the exact constants, avoiding a second
existential choice at the scalar-budget seam. -/
theorem sourceLemma92ConcreteFourierPackage20 :
    0 ≤ sourceLemma92Decay20 ∧ 0 ≤ sourceLemma92Sup0 ∧
    (∀ xi, ‖FourierTransform.fourier
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) xi‖ ≤
        sourceBumpFourierConstant 1 zero_lt_one 2 / (1 + |xi|) ^ 2) ∧
    (∀ xi, ‖FourierTransform.fourier
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) xi‖ ≤
        sourceLemma92Decay20 / (1 + |xi|) ^ (20 + 2)) ∧
    (∀ xi, ‖FourierTransform.fourier
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) xi‖ ≤
        sourceLemma92Sup0) := by
  simpa [sourceLemma92Decay, sourceLemma92Decay20] using
    (sourceLemma92ConcreteFourierPackage 20)

/-- **Scalar stress test, not a source iteration endpoint.**  This theorem
shows that the analytic producer itself accepts `B=T^6`, `q=20`, and that its
budget is then fully discharged.  The source Proposition 9.1 iteration cannot
use this specialization: its smoothing profile must have radius `T^δ`, while
`T^6` belongs only to the high-frequency `ξ` split. -/
theorem sigmaIIFinite_sourcePositiveDyadic_concreteBumps_timeSix_q20_stressTest_le
    {T S F Ctau : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    {M : ℕ} (hM : 0 < M)
    (hT : 1 ≤ T) (hF0 : 0 ≤ F) (hF : F ≤ T)
    (hMhi : (M : ℝ) ≤ T ^ 4) (hCtau : 0 ≤ Ctau)
    (hthreshold :
      25 * sourceLemma92Decay20 * integerQuadraticMass ≤ T ^ 13) :
    sigmaIIFinite (sourceBumpEllRange M T 1)
          (sourcePositiveDyadicRange M)
          (fun x => sourceBump 1 zero_lt_one x)
          (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
          (M : ℝ) T (M : ℝ) Ctau ≤
        ((2 * Ctau * sourceLemma92Sup0) * (2 : ℝ) ^ 2 * (M : ℝ)) *
          Real.sqrt ((∫ u : ℝ, f u ^ 2) *
            sourceAffineJ
              (sourceAffineConfigs (sourcePositiveDyadicRange M)
                (sourceLemma92JRange M T F (2 * T ^ 6)))
              (affineSmoothing T (fun z => sourceBump (T ^ 6)
                (by positivity) z) f)) +
        ∑ m2 ∈ sourcePositiveDyadicRange M,
          ∑ m2' ∈ sourcePositiveDyadicRange M,
            |(m2 : ℝ) * (m2' : ℝ)| *
              (((∫ u : ℝ, |f u|) ^ 2 * (2 * Ctau)) *
                (sourceLemma92SecondPoissonC20 T F M / T ^ 100))
      ∧ sourceLemma92SecondPoissonC20 T F M / T ^ 100 ≤ T⁻¹ ^ 100 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hBpos : 0 < T ^ 6 := pow_pos hTpos 6
  have hMreal : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hY : 0 ≤ 4 * (M : ℝ) * F := by positivity
  have hM3 : (M : ℝ) ≠ 0 := hMreal.ne'
  obtain ⟨hKdec, hKsup, hdecay2, hdecay, hFourierSup⟩ :=
    sourceLemma92ConcreteFourierPackage20
  have hbudget := sourceLemma92SecondPoissonC20_budget
    (T := T) (F := F) (M := M) hTpos
  have hp : SourceLemma92ProfilePremises T S F (2 * T ^ 6) (M : ℝ)
      (T ^ 6) f (fun z => sourceBump (T ^ 6) hBpos z) M :=
    sourceLemma92_profilePremises_sourceBump hTpos hf hBpos hM
  have hy : ∀ m2 ∈ sourcePositiveDyadicRange M,
      ∀ m2' ∈ sourcePositiveDyadicRange M, ∀ z : ℝ × ℝ,
        f z.1 * f z.2 ≠ 0 →
        |(m2' : ℝ) * z.2 - (m2 : ℝ) * z.1| ≤ 4 * (M : ℝ) * F := by
    intro m2 hm2 m2' hm2' z hz
    exact sourceLemma92_determinant_le_four_mul hf hM hm2 hm2' z hz
  have hsupport : ∀ ell : ℤ,
      ell ∉ sourceBumpEllRange M T 1 →
        sourceBump 1 zero_lt_one ((M : ℝ) * (ell : ℝ) / T) = 0 :=
    sourceBump_support_on_sourceBumpEllRange hM hTpos zero_lt_one
  have hret : ∀ m2 ∈ sourcePositiveDyadicRange M,
      ∀ m2' ∈ sourcePositiveDyadicRange M,
      Integrable (sigmaIIZPairRetainedKernel
        (fun x => sourceBump 1 zero_lt_one x) f
        (M : ℝ) T (M : ℝ) Ctau (T ^ 6) m2 m2')
        (volume.prod volume) := by
    intro m2 hm2 m2' hm2'
    exact integrable_sigmaIIZPairRetainedKernel_of_budget
      (sourceBumpEllRange M T 1) (fun x => sourceBump 1 zero_lt_one x) f
      hf.integrable (sourceBump_complex_hasCompactSupport 1 zero_lt_one)
      (sourceBump_complex_contDiff 1 zero_lt_one) 20 hKdec hMreal hTpos
      hBpos hY hM3 hCtau hdecay2 hdecay hbudget m2 m2'
      (hy m2 hm2 m2' hm2') hsupport
  have htail : ∀ m2 ∈ sourcePositiveDyadicRange M,
      ∀ m2' ∈ sourcePositiveDyadicRange M,
      Integrable (sigmaIIZPairTailKernel
        (fun x => sourceBump 1 zero_lt_one x) f
        (M : ℝ) T (M : ℝ) Ctau (T ^ 6) m2 m2')
        (volume.prod volume) := by
    intro m2 hm2 m2' hm2'
    exact integrable_sigmaIIZPairTailKernel_of_budget
      (M3 := (M : ℝ)) (fun x => sourceBump 1 zero_lt_one x) f
      hf.integrable (sourceBump_complex_hasCompactSupport 1 zero_lt_one)
      (sourceBump_complex_contDiff 1 zero_lt_one) 20 hKdec hMreal hTpos
      hBpos hY hCtau hdecay hbudget m2 m2' (hy m2 hm2 m2' hm2')
  constructor
  · apply sigmaIIFinite_le_canonicalAffineJ_sqrt_add_time_neg100
      f (fun x => sourceBump 1 zero_lt_one x)
        (fun z => sourceBump (T ^ 6) hBpos z) hf.integrable
        (sourceBumpEllRange M T 1) (sourcePositiveDyadicRange M)
        (sourceLemma92JRange M T F (2 * T ^ 6))
        (sourceBump_complex_hasCompactSupport 1 zero_lt_one)
        (sourceBump_complex_contDiff 1 zero_lt_one) 20 hKdec hKsup
        hMreal hTpos hBpos hY hM3 hCtau
        (show 0 ≤ (2 : ℝ) by norm_num) hf.nonneg
        (sourceBump_nonneg (T ^ 6) hBpos) hdecay2 hdecay hFourierSup
        hbudget hsupport
        (fun m hm => by exact_mod_cast sourcePositiveDyadicRange_pos hM hm)
        (fun m hm => by
          simpa using (sourcePositiveDyadicRange_abs_bounds hM hm).2)
        hy (sourceBump_majorizes_sourcePositiveDyadic_localization hM hBpos)
        hp.localIntegrable hp.affineSmooth hp.summable hret htail
        (fun m2 hm2 m2' hm2' =>
          hp.pairMajorantIntegrable
            ((2 * Ctau * sourceLemma92Sup0) / (M : ℝ))
            m2 hm2 m2' hm2')
        hp.pairMassIntegrable hp.cover hp.fMeasurable hp.affineSumMeasurable
        hp.fSquareIntegrable hp.affineSumSquareIntegrable
  · exact sourceLemma92SecondPoissonC20_div_time100_le
      hT hM hMhi hF0 hF hthreshold

#print axioms GuthMaynardJIteration.sourceLemma92SecondPoissonC20_budget
#print axioms GuthMaynardJIteration.sourceLemma92SecondPoissonNumerator_le
#print axioms GuthMaynardJIteration.sourceLemma92SecondPoissonCDelta_budget
#print axioms GuthMaynardJIteration.sourceLemma92SecondPoissonCDelta_le
#print axioms GuthMaynardJIteration.sourceLemma92SecondPoissonCDelta_div_time100_le
#print axioms GuthMaynardJIteration.exists_sourceLemma92_decayOrder_reserve_pos
#print axioms GuthMaynardJIteration.exists_sourceLemma92_fixedConstant_threshold
#print axioms GuthMaynardJIteration.sourceLemma92SecondPoissonNumerator20_le
#print axioms GuthMaynardJIteration.sourceLemma92SecondPoissonC20_le
#print axioms GuthMaynardJIteration.sourceLemma92SecondPoissonC20_div_time100_le
#print axioms GuthMaynardJIteration.sourceLemma92ConcreteFourierPackage
#print axioms GuthMaynardJIteration.sourceLemma92ConcreteFourierPackage20
#print axioms GuthMaynardJIteration.sigmaIIFinite_sourcePositiveDyadic_concreteBumps_timeSix_q20_stressTest_le

end GuthMaynardJIteration
