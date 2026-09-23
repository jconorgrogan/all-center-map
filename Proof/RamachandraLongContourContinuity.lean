import RamachandraLongFamilyLpAssembly

/-!
# Continuity of the literal long contour

The full reflected-tail integral is handled as the locally uniformly
convergent sum of its exact dyadic shell integrals.  The only domination used
below is the already-certified global functional-factor envelope; the sharp
second-moment envelope is not extended across its exceptional ordinate.
-/

namespace RamachandraLongContourContinuity

open scoped BigOperators Interval ENNReal
open Complex MeasureTheory Filter Topology
open RamachandraPrimitiveShiftedContourReduction
open RamachandraLongTailShellCauchy
open RamachandraLongContourInfiniteAssembly
open RamachandraGammaWeightIntegrability
open RamachandraFunctionalFactorEnvelope
open BHPRamachandraMeanValueFromDyadicAFE

noncomputable section

set_option maxHeartbeats 1200000

variable {d : ℕ} [NeZero d]

/-- A qualitative global functional-factor envelope for an arbitrary
character.  Primitivity is only needed for the sharp unit-root normalization;
for continuity the fixed factor `‖rootNumber‖` is harmless. -/
theorem exists_norm_ramachandraFunctionalFactor_le_global_character
    (psi : DirichletCharacter ℂ d) :
    ∃ Cgamma : ℝ, 0 ≤ Cgamma ∧
      ∀ z : ℂ, -(1 / 4 : ℝ) ≤ z.re → z.re ≤ 1 / 2 →
        ‖ramachandraFunctionalFactor psi z‖ ≤
          Real.rpow (d : ℝ) (1 / 2 - z.re) *
            (Cgamma * (1 + |z.im|) ^ 3) := by
  rcases exists_gammaFactor_reflected_quotient_norm_le_global (q := d) with
    ⟨Carch, hCarch, hquot⟩
  let Cgamma : ℝ := Carch * ‖psi.rootNumber‖
  have hCarch0 : 0 ≤ Carch := le_trans (by norm_num) hCarch
  have hCgamma0 : 0 ≤ Cgamma := by dsimp [Cgamma]; positivity
  refine ⟨Cgamma, hCgamma0, ?_⟩
  intro z hzlo hzhi
  unfold ramachandraFunctionalFactor
  rw [show
      (d : ℂ) ^ (1 / 2 - z) * psi.rootNumber *
          psi⁻¹.gammaFactor (1 - z) / psi.gammaFactor z =
        ((d : ℂ) ^ (1 / 2 - z) * psi.rootNumber) *
          (psi⁻¹.gammaFactor (1 - z) / psi.gammaFactor z) by ring,
    norm_mul]
  have hroot :
      ‖(d : ℂ) ^ (1 / 2 - z) * psi.rootNumber‖ =
        Real.rpow (d : ℝ) (1 / 2 - z.re) * ‖psi.rootNumber‖ := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (NeZero.pos d)]
    congr 2
    simp
  rw [hroot]
  have hq := hquot psi z hzlo hzhi
  have hpow0 : 0 ≤ Real.rpow (d : ℝ) (1 / 2 - z.re) :=
    Real.rpow_nonneg (Nat.cast_nonneg d) _
  calc
    Real.rpow (d : ℝ) (1 / 2 - z.re) * ‖psi.rootNumber‖ *
        ‖psi⁻¹.gammaFactor (1 - z) / psi.gammaFactor z‖ ≤
      Real.rpow (d : ℝ) (1 / 2 - z.re) * ‖psi.rootNumber‖ *
        (Carch * (1 + |z.im|) ^ 3) := by
          exact mul_le_mul_of_nonneg_left hq
            (mul_nonneg hpow0 (norm_nonneg _))
    _ = Real.rpow (d : ℝ) (1 / 2 - z.re) *
        (Cgamma * (1 + |z.im|) ^ 3) := by
      dsimp [Cgamma]
      ring

/-- One exact integrated dyadic long shell depends continuously on the source
ordinate. -/
theorem continuous_integral_longTailShellIntegrand_of_envelope
    (psi : DirichletCharacter ℂ d) {Cgamma : ℝ}
    (hCgamma : 0 ≤ Cgamma)
    (hglobal : ∀ z : ℂ, -(1 / 4 : ℝ) ≤ z.re → z.re ≤ 1 / 2 →
      ‖ramachandraFunctionalFactor psi z‖ ≤
        Real.rpow (d : ℝ) (1 / 2 - z.re) *
          (Cgamma * (1 + |z.im|) ^ 3))
    {X sigma : ℝ} (hX : 0 < X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) (j : ℕ) :
    Continuous (fun t => ∫ v : ℝ,
      longTailShellIntegrand psi X sigma t j v) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  let B : ℝ := Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
    Real.rpow X (-(sigma + 1 / 4)) * (1 + (|t₀| + 1)) ^ 6
  let Cj : ℝ := longTailShellUniformNormBound psi X sigma j
  let bound : ℝ → ℝ := fun v =>
    (B * Cj) * gammaPolynomialWeight (-(sigma + 1 / 4)) v
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hCj0 : 0 ≤ Cj := by
    dsimp [Cj, longTailShellUniformNormBound]
    positivity
  have hbound : Integrable bound := by
    dsimp [bound]
    exact (integrable_gammaPolynomialWeight hcLo hcHi).const_mul (B * Cj)
  have htNear : ∀ᶠ t in nhds t₀, |t| ≤ |t₀| + 1 := by
    have hdist : ∀ᶠ t in nhds t₀, t ∈ Metric.ball t₀ 1 :=
      Metric.ball_mem_nhds t₀ (by norm_num)
    filter_upwards [hdist] with t ht
    have ht' : dist t t₀ < 1 := by simpa [Metric.mem_ball] using ht
    rw [Real.dist_eq] at ht'
    calc
      |t| = |(t - t₀) + t₀| := by ring_nf
      _ ≤ |t - t₀| + |t₀| := abs_add_le _ _
      _ ≤ |t₀| + 1 := by linarith
  apply tendsto_integral_filter_of_dominated_convergence bound
  · filter_upwards with t
    exact (continuous_longTailShellIntegrand psi hX hcLo hcHi j).aestronglyMeasurable
  · filter_upwards [htNear] with t ht
    filter_upwards with v
    have hraw := norm_longTailShellIntegrand_le_global_of_envelope psi
      (sigma := sigma) hX hCgamma hglobal j v (t := t)
    have ht6 : (1 + |t|) ^ 6 ≤ (1 + (|t₀| + 1)) ^ 6 := by
      gcongr
    have hW0 := gammaPolynomialWeight_nonneg (-(sigma + 1 / 4)) v
    calc
      ‖longTailShellIntegrand psi X sigma t j v‖ ≤
          (Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
              Real.rpow X (-(sigma + 1 / 4)) * (1 + |t|) ^ 6) *
            gammaPolynomialWeight (-(sigma + 1 / 4)) v * Cj := by
        simpa only [Cj] using hraw
      _ ≤ B * gammaPolynomialWeight (-(sigma + 1 / 4)) v * Cj := by
        have hbase : 0 ≤ Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
            Real.rpow X (-(sigma + 1 / 4)) := by
          exact mul_nonneg
            (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
            (Real.rpow_nonneg hX.le _)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left ht6 hbase) hW0) hCj0
      _ = bound v := by dsimp [bound]; ring
  · exact hbound
  · filter_upwards with v
    have hcont := (continuous_uncurry_longTailShellIntegrand psi hX hcLo hcHi j).comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _t : ℝ => v)))
    simpa only [Function.uncurry_apply_pair] using! hcont.continuousAt

/-- Primitive wrapper for the envelope-parametrized shell continuity result. -/
theorem continuous_integral_longTailShellIntegrand
    (psi : DirichletCharacter ℂ d) (hprim : psi.IsPrimitive)
    {X sigma : ℝ} (hX : 0 < X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) (j : ℕ) :
    Continuous (fun t => ∫ v : ℝ,
      longTailShellIntegrand psi X sigma t j v) := by
  rcases exists_norm_ramachandraFunctionalFactor_le_global (q := d) with
    ⟨Cgamma, hCgamma, hglobal⟩
  exact continuous_integral_longTailShellIntegrand_of_envelope psi
    (le_trans (by norm_num) hCgamma) (hglobal psi hprim) hX hcLo hcHi j

private theorem integrable_longTailShellIntegrand_of_envelope
    (psi : DirichletCharacter ℂ d) {Cgamma : ℝ}
    (hCgamma : 0 ≤ Cgamma)
    (hglobal : ∀ z : ℂ, -(1 / 4 : ℝ) ≤ z.re → z.re ≤ 1 / 2 →
      ‖ramachandraFunctionalFactor psi z‖ ≤
        Real.rpow (d : ℝ) (1 / 2 - z.re) *
          (Cgamma * (1 + |z.im|) ^ 3))
    {X sigma t : ℝ} (hX : 0 < X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) (j : ℕ) :
    Integrable (longTailShellIntegrand psi X sigma t j) := by
  let B : ℝ := Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
    Real.rpow X (-(sigma + 1 / 4)) * (1 + |t|) ^ 6
  let Cj : ℝ := longTailShellUniformNormBound psi X sigma j
  have hmajor : Integrable (fun v : ℝ =>
      (B * Cj) * gammaPolynomialWeight (-(sigma + 1 / 4)) v) :=
    (integrable_gammaPolynomialWeight hcLo hcHi).const_mul (B * Cj)
  apply hmajor.mono'
  · exact (continuous_longTailShellIntegrand psi hX hcLo hcHi j).aestronglyMeasurable
  · filter_upwards with v
    have h := norm_longTailShellIntegrand_le_global_of_envelope psi
      (sigma := sigma) (t := t) hX hCgamma hglobal j v
    simpa [B, Cj, mul_assoc, mul_comm, mul_left_comm] using h

private theorem norm_integral_longTailShell_le_of_envelope
    (psi : DirichletCharacter ℂ d) {Cgamma : ℝ}
    (hCgamma : 0 ≤ Cgamma)
    (hglobal : ∀ z : ℂ, -(1 / 4 : ℝ) ≤ z.re → z.re ≤ 1 / 2 →
      ‖ramachandraFunctionalFactor psi z‖ ≤
        Real.rpow (d : ℝ) (1 / 2 - z.re) *
          (Cgamma * (1 + |z.im|) ^ 3))
    {X sigma t : ℝ} (hX : 0 < X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) (j : ℕ) :
    ‖∫ v : ℝ, longTailShellIntegrand psi X sigma t j v‖ ≤
      (Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
        Real.rpow X (-(sigma + 1 / 4)) * (1 + |t|) ^ 6) *
      (∫ v : ℝ, gammaPolynomialWeight (-(sigma + 1 / 4)) v) *
      longTailShellUniformNormBound psi X sigma j := by
  let B : ℝ := Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
    Real.rpow X (-(sigma + 1 / 4)) * (1 + |t|) ^ 6
  have hInt := integrable_longTailShellIntegrand_of_envelope psi
    hCgamma hglobal (t := t) hX hcLo hcHi j
  have hmajor := (integrable_gammaPolynomialWeight hcLo hcHi).const_mul
    (B * longTailShellUniformNormBound psi X sigma j)
  calc
    ‖∫ v : ℝ, longTailShellIntegrand psi X sigma t j v‖ ≤
        ∫ v : ℝ, ‖longTailShellIntegrand psi X sigma t j v‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ v : ℝ, B * longTailShellUniformNormBound psi X sigma j *
        gammaPolynomialWeight (-(sigma + 1 / 4)) v := by
      apply integral_mono hInt.norm hmajor
      intro v
      have h := norm_longTailShellIntegrand_le_global_of_envelope psi
        (sigma := sigma) (t := t) hX hCgamma hglobal j v
      simpa [B, mul_assoc, mul_comm, mul_left_comm] using h
    _ = B * (∫ v : ℝ, gammaPolynomialWeight (-(sigma + 1 / 4)) v) *
        longTailShellUniformNormBound psi X sigma j := by
      rw [MeasureTheory.integral_const_mul]
      ring

private theorem hasSum_integral_longTailShellIntegrand_of_envelope
    (psi : DirichletCharacter ℂ d) {Cgamma : ℝ}
    (hCgamma : 0 ≤ Cgamma)
    (hglobal : ∀ z : ℂ, -(1 / 4 : ℝ) ≤ z.re → z.re ≤ 1 / 2 →
      ‖ramachandraFunctionalFactor psi z‖ ≤
        Real.rpow (d : ℝ) (1 / 2 - z.re) *
          (Cgamma * (1 + |z.im|) ^ 3))
    {X sigma t : ℝ} (hX : 1 ≤ X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) :
    HasSum (fun j : ℕ =>
      ∫ v : ℝ, longTailShellIntegrand psi X sigma t j v)
      (∫ v : ℝ, ramachandraShiftedContourIntegrand psi X sigma
        (-(sigma + 1 / 4)) t v true) := by
  let B : ℝ := Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
    Real.rpow X (-(sigma + 1 / 4)) * (1 + |t|) ^ 6
  let W : ℝ := ∫ v : ℝ, gammaPolynomialWeight (-(sigma + 1 / 4)) v
  have hInt : ∀ j : ℕ, Integrable
      (longTailShellIntegrand psi X sigma t j) := fun j =>
    integrable_longTailShellIntegrand_of_envelope psi hCgamma hglobal
      (lt_of_lt_of_le zero_lt_one hX) hcLo hcHi j
  have hnormSum : Summable (fun j : ℕ =>
      ∫ v : ℝ, ‖longTailShellIntegrand psi X sigma t j v‖) := by
    have hbase := (summable_longTailShellUniformNormBound psi
      (sigma := sigma) hX).mul_left (B * W)
    apply Summable.of_nonneg_of_le
      (fun j => integral_nonneg (fun v => norm_nonneg _)) (fun j => ?_) hbase
    have hmajor := (integrable_gammaPolynomialWeight hcLo hcHi).const_mul
      (B * longTailShellUniformNormBound psi X sigma j)
    calc
      (∫ v : ℝ, ‖longTailShellIntegrand psi X sigma t j v‖) ≤
          ∫ v : ℝ, B * longTailShellUniformNormBound psi X sigma j *
            gammaPolynomialWeight (-(sigma + 1 / 4)) v := by
        apply integral_mono (hInt j).norm hmajor
        intro v
        have h := norm_longTailShellIntegrand_le_global_of_envelope psi
          (sigma := sigma) (t := t) (lt_of_lt_of_le zero_lt_one hX)
          hCgamma hglobal j v
        simpa [B, mul_assoc, mul_comm, mul_left_comm] using h
      _ = (B * W) * longTailShellUniformNormBound psi X sigma j := by
        rw [MeasureTheory.integral_const_mul]
        dsimp [W]
        ring
  have h := MeasureTheory.hasSum_integral_of_summable_integral_norm hInt hnormSum
  simpa only [tsum_longTailShellIntegrand_eq psi hX] using h

/-- The literal full reflected-tail contour integral is continuous in the
source ordinate.  This is a local Weierstrass argument over the exact shell
identity, with no truncation of the Mellin line. -/
theorem continuous_integral_longContourIntegrand_character
    (psi : DirichletCharacter ℂ d)
    {X sigma : ℝ} (hX : 1 ≤ X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) :
    Continuous (fun t => ∫ v : ℝ,
      ramachandraShiftedContourIntegrand psi X sigma
        (-(sigma + 1 / 4)) t v true) := by
  rcases exists_norm_ramachandraFunctionalFactor_le_global_character psi with
    ⟨Cgamma, hCgamma, hglobal⟩
  rw [continuous_iff_continuousAt]
  intro t₀
  let s : Set ℝ := Set.Icc (t₀ - 1) (t₀ + 1)
  let B : ℝ := Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
    Real.rpow X (-(sigma + 1 / 4)) * (1 + (|t₀| + 1)) ^ 6
  let W : ℝ := ∫ v : ℝ, gammaPolynomialWeight (-(sigma + 1 / 4)) v
  let u : ℕ → ℝ := fun j =>
    (B * W) * longTailShellUniformNormBound psi X sigma j
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hW0 : 0 ≤ W := by
    dsimp [W]
    exact integral_nonneg (fun v => gammaPolynomialWeight_nonneg _ _)
  have hu : Summable u :=
    (summable_longTailShellUniformNormBound psi hX).mul_left (B * W)
  have hcontOn : ContinuousOn
      (fun t => ∑' j : ℕ, ∫ v : ℝ,
        longTailShellIntegrand psi X sigma t j v) s := by
    apply continuousOn_tsum
    · intro j
      exact (continuous_integral_longTailShellIntegrand_of_envelope psi
        hCgamma hglobal (lt_of_lt_of_le zero_lt_one hX) hcLo hcHi j).continuousOn
    · exact hu
    · intro j t ht
      have htIcc : t₀ - 1 ≤ t ∧ t ≤ t₀ + 1 := by simpa [s] using ht
      have htAbs : |t| ≤ |t₀| + 1 := by
        rw [abs_le]
        constructor <;> linarith [neg_abs_le t₀, le_abs_self t₀]
      have hraw := norm_integral_longTailShell_le_of_envelope psi hCgamma hglobal
        (sigma := sigma) (t := t) (lt_of_lt_of_le zero_lt_one hX)
        hcLo hcHi j
      have ht6 : (1 + |t|) ^ 6 ≤ (1 + (|t₀| + 1)) ^ 6 := by gcongr
      have hbase : 0 ≤ Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
          Real.rpow X (-(sigma + 1 / 4)) := by
        exact mul_nonneg
          (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
          (Real.rpow_nonneg (by linarith) _)
      have hCj0 : 0 ≤ longTailShellUniformNormBound psi X sigma j := by
        unfold longTailShellUniformNormBound
        positivity
      calc
        ‖∫ v : ℝ, longTailShellIntegrand psi X sigma t j v‖ ≤
            (Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
              Real.rpow X (-(sigma + 1 / 4)) * (1 + |t|) ^ 6) *
              W * longTailShellUniformNormBound psi X sigma j := by
          simpa only [W] using hraw
        _ ≤ B * W * longTailShellUniformNormBound psi X sigma j := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left ht6 hbase) hW0) hCj0
        _ = u j := by rfl
  have heq : (fun t => ∑' j : ℕ, ∫ v : ℝ,
        longTailShellIntegrand psi X sigma t j v) =
      (fun t => ∫ v : ℝ,
        ramachandraShiftedContourIntegrand psi X sigma
          (-(sigma + 1 / 4)) t v true) := by
    funext t
    exact (hasSum_integral_longTailShellIntegrand_of_envelope psi
      hCgamma hglobal hX hcLo hcHi).tsum_eq
  rw [heq] at hcontOn
  apply hcontOn.continuousAt
  have hopen : Set.Ioo (t₀ - 1) (t₀ + 1) ∈ nhds t₀ := by
    exact Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [hopen] with t ht
  exact ⟨ht.1.le, ht.2.le⟩

/-- Primitive wrapper retained for downstream callers that already carry the
source-family hypothesis. -/
theorem continuous_integral_longContourIntegrand
    (psi : DirichletCharacter ℂ d) (_hprim : psi.IsPrimitive)
    {X sigma : ℝ} (hX : 1 ≤ X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) :
    Continuous (fun t => ∫ v : ℝ,
      ramachandraShiftedContourIntegrand psi X sigma
        (-(sigma + 1 / 4)) t v true) :=
  continuous_integral_longContourIntegrand_character psi hX hcLo hcHi

/-- Source-normalized long-contour square norms are continuous. -/
theorem continuous_primitiveShiftedLongContour_sq
    (psi : DirichletCharacter ℂ d)
    {T sigma : ℝ} (hT : 1 ≤ T)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) :
    Continuous (fun t => ‖primitiveShiftedLongContour psi T sigma t‖ ^ 2) := by
  have hX : 1 ≤ primitiveShiftedScale d T := by
    unfold primitiveShiftedScale
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
    nlinarith
  have hraw := continuous_integral_longContourIntegrand_character psi hX hcLo hcHi
  unfold primitiveShiftedLongContour ramachandraShiftedContourPiece
  exact (continuous_const.mul hraw).norm.pow 2

end
end RamachandraLongContourContinuity

#print axioms RamachandraLongContourContinuity.continuous_integral_longTailShellIntegrand
#print axioms RamachandraLongContourContinuity.continuous_integral_longContourIntegrand
#print axioms RamachandraLongContourContinuity.continuous_primitiveShiftedLongContour_sq
