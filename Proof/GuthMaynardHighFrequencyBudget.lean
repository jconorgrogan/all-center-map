import GuthMaynardJIterationSourceHighFrequency

/-!
# Polynomial budget for Guth--Maynard region III

The high-frequency cutoff is exactly `T^6`.  This file certifies the source's
claim that one selectable rapid-decay order pays the `T^-100` remainder once
the remaining seminorm/range factors have polynomial growth.
-/

open scoped Real
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- Source-shaped polynomial collection for the complete region-III envelope.
The combined finite-range, bump, ratio-upper, seminorm, and `sup f` factors
are allowed growth `T^(d+16)`, while the reciprocal dyadic ratio costs `T^5`.
At the selected order `q=d+77`, the full envelope has exactly the growth
required by `highFrequencyBudget_of_polynomialGrowth` with parameter `d+27`.
-/
theorem sourceHighFrequencyEnvelope_polynomialGrowth
    (d : ℕ) {T N1 N2 N3 P1 Rhi Cdec S Rlo C D : ℝ}
    (hT : 1 ≤ T)
    (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2) (hN3 : 0 ≤ N3)
    (hP1 : 0 ≤ P1) (hRhi : 0 ≤ Rhi) (hCdec : 0 ≤ Cdec)
    (hS : 0 ≤ S) (hRlo : 0 < Rlo) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hprefix : N1 * N2 * N3 * P1 * Rhi * Cdec * S ≤
      C * T ^ (d + 16))
    (hratio : T / Rlo ≤ D * T ^ 5) :
    N1 * N2 * N3 * P1 * Rhi *
        (Cdec * Real.rpow T 1 * (T / Rlo) ^ (d + 79) *
          2 ^ (d + 79) * S) ≤
      (C * D ^ (d + 79) * 2 ^ (d + 79)) *
        T ^ (6 * (d + 27) + 250) := by
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hratio0 : 0 ≤ T / Rlo := div_nonneg hT0 hRlo.le
  have hratioPow := pow_le_pow_left₀ hratio0 hratio (d + 79)
  calc
    N1 * N2 * N3 * P1 * Rhi *
          (Cdec * Real.rpow T 1 * (T / Rlo) ^ (d + 79) *
            2 ^ (d + 79) * S) =
        (N1 * N2 * N3 * P1 * Rhi * Cdec * S) * T *
          (T / Rlo) ^ (d + 79) * 2 ^ (d + 79) := by
      have hRpowOne : Real.rpow T (1 : ℝ) = T := Real.rpow_one T
      rw [hRpowOne]
      ring
    _ ≤ (C * T ^ (d + 16)) * T *
          (D * T ^ 5) ^ (d + 79) * 2 ^ (d + 79) := by
      gcongr
    _ = (C * D ^ (d + 79) * 2 ^ (d + 79)) *
          T ^ (6 * (d + 27) + 250) := by
      have hexp : (d + 16) + 1 + 5 * (d + 79) =
          6 * (d + 27) + 250 := by omega
      have hTcombine : T ^ (d + 16) * T * (T ^ 5) ^ (d + 79) =
          T ^ (6 * (d + 27) + 250) := by
        calc
          T ^ (d + 16) * T * (T ^ 5) ^ (d + 79) =
          T ^ (d + 16) * T ^ 1 * T ^ (5 * (d + 79)) := by
            rw [pow_one, pow_mul]
          _ = T ^ ((d + 16) + 1 + 5 * (d + 79)) := by
            rw [← pow_add, ← pow_add]
          _ = T ^ (6 * (d + 27) + 250) := by rw [hexp]
      rw [mul_pow]
      calc
        C * T ^ (d + 16) * T *
              (D ^ (d + 79) * (T ^ 5) ^ (d + 79)) * 2 ^ (d + 79) =
            (C * D ^ (d + 79) * 2 ^ (d + 79)) *
              (T ^ (d + 16) * T * (T ^ 5) ^ (d + 79)) := by ring
        _ = _ := by rw [hTcombine]

/-- The literal Section 9 scale package implies the complete region-III
envelope bound.  The constants `7,7,5,1,2` are the source dyadic cardinality,
bump, and ratio bounds; the deliberately loose reciprocal-ratio budget is
`T/Rlo <= 2*T^5`.  At the single selected order `q=77`, all factors fit the
polynomial exponent `412 = 6*27+250` required below. -/
theorem sourceHighFrequencyEnvelope_of_literalScaleBounds
    {T N1 N2 N3 P1 Rhi Cdec S Rlo : ℝ}
    (hT : 1 ≤ T)
    (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2) (hN3 : 0 ≤ N3)
    (hP1 : 0 ≤ P1) (hRhi : 0 ≤ Rhi) (hCdec : 0 ≤ Cdec)
    (hS : 0 ≤ S) (hRlo : 0 < Rlo)
    (hN1scale : N1 ≤ 7 * T) (hN2scale : N2 ≤ 7 * T)
    (hN3scale : N3 ≤ 5 * T) (hP1scale : P1 ≤ 1)
    (hRhiscale : Rhi ≤ 2 * T)
    (hratio : T / Rlo ≤ 2 * T ^ 5) :
    N1 * N2 * N3 * P1 * Rhi *
        (Cdec * Real.rpow T 1 * (T / Rlo) ^ 79 * 2 ^ 79 * S) ≤
      ((490 * Cdec * S) * 2 ^ 79 * 2 ^ 79) * T ^ 412 := by
  have hprefix : N1 * N2 * N3 * P1 * Rhi * Cdec * S ≤
      (490 * Cdec * S) * T ^ (0 + 16) := by
    calc
      N1 * N2 * N3 * P1 * Rhi * Cdec * S ≤
          (7 * T) * (7 * T) * (5 * T) * 1 * (2 * T) * Cdec * S := by
        gcongr
      _ = (490 * Cdec * S) * T ^ 4 := by ring
      _ ≤ (490 * Cdec * S) * T ^ 16 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hT (show 4 ≤ 16 by omega)) (by positivity)
      _ = (490 * Cdec * S) * T ^ (0 + 16) := by norm_num
  have h := sourceHighFrequencyEnvelope_polynomialGrowth 0 hT hN1 hN2 hN3
    hP1 hRhi hCdec hS hRlo (by positivity) (by positivity) hprefix hratio
  norm_num at h ⊢
  exact h

/-- If the complete high-frequency envelope constant grows like
`T^(6d+250)`, choosing decay order `q=d+50` exactly cancels the requested
`T^100` after squaring against the cutoff `(T^6)^q`. -/
theorem highFrequencyBudget_of_polynomialGrowth
    (d : ℕ) {T K C B mass : ℝ}
    (hT : 1 ≤ T) (hK0 : 0 ≤ K) (hC : 0 ≤ C)
    (hmass0 : 0 ≤ mass) (hmass : mass ≤ B)
    (hK : K ≤ C * T ^ (6 * d + 250)) :
    (K / (sourceHighFrequencyCutoff T) ^ (d + 50)) ^ 2 *
        mass * T ^ 100 ≤ C ^ 2 * B := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hcut : sourceHighFrequencyCutoff T = T ^ 6 := rfl
  have hdenpos : 0 < (sourceHighFrequencyCutoff T) ^ (d + 50) := by
    rw [hcut]
    positivity
  have hratio0 : 0 ≤ K / (sourceHighFrequencyCutoff T) ^ (d + 50) :=
    div_nonneg hK0 hdenpos.le
  have hratioUpper0 :
      0 ≤ (C * T ^ (6 * d + 250)) /
        (sourceHighFrequencyCutoff T) ^ (d + 50) := by positivity
  have hratio :
      K / (sourceHighFrequencyCutoff T) ^ (d + 50) ≤
        (C * T ^ (6 * d + 250)) /
          (sourceHighFrequencyCutoff T) ^ (d + 50) :=
    div_le_div_of_nonneg_right hK hdenpos.le
  have hsq := (sq_le_sq₀ hratio0 hratioUpper0).2 hratio
  calc
    (K / (sourceHighFrequencyCutoff T) ^ (d + 50)) ^ 2 *
          mass * T ^ 100 ≤
        ((C * T ^ (6 * d + 250)) /
          (sourceHighFrequencyCutoff T) ^ (d + 50)) ^ 2 *
            mass * T ^ 100 := by
      gcongr
    _ ≤ ((C * T ^ (6 * d + 250)) /
          (sourceHighFrequencyCutoff T) ^ (d + 50)) ^ 2 *
            B * T ^ 100 := by
      gcongr
    _ = C ^ 2 * B := by
      rw [hcut, ← pow_mul]
      have hexp : 6 * (d + 50) = (6 * d + 250) + 50 := by omega
      rw [hexp, pow_add]
      have h100 : 100 = 50 * 2 := by norm_num
      rw [h100, pow_mul]
      field_simp [hTpos.ne']
      ring

/-- Direct specialization to the actual quartic envelope mass. -/
theorem sourceHighFrequencyBudget_of_polynomialGrowth
    (d : ℕ) {T K C B : ℝ}
    (hT : 1 ≤ T) (hK0 : 0 ≤ K) (hC : 0 ≤ C)
    (hmass : quarticDecayMass ≤ B)
    (hK : K ≤ C * T ^ (6 * d + 250)) :
    (K / (sourceHighFrequencyCutoff T) ^ (d + 50)) ^ 2 *
        quarticDecayMass * T ^ 100 ≤ C ^ 2 * B := by
  apply highFrequencyBudget_of_polynomialGrowth d hT hK0 hC
  · unfold quarticDecayMass
    exact integral_nonneg fun xi => by
      unfold quarticDecayEnvelope
      positivity
  · exact hmass
  · exact hK

/-- Fully instantiated polynomial budget for the literal source scale bounds.
This is the exact `q=77` premise consumed by
`sourceGFinite_highFrequencyIntegral_le_time_neg100`; only the analytic rapid
decay estimate and the elementary scale/cardinality inequalities remain to be
supplied by the concrete profile and dyadic ranges. -/
theorem sourceHighFrequencyBudget_of_literalScaleBounds
    {T N1 N2 N3 P1 Rhi Cdec S Rlo B : ℝ}
    (hT : 1 ≤ T)
    (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2) (hN3 : 0 ≤ N3)
    (hP1 : 0 ≤ P1) (hRhi : 0 ≤ Rhi) (hCdec : 0 ≤ Cdec)
    (hS : 0 ≤ S) (hRlo : 0 < Rlo)
    (hN1scale : N1 ≤ 7 * T) (hN2scale : N2 ≤ 7 * T)
    (hN3scale : N3 ≤ 5 * T) (hP1scale : P1 ≤ 1)
    (hRhiscale : Rhi ≤ 2 * T)
    (hratio : T / Rlo ≤ 2 * T ^ 5)
    (hmass : quarticDecayMass ≤ B) :
    ((N1 * N2 * N3 * P1 * Rhi *
          (Cdec * Real.rpow T 1 * (T / Rlo) ^ 79 * 2 ^ 79 * S)) /
        (sourceHighFrequencyCutoff T) ^ 77) ^ 2 *
          quarticDecayMass * T ^ 100 ≤
      ((490 * Cdec * S) * 2 ^ 79 * 2 ^ 79) ^ 2 * B := by
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hratio0 : 0 ≤ T / Rlo := div_nonneg hT0 hRlo.le
  have hRpow0 : 0 ≤ Real.rpow T (1 : ℝ) := Real.rpow_nonneg hT0 1
  apply sourceHighFrequencyBudget_of_polynomialGrowth 27 hT
  · positivity
  · positivity
  · exact hmass
  · have henv := sourceHighFrequencyEnvelope_of_literalScaleBounds hT hN1 hN2 hN3
      hP1 hRhi hCdec hS hRlo hN1scale hN2scale hN3scale hP1scale
      hRhiscale hratio
    have hRpowOne : Real.rpow T (1 : ℝ) = T := Real.rpow_one T
    norm_num at henv ⊢
    simpa only [hRpowOne] using henv

/-- The quantified source rapid-decay hypothesis selects the single order and
constant needed by the literal `q=77` region-III estimate.  This eliminates
the last profile-seminorm choice from the high-frequency branch. -/
theorem exists_sourceHighFrequencyBudget_of_rapidDecay_literalScaleBounds
    (fhat : ℝ → ℂ) {T S N1 N2 N3 P1 Rhi Rlo B : ℝ}
    (hdecay : SourceFourierRapidDecay fhat T S)
    (hT : 1 ≤ T)
    (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2) (hN3 : 0 ≤ N3)
    (hP1 : 0 ≤ P1) (hRhi : 0 ≤ Rhi) (hS : 0 ≤ S)
    (hRlo : 0 < Rlo)
    (hN1scale : N1 ≤ 7 * T) (hN2scale : N2 ≤ 7 * T)
    (hN3scale : N3 ≤ 5 * T) (hP1scale : P1 ≤ 1)
    (hRhiscale : Rhi ≤ 2 * T)
    (hratio : T / Rlo ≤ 2 * T ^ 5)
    (hmass : quarticDecayMass ≤ B) :
    ∃ Cdec : ℝ, 0 ≤ Cdec ∧
      (∀ {m1 m2 xi : ℝ},
        m1 ≠ 0 → m2 ≠ 0 → xi ≠ 0 →
        ‖fhat ((m2 / m1) * xi)‖ ≤
          Cdec * Real.rpow T 1 *
            (T / (|m2 / m1| * |xi|)) ^ 79 * S) ∧
      ((N1 * N2 * N3 * P1 * Rhi *
            (Cdec * Real.rpow T 1 * (T / Rlo) ^ 79 * 2 ^ 79 * S)) /
          (sourceHighFrequencyCutoff T) ^ 77) ^ 2 *
            quarticDecayMass * T ^ 100 ≤
        ((490 * Cdec * S) * 2 ^ 79 * 2 ^ 79) ^ 2 * B := by
  obtain ⟨Cdec, hCdec, hbound⟩ :=
    sourceFourierRapidDecay_at_dyadicRatio fhat hdecay zero_lt_one 79
  refine ⟨Cdec, hCdec, hbound, ?_⟩
  exact sourceHighFrequencyBudget_of_literalScaleBounds hT hN1 hN2 hN3 hP1
    hRhi hCdec hS hRlo hN1scale hN2scale hN3scale hP1scale hRhiscale
    hratio hmass

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.highFrequencyBudget_of_polynomialGrowth
#print axioms GuthMaynardJIteration.sourceHighFrequencyBudget_of_polynomialGrowth
#print axioms GuthMaynardJIteration.sourceHighFrequencyEnvelope_polynomialGrowth
#print axioms GuthMaynardJIteration.sourceHighFrequencyEnvelope_of_literalScaleBounds
#print axioms GuthMaynardJIteration.sourceHighFrequencyBudget_of_literalScaleBounds
#print axioms GuthMaynardJIteration.exists_sourceHighFrequencyBudget_of_rapidDecay_literalScaleBounds
