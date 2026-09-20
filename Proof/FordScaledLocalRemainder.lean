import FordScaledBlaschkeBorel
import FordScaledBlaschkeLogDerivative
import FordScaledJensenCount
import FordScaledCanonicalCorrection
import FordScaledZeroSet

open scoped BigOperators
noncomputable section

namespace FordScaledLocalRemainder

open Complex Set Metric
open FordScaledBlaschkeFill
open WideDiskLocalLogDerivative

/-- The local logarithmic derivative remainder after removing the poles at the
listed zeros.  The extra `hSzero` records that the finite list has no
extraneous points, which is exactly what lets a nonzero evaluation point avoid
all members of the list. -/
theorem norm_logDeriv_sub_poleSum_le
    {f : ℂ → ℂ} {c s : ℂ} {a G M : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    (ha : 0 < a) (hG : 0 < G) (hM : 0 < M) (hfc : f c ≠ 0)
    (hf : AnalyticOnNhd ℂ f (closedBall c (6 * a)))
    (hbound : ∀ z ∈ closedBall c (6 * a), ‖f z‖ ≤ G)
    (hS : ∀ ρ ∈ S, ρ ∈ ball c (3 * a))
    (hSzero : ∀ ρ ∈ S, f ρ = 0)
    (hm : ∀ ρ ∈ S, m ρ = analyticOrderNatAt f ρ)
    (hfinite : ∀ ρ ∈ S, analyticOrderAt f ρ ≠ ⊤)
    (hcover : ∀ z ∈ ball c (3 * a), f z = 0 → z ∈ S)
    (hlogM : Real.log G - Real.log ‖f c‖ ≤ M)
    (hs : s ∈ ball c a) (hfs : f s ≠ 0) :
    ‖logDeriv f s - ∑ ρ ∈ S, (m ρ : ℂ) / (s - ρ)‖ ≤
      (20 + 1 / (2 * Real.log 2)) * M / a := by
  have hsF : s ∉ S := by
    intro hsS
    have : f s = 0 := hSzero s hsS
    exact hfs this
  have hf3 : AnalyticOnNhd ℂ f (closedBall c (3 * a)) := by
    intro z hz
    apply hf z
    rw [mem_closedBall] at hz ⊢
    linarith [hz, ha]
  have hBorel := FordScaledBlaschkeBorel.norm_logDeriv_scaledBlaschkeFill_le
    (f := f) (c := c) (s := s) (a := a) (G := G) (M := M) (S := S) (m := m)
    ha hG hM hfc hf hbound hS hm hfinite hcover hlogM
    (by simpa [mem_ball] using hs)
  have hcount := FordScaledJensenCount.finite_analyticMultiplicity_le
    (a := a) (c := c) (f := f) ha hf hfc hG hbound S
    (by intro ρ hρ; exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp (hS ρ hρ)).le)
  have hcorr := FordScaledCanonicalCorrection.norm_finiteWeightedCorrection_le
    (a := a) (c := c) ha S m hs hS
  have hdec := FordScaledBlaschkeLogDerivative.logDeriv_scaledBlaschkeFill_decomposition
    (a := a) (c := c) (f := f) (S := S) (m := m) (s := s)
    ha hf3 hS hm hfinite hs hfs hsF
  have hsum_m :
      (∑ ρ ∈ S, (m ρ : ℝ)) =
        ∑ ρ ∈ S, (FordScaledJensenCount.analyticMultiplicity f ρ : ℝ) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp [FordScaledJensenCount.analyticMultiplicity, hm ρ hρ]
  have hcorr' :
      ‖∑ ρ ∈ S, (m ρ : ℂ) *
          logDeriv (shiftedCanonicalNumerator c ρ (3 * a)) s‖ ≤
        (∑ ρ ∈ S, (FordScaledJensenCount.analyticMultiplicity f ρ : ℝ)) /
          (2 * a) := by
    simpa [hsum_m] using hcorr
  have hmain :
      ‖logDeriv f s - ∑ ρ ∈ S, (m ρ : ℂ) / (s - ρ)‖ ≤
        20 * M / a +
          (∑ ρ ∈ S, (FordScaledJensenCount.analyticMultiplicity f ρ : ℝ)) /
            (2 * a) := by
    have hid :
        logDeriv f s - ∑ ρ ∈ S, (m ρ : ℂ) / (s - ρ) =
          logDeriv (scaledBlaschkeFill f c (3 * a) S m) s -
            ∑ ρ ∈ S, (m ρ : ℂ) *
              logDeriv (shiftedCanonicalNumerator c ρ (3 * a)) s := by
      rw [hdec]
      ring
    rw [hid]
    exact (norm_sub_le _ _).trans (add_le_add hBorel hcorr')
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcount' :
      (∑ ρ ∈ S, (FordScaledJensenCount.analyticMultiplicity f ρ : ℝ)) /
          (2 * a) ≤
        (Real.log G - Real.log ‖f c‖) / (2 * a * Real.log 2) := by
    calc
      (∑ ρ ∈ S, (FordScaledJensenCount.analyticMultiplicity f ρ : ℝ)) /
          (2 * a) ≤
          ((Real.log G - Real.log ‖f c‖) / Real.log 2) / (2 * a) :=
        div_le_div_of_nonneg_right hcount (by positivity)
      _ = (Real.log G - Real.log ‖f c‖) / (2 * a * Real.log 2) := by
        field_simp [ne_of_gt ha, ne_of_gt hlog2]
  have hbudget :
      (Real.log G - Real.log ‖f c‖) / (2 * a * Real.log 2) ≤
        M / (2 * a * Real.log 2) := by
    exact div_le_div_of_nonneg_right hlogM (by positivity)
  calc
    ‖logDeriv f s - ∑ ρ ∈ S, (m ρ : ℂ) / (s - ρ)‖ ≤
        20 * M / a +
          (∑ ρ ∈ S, (FordScaledJensenCount.analyticMultiplicity f ρ : ℝ)) /
            (2 * a) := hmain
    _ ≤ 20 * M / a + M / (2 * a * Real.log 2) :=
      by
        simpa [add_comm] using
          (add_le_add_left (hcount'.trans hbudget) (20 * M / a))
    _ = (20 + 1 / (2 * Real.log 2)) * M / a := by
      field_simp [ne_of_gt ha, ne_of_gt hlog2]


/-- Finite zero set and the corresponding local logarithmic derivative remainder. -/
theorem exists_finite_zero_set_remainder
    {f : ℂ → ℂ} {c : ℂ} {a G M : ℝ}
    (ha : 0 < a) (hG : 0 < G) (hM : 0 < M) (hfc : f c ≠ 0)
    (hf : AnalyticOnNhd ℂ f (closedBall c (6 * a)))
    (hbound : ∀ z ∈ closedBall c (6 * a), ‖f z‖ ≤ G)
    (hlogM : Real.log G - Real.log ‖f c‖ ≤ M) :
    ∃ S : Finset ℂ,
      (∀ ρ, ρ ∈ S ↔ ρ ∈ ball c (3 * a) ∧ f ρ = 0) ∧
      (∀ ρ ∈ S,
        analyticOrderAt f ρ ≠ ⊤ ∧ 1 ≤ analyticOrderNatAt f ρ) ∧
      (∀ s, s ∈ ball c a → f s ≠ 0 →
        ‖logDeriv f s -
            ∑ ρ ∈ S, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤
          (20 + 1 / (2 * Real.log 2)) * M / a) := by
  obtain ⟨S, hSiff, hSprops⟩ :=
    FordScaledZeroSet.exists_finite_zero_set ha hf hfc
  refine ⟨S, hSiff, hSprops, ?_⟩
  intro s hs hfs
  have hS : ∀ ρ ∈ S, ρ ∈ ball c (3 * a) := by
    intro ρ hρ
    exact (hSiff ρ).mp hρ |>.1
  have hSzero : ∀ ρ ∈ S, f ρ = 0 := by
    intro ρ hρ
    exact (hSiff ρ).mp hρ |>.2
  have hm : ∀ ρ ∈ S, analyticOrderNatAt f ρ = analyticOrderNatAt f ρ := by
    intro ρ hρ
    rfl
  have hfinite : ∀ ρ ∈ S, analyticOrderAt f ρ ≠ ⊤ := by
    intro ρ hρ
    exact (hSprops ρ hρ).1
  have hcover : ∀ z ∈ ball c (3 * a), f z = 0 → z ∈ S := by
    intro z hzball hzero
    exact (hSiff z).mpr ⟨hzball, hzero⟩
  have hmain := norm_logDeriv_sub_poleSum_le
    (f := f) (c := c) (s := s) (a := a) (G := G) (M := M)
    (S := S) (m := analyticOrderNatAt f)
    ha hG hM hfc hf hbound hS hSzero hm hfinite hcover hlogM hs hfs
  simpa using hmain

end FordScaledLocalRemainder

#print axioms FordScaledLocalRemainder.norm_logDeriv_sub_poleSum_le
#print axioms FordScaledLocalRemainder.exists_finite_zero_set_remainder
