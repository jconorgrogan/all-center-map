import FordScaledBlaschkeFill
import CompactDeflatedBorelBridge
import Mathlib.Analysis.Complex.AbsMax

open Complex Set Metric
noncomputable section

namespace FordScaledBlaschkeBorel

open FordScaledBlaschkeFill

theorem norm_logDeriv_scaledBlaschkeFill_le
    {f : ℂ → ℂ} {c s : ℂ} {a G M : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    (ha : 0 < a) (hG : 0 < G) (hM : 0 < M) (hfc : f c ≠ 0)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c (6 * a)))
    (hbound : ∀ z ∈ Metric.closedBall c (6 * a), ‖f z‖ ≤ G)
    (hS : ∀ ρ ∈ S, ρ ∈ Metric.ball c (3 * a))
    (hm : ∀ ρ ∈ S, m ρ = analyticOrderNatAt f ρ)
    (hfinite : ∀ ρ ∈ S, analyticOrderAt f ρ ≠ ⊤)
    (hcover : ∀ z ∈ Metric.ball c (3 * a), f z = 0 → z ∈ S)
    (hlogM : Real.log G - Real.log ‖f c‖ ≤ M)
    (hs : dist s c < a) :
    ‖logDeriv (scaledBlaschkeFill f c (3 * a) S m) s‖ ≤ 20 * M / a := by
  have h3 : 0 < (3 : ℝ) * a := by linarith
  have hsubset : Metric.closedBall c (3 * a) ⊆
      Metric.closedBall c (6 * a) := by
    intro z hz
    rw [Metric.mem_closedBall] at hz ⊢
    linarith [hz, ha]
  have hf3 : AnalyticOnNhd ℂ f (Metric.closedBall c (3 * a)) := by
    intro z hz
    exact hf z (hsubset hz)
  let g : ℂ → ℂ := scaledBlaschkeFill f c (3 * a) S m
  have hgAn : AnalyticOnNhd ℂ g (Metric.closedBall c (3 * a)) := by
    exact analyticOnNhd_scaledBlaschkeFill h3 hf3 hS hm hfinite hcover
  have hgDiff : DifferentiableOn ℂ g (Metric.closedBall c (3 * a)) :=
    hgAn.differentiableOn
  have hgNe : ∀ z ∈ Metric.ball c (3 * a), g z ≠ 0 := by
    intro z hz
    exact scaledBlaschkeFill_ne_zero_of_zero_covered h3 hf3 hS hm hfinite hcover hz
  have hgBoundary : ∀ z ∈ Metric.sphere c (3 * a), ‖g z‖ = ‖f z‖ := by
    intro z hz
    exact norm_scaledBlaschkeFill_eq_on_sphere h3 hf3 hS hm hfinite hcover hz
  have hgBound : ∀ z ∈ Metric.closedBall c (3 * a), ‖g z‖ ≤ G := by
    intro z hz
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball (hgDiff.diffContOnCl_ball subset_rfl)
    · intro w hw
      have hwsphere : w ∈ Metric.sphere c (3 * a) := frontier_ball_subset_sphere hw
      rw [hgBoundary w hwsphere]
      apply hbound w
      rw [Metric.mem_closedBall]
      have hdist : dist w c = 3 * a := by
        rw [Metric.mem_sphere] at hwsphere
        exact hwsphere
      rw [hdist]
      linarith [ha]
    · rw [closure_ball c (by linarith : (3 : ℝ) * a ≠ 0)]
      exact hz
  have hfcpos : 0 < ‖f c‖ := norm_pos_iff.mpr hfc
  have hgc_le : ‖f c‖ ≤ ‖g c‖ := by
    exact norm_f_center_le_scaledBlaschkeFill_center h3 hf3 hS hm hfinite hcover hfc
  have hgcpos : 0 < ‖g c‖ := lt_of_lt_of_le hfcpos hgc_le
  have hlog : ∀ z ∈ Metric.ball c (3 * a),
      Real.log (‖g z‖ / ‖g c‖) ≤ M := by
    intro z hz
    have hzclosed : z ∈ Metric.closedBall c (3 * a) :=
      Metric.mem_closedBall.mpr (Metric.mem_ball.mp hz).le
    have hgz : 0 < ‖g z‖ := norm_pos_iff.mpr (hgNe z hz)
    have hratio : ‖g z‖ / ‖g c‖ ≤ G / ‖f c‖ := by
      apply (div_le_div_iff₀ hgcpos hfcpos).2
      exact mul_le_mul (hgBound z hzclosed) hgc_le (norm_nonneg _) hG.le
    calc
      Real.log (‖g z‖ / ‖g c‖) ≤ Real.log (G / ‖f c‖) :=
        Real.log_le_log (by positivity) hratio
      _ = Real.log G - Real.log ‖f c‖ := by
        rw [Real.log_div (ne_of_gt hG) (ne_of_gt hfcpos)]
      _ ≤ M := hlogM
  have hbase := CompactDeflatedBorelBridge.norm_logDeriv_le_of_scaled_log_norm_ratio_le_at
    (g := g) (c := c) (s := s) (r := 2 * a) (M := M)
    (by linarith)
    (by
      simpa only [show (3 : ℝ) * (2 * a) / 2 = 3 * a by ring] using
        (hgDiff.mono (ball_subset_closedBall)))
    (by
      intro z hz
      apply hgNe z
      simpa only [show (3 : ℝ) * (2 * a) / 2 = 3 * a by ring] using hz)
    hM
    (by
      intro z hz
      apply hlog z
      simpa only [show (3 : ℝ) * (2 * a) / 2 = 3 * a by ring] using hz)
    (by linarith [hs])
  calc
    ‖logDeriv g s‖ ≤ 40 * M / (2 * a) := hbase
    _ = 20 * M / a := by field_simp [ne_of_gt ha] <;> ring

end FordScaledBlaschkeBorel

#print axioms FordScaledBlaschkeBorel.norm_logDeriv_scaledBlaschkeFill_le
