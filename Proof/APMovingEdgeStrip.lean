import APLeftLineWindowKernel
import PrimitiveContourComponentBounds

/-!
# The moving paper-edge strip

The right edge `1 + 1/log u` moves by order `Δu/(u log^2 u)` across an
aligned window.  This file records that exact scalar gain before attaching
the horizontal contour integrand.
-/

namespace MAPAPMovingEdgeStrip

open MeasureTheory Set
open PrimitiveTruncatedExplicitFormulaBridge TruncatedTwistedPerron
open PaperEdgePrimitiveComponents

noncomputable section

/-- Reciprocal-log Lipschitz bound on `[a,b]`, source-faithful to the paper
edge `1+1/log`. -/
theorem inv_log_sub_inv_log_le
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (Real.log a)⁻¹ - (Real.log b)⁻¹ ≤
      (b - a) / (a * (Real.log a) ^ 2) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlmono : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  have hlb : 0 < Real.log b := hla.trans_le hlmono
  have hratio : 0 < b / a := div_pos hb0 ha0
  have hlogdiff : Real.log b - Real.log a ≤ (b - a) / a := by
    have h := Real.log_le_sub_one_of_pos hratio
    rw [Real.log_div hb0.ne' ha0.ne'] at h
    calc
      Real.log b - Real.log a ≤ b / a - 1 := h
      _ = (b - a) / a := by field_simp [ha0.ne']
  have hden : Real.log a * Real.log a ≤ Real.log a * Real.log b :=
    mul_le_mul_of_nonneg_left hlmono hla.le
  have hnum : 0 ≤ Real.log b - Real.log a := sub_nonneg.mpr hlmono
  calc
    (Real.log a)⁻¹ - (Real.log b)⁻¹ =
        (Real.log b - Real.log a) /
          (Real.log a * Real.log b) := by
      field_simp [hla.ne', hlb.ne']
    _ ≤ (Real.log b - Real.log a) /
          (Real.log a * Real.log a) := by
      exact div_le_div_of_nonneg_left hnum
        (mul_pos hla hla) hden
    _ ≤ ((b - a) / a) / (Real.log a * Real.log a) := by
      exact div_le_div_of_nonneg_right hlogdiff
        (mul_nonneg hla.le hla.le)
    _ = (b - a) / (a * (Real.log a) ^ 2) := by
      field_simp [ha0.ne', hla.ne']

/-- The standard paper edge is antitone. -/
theorem standardEdge_antitone
    {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    standardEdge N ≤ standardEdge m := by
  have ha : 0 < halfIntegerPoint m := halfIntegerPoint_pos m
  have hab : halfIntegerPoint m ≤ halfIntegerPoint N := by
    have hmNReal : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
    unfold halfIntegerPoint
    linarith
  have hma : 1 < halfIntegerPoint m := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    unfold halfIntegerPoint
    linarith
  have hlogmono := Real.log_le_log ha hab
  have hlogm : 0 < Real.log (halfIntegerPoint m) := Real.log_pos hma
  have hinv := inv_anti₀ hlogm hlogmono
  unfold standardEdge
  linarith

/-- Quantitative motion of the endpoint-dependent standard edge. -/
theorem standardEdge_sub_le_alignedWidth
    {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    standardEdge m - standardEdge N ≤
      ((N : ℝ) - (m : ℝ)) /
        (halfIntegerPoint m * (Real.log (halfIntegerPoint m)) ^ 2) := by
  have hma : 1 < halfIntegerPoint m := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    unfold halfIntegerPoint
    linarith
  have hab : halfIntegerPoint m ≤ halfIntegerPoint N := by
    have hmNReal : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
    unfold halfIntegerPoint
    linarith
  have h := inv_log_sub_inv_log_le hma hab
  unfold standardEdge
  have hdiff : halfIntegerPoint N - halfIntegerPoint m =
      (N : ℝ) - (m : ℝ) := by unfold halfIntegerPoint; ring
  rw [hdiff] at h
  linarith

/-! ## Horizontal edge-strip identity and bound -/

variable {q : ℕ} [NeZero q]

/-- Changing only the right edge adds exactly the horizontal contour over the
intervening strip. -/
theorem horizontalBoundaryIntegral_sub_eq_edgeStrip
    (chi : DirichletCharacter ℂ q)
    {x sigma cLo cHi T : ℝ}
    (htopLeft : IntervalIntegrable
      (fun r : ℝ => perronContourIntegrand chi x
        ((r : ℂ) + Complex.I * T)) volume sigma cLo)
    (htopStrip : IntervalIntegrable
      (fun r : ℝ => perronContourIntegrand chi x
        ((r : ℂ) + Complex.I * T)) volume cLo cHi)
    (hbotLeft : IntervalIntegrable
      (fun r : ℝ => perronContourIntegrand chi x
        ((r : ℂ) - Complex.I * T)) volume sigma cLo)
    (hbotStrip : IntervalIntegrable
      (fun r : ℝ => perronContourIntegrand chi x
        ((r : ℂ) - Complex.I * T)) volume cLo cHi) :
    horizontalBoundaryIntegral chi x sigma cHi T -
        horizontalBoundaryIntegral chi x sigma cLo T =
      horizontalBoundaryIntegral chi x cLo cHi T := by
  have ht := intervalIntegral.integral_add_adjacent_intervals
    htopLeft htopStrip
  have hb := intervalIntegral.integral_add_adjacent_intervals
    hbotLeft hbotStrip
  unfold horizontalBoundaryIntegral
  rw [← ht, ← hb]
  ring

/-- Quantitative norm bound for the horizontal edge strip. -/
theorem norm_horizontalEdgeStrip_le
    (chi : DirichletCharacter ℂ q)
    {x cLo cHi T M : ℝ} (hx : 1 ≤ x) (hc : cLo ≤ cHi)
    (hT : 0 < T)
    (htop : ∀ r ∈ Set.Icc cLo cHi,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * T)‖ ≤ M)
    (hbottom : ∀ r ∈ Set.Icc cLo cHi,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) - Complex.I * T)‖ ≤ M) :
    ‖horizontalBoundaryIntegral chi x cLo cHi T‖ ≤
      (cHi - cLo) / Real.pi * (M * Real.rpow x cHi / T) := by
  exact PrimitiveContourComponentBounds.norm_horizontalBoundaryIntegral_le_of_logDeriv
    chi hx hc hT htop hbottom

/-- The literal standard-edge strip width is the reciprocal-log gain. -/
theorem norm_standardEdgeHorizontalStrip_le
    (chi : DirichletCharacter ℂ q)
    {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N)
    {T M : ℝ} (hT : 0 < T)
    (htop : ∀ r ∈ Set.Icc (standardEdge N) (standardEdge m),
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * T)‖ ≤ M)
    (hbottom : ∀ r ∈ Set.Icc (standardEdge N) (standardEdge m),
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) - Complex.I * T)‖ ≤ M) :
    ‖horizontalBoundaryIntegral chi (halfIntegerPoint N)
        (standardEdge N) (standardEdge m) T‖ ≤
      (((N : ℝ) - (m : ℝ)) /
          (halfIntegerPoint m * (Real.log (halfIntegerPoint m)) ^ 2)) /
        Real.pi *
          (M * Real.rpow (halfIntegerPoint N) (standardEdge m) / T) := by
  have hx : 1 ≤ halfIntegerPoint N := by
    have hN : 1 ≤ N := hm.trans hmN
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    unfold halfIntegerPoint
    linarith
  have hc := standardEdge_antitone hm hmN
  have hbase := norm_horizontalEdgeStrip_le chi hx hc hT htop hbottom
  have hwidth := standardEdge_sub_le_alignedWidth hm hmN
  have hrest : 0 ≤ M * Real.rpow (halfIntegerPoint N) (standardEdge m) / T := by
    have hM : 0 ≤ M := by
      have hz := htop (standardEdge N) ⟨le_rfl, hc⟩
      exact (norm_nonneg _).trans hz
    exact div_nonneg
      (mul_nonneg hM (Real.rpow_nonneg (halfIntegerPoint_pos N).le _)) hT.le
  calc
    ‖horizontalBoundaryIntegral chi (halfIntegerPoint N)
        (standardEdge N) (standardEdge m) T‖ ≤
      (standardEdge m - standardEdge N) / Real.pi *
        (M * Real.rpow (halfIntegerPoint N) (standardEdge m) / T) := hbase
    _ ≤ (((N : ℝ) - (m : ℝ)) /
          (halfIntegerPoint m * (Real.log (halfIntegerPoint m)) ^ 2)) /
        Real.pi *
          (M * Real.rpow (halfIntegerPoint N) (standardEdge m) / T) := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hwidth Real.pi_pos.le) hrest

end

end MAPAPMovingEdgeStrip
