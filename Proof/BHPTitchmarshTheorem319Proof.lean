import BHPTitchmarshPerronCore
import MRTCorollary25TransitionBand
import MertensAnalyticLeaf
import PaperEdgePerronRemainder
import Mathlib.NumberTheory.Harmonic.Bounds

namespace MAPBHPTitchmarshTheorem319Proof
open Set MeasureTheory Metric TopologicalSpace PerronKernel
open scoped BigOperators Interval LSeries.notation
open MAPBHPCorrectedContourShift
open MAPMRTLemma210OrthogonalityReduction
open MAPMRTLemma211AllCharacterSource
open MAPBHPTitchmarshPerronCore

noncomputable section

theorem norm_bhpCriticalLSeriesCoefficient_le
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ)
    {n : ℕ} (hn : n ≠ 0) :
    ‖bhpCriticalLSeriesCoefficient chi t n‖ ≤
      1 / Real.sqrt (n : ℝ) := by
  rw [bhpCriticalLSeriesCoefficient, LSeries.norm_term_eq, if_neg hn]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hchar := chi.norm_le_one n
  have hpow : (n : ℝ) ^ (((((1 / 2 : ℝ) : ℂ) + t * Complex.I)).re) =
      Real.sqrt (n : ℝ) := by
    have hre : (((((1 / 2 : ℝ) : ℂ) + t * Complex.I)).re) = 1 / 2 := by
      simp
    rw [hre]
    simpa [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num] using
      (Real.sqrt_eq_rpow (n : ℝ)).symm
  rw [hpow]
  exact div_le_div_of_nonneg_right hchar (Real.sqrt_nonneg _)

theorem bhpCriticalLSeriesCoefficient_eq_prefixTerm
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ)
    {n : ℕ} (hn : n ≠ 0) :
    bhpCriticalLSeriesCoefficient chi t n =
      (criticalPrefixCoefficient n * chi n) * twistedPhase n t := by
  unfold bhpCriticalLSeriesCoefficient criticalPrefixCoefficient twistedPhase
  rw [LSeries.term_of_ne_zero hn]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]
  have hsqrt : ((Real.sqrt (n : ℝ) : ℂ)⁻¹) =
      Complex.exp (-(((1 / 2 : ℝ) : ℂ) * Real.log (n : ℝ))) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnpos]
    rw [Complex.ofReal_exp]
    rw [← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [hsqrt, div_eq_mul_inv, ← Complex.exp_neg]
  have hexponent :
      -(Complex.log (n : ℂ) *
          ((((1 / 2 : ℝ) : ℂ) + t * Complex.I))) =
        -(((1 / 2 : ℝ) : ℂ) * Real.log (n : ℝ)) +
          ((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I := by
    rw [← Complex.natCast_log]
    push_cast
    ring
  rw [hexponent, Complex.exp_add]
  ring

theorem criticalPrefixPolynomial_eq_sum_bhpCriticalCoefficient
    {q X : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ) :
    criticalPrefixPolynomial q X chi t =
      ∑ n ∈ Finset.Icc 1 X, bhpCriticalLSeriesCoefficient chi t n := by
  unfold criticalPrefixPolynomial prefixSupport twistedFinitePolynomial
  apply Finset.sum_congr rfl
  intro n hn
  exact (bhpCriticalLSeriesCoefficient_eq_prefixTerm chi t
    (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)).symm

theorem summable_bhpCriticalCoefficient_mul_kernel
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X t c T : ℝ} (hX : 0 < X) (hc : 1 / 2 < c) :
    Summable fun n : ℕ =>
      bhpCriticalLSeriesCoefficient chi t n *
        PerronKernel.kernel (X / n) c T := by
  let F : ℕ → C(ℝ, ℂ) := fun n =>
    ContinuousMap.mk (bhpRightPerronTerm chi X t c n)
      (continuous_bhpRightPerronTerm chi hX (by linarith) n)
  have hsup : Summable fun n : ℕ =>
      ‖(F n).restrict (⟨uIcc (-T) T, isCompact_uIcc⟩ : Compacts ℝ)‖ := by
    simpa only [F] using
      summable_restricted_bhpRightPerronTerm chi hX hc (t := t) (T := T)
  have hint : Summable fun n : ℕ =>
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ∫ u in (-T)..T, bhpRightPerronTerm chi X t c n u := by
    have hi : Summable fun n : ℕ =>
        ∫ u in (-T)..T, F n u :=
      (intervalIntegral.hasSum_intervalIntegral_of_summable_norm hsup).summable
    exact (hi.mul_left (((2 * Real.pi : ℝ) : ℂ)⁻¹)).congr
      (fun n => by simp only [F, ContinuousMap.coe_mk])
  apply hint.congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [bhpRightPerronTerm, bhpCriticalLSeriesCoefficient]
  · simp_rw [bhpRightPerronTerm_eq_coefficient_mul_verticalIntegrand
      chi hX (by linarith) hn]
    rw [intervalIntegral.integral_const_mul, PerronKernel.kernel]
    ring

/-- Exact inside/outside decomposition of Titchmarsh's truncated Perron
error.  The right edge is still the literal infinite Dirichlet series. -/
theorem criticalPrefix_sub_vertical_eq_inside_sub_outside
    {q X : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {t c T : ℝ} (hX : 0 < (X : ℝ)) (hc : 1 / 2 < c) :
    criticalPrefixPolynomial q X chi t -
        bhpVerticalLineIntegral chi (X : ℝ) t c T =
      (∑ n ∈ Finset.Icc 1 X,
        bhpCriticalLSeriesCoefficient chi t n *
          (1 - PerronKernel.kernel ((X : ℝ) / n) c T)) -
      ∑' n : {n // n ∉ Finset.Icc 1 X},
        bhpCriticalLSeriesCoefficient chi t n *
          PerronKernel.kernel ((X : ℝ) / n) c T := by
  rw [criticalPrefixPolynomial_eq_sum_bhpCriticalCoefficient]
  rw [bhpVerticalLineIntegral_eq_tsum_kernels chi hX hc]
  let f : ℕ → ℂ := fun n =>
    bhpCriticalLSeriesCoefficient chi t n *
      PerronKernel.kernel ((X : ℝ) / n) c T
  have hf : Summable f := by
    simpa only [f] using
      summable_bhpCriticalCoefficient_mul_kernel chi hX hc (t := t) (T := T)
  rw [← hf.sum_add_tsum_subtype_compl (Finset.Icc 1 X)]
  dsimp only [f]
  rw [sub_add_eq_sub_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem norm_inside_nonendpoint_term_le
    {q X n : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ)
    {T x0 : ℝ} (hX : 2 ≤ X) (hn1 : 1 ≤ n) (hnX : n < X)
    (hT : 0 < T) (hXx : (X : ℝ) ≤ x0) :
    ‖bhpCriticalLSeriesCoefficient chi t n *
        (1 - PerronKernel.kernel ((X : ℝ) / n)
          ((1 / 2 : ℝ) + (Real.log x0)⁻¹) T)‖ ≤
      (Real.exp 1 * Real.sqrt (X : ℝ) / (Real.pi * T)) *
        (1 / (n : ℝ) + 1 / ((X : ℝ) - n)) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
  have hXpos : 0 < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hx0pos : 0 < x0 := hXpos.trans_le hXx
  have hx0one : 1 < x0 := by
    have : (1 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hX)
    exact this.trans_le hXx
  have hlog : 0 < Real.log x0 := Real.log_pos hx0one
  let delta : ℝ := (Real.log x0)⁻¹
  have hdelta : 0 < delta := inv_pos.mpr hlog
  have hc : 0 < (1 / 2 : ℝ) + delta := by positivity
  have hnXr : (n : ℝ) < X := by exact_mod_cast hnX
  have hypos : 0 < (X : ℝ) / (n : ℝ) := div_pos hXpos hnpos
  have hyone : 1 < (X : ℝ) / (n : ℝ) := (one_lt_div hnpos).2 hnXr
  have hk := SharpFinitePerronStep.norm_kernel_sub_one_le
    hyone hc hT
  have hflip :
      ‖1 - PerronKernel.kernel ((X : ℝ) / n)
          ((1 / 2 : ℝ) + delta) T‖ =
        ‖PerronKernel.kernel ((X : ℝ) / n)
          ((1 / 2 : ℝ) + delta) T - 1‖ := by
    rw [← norm_neg]
    congr 1
    ring
  have hcoeff := norm_bhpCriticalLSeriesCoefficient_le chi t hn0
  have hpowSplit :
      ((X : ℝ) / (n : ℝ)) ^ ((1 / 2 : ℝ) + delta) =
        Real.sqrt ((X : ℝ) / (n : ℝ)) *
          ((X : ℝ) / (n : ℝ)) ^ delta := by
    rw [Real.rpow_add hypos]
    congr 1
    simpa [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num] using
      (Real.sqrt_eq_rpow ((X : ℝ) / (n : ℝ))).symm
  have hratioX : (X : ℝ) / (n : ℝ) ≤ x0 := by
    rw [div_le_iff₀ hnpos]
    have hnOneR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    nlinarith
  have hdeltaPow :
      ((X : ℝ) / (n : ℝ)) ^ delta ≤ Real.exp 1 := by
    have hmono := Real.rpow_le_rpow hypos.le hratioX hdelta.le
    exact hmono.trans_eq (Real.rpow_inv_log hx0pos hx0one.ne')
  have hlogLower :
      ((X : ℝ) - (n : ℝ)) / (X : ℝ) ≤
        |Real.log ((X : ℝ) / (n : ℝ))| := by
    have hbase := PerronKernel.abs_log_div_ge_abs_sub_div_max hXpos hnpos
    rw [max_eq_left hnXr.le, abs_of_pos (sub_pos.mpr hnXr)] at hbase
    exact hbase
  have hdist : 0 < (X : ℝ) - (n : ℝ) := sub_pos.mpr hnXr
  have hlogAbs : 0 < |Real.log ((X : ℝ) / (n : ℝ))| :=
    abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hypos hyone.ne')
  have hsqrtScale :
      (1 / Real.sqrt (n : ℝ)) * Real.sqrt ((X : ℝ) / (n : ℝ)) =
        Real.sqrt (X : ℝ) / (n : ℝ) := by
    rw [Real.sqrt_div hXpos.le]
    have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
    field_simp [hsqrtn.ne']
    rw [Real.sq_sqrt hnpos.le]
  have hscalar :
      (1 / Real.sqrt (n : ℝ)) *
          (((X : ℝ) / (n : ℝ)) ^ ((1 / 2 : ℝ) + delta) /
            (Real.pi * T * |Real.log ((X : ℝ) / (n : ℝ))|)) ≤
        (Real.exp 1 * Real.sqrt (X : ℝ) / (Real.pi * T)) *
          (1 / (n : ℝ) + 1 / ((X : ℝ) - n)) := by
    rw [hpowSplit]
    have hlogInv :
        1 / |Real.log ((X : ℝ) / (n : ℝ))| ≤
          (X : ℝ) / ((X : ℝ) - (n : ℝ)) := by
      have h := one_div_le_one_div_of_le
        (div_pos hdist hXpos) hlogLower
      field_simp [hXpos.ne', hdist.ne'] at h ⊢
      exact h
    rw [show (1 / Real.sqrt (n : ℝ)) *
        (Real.sqrt ((X : ℝ) / (n : ℝ)) *
          ((X : ℝ) / (n : ℝ)) ^ delta /
            (Real.pi * T * |Real.log ((X : ℝ) / (n : ℝ))|)) =
        ((1 / Real.sqrt (n : ℝ)) *
          Real.sqrt ((X : ℝ) / (n : ℝ))) *
        (((X : ℝ) / (n : ℝ)) ^ delta) *
        (1 / |Real.log ((X : ℝ) / (n : ℝ))|) /
        (Real.pi * T) by ring]
    rw [hsqrtScale]
    have hpiT : 0 < Real.pi * T := mul_pos Real.pi_pos hT
    have hnonneg : 0 ≤ Real.sqrt (X : ℝ) / (n : ℝ) := by positivity
    calc
      (Real.sqrt (X : ℝ) / (n : ℝ)) *
          (((X : ℝ) / (n : ℝ)) ^ delta) *
          (1 / |Real.log ((X : ℝ) / (n : ℝ))|) / (Real.pi * T) ≤
        (Real.sqrt (X : ℝ) / (n : ℝ)) * Real.exp 1 *
          ((X : ℝ) / ((X : ℝ) - (n : ℝ))) / (Real.pi * T) := by
        gcongr
      _ = (Real.exp 1 * Real.sqrt (X : ℝ) / (Real.pi * T)) *
          (1 / (n : ℝ) + 1 / ((X : ℝ) - n)) := by
        field_simp [hnpos.ne', hdist.ne', hpiT.ne']
        ring
  rw [norm_mul, hflip]
  calc
    ‖bhpCriticalLSeriesCoefficient chi t n‖ *
        ‖PerronKernel.kernel ((X : ℝ) / n)
            ((1 / 2 : ℝ) + delta) T - 1‖ ≤
      (1 / Real.sqrt (n : ℝ)) *
        (((X : ℝ) / (n : ℝ)) ^ ((1 / 2 : ℝ) + delta) /
          (Real.pi * T * |Real.log ((X : ℝ) / (n : ℝ))|)) := by
      exact mul_le_mul hcoeff hk (norm_nonneg _)
        (by positivity)
    _ ≤ _ := hscalar

theorem sum_inside_reciprocal_pair_eq_two_harmonic
    {X : ℕ} (hX : 2 ≤ X) :
    (∑ n ∈ Finset.Icc 1 (X - 1),
      (1 / (n : ℝ) + 1 / ((X : ℝ) - n))) =
        2 * (((harmonic (X - 1) : ℚ) : ℝ)) := by
  rw [Finset.sum_add_distrib]
  rw [PaperEdgePerronRemainder.sum_Icc_one_div_eq_harmonic]
  have hreverse :=
    PaperEdgePerronRemainder.sum_Icc_reverse_one_div_eq_harmonic (X - 1)
  have hden : ∀ n ∈ Finset.Icc 1 (X - 1),
      (((X - 1 + 1 - n : ℕ) : ℝ)) = (X : ℝ) - (n : ℝ) := by
    intro n hn
    have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2.trans (by omega)
    rw [show X - 1 + 1 = X by omega, Nat.cast_sub hnX]
  have heq :
      (∑ n ∈ Finset.Icc 1 (X - 1), 1 / ((X : ℝ) - n)) =
        (((harmonic (X - 1) : ℚ) : ℝ)) := by
    rw [← hreverse]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hden n hn]
  rw [heq]
  ring

theorem norm_inside_error_sum_le
    {q X : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ)
    {T x0 : ℝ} (hX : 2 ≤ X) (hT : 0 < T)
    (hXx : (X : ℝ) ≤ x0) :
    ‖∑ n ∈ Finset.Icc 1 X,
        bhpCriticalLSeriesCoefficient chi t n *
          (1 - PerronKernel.kernel ((X : ℝ) / n)
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) T)‖ ≤
      (Real.exp 1 * Real.sqrt (X : ℝ) / (Real.pi * T)) *
          (2 * (((harmonic (X - 1) : ℚ) : ℝ))) +
        1 / Real.sqrt (X : ℝ) := by
  let F : ℕ → ℂ := fun n =>
    bhpCriticalLSeriesCoefficient chi t n *
      (1 - PerronKernel.kernel ((X : ℝ) / n)
        ((1 / 2 : ℝ) + (Real.log x0)⁻¹) T)
  have hsplit : (∑ n ∈ Finset.Icc 1 X, F n) =
      (∑ n ∈ Finset.Icc 1 (X - 1), F n) + F X := by
    rw [show X = (X - 1) + 1 by omega]
    exact Finset.sum_Icc_succ_top (by omega) F
  rw [hsplit]
  have hfirst :
      ‖∑ n ∈ Finset.Icc 1 (X - 1), F n‖ ≤
        (Real.exp 1 * Real.sqrt (X : ℝ) / (Real.pi * T)) *
          (2 * (((harmonic (X - 1) : ℚ) : ℝ))) := by
    calc
      ‖∑ n ∈ Finset.Icc 1 (X - 1), F n‖ ≤
          ∑ n ∈ Finset.Icc 1 (X - 1), ‖F n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 (X - 1),
          (Real.exp 1 * Real.sqrt (X : ℝ) / (Real.pi * T)) *
            (1 / (n : ℝ) + 1 / ((X : ℝ) - n)) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnlt : n < X := by
          have htop : n ≤ X - 1 := (Finset.mem_Icc.mp hn).2
          omega
        exact norm_inside_nonendpoint_term_le chi t hX
          (Finset.mem_Icc.mp hn).1 hnlt hT hXx
      _ = (Real.exp 1 * Real.sqrt (X : ℝ) / (Real.pi * T)) *
          (2 * (((harmonic (X - 1) : ℚ) : ℝ))) := by
        rw [← Finset.mul_sum, sum_inside_reciprocal_pair_eq_two_harmonic hX]
  have hX0 : X ≠ 0 := by omega
  have hcoeff := norm_bhpCriticalLSeriesCoefficient_le chi t hX0
  have hcenter :=
    MAPMRTCorollary25TransitionBand.norm_kernel_one_sub_step_le_one
      (y := (2 : ℝ))
      (c := (1 / 2 : ℝ) + (Real.log x0)⁻¹) (T := T)
      (by
        have hXpos : 0 < (X : ℝ) := by positivity
        have hx0one : 1 < x0 := (by
          have : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
          exact this.trans_le hXx)
        have hinv : 0 < (Real.log x0)⁻¹ := inv_pos.mpr (Real.log_pos hx0one)
        linarith)
      hT.le
  have hendpoint : ‖F X‖ ≤ 1 / Real.sqrt (X : ℝ) := by
    dsimp only [F]
    have hXreal0 : (X : ℝ) ≠ 0 := by positivity
    rw [show (X : ℝ) / (X : ℝ) = 1 by field_simp]
    rw [norm_mul]
    have hflip :
        ‖1 - PerronKernel.kernel 1
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) T‖ =
          ‖PerronKernel.kernel 1
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) T - 1‖ := by
      rw [← norm_neg]
      congr 1
      ring
    rw [hflip]
    have hcenter' :
        ‖PerronKernel.kernel 1
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) T - 1‖ ≤ 1 := by
      simpa using hcenter
    calc
      ‖bhpCriticalLSeriesCoefficient chi t X‖ *
          ‖PerronKernel.kernel 1
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) T - 1‖ ≤
        (1 / Real.sqrt (X : ℝ)) * 1 :=
          mul_le_mul hcoeff hcenter' (norm_nonneg _) (by positivity)
      _ = 1 / Real.sqrt (X : ℝ) := by ring
  calc
    ‖∑ n ∈ Finset.Icc 1 (X - 1), F n + F X‖ ≤
        ‖∑ n ∈ Finset.Icc 1 (X - 1), F n‖ + ‖F X‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hfirst hendpoint

theorem norm_outside_near_term_le
    {q X n : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ)
    {T x0 : ℝ} (hX : 2 ≤ X) (hnX : X < n) (hn2X : n ≤ 2 * X)
    (hT : 0 < T) (hXx : (X : ℝ) ≤ x0) :
    ‖bhpCriticalLSeriesCoefficient chi t n *
        PerronKernel.kernel ((X : ℝ) / n)
          ((1 / 2 : ℝ) + (Real.log x0)⁻¹) T‖ ≤
      Real.sqrt (X : ℝ) / (Real.pi * T) *
        (1 / ((n : ℝ) - X)) := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hXpos : 0 < (X : ℝ) := by positivity
  have hx0one : 1 < x0 := by
    have : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
    exact this.trans_le hXx
  let delta : ℝ := (Real.log x0)⁻¹
  have hdelta : 0 < delta := inv_pos.mpr (Real.log_pos hx0one)
  have hc : 0 < (1 / 2 : ℝ) + delta := by positivity
  have hnXr : (X : ℝ) < n := by exact_mod_cast hnX
  have hypos : 0 < (X : ℝ) / (n : ℝ) := div_pos hXpos hnpos
  have hylt : (X : ℝ) / (n : ℝ) < 1 := (div_lt_one hnpos).2 hnXr
  have hk := SharpFinitePerronStep.norm_kernel_le_of_lt_one
    hypos hylt hc hT
  have hcoeff := norm_bhpCriticalLSeriesCoefficient_le chi t hn0
  have hpowSplit :
      ((X : ℝ) / (n : ℝ)) ^ ((1 / 2 : ℝ) + delta) =
        Real.sqrt ((X : ℝ) / (n : ℝ)) *
          ((X : ℝ) / (n : ℝ)) ^ delta := by
    rw [Real.rpow_add hypos]
    congr 1
    simpa [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num] using
      (Real.sqrt_eq_rpow ((X : ℝ) / (n : ℝ))).symm
  have hdeltaPow : ((X : ℝ) / (n : ℝ)) ^ delta ≤ 1 :=
    Real.rpow_le_one hypos.le hylt.le hdelta.le
  have hlogLower :
      ((n : ℝ) - (X : ℝ)) / (n : ℝ) ≤
        |Real.log ((X : ℝ) / (n : ℝ))| := by
    have hbase := PerronKernel.abs_log_div_ge_abs_sub_div_max hXpos hnpos
    rw [max_eq_right hnXr.le, abs_of_neg (sub_neg.mpr hnXr)] at hbase
    have hnum : -((X : ℝ) - (n : ℝ)) = (n : ℝ) - (X : ℝ) := by ring
    simpa [hnum] using hbase
  have hdist : 0 < (n : ℝ) - (X : ℝ) := sub_pos.mpr hnXr
  have hsqrtScale :
      (1 / Real.sqrt (n : ℝ)) * Real.sqrt ((X : ℝ) / (n : ℝ)) =
        Real.sqrt (X : ℝ) / (n : ℝ) := by
    rw [Real.sqrt_div hXpos.le]
    have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
    field_simp [hsqrtn.ne']
    rw [Real.sq_sqrt hnpos.le]
  rw [norm_mul]
  calc
    ‖bhpCriticalLSeriesCoefficient chi t n‖ *
        ‖PerronKernel.kernel ((X : ℝ) / n)
          ((1 / 2 : ℝ) + delta) T‖ ≤
      (1 / Real.sqrt (n : ℝ)) *
        (((X : ℝ) / (n : ℝ)) ^ ((1 / 2 : ℝ) + delta) /
          (Real.pi * T * |Real.log ((X : ℝ) / (n : ℝ))|)) :=
      mul_le_mul hcoeff hk (norm_nonneg _) (by positivity)
    _ = (Real.sqrt (X : ℝ) / (n : ℝ)) *
        (((X : ℝ) / (n : ℝ)) ^ delta) *
        (1 / |Real.log ((X : ℝ) / (n : ℝ))|) /
        (Real.pi * T) := by
      rw [hpowSplit]
      calc
        (1 / Real.sqrt (n : ℝ)) *
              (Real.sqrt ((X : ℝ) / (n : ℝ)) *
                ((X : ℝ) / (n : ℝ)) ^ delta /
                (Real.pi * T * |Real.log ((X : ℝ) / (n : ℝ))|)) =
            ((1 / Real.sqrt (n : ℝ)) *
                Real.sqrt ((X : ℝ) / (n : ℝ))) *
              ((X : ℝ) / (n : ℝ)) ^ delta *
              (1 / |Real.log ((X : ℝ) / (n : ℝ))|) /
              (Real.pi * T) := by ring
        _ = _ := by rw [hsqrtScale]
    _ ≤ (Real.sqrt (X : ℝ) / (n : ℝ)) * 1 *
        ((n : ℝ) / ((n : ℝ) - (X : ℝ))) /
        (Real.pi * T) := by
      have hloginv :
          1 / |Real.log ((X : ℝ) / (n : ℝ))| ≤
            (n : ℝ) / ((n : ℝ) - (X : ℝ)) := by
        have h := one_div_le_one_div_of_le
          (div_pos hdist hnpos) hlogLower
        field_simp [hnpos.ne', hdist.ne'] at h ⊢
        exact h
      gcongr
    _ = Real.sqrt (X : ℝ) / (Real.pi * T) *
        (1 / ((n : ℝ) - X)) := by
      field_simp [hnpos.ne', hdist.ne', hT.ne', Real.pi_ne_zero]

/-- Reindexing the finite collar immediately to the right of the integer
endpoint gives exactly an ordinary harmonic number. -/
theorem outside_near_reciprocal_sum_eq_harmonic (X : ℕ) :
    (∑ n ∈ Finset.Icc (X + 1) (2 * X),
        1 / ((n : ℝ) - (X : ℝ))) =
      ((harmonic X : ℚ) : ℝ) := by
  have hreindex :
      (∑ n ∈ Finset.Icc (X + 1) (2 * X),
          1 / ((n : ℝ) - (X : ℝ))) =
        ∑ k ∈ Finset.Icc 1 X, 1 / (k : ℝ) := by
    apply Finset.sum_bij (fun n _ => n - X)
    · intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_Icc] at ha hb
      omega
    · intro k hk
      refine ⟨X + k, ?_, ?_⟩
      · simp only [Finset.mem_Icc] at hk ⊢
        omega
      · omega
    · intro n hn
      have hXn : X ≤ n := by
        simp only [Finset.mem_Icc] at hn
        omega
      rw [Nat.cast_sub hXn]
  rw [hreindex]
  rw [harmonic_eq_sum_Icc]
  norm_num

/-- Away from the endpoint collar, the positive Perron offset restores a
summable `n^(-1-delta)` tail.  This is the quantitative fact lost if the
`/w` kernel is dropped before moving the contour. -/
theorem norm_outside_far_term_le
    {q X n : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ)
    {T x0 : ℝ} (hX : 2 ≤ X) (hn2X : 2 * X < n)
    (hT : 0 < T) (hXx : (X : ℝ) ≤ x0) :
    ‖bhpCriticalLSeriesCoefficient chi t n *
        PerronKernel.kernel ((X : ℝ) / n)
          ((1 / 2 : ℝ) + (Real.log x0)⁻¹) T‖ ≤
      (2 * Real.exp 1 * Real.sqrt (X : ℝ) / (Real.pi * T)) *
        (n : ℝ) ^ (-(1 + (Real.log x0)⁻¹)) := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hXpos : 0 < (X : ℝ) := by positivity
  have hx0one : 1 < x0 := by
    have : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
    exact this.trans_le hXx
  let delta : ℝ := (Real.log x0)⁻¹
  have hdelta : 0 < delta := inv_pos.mpr (Real.log_pos hx0one)
  have hc : 0 < (1 / 2 : ℝ) + delta := by positivity
  have hnX : X < n := by omega
  have hnXr : (X : ℝ) < n := by exact_mod_cast hnX
  have hypos : 0 < (X : ℝ) / (n : ℝ) := div_pos hXpos hnpos
  have hylt : (X : ℝ) / (n : ℝ) < 1 := (div_lt_one hnpos).2 hnXr
  have hk := SharpFinitePerronStep.norm_kernel_le_of_lt_one
    hypos hylt hc hT
  have hcoeff := norm_bhpCriticalLSeriesCoefficient_le chi t hn0
  have hpowSplit :
      ((X : ℝ) / (n : ℝ)) ^ ((1 / 2 : ℝ) + delta) =
        Real.sqrt ((X : ℝ) / (n : ℝ)) *
          ((X : ℝ) / (n : ℝ)) ^ delta := by
    rw [Real.rpow_add hypos]
    congr 1
    simpa [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num] using
      (Real.sqrt_eq_rpow ((X : ℝ) / (n : ℝ))).symm
  have hXdelta : (X : ℝ) ^ delta ≤ Real.exp 1 := by
    have hmono := Real.rpow_le_rpow hXpos.le hXx hdelta.le
    exact hmono.trans_eq (Real.rpow_inv_log
      (hXpos.trans_le hXx) hx0one.ne')
  have hratioDelta :
      ((X : ℝ) / (n : ℝ)) ^ delta ≤
        Real.exp 1 * (n : ℝ) ^ (-delta) := by
    rw [Real.div_rpow hXpos.le hnpos.le, Real.rpow_neg hnpos.le]
    exact mul_le_mul_of_nonneg_right hXdelta (inv_nonneg.mpr
      (Real.rpow_nonneg hnpos.le delta))
  have hlogLower :
      ((n : ℝ) - (X : ℝ)) / (n : ℝ) ≤
        |Real.log ((X : ℝ) / (n : ℝ))| := by
    have hbase := PerronKernel.abs_log_div_ge_abs_sub_div_max hXpos hnpos
    rw [max_eq_right hnXr.le, abs_of_neg (sub_neg.mpr hnXr)] at hbase
    have hnum : -((X : ℝ) - (n : ℝ)) = (n : ℝ) - (X : ℝ) := by ring
    simpa [hnum] using hbase
  have hhalf : (1 / 2 : ℝ) ≤
      ((n : ℝ) - (X : ℝ)) / (n : ℝ) := by
    have hn2Xr : (2 : ℝ) * X < n := by exact_mod_cast hn2X
    rw [le_div_iff₀ hnpos]
    linarith
  have hlogHalf : (1 / 2 : ℝ) ≤
      |Real.log ((X : ℝ) / (n : ℝ))| := hhalf.trans hlogLower
  have hlogInv :
      1 / |Real.log ((X : ℝ) / (n : ℝ))| ≤ 2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hlogHalf
    norm_num at h ⊢
    exact h
  have hsqrtScale :
      (1 / Real.sqrt (n : ℝ)) * Real.sqrt ((X : ℝ) / (n : ℝ)) =
        Real.sqrt (X : ℝ) / (n : ℝ) := by
    rw [Real.sqrt_div hXpos.le]
    have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
    field_simp [hsqrtn.ne']
    rw [Real.sq_sqrt hnpos.le]
  rw [norm_mul]
  calc
    ‖bhpCriticalLSeriesCoefficient chi t n‖ *
        ‖PerronKernel.kernel ((X : ℝ) / n)
          ((1 / 2 : ℝ) + delta) T‖ ≤
      (1 / Real.sqrt (n : ℝ)) *
        (((X : ℝ) / (n : ℝ)) ^ ((1 / 2 : ℝ) + delta) /
          (Real.pi * T * |Real.log ((X : ℝ) / (n : ℝ))|)) :=
      mul_le_mul hcoeff hk (norm_nonneg _) (by positivity)
    _ = (Real.sqrt (X : ℝ) / (n : ℝ)) *
        (((X : ℝ) / (n : ℝ)) ^ delta) *
        (1 / |Real.log ((X : ℝ) / (n : ℝ))|) /
        (Real.pi * T) := by
      rw [hpowSplit]
      rw [show (1 / Real.sqrt (n : ℝ)) *
          (Real.sqrt ((X : ℝ) / (n : ℝ)) *
            ((X : ℝ) / (n : ℝ)) ^ delta /
            (Real.pi * T * |Real.log ((X : ℝ) / (n : ℝ))|)) =
          ((1 / Real.sqrt (n : ℝ)) *
            Real.sqrt ((X : ℝ) / (n : ℝ))) *
            ((X : ℝ) / (n : ℝ)) ^ delta *
            (1 / |Real.log ((X : ℝ) / (n : ℝ))|) /
            (Real.pi * T) by ring]
      rw [hsqrtScale]
    _ ≤ (Real.sqrt (X : ℝ) / (n : ℝ)) *
        (Real.exp 1 * (n : ℝ) ^ (-delta)) * 2 /
        (Real.pi * T) := by gcongr
    _ = (2 * Real.exp 1 * Real.sqrt (X : ℝ) / (Real.pi * T)) *
        (n : ℝ) ^ (-(1 + delta)) := by
      rw [show -(1 + delta) = -1 + -delta by ring,
        Real.rpow_add hnpos, Real.rpow_neg_one]
      ring

/-- The complete right-of-endpoint tail: one finite harmonic collar plus a
genuinely summable offset tail.  Every logarithm displayed here comes from an
explicit summation or from the chosen Perron offset. -/
theorem norm_outside_error_tsum_le
    {q X : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (t : ℝ)
    {T x0 : ℝ} (hX : 2 ≤ X) (hT : 0 < T)
    (hXx : (X : ℝ) ≤ x0) :
    ‖∑' n : {n // n ∉ Finset.Icc 1 X},
        bhpCriticalLSeriesCoefficient chi t n *
          PerronKernel.kernel ((X : ℝ) / n)
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) T‖ ≤
      (Real.sqrt (X : ℝ) / (Real.pi * T)) *
          ((harmonic X : ℚ) : ℝ) +
        (2 * Real.exp 1 * Real.sqrt (X : ℝ) / (Real.pi * T)) *
          (1 + Real.log x0) := by
  have hXpos : 0 < (X : ℝ) := by positivity
  have hx0one : 1 < x0 := by
    have : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
    exact this.trans_le hXx
  have hlogpos : 0 < Real.log x0 := Real.log_pos hx0one
  let delta : ℝ := (Real.log x0)⁻¹
  let c : ℝ := (1 / 2 : ℝ) + delta
  let f : ℕ → ℂ := fun n =>
    bhpCriticalLSeriesCoefficient chi t n *
      PerronKernel.kernel ((X : ℝ) / n) c T
  let outside : Set ℕ := {n | n ∉ Finset.Icc 1 X}
  let Knear : ℝ := Real.sqrt (X : ℝ) / (Real.pi * T)
  let Kfar : ℝ := 2 * Real.exp 1 * Real.sqrt (X : ℝ) / (Real.pi * T)
  let near : ℕ → ℝ := fun n =>
    if n ∈ Finset.Icc (X + 1) (2 * X) then
      Knear * (1 / ((n : ℝ) - (X : ℝ))) else 0
  let far : ℕ → ℝ := fun n =>
    if 2 * X < n then Kfar * (n : ℝ) ^ (-(1 + delta)) else 0
  have hdelta : 0 < delta := inv_pos.mpr hlogpos
  have hc : 1 / 2 < c := by dsimp only [c]; linarith
  have hKnear : 0 ≤ Knear := by
    dsimp only [Knear]
    positivity
  have hKfar : 0 ≤ Kfar := by
    dsimp only [Kfar]
    positivity
  have hf : Summable f := by
    simpa only [f, c, delta] using
      summable_bhpCriticalCoefficient_mul_kernel chi hXpos hc (t := t) (T := T)
  have hfi : Summable (outside.indicator f) := hf.indicator outside
  have hnearSummable : Summable near := by
    apply summable_of_ne_finset_zero (s := Finset.Icc (X + 1) (2 * X))
    intro n hn
    dsimp only [near]
    rw [if_neg hn]
  have hbaseSummable : Summable fun n : ℕ =>
      (n : ℝ) ^ (-(1 + delta)) := by
    exact Real.summable_nat_rpow.mpr (by linarith)
  have hfarPoint : ∀ n : ℕ,
      far n ≤ Kfar * (n : ℝ) ^ (-(1 + delta)) := by
    intro n
    dsimp only [far]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg hKfar (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hfarSummable : Summable far := by
    apply Summable.of_nonneg_of_le
      (fun n => by
        dsimp only [far]
        split_ifs
        · exact mul_nonneg hKfar (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        · exact le_rfl)
      hfarPoint
    exact hbaseSummable.mul_left Kfar
  have hpoint : ∀ n : ℕ,
      ‖outside.indicator f n‖ ≤ near n + far n := by
    intro n
    by_cases hnOut : n ∈ outside
    · rw [Set.indicator_of_mem hnOut]
      have hnIcc : n ∉ Finset.Icc 1 X := hnOut
      by_cases hn0 : n = 0
      · subst n
        simp [f, near, far, bhpCriticalLSeriesCoefficient]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hnX : X < n := by
          by_contra hnot
          apply hnIcc
          exact Finset.mem_Icc.mpr ⟨hnpos, Nat.le_of_not_gt hnot⟩
        by_cases hn2X : n ≤ 2 * X
        · have hnNear : n ∈ Finset.Icc (X + 1) (2 * X) := by
            exact Finset.mem_Icc.mpr ⟨by omega, hn2X⟩
          have hterm := norm_outside_near_term_le chi t hX hnX hn2X hT hXx
          simpa only [f, c, delta, near, far, if_pos hnNear,
            if_neg (show ¬ 2 * X < n by omega), add_zero] using hterm
        · have hnFar : 2 * X < n := by omega
          have hnNotNear : n ∉ Finset.Icc (X + 1) (2 * X) := by
            simp only [Finset.mem_Icc, not_and]
            exact fun _ => by omega
          have hterm := norm_outside_far_term_le chi t hX hnFar hT hXx
          simpa only [f, c, delta, near, far, if_neg hnNotNear,
            if_pos hnFar, zero_add] using hterm
    · simp only [Set.indicator, if_neg hnOut, Pi.zero_apply, norm_zero]
      have hnear0 : near n = 0 := by
        dsimp only [near]
        split_ifs with hn
        · exfalso
          apply hnOut
          simp only [outside]
          intro hnIcc
          have hleX := (Finset.mem_Icc.mp hnIcc).2
          have hgtX : X < n := by
            have := (Finset.mem_Icc.mp hn).1
            omega
          omega
        · rfl
      have hfar0 : far n = 0 := by
        dsimp only [far]
        split_ifs with hn
        · exfalso
          apply hnOut
          simp only [outside]
          intro hnIcc
          have hleX := (Finset.mem_Icc.mp hnIcc).2
          omega
        · rfl
      simp [hnear0, hfar0]
  have hnearTsum : (∑' n, near n) =
      Knear * ((harmonic X : ℚ) : ℝ) := by
    rw [tsum_eq_sum (s := Finset.Icc (X + 1) (2 * X))]
    · calc
        (∑ x ∈ Finset.Icc (X + 1) (2 * X), near x) =
            ∑ x ∈ Finset.Icc (X + 1) (2 * X),
              Knear * (1 / ((x : ℝ) - (X : ℝ))) := by
          apply Finset.sum_congr rfl
          intro n hn
          dsimp only [near]
          rw [if_pos hn]
        _ = Knear * ∑ x ∈ Finset.Icc (X + 1) (2 * X),
              1 / ((x : ℝ) - (X : ℝ)) := by rw [Finset.mul_sum]
        _ = Knear * ((harmonic X : ℚ) : ℝ) := by
          rw [outside_near_reciprocal_sum_eq_harmonic]
    · intro n hn
      dsimp only [near]
      rw [if_neg hn]
  have hfarTsum : (∑' n, far n) ≤ Kfar * (1 + Real.log x0) := by
    have hsum := hfarSummable.tsum_le_tsum hfarPoint
      (hbaseSummable.mul_left Kfar)
    rw [tsum_mul_left] at hsum
    have hp := MAPMertensAnalyticLeaf.pSeries_le_one_add_inv_sub_one
      (show 1 < 1 + delta by linarith)
    have hcollapse : 1 + ((1 + delta) - 1)⁻¹ =
        1 + Real.log x0 := by
      dsimp only [delta]
      rw [show (1 + (Real.log x0)⁻¹) - 1 =
        (Real.log x0)⁻¹ by ring, inv_inv]
    calc
      (∑' n, far n) ≤ Kfar * ∑' n : ℕ,
          (n : ℝ) ^ (-(1 + delta)) := hsum
      _ ≤ Kfar * (1 + ((1 + delta) - 1)⁻¹) :=
        mul_le_mul_of_nonneg_left hp hKfar
      _ = Kfar * (1 + Real.log x0) := by rw [hcollapse]
  change ‖∑' n : outside, f n‖ ≤ _
  rw [tsum_subtype outside f]
  have hnorm : Summable fun n => ‖outside.indicator f n‖ := hfi.norm
  calc
    ‖∑' n : ℕ, outside.indicator f n‖ ≤
        ∑' n : ℕ, ‖outside.indicator f n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, (near n + far n) :=
      hnorm.tsum_le_tsum hpoint (hnearSummable.add hfarSummable)
    _ = (∑' n, near n) + ∑' n, far n :=
      (hnearSummable.tsum_add hfarSummable)
    _ ≤ Knear * ((harmonic X : ℚ) : ℝ) +
        Kfar * (1 + Real.log x0) := by
      rw [hnearTsum]
      exact add_le_add (le_refl _) hfarTsum
    _ = _ := rfl

/-- A premise-free proof of the Titchmarsh 3.19 specialization consumed by
BHP.  The constant `50` is deliberately coarse; the proof above retains the
sharper finite collar and offset-tail ledger. -/
theorem bhpTheorem319TruncatedPerronSource_proved :
    MAPBHPRademacherTitchmarshSources.BHPTheorem319TruncatedPerronSource := by
  refine ⟨50, by norm_num, ?_⟩
  intro q X _ chi t T x0 hX hT _hq hXx _hTx
  have hXpos : 0 < (X : ℝ) := by positivity
  have hTpos : 0 < T := by linarith
  have hx0two : (2 : ℝ) ≤ x0 := by
    exact (by exact_mod_cast hX : (2 : ℝ) ≤ X).trans hXx
  have hx0one : 1 < x0 := lt_of_lt_of_le (by norm_num) hx0two
  have hlogpos : 0 < Real.log x0 := Real.log_pos hx0one
  have hlog2x : Real.log 2 ≤ Real.log x0 := by
    exact Real.strictMonoOn_log.monotoneOn (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show x0 ∈ Set.Ioi 0 by exact hx0one.trans' (by norm_num)) hx0two
  have hhalfLog : (1 / 2 : ℝ) ≤ Real.log x0 := by
    have hhalfTwo : (1 / 2 : ℝ) < Real.log 2 :=
      (show (1 / 2 : ℝ) < 0.6931471803 by norm_num).trans
        Real.log_two_gt_d9
    exact hhalfTwo.le.trans hlog2x
  have honeLog : (1 : ℝ) ≤ 2 * Real.log x0 := by linarith
  have hXm1pos : 0 < ((X - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < X - 1 by omega)
  have hXm1x0 : ((X - 1 : ℕ) : ℝ) ≤ x0 := by
    have : X - 1 ≤ X := Nat.sub_le X 1
    exact (by exact_mod_cast this : ((X - 1 : ℕ) : ℝ) ≤ X).trans hXx
  have hlogXm1 : Real.log ((X - 1 : ℕ) : ℝ) ≤ Real.log x0 :=
    Real.strictMonoOn_log.monotoneOn hXm1pos
      (show x0 ∈ Set.Ioi 0 by exact hx0one.trans' (by norm_num)) hXm1x0
  have hlogX : Real.log (X : ℝ) ≤ Real.log x0 :=
    Real.strictMonoOn_log.monotoneOn hXpos
      (show x0 ∈ Set.Ioi 0 by exact hx0one.trans' (by norm_num)) hXx
  have hHarmXm1 : (((harmonic (X - 1) : ℚ) : ℝ)) ≤
      3 * Real.log x0 := by
    have h := harmonic_le_one_add_log (X - 1)
    linarith
  have hHarmX : (((harmonic X : ℚ) : ℝ)) ≤
      3 * Real.log x0 := by
    have h := harmonic_le_one_add_log X
    linarith
  have hHarmXm10 : 0 ≤ (((harmonic (X - 1) : ℚ) : ℝ)) := by
    exact_mod_cast (harmonic_pos (show X - 1 ≠ 0 by omega)).le
  have hHarmX0 : 0 ≤ (((harmonic X : ℚ) : ℝ)) := by
    exact_mod_cast (harmonic_pos (show X ≠ 0 by omega)).le
  have hExp : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hA0 : 0 ≤ Real.sqrt (X : ℝ) / (Real.pi * T) := by positivity
  have hAcompare :
      Real.sqrt (X : ℝ) / (Real.pi * T) ≤
        Real.sqrt (X : ℝ) / T := by
    apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hTpos
    have hpi : (1 : ℝ) ≤ Real.pi := Real.pi_gt_three.le.trans' (by norm_num)
    nlinarith
  have hbracket :
      Real.exp 1 * 2 * (((harmonic (X - 1) : ℚ) : ℝ)) +
          (((harmonic X : ℚ) : ℝ)) +
          2 * Real.exp 1 * (1 + Real.log x0) ≤
        39 * Real.log x0 := by
    calc
      Real.exp 1 * 2 * (((harmonic (X - 1) : ℚ) : ℝ)) +
          (((harmonic X : ℚ) : ℝ)) +
          2 * Real.exp 1 * (1 + Real.log x0) ≤
        3 * 2 * (3 * Real.log x0) +
          3 * Real.log x0 + 2 * 3 * (3 * Real.log x0) := by
            gcongr
            linarith
      _ = 39 * Real.log x0 := by ring
  have hinside := norm_inside_error_sum_le chi t hX hTpos hXx
  have houtside := norm_outside_error_tsum_le chi t hX hTpos hXx
  have hdecomp := criticalPrefix_sub_vertical_eq_inside_sub_outside
    chi hXpos (show 1 / 2 < (1 / 2 : ℝ) + (Real.log x0)⁻¹ by
      have : 0 < (Real.log x0)⁻¹ := inv_pos.mpr hlogpos
      linarith) (t := t) (T := T)
  rw [hdecomp]
  calc
    ‖(∑ n ∈ Finset.Icc 1 X,
          bhpCriticalLSeriesCoefficient chi t n *
            (1 - PerronKernel.kernel ((X : ℝ) / n)
              ((1 / 2 : ℝ) + (Real.log x0)⁻¹) T)) -
        ∑' n : {n // n ∉ Finset.Icc 1 X},
          bhpCriticalLSeriesCoefficient chi t n *
            PerronKernel.kernel ((X : ℝ) / n)
              ((1 / 2 : ℝ) + (Real.log x0)⁻¹) T‖ ≤
      ‖∑ n ∈ Finset.Icc 1 X,
          bhpCriticalLSeriesCoefficient chi t n *
            (1 - PerronKernel.kernel ((X : ℝ) / n)
              ((1 / 2 : ℝ) + (Real.log x0)⁻¹) T)‖ +
        ‖∑' n : {n // n ∉ Finset.Icc 1 X},
          bhpCriticalLSeriesCoefficient chi t n *
            PerronKernel.kernel ((X : ℝ) / n)
              ((1 / 2 : ℝ) + (Real.log x0)⁻¹) T‖ := norm_sub_le _ _
    _ ≤
      (Real.exp 1 * Real.sqrt (X : ℝ) / (Real.pi * T)) *
          (2 * ((harmonic (X - 1) : ℚ) : ℝ)) +
          1 / Real.sqrt (X : ℝ) +
        ((Real.sqrt (X : ℝ) / (Real.pi * T)) *
            ((harmonic X : ℚ) : ℝ) +
          (2 * Real.exp 1 * Real.sqrt (X : ℝ) / (Real.pi * T)) *
            (1 + Real.log x0)) := add_le_add hinside houtside
    _ = (Real.sqrt (X : ℝ) / (Real.pi * T)) *
          (Real.exp 1 * 2 * (((harmonic (X - 1) : ℚ) : ℝ)) +
            (((harmonic X : ℚ) : ℝ)) +
            2 * Real.exp 1 * (1 + Real.log x0)) +
          1 / Real.sqrt (X : ℝ) := by ring
    _ ≤ (Real.sqrt (X : ℝ) / (Real.pi * T)) *
          (39 * Real.log x0) + 1 / Real.sqrt (X : ℝ) := by
      gcongr
    _ ≤ 39 * (Real.log x0 * Real.sqrt (X : ℝ) / T) +
          1 / Real.sqrt (X : ℝ) := by
      have hscale : 0 ≤ (39 : ℝ) * Real.log x0 :=
        mul_nonneg (by norm_num) hlogpos.le
      have hm := mul_le_mul_of_nonneg_left hAcompare
        hscale
      have hm' :
          (Real.sqrt (X : ℝ) / (Real.pi * T)) *
              (39 * Real.log x0) ≤
            39 * (Real.log x0 * Real.sqrt (X : ℝ) / T) := by
        convert hm using 1 <;> ring
      exact add_le_add hm' (le_refl _)
    _ ≤ 50 *
        (Real.log x0 * Real.sqrt (X : ℝ) / T +
          1 / Real.sqrt (X : ℝ)) := by
      have hmain : 0 ≤ Real.log x0 * Real.sqrt (X : ℝ) / T := by positivity
      have hend : 0 ≤ 1 / Real.sqrt (X : ℝ) := by positivity
      nlinarith

end
end MAPBHPTitchmarshTheorem319Proof

#print axioms MAPBHPTitchmarshTheorem319Proof.norm_bhpCriticalLSeriesCoefficient_le
