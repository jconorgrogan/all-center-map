import PrimitiveLogDerivativeRemainderUnconditional
import PrincipalZetaFullStrip
import PrincipalZetaTransport

/-!
# The conductor-one half of Koukoulopoulos Lemma 11.4(b)

The nonprincipal half is `publishedUniformPrimitiveLogDerivativeRemainderBound`.
This file repeats the same finite Blaschke argument for the regularized zeta
function.  Keeping the principal pole inside the regularization is essential
for the later 3-4-1 argument in Theorem 12.3.
-/

namespace MAPPrincipalLogDerivativeRemainderUnconditional

open Complex Set Metric DirichletZeros MAPLocalZeroWindow
open WideDiskLFunctionGrowth WideDiskBlaschkeAssembly
open WideDiskBlaschkeGrowth WideDiskLocalLogDerivative
open FiniteBlaschkeAlgebra
open MAPZeroFreeSiegelSpine
open MAPPrimitiveLogDerivativeRemainderUnconditional
open scoped BigOperators

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "χ₁" => (1 : DirichletCharacter ℂ 1)

/-- Radius-three polynomial growth for the regularized zeta function. -/
theorem norm_principalRegularized_wideCircle_le
    {t : ℝ} {z : ℂ} (hz : z ∈ Metric.sphere (wideCenter t) wideRadius) :
    ‖regularizedLFunction χ₁ z‖ ≤
      74649600 * (arithmeticScale 1 t) ^ 6 := by
  have hcoord := wideCircle_coordinates hz
  have hscale : arithmeticScale 1 t = |t| + 2 := by
    simp [arithmeticScale]
  rw [MAPPrincipalZetaTransport.regularized_principal_eq]
  by_cases hzright : 2 ≤ z.re
  · have hz1 : z ≠ 1 := by
      intro heq
      have hre := congrArg Complex.re heq
      norm_num at hre
      linarith
    have hL : ‖riemannZeta z‖ < 3 := by
      rw [← DirichletCharacter.LFunction_modOne_eq]
      exact MAPPrimitiveLFixedStrip.norm_LFunction_lt_three_of_two_le_re χ₁ hzright
    have hsub : ‖z - 1‖ ≤ 4 * (|t| + 2) := by
      calc
        ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ = |z.re - 1| + |z.im| := by simp
        _ ≤ 4 + (|t| + 3) := by
          have hre : |z.re - 1| ≤ 4 := by
            rw [abs_of_nonneg (by linarith)]
            linarith [hcoord.2.1]
          linarith [hcoord.2.2]
        _ ≤ 4 * (|t| + 2) := by nlinarith [abs_nonneg t]
    rw [MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hz1,
      norm_mul, hscale]
    have hS : 2 ≤ |t| + 2 := by linarith [abs_nonneg t]
    calc
      ‖z - 1‖ * ‖riemannZeta z‖ ≤ (4 * (|t| + 2)) * 3 :=
        mul_le_mul hsub hL.le (norm_nonneg _) (by positivity)
      _ ≤ 12 * (|t| + 2) ^ 6 := by
        have hpow : |t| + 2 ≤ (|t| + 2) ^ 6 := by
          have h1 : 1 ≤ |t| + 2 := by linarith [abs_nonneg t]
          simpa using (pow_le_pow_right₀ h1 (by norm_num : 1 ≤ 6))
        nlinarith
      _ ≤ 74649600 * (|t| + 2) ^ 6 := by
        exact mul_le_mul_of_nonneg_right (by norm_num)
          (pow_nonneg (by positivity) 6)
  · have hzle : z.re ≤ 2 := le_of_not_ge hzright
    have hF := MAPPrincipalZetaFixedStrip.norm_principalRegularized_fixedStrip_le
      hcoord.1 hzle
    have hreadd : |(z + 3).re| ≤ 8 := by
      rw [show (z + 3).re = z.re + 3 by norm_num]
      rw [abs_of_nonneg (by linarith [hcoord.1])]
      linarith [hcoord.2.1]
    have himadd : |(z + 3).im| ≤ |t| + 3 := by
      simpa using hcoord.2.2
    have hshift : ‖z + 3‖ ≤ 6 * (|t| + 2) := by
      calc
        ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 8 + (|t| + 3) := add_le_add hreadd himadd
        _ ≤ 6 * (|t| + 2) := by nlinarith [abs_nonneg t]
    rw [hscale]
    calc
      ‖MAPPrincipalZetaFixedStrip.principalRegularized z‖ ≤
          1600 * ‖z + 3‖ ^ 6 := hF
      _ ≤ 1600 * (6 * (|t| + 2)) ^ 6 := by gcongr
      _ = 74649600 * (|t| + 2) ^ 6 := by ring

/-- The Euler product gives the same one-third lower bound at the center as
in the nonprincipal proof; the extra regularizing factor has norm at least
one. -/
theorem one_third_le_norm_principalRegularized_wideCenter (t : ℝ) :
    (1 / 3 : ℝ) ≤ ‖regularizedLFunction χ₁ (wideCenter t)‖ := by
  have hz1 : wideCenter t ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    norm_num [wideCenter] at hre
  rw [MAPPrincipalZetaTransport.regularized_principal_eq,
    MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hz1,
    norm_mul]
  have hfac : 1 ≤ ‖wideCenter t - 1‖ := by
    have hre : 1 ≤ |(wideCenter t - 1).re| := by norm_num [wideCenter]
    exact hre.trans (Complex.abs_re_le_norm _)
  have hzeta : (1 / 3 : ℝ) ≤ ‖riemannZeta (wideCenter t)‖ := by
    have h := MAPPrimitiveLFixedStrip.one_third_le_norm_LFunction_two_add χ₁ t
    rw [DirichletCharacter.LFunction_modOne_eq] at h
    simpa [wideCenter, mul_comm] using h
  nlinarith [norm_nonneg (riemannZeta (wideCenter t))]

/-- Maximum-modulus transfer of the principal circle bound. -/
theorem norm_analyticWideBlaschkeDeflated_principal_le_on_closedBall
    {t : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall (wideCenter t) wideRadius) :
    ‖analyticWideBlaschkeDeflated χ₁ t z‖ ≤
      74649600 * (arithmeticScale 1 t) ^ 6 := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    Metric.isBounded_ball
    ((analyticOnNhd_analyticWideBlaschkeDeflated_closedBall χ₁ t).differentiableOn
      |>.diffContOnCl_ball subset_rfl)
  · intro w hw
    have hwsphere : w ∈ Metric.sphere (wideCenter t) wideRadius :=
      frontier_ball_subset_sphere hw
    rw [norm_analyticWideBlaschkeDeflated_eq_regularized_on_sphere χ₁ hwsphere]
    exact norm_principalRegularized_wideCircle_le hwsphere
  · rw [closure_ball _ (by norm_num [wideRadius])]
    exact hz

/-- Explicit logarithmic growth ratio for the conductor-one Blaschke fill. -/
theorem log_analyticWideBlaschkeDeflated_principal_ratio_le
    {t : ℝ} {z : ℂ} (hz : z ∈ Metric.ball (wideCenter t) wideRadius) :
    Real.log
        (‖analyticWideBlaschkeDeflated χ₁ t z‖ /
          ‖analyticWideBlaschkeDeflated χ₁ t (wideCenter t)‖) ≤
      Real.log 223948800 + 6 * Real.log (arithmeticScale 1 t) := by
  have hupper := norm_analyticWideBlaschkeDeflated_principal_le_on_closedBall
    (show z ∈ Metric.closedBall (wideCenter t) wideRadius by
      rw [Metric.mem_closedBall]
      exact (Metric.mem_ball.mp hz).le)
  have hcenterLower : (1 / 3 : ℝ) ≤
      ‖analyticWideBlaschkeDeflated χ₁ t (wideCenter t)‖ :=
    (one_third_le_norm_principalRegularized_wideCenter t).trans
      (norm_regularizedLFunction_center_le_analyticWideBlaschkeDeflated χ₁ t)
  have hcenterPos : 0 <
      ‖analyticWideBlaschkeDeflated χ₁ t (wideCenter t)‖ := by linarith
  have hratio :
      ‖analyticWideBlaschkeDeflated χ₁ t z‖ /
          ‖analyticWideBlaschkeDeflated χ₁ t (wideCenter t)‖ ≤
        223948800 * (arithmeticScale 1 t) ^ 6 := by
    apply (div_le_iff₀ hcenterPos).2
    have hone : 1 ≤ 3 *
        ‖analyticWideBlaschkeDeflated χ₁ t (wideCenter t)‖ := by linarith
    calc
      ‖analyticWideBlaschkeDeflated χ₁ t z‖ ≤
          74649600 * (arithmeticScale 1 t) ^ 6 := hupper
      _ ≤ (223948800 * (arithmeticScale 1 t) ^ 6) *
          ‖analyticWideBlaschkeDeflated χ₁ t (wideCenter t)‖ := by
        have h := mul_le_mul_of_nonneg_left hone
          (show 0 ≤ 74649600 * (arithmeticScale 1 t) ^ 6 by positivity)
        convert h using 1 <;> ring
  have hscale : 0 < arithmeticScale 1 t :=
    lt_of_lt_of_le zero_lt_one
      (MAPPrimitiveLFixedStrip.one_le_arithmeticScale t)
  have hlogeq :
      Real.log (223948800 * (arithmeticScale 1 t) ^ 6) =
        Real.log 223948800 + 6 * Real.log (arithmeticScale 1 t) := by
    rw [Real.log_mul (by norm_num : (223948800 : ℝ) ≠ 0)
      (pow_ne_zero 6 hscale.ne'), Real.log_pow]
    norm_num
  have hzpos : 0 < ‖analyticWideBlaschkeDeflated χ₁ t z‖ :=
    norm_pos_iff.mpr (analyticWideBlaschkeDeflated_ne_zero_ball χ₁ t hz)
  calc
    Real.log
        (‖analyticWideBlaschkeDeflated χ₁ t z‖ /
          ‖analyticWideBlaschkeDeflated χ₁ t (wideCenter t)‖) ≤
        Real.log (223948800 * (arithmeticScale 1 t) ^ 6) :=
      Real.log_le_log (div_pos hzpos hcenterPos) hratio
    _ = Real.log 223948800 + 6 * Real.log (arithmeticScale 1 t) := hlogeq

/-- Borel--Caratheodory on the radius-two inner disk. -/
theorem norm_logDeriv_analyticWideBlaschkeDeflated_principal_le
    {t : ℝ} {s : ℂ} (hs : dist s (wideCenter t) < 2) :
    ‖logDeriv (analyticWideBlaschkeDeflated χ₁ t) s‖ ≤
      20 * (Real.log 223948800 +
        6 * Real.log (arithmeticScale 1 t)) := by
  let M := Real.log 223948800 + 6 * Real.log (arithmeticScale 1 t)
  have hM : 0 < M := by
    have hscale : 1 ≤ arithmeticScale 1 t :=
      MAPPrimitiveLFixedStrip.one_le_arithmeticScale t
    dsimp [M]
    have hlogC : 0 < Real.log (223948800 : ℝ) :=
      Real.log_pos (by norm_num)
    have hlogscale : 0 ≤ Real.log (arithmeticScale 1 t) :=
      Real.log_nonneg hscale
    linarith
  have hbase := CompactDeflatedBorelBridge.norm_logDeriv_le_of_scaled_log_norm_ratio_le_at
    (g := analyticWideBlaschkeDeflated χ₁ t)
    (c := wideCenter t) (s := s) (r := (2 : ℝ)) (M := M)
    (by norm_num)
    (by simpa [wideRadius] using
      (analyticOnNhd_analyticWideBlaschkeDeflated_ball χ₁ t).differentiableOn)
    (fun z hz => analyticWideBlaschkeDeflated_ne_zero_ball χ₁ t
      (by simpa [wideRadius] using hz))
    hM
    (fun z hz => log_analyticWideBlaschkeDeflated_principal_ratio_le
      (by simpa [wideRadius] using hz)) hs
  dsimp [M] at hbase ⊢
  convert hbase using 1 <;> ring

/-! ## Principal radius-three zero mass -/

/-- The regularized zeta function has no zeros in `-1 < re s < 0`. -/
theorem regularizedLFunction_principal_ne_zero_of_neg_one_lt_re_lt_zero
    {s : ℂ} (hlo : -1 < s.re) (hhi : s.re < 0) :
    regularizedLFunction χ₁ s ≠ 0 := by
  intro hzero
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hhi
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hhi
  have hzeta : riemannZeta s = 0 := by
    rw [MAPPrincipalZetaTransport.regularized_principal_eq,
      MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hs1,
      mul_eq_zero] at hzero
    exact hzero.resolve_left (sub_ne_zero.mpr hs1)
  have hgamma : Complex.Gammaℝ s ≠ 0 := by
    rw [Ne, Complex.Gammaℝ_eq_zero_iff]
    push_neg
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num at hre
    by_cases hnzero : n = 0
    · subst n
      norm_num at hre
      linarith
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hnzero)
      linarith
  have hcompS : completedRiemannZeta s = 0 := by
    have heq := riemannZeta_def_of_ne_zero hs0
    rw [hzeta] at heq
    have hdiv := (div_eq_zero_iff.mp heq.symm)
    exact hdiv.resolve_right hgamma
  let u : ℂ := 1 - s
  have hcompU : completedRiemannZeta u = 0 := by
    dsimp [u]
    rw [completedRiemannZeta_one_sub, hcompS]
  have hu0 : u ≠ 0 := by
    intro hu
    have hre := congrArg Complex.re hu
    simp [u] at hre
    linarith
  have huRe : 1 < u.re := by
    change 1 < 1 - s.re
    linarith
  have hzetaU : riemannZeta u = 0 := by
    rw [riemannZeta_def_of_ne_zero hu0, hcompU, zero_div]
  exact (riemannZeta_ne_zero_of_one_le_re huRe.le) hzetaU

/-- Principal wide-disk zeros lie in the closed critical strip. -/
theorem re_nonneg_of_mem_principal_wideZeroSupport
    {t : ℝ} {rho : ℂ} (hrho : rho ∈ wideZeroSupport χ₁ t) :
    0 ≤ rho.re := by
  by_contra hnot
  have hreNeg : rho.re < 0 := lt_of_not_ge hnot
  have hball := mem_ball_of_mem_wideZeroSupport χ₁ hrho
  have hnorm : ‖rho - wideCenter t‖ < 3 := by
    simpa [Metric.mem_ball, dist_eq_norm, wideRadius] using hball
  have hreDiff : |rho.re - 2| < 3 := by
    simpa [wideCenter] using
      (Complex.abs_re_le_norm (rho - wideCenter t)).trans_lt hnorm
  have hlo : -1 < rho.re := by
    have := neg_lt_of_abs_lt hreDiff
    linarith
  exact (regularizedLFunction_principal_ne_zero_of_neg_one_lt_re_lt_zero
    hlo hreNeg)
      (regularizedLFunction_eq_zero_of_mem_zeroSupport χ₁ (-1) (|t| + 3)
        (mem_baseZeroSupport_of_mem_wideZeroSupport χ₁ hrho))

def principalWideUnitSlice (t u : ℝ) : Finset ℂ :=
  (wideZeroSupport χ₁ t).filter fun rho => u ≤ rho.im ∧ rho.im ≤ u + 1

theorem principalWideUnitSlice_mass_le_closedUnitWindowCount
    (t u : ℝ) :
    (∑ rho ∈ principalWideUnitSlice t u, wideZeroMultiplicity χ₁ t rho) ≤
      closedUnitWindowCount χ₁ 0 u := by
  have hsubset : principalWideUnitSlice t u ⊆
      closedUnitWindowSupport χ₁ 0 u := by
    intro rho hrho
    have hmem := Finset.mem_filter.mp hrho
    have hwide := hmem.1
    have hbase := mem_baseZeroSupport_of_mem_wideZeroSupport χ₁ hwide
    have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport
      χ₁ (-1) (|t| + 3) hbase
    have hbaseRect : rho ∈ zeroRectangle (-1) (|t| + 3) :=
      (zeroDivisor χ₁ (-1) (|t| + 3)).supportWithinDomain
        ((zeroSupport_mem_iff χ₁ (-1) (|t| + 3) rho).mp hbase)
    have himabs : |rho.im| ≤ windowHeight u := by
      have him := hmem.2
      unfold windowHeight
      rw [abs_le]
      constructor <;> linarith [le_abs_self u, neg_le_abs u]
    have hrect : rho ∈ zeroRectangle 0 (windowHeight u) := by
      rw [zeroRectangle, Complex.mem_reProdIm]
      exact ⟨⟨re_nonneg_of_mem_principal_wideZeroSupport hwide,
        hbaseRect.1.2⟩, abs_le.mp himabs⟩
    rw [closedUnitWindowSupport, Finset.mem_filter]
    exact ⟨(MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
      χ₁ 0 (windowHeight u) hrect).2 hzero, hmem.2⟩
  unfold principalWideUnitSlice closedUnitWindowCount
  calc
    (∑ rho ∈ (wideZeroSupport χ₁ t).filter
        (fun rho => u ≤ rho.im ∧ rho.im ≤ u + 1),
        wideZeroMultiplicity χ₁ t rho) =
      ∑ rho ∈ (wideZeroSupport χ₁ t).filter
        (fun rho => u ≤ rho.im ∧ rho.im ≤ u + 1),
        zeroMultiplicity χ₁ 0 (windowHeight u) rho := by
      apply Finset.sum_congr rfl
      intro rho hrho
      have hwide := (Finset.mem_filter.mp hrho).1
      have hbase := mem_baseZeroSupport_of_mem_wideZeroSupport χ₁ hwide
      have hbaseRect : rho ∈ zeroRectangle (-1) (|t| + 3) :=
        (zeroDivisor χ₁ (-1) (|t| + 3)).supportWithinDomain
          ((zeroSupport_mem_iff χ₁ (-1) (|t| + 3) rho).mp hbase)
      have htarget := hsubset hrho
      have htargetBase := (Finset.mem_filter.mp htarget).1
      have htargetRect : rho ∈ zeroRectangle 0 (windowHeight u) :=
        (zeroDivisor χ₁ 0 (windowHeight u)).supportWithinDomain
          ((zeroSupport_mem_iff χ₁ 0 (windowHeight u) rho).mp htargetBase)
      exact MAPMellinDetectorLeaf.zeroMultiplicity_eq_of_mem_rectangles
        χ₁ hbaseRect htargetRect
    _ ≤ ∑ rho ∈ closedUnitWindowSupport χ₁ 0 u,
        zeroMultiplicity χ₁ 0 (windowHeight u) rho :=
      Finset.sum_le_sum_of_subset hsubset

private theorem exists_window_index_of_mem_principal_wideZeroSupport
    {t : ℝ} {rho : ℂ} (hrho : rho ∈ wideZeroSupport χ₁ t) :
    ∃ j ∈ Finset.range 6,
      t - 3 + (j : ℝ) ≤ rho.im ∧ rho.im ≤ t - 3 + (j : ℝ) + 1 := by
  have hball := mem_ball_of_mem_wideZeroSupport χ₁ hrho
  have hnorm : ‖rho - wideCenter t‖ < 3 := by
    simpa [Metric.mem_ball, dist_eq_norm, wideRadius] using hball
  have himDiff : |rho.im - t| < 3 := by
    simpa [wideCenter] using
      (Complex.abs_im_le_norm (rho - wideCenter t)).trans_lt hnorm
  have hlo : t - 3 < rho.im := by
    have := neg_lt_of_abs_lt himDiff
    linarith
  have hhi : rho.im < t + 3 := by
    have := lt_of_abs_lt himDiff
    linarith
  by_cases h0 : rho.im ≤ t - 2
  · exact ⟨0, by simp, by norm_num; constructor <;> linarith⟩
  by_cases h1 : rho.im ≤ t - 1
  · exact ⟨1, by simp, by norm_num; constructor <;> linarith⟩
  by_cases h2 : rho.im ≤ t
  · exact ⟨2, by simp, by norm_num; constructor <;> linarith⟩
  by_cases h3 : rho.im ≤ t + 1
  · exact ⟨3, by simp, by norm_num; constructor <;> linarith⟩
  by_cases h4 : rho.im ≤ t + 2
  · exact ⟨4, by simp, by norm_num; constructor <;> linarith⟩
  · exact ⟨5, by simp, by norm_num; constructor <;> linarith⟩

theorem principal_wideZeroMultiplicity_mass_le_six_windows (t : ℝ) :
    (∑ rho ∈ wideZeroSupport χ₁ t, wideZeroMultiplicity χ₁ t rho) ≤
      ∑ j ∈ Finset.range 6,
        closedUnitWindowCount χ₁ 0 (t - 3 + (j : ℝ)) := by
  calc
    (∑ rho ∈ wideZeroSupport χ₁ t, wideZeroMultiplicity χ₁ t rho) ≤
      ∑ rho ∈ wideZeroSupport χ₁ t,
        ∑ j ∈ Finset.range 6,
          if t - 3 + (j : ℝ) ≤ rho.im ∧
              rho.im ≤ t - 3 + (j : ℝ) + 1 then
            wideZeroMultiplicity χ₁ t rho else 0 := by
      apply Finset.sum_le_sum
      intro rho hrho
      obtain ⟨j, hj, hinterval⟩ :=
        exists_window_index_of_mem_principal_wideZeroSupport hrho
      calc
        wideZeroMultiplicity χ₁ t rho =
            if t - 3 + (j : ℝ) ≤ rho.im ∧
                rho.im ≤ t - 3 + (j : ℝ) + 1 then
              wideZeroMultiplicity χ₁ t rho else 0 := by simp [hinterval]
        _ ≤ ∑ k ∈ Finset.range 6,
            if t - 3 + (k : ℝ) ≤ rho.im ∧
                rho.im ≤ t - 3 + (k : ℝ) + 1 then
              wideZeroMultiplicity χ₁ t rho else 0 := by
          apply Finset.single_le_sum (fun k hk => by positivity) hj
    _ = ∑ j ∈ Finset.range 6,
        ∑ rho ∈ principalWideUnitSlice t (t - 3 + (j : ℝ)),
          wideZeroMultiplicity χ₁ t rho := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      unfold principalWideUnitSlice
      rw [Finset.sum_filter]
    _ ≤ ∑ j ∈ Finset.range 6,
        closedUnitWindowCount χ₁ 0 (t - 3 + (j : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact principalWideUnitSlice_mass_le_closedUnitWindowCount t _

/-- Explicit principal multiplicity mass in the radius-three disk. -/
theorem principal_wideZeroMultiplicity_mass_le_logScale (t : ℝ) :
    (∑ rho ∈ wideZeroSupport χ₁ t,
        (wideZeroMultiplicity χ₁ t rho : ℝ)) ≤
      30300 * Real.log (arithmeticScale 1 t) := by
  have hmass := principal_wideZeroMultiplicity_mass_le_six_windows t
  have hcast :
      (∑ rho ∈ wideZeroSupport χ₁ t,
        (wideZeroMultiplicity χ₁ t rho : ℝ)) ≤
      ∑ j ∈ Finset.range 6,
        (closedUnitWindowCount χ₁ 0 (t - 3 + (j : ℝ)) : ℝ) := by
    exact_mod_cast hmass
  apply hcast.trans
  calc
    (∑ j ∈ Finset.range 6,
        (closedUnitWindowCount χ₁ 0 (t - 3 + (j : ℝ)) : ℝ)) ≤
      ∑ _j ∈ Finset.range 6,
        5050 * Real.log (arithmeticScale 1 t) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjlt : j < 6 := Finset.mem_range.mp hj
      have hjle : (j : ℝ) ≤ 5 := by exact_mod_cast (Nat.le_of_lt_succ hjlt)
      have hj0 : (0 : ℝ) ≤ j := by positivity
      have hnear : |(t - 3 + (j : ℝ)) - t| ≤ 3 := by
        rw [show t - 3 + (j : ℝ) - t = (j : ℝ) - 3 by ring]
        rw [abs_le]
        constructor <;> linarith
      have hlog :=
        log_arithmeticScale_le_three_mul_of_abs_sub_le_three
          (q := 1) hnear
      have hcount :=
        MAPPrincipalZetaFullStrip.principal_fullStrip_count_le_log
          (t - 3 + (j : ℝ))
      nlinarith
    _ = 30300 * Real.log (arithmeticScale 1 t) := by simp; ring

/-! ## The principal Lemma 11.4(b) remainder -/

theorem norm_principal_localDeflatedLogDeriv_le
    {t : ℝ} {s : ℂ} (hs : s ∈ Metric.ball (wideCenter t) 2)
    (hsF : s ∉ wideZeroSupport χ₁ t) :
    ‖logDeriv (regularizedLFunction χ₁) s -
        ∑ rho ∈ wideZeroSupport χ₁ t,
          (wideZeroMultiplicity χ₁ t rho : ℂ) / (s - rho)‖ ≤
      20 * (Real.log 223948800 +
        6 * Real.log (arithmeticScale 1 t)) +
      ∑ rho ∈ wideZeroSupport χ₁ t,
        (wideZeroMultiplicity χ₁ t rho : ℝ) := by
  have hid := localDeflatedLogDeriv_eq_blaschke_sub_correction χ₁ hs hsF
  rw [hid]
  have hB := norm_logDeriv_analyticWideBlaschkeDeflated_principal_le
    (Metric.mem_ball.mp hs)
  have hcorr :
      ‖∑ rho ∈ wideZeroSupport χ₁ t,
          (wideZeroMultiplicity χ₁ t rho : ℂ) *
            logDeriv (shiftedCanonicalNumerator
              (wideCenter t) rho wideRadius) s‖ ≤
        ∑ rho ∈ wideZeroSupport χ₁ t,
          (wideZeroMultiplicity χ₁ t rho : ℝ) := by
    calc
      ‖∑ rho ∈ wideZeroSupport χ₁ t,
          (wideZeroMultiplicity χ₁ t rho : ℂ) *
            logDeriv (shiftedCanonicalNumerator
              (wideCenter t) rho wideRadius) s‖ ≤
          ∑ rho ∈ wideZeroSupport χ₁ t,
            ‖(wideZeroMultiplicity χ₁ t rho : ℂ) *
              logDeriv (shiftedCanonicalNumerator
                (wideCenter t) rho wideRadius) s‖ := norm_sum_le _ _
      _ ≤ ∑ rho ∈ wideZeroSupport χ₁ t,
          (wideZeroMultiplicity χ₁ t rho : ℝ) := by
        apply Finset.sum_le_sum
        intro rho hrho
        rw [norm_mul, Complex.norm_natCast]
        have hnum :=
          norm_logDeriv_shiftedCanonicalNumerator_le_one
            (c := wideCenter t) (ρ := rho) (s := s)
            (by simpa [wideRadius] using
              mem_ball_of_mem_wideZeroSupport χ₁ hrho) hs
        exact (mul_le_mul_of_nonneg_left hnum (Nat.cast_nonneg _)).trans_eq
          (mul_one _)
  exact (norm_sub_le _ _).trans (add_le_add hB hcorr)

/-- Premise-free conductor-one form of Koukoulopoulos Lemma 11.4(b). -/
theorem principalLogDerivativeRemainder_le
    {u t : ℝ} (hu : 1 < u) (hu2 : u ≤ 2) :
    ‖primitiveLogDerivativeRemainder χ₁ u t‖ ≤
      100000 * Real.log (arithmeticScale 1 t) := by
  let s : ℂ := (u : ℂ) + Complex.I * t
  let W : ℂ := ∑ rho ∈ wideZeroSupport χ₁ t,
    (wideZeroMultiplicity χ₁ t rho : ℂ) / (s - rho)
  let C : ℂ := centeredZeroPoleSum χ₁ t s
  let M : ℝ := ∑ rho ∈ wideZeroSupport χ₁ t,
    (wideZeroMultiplicity χ₁ t rho : ℝ)
  have hs : s ∈ Metric.ball (wideCenter t) 2 := by
    rw [Metric.mem_ball, dist_eq_norm]
    dsimp [s, wideCenter]
    have huabs : |u - 2| < 2 := by
      rw [abs_lt]
      constructor <;> linarith
    rw [show (u : ℂ) + Complex.I * (t : ℂ) -
        (2 + Complex.I * (t : ℂ)) = ((u - 2 : ℝ) : ℂ) by
      push_cast
      ring]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact huabs
  have hsF : s ∉ wideZeroSupport χ₁ t := by
    intro hmem
    have hre := MAPMellinDetectorLeaf.re_lt_one_of_mem_zeroSupport χ₁
      (mem_baseZeroSupport_of_mem_wideZeroSupport χ₁ hmem)
    dsimp [s] at hre
    simp at hre
    linarith
  have hlocal := norm_principal_localDeflatedLogDeriv_le hs hsF
  have hmismatch : ‖W - C‖ ≤ 2 * M := by
    simpa only [W, C, M, s] using
      norm_widePoleSum_sub_centeredPoleSum_le χ₁ hu
  have hremEq :
      primitiveLogDerivativeRemainder χ₁ u t =
        -(logDeriv (regularizedLFunction χ₁) s - C) := by
    have heq :=
      neg_logDeriv_regularizedLFunction_eq_centeredZeroSum_add_deflated
        χ₁ t (s := s) (by dsimp [s]; simpa using hu.le)
    dsimp [primitiveLogDerivativeRemainder, C, s] at heq ⊢
    linear_combination -heq
  have hsplit :
      logDeriv (regularizedLFunction χ₁) s - C =
        (logDeriv (regularizedLFunction χ₁) s - W) + (W - C) := by ring
  have hraw :
      ‖primitiveLogDerivativeRemainder χ₁ u t‖ ≤
        20 * (Real.log 223948800 +
          6 * Real.log (arithmeticScale 1 t)) + 3 * M := by
    rw [hremEq, norm_neg, hsplit]
    calc
      ‖(logDeriv (regularizedLFunction χ₁) s - W) + (W - C)‖ ≤
          ‖logDeriv (regularizedLFunction χ₁) s - W‖ + ‖W - C‖ :=
        norm_add_le _ _
      _ ≤ (20 * (Real.log 223948800 +
            6 * Real.log (arithmeticScale 1 t)) + M) + 2 * M := by
        exact add_le_add (by simpa only [W, M, s] using hlocal) hmismatch
      _ = 20 * (Real.log 223948800 +
            6 * Real.log (arithmeticScale 1 t)) + 3 * M := by ring
  have hmass : M ≤ 30300 * Real.log (arithmeticScale 1 t) := by
    simpa only [M] using principal_wideZeroMultiplicity_mass_le_logScale t
  have hscale2 := two_le_arithmeticScale (q := 1) t
  have hscale0 : 0 < arithmeticScale 1 t := by linarith
  have hC :
      Real.log 223948800 ≤ 28 * Real.log (arithmeticScale 1 t) := by
    have hpow : (223948800 : ℝ) ≤
        arithmeticScale 1 t ^ (28 : ℕ) := by
      calc
        (223948800 : ℝ) ≤ 2 ^ (28 : ℕ) := by norm_num
        _ ≤ arithmeticScale 1 t ^ (28 : ℕ) := by
          exact pow_le_pow_left₀ (by norm_num) hscale2 28
    calc
      Real.log 223948800 ≤
          Real.log (arithmeticScale 1 t ^ (28 : ℕ)) :=
        Real.log_le_log (by norm_num) hpow
      _ = 28 * Real.log (arithmeticScale 1 t) := by
        rw [Real.log_pow]
        norm_num
  have hlog0 : 0 ≤ Real.log (arithmeticScale 1 t) :=
    Real.log_nonneg (by linarith)
  exact hraw.trans (by nlinarith)

/-- Exact principal local formula, with the pole at one retained explicitly. -/
theorem neg_logDeriv_riemannZeta_eq_pole_sub_centered_add_remainder
    {u t : ℝ} (hu : 1 < u) :
    -logDeriv riemannZeta ((u : ℂ) + Complex.I * t) =
      (1 / (((u : ℂ) + Complex.I * t) - 1)) -
        centeredZeroPoleSum χ₁ t ((u : ℂ) + Complex.I * t) +
        primitiveLogDerivativeRemainder χ₁ u t := by
  let s : ℂ := (u : ℂ) + Complex.I * t
  have hs1 : s ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    dsimp [s] at hre
    simp at hre
    linarith
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by dsimp [s]; simpa using hu.le)
  have hlin : (fun z : ℂ => z - 1) s ≠ 0 := sub_ne_zero.mpr hs1
  have hmul := logDeriv_mul (f := fun z : ℂ => z - 1) (g := riemannZeta)
    s hlin hzeta (by fun_prop)
    (differentiableAt_riemannZeta hs1)
  have hlinLog : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
    simp only [logDeriv_apply, deriv_sub_const]
    rw [show deriv (fun y : ℂ => y) s = 1 by simpa using deriv_id s]
  have hregLog :
      logDeriv (regularizedLFunction χ₁) s =
        1 / (s - 1) + logDeriv riemannZeta s := by
    have hevent : Filter.EventuallyEq (nhds s) (regularizedLFunction χ₁)
        (fun z => (z - 1) * riemannZeta z) := by
      filter_upwards [eventually_ne_nhds hs1] with z hz1
      rw [MAPPrincipalZetaTransport.regularized_principal_eq,
        MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hz1]
    calc
      logDeriv (regularizedLFunction χ₁) s =
          logDeriv (fun z => (z - 1) * riemannZeta z) s := by
        rw [logDeriv_apply, logDeriv_apply, hevent.deriv_eq,
          hevent.self_of_nhds]
      _ = logDeriv (fun z : ℂ => z - 1) s + logDeriv riemannZeta s := hmul
      _ = 1 / (s - 1) + logDeriv riemannZeta s := by rw [hlinLog]
  have hdec :
      -logDeriv (regularizedLFunction χ₁) s =
        -centeredZeroPoleSum χ₁ t s +
          primitiveLogDerivativeRemainder χ₁ u t := by
    have h :=
      neg_logDeriv_regularizedLFunction_eq_centeredZeroSum_add_deflated
        χ₁ t (s := s) (by dsimp [s]; simpa using hu.le)
    simpa [primitiveLogDerivativeRemainder, s, sub_eq_add_neg] using h
  dsimp [s] at hregLog
  rw [hregLog] at hdec
  linear_combination hdec

end

end MAPPrincipalLogDerivativeRemainderUnconditional

#print axioms MAPPrincipalLogDerivativeRemainderUnconditional.norm_principalRegularized_wideCircle_le
#print axioms MAPPrincipalLogDerivativeRemainderUnconditional.norm_logDeriv_analyticWideBlaschkeDeflated_principal_le
#print axioms MAPPrincipalLogDerivativeRemainderUnconditional.regularizedLFunction_principal_ne_zero_of_neg_one_lt_re_lt_zero
#print axioms MAPPrincipalLogDerivativeRemainderUnconditional.principal_wideZeroMultiplicity_mass_le_logScale
#print axioms MAPPrincipalLogDerivativeRemainderUnconditional.principalLogDerivativeRemainder_le
#print axioms MAPPrincipalLogDerivativeRemainderUnconditional.neg_logDeriv_riemannZeta_eq_pole_sub_centered_add_remainder
