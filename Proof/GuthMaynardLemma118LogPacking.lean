import GuthMaynardLemma117Cubic
import GuthMaynardLemma118EnergyPacking

/-!
# Log-frequency packing for Guth--Maynard Lemma 11.8

The ratio kernel is locally constant in the Fourier coordinate
`log v / (-2*pi)`, whereas the source enumerates reduced rational ratios.
This file certifies that the logarithmic map preserves the rational spacing
up to the exact compact-range factor used for ratios in `[1/2,2]`.
-/

open scoped BigOperators FourierTransform SchwartzMap
open MeasureTheory

namespace GuthMaynardLemma118

open GuthMaynardJIteration GuthMaynardRatioKernelIdentity

noncomputable section

/-- On the compact positive range with upper endpoint two, logarithm loses at
most a factor two in separation. -/
theorem half_abs_sub_le_abs_log_sub
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hx2 : x ≤ 2) (hy2 : y ≤ 2) :
    |x-y| / 2 ≤ |Real.log x - Real.log y| := by
  rcases le_total x y with hxy | hyx
  · have hratio : 0 < y/x := div_pos hy hx
    have hlog0 : 0 ≤ Real.log y - Real.log x := by
      rw [sub_nonneg]
      exact Real.strictMonoOn_log.monotoneOn hx hy hxy
    have hbase := Real.one_sub_inv_le_log_of_pos hratio
    have hid : Real.log (y/x) = Real.log y - Real.log x := by
      rw [Real.log_div hy.ne' hx.ne']
    have hfrac : (y-x)/y ≤ Real.log y - Real.log x := by
      rw [← hid]
      convert hbase using 1 <;> field_simp [hx.ne', hy.ne'] <;> ring
    have hhalf : (y-x)/2 ≤ (y-x)/y := by
      have hnum : 0 ≤ y-x := sub_nonneg.mpr hxy
      exact (div_le_div_iff₀ (by norm_num : (0:ℝ)<2) hy).2 (by
        nlinarith)
    rw [abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr (Real.strictMonoOn_log.monotoneOn hx hy hxy)),
      neg_sub, neg_sub]
    exact hhalf.trans hfrac
  · have hratio : 0 < x/y := div_pos hx hy
    have hlog0 : 0 ≤ Real.log x - Real.log y := by
      rw [sub_nonneg]
      exact Real.strictMonoOn_log.monotoneOn hy hx hyx
    have hbase := Real.one_sub_inv_le_log_of_pos hratio
    have hid : Real.log (x/y) = Real.log x - Real.log y := by
      rw [Real.log_div hx.ne' hy.ne']
    have hfrac : (x-y)/x ≤ Real.log x - Real.log y := by
      rw [← hid]
      convert hbase using 1 <;> field_simp [hx.ne', hy.ne'] <;> ring
    have hhalf : (x-y)/2 ≤ (x-y)/x := by
      have hnum : 0 ≤ x-y := sub_nonneg.mpr hyx
      exact (div_le_div_iff₀ (by norm_num : (0:ℝ)<2) hx).2 (by
        nlinarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hyx), abs_of_nonneg hlog0]
    exact hhalf.trans hfrac

/-- Distinct reduced natural fractions in the dyadic ratio range remain
separated after passage to the exact Fourier coordinate in (7.2). -/
theorem distinct_nat_fraction_logFrequency_separation
    {a b c d : ℕ} {B : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hB : 0 < B)
    (hbB : (b : ℝ) ≤ B) (hdB : (d : ℝ) ≤ B)
    (hac : a*d ≠ c*b)
    (haRatio : (a:ℝ)/(b:ℝ) ≤ 2)
    (hcRatio : (c:ℝ)/(d:ℝ) ≤ 2) :
    1 / (4 * Real.pi * B^2) ≤
      |Real.log ((a:ℝ)/(b:ℝ)) / (-2*Real.pi) -
        Real.log ((c:ℝ)/(d:ℝ)) / (-2*Real.pi)| := by
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  let x : ℝ := (a:ℝ)/(b:ℝ)
  let y : ℝ := (c:ℝ)/(d:ℝ)
  have hx : 0 < x := div_pos haR hbR
  have hy : 0 < y := div_pos hcR hdR
  have hrat := GuthMaynardS3Source.distinct_nat_fraction_separation_of_denominator_le
    hb hd hB hbB hdB hac
  have hlog : 1/(2*B^2) ≤ |Real.log x-Real.log y| := by
    have hhalf := half_abs_sub_le_abs_log_sub hx hy haRatio hcRatio
    dsimp only [x,y] at hhalf
    calc
      1/(2*B^2) = (1/B^2)/2 := by ring
      _ ≤ |(a:ℝ)/(b:ℝ)-(c:ℝ)/(d:ℝ)|/2 := by gcongr
      _ ≤ |Real.log x-Real.log y| := hhalf
  have hden : 0 < 2*Real.pi := by positivity
  have heq :
      |Real.log x / (-2*Real.pi) - Real.log y / (-2*Real.pi)| =
        |Real.log x-Real.log y| / (2*Real.pi) := by
    rw [← sub_div]
    rw [abs_div, abs_of_neg (by nlinarith [Real.pi_pos] : -2*Real.pi < 0)]
    ring
  rw [heq]
  have hscale := div_le_div_of_nonneg_right hlog hden.le
  convert hscale using 1 <;> field_simp [Real.pi_ne_zero, hB.ne'] <;> ring

/-- The exact collar-packing theorem in the coordinate naturally produced by
Lemma 11.7.  This avoids an unnecessary nonlinear change of variables: the
reduced rational samples are packed directly after applying `log/(-2*pi)`.
The factor `4*pi` is the certified compact-range loss. -/
theorem sum_rational_logFrequency_samples_le_packing_mul_integral
    (P : Finset (ℕ × ℕ)) {B r C : ℝ}
    (hB : 0 < B) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hnumden : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
      (p.2 : ℝ) ≤ B ∧ (p.1 : ℝ)/(p.2 : ℝ) ≤ 2)
    (hcross : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      p.1 * q.2 ≠ q.1 * p.2)
    (F : ℝ → ℝ) (hFint : Integrable F) (hF : ∀ u, 0 ≤ F u)
    (hlocal : ∀ p ∈ P,
      F (Real.log ((p.1:ℝ)/(p.2:ℝ)) / (-2*Real.pi)) ≤
        C * ∫ u, (sampleCollar
          (fun z : ℕ × ℕ =>
            Real.log ((z.1:ℝ)/(z.2:ℝ)) / (-2*Real.pi)) r p).indicator F u) :
    (∑ p ∈ P,
      F (Real.log ((p.1:ℝ)/(p.2:ℝ)) / (-2*Real.pi))) ≤
      C * ((⌊(8 * Real.pi * r) * B^2⌋₊ + 1 : ℕ) : ℝ) *
        ∫ u, F u := by
  let x : ℕ × ℕ → ℝ := fun p =>
    Real.log ((p.1:ℝ)/(p.2:ℝ)) / (-2*Real.pi)
  have hδ : 0 < (1:ℝ)/(4*Real.pi*B^2) := by positivity
  have hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      (1:ℝ)/(4*Real.pi*B^2) ≤ |x p-x q| := by
    intro p hp q hq hpq
    exact distinct_nat_fraction_logFrequency_separation
      (hnumden p hp).1 (hnumden p hp).2.1
      (hnumden q hq).1 (hnumden q hq).2.1 hB
      (hnumden p hp).2.2.1 (hnumden q hq).2.2.1
      (hcross p hp q hq hpq)
      (hnumden p hp).2.2.2 (hnumden q hq).2.2.2
  have hmain := sum_samples_le_packing_mul_integral P x hr hδ hC hsep
    F hFint hF hlocal
  have hscale : (2*r)/((1:ℝ)/(4*Real.pi*B^2)) =
      (8*Real.pi*r)*B^2 := by
    field_simp [Real.pi_ne_zero, hB.ne']
    ring
  simpa only [x, hscale] using hmain

/-- Compactly supported cubic Fourier field used to make the source's
`v asymp 1` integral literal and integrable. -/
def compactCubicField (W : Finset ℝ) (lo hi u : ℝ) : ℝ :=
  (Set.Icc lo hi).indicator
    (fun z => ‖GuthMaynardRatioKernelIdentity.pointMassFourierKernel W z‖^3) u

/-- The nonnegative compact field whose second and fourth moments are the
literal `v asymp 1` moments in the last line of Lemma 11.8. -/
def compactKernelField (W : Finset ℝ) (lo hi u : ℝ) : ℝ :=
  (Set.Icc lo hi).indicator
    (fun z => ‖GuthMaynardRatioKernelIdentity.pointMassFourierKernel W z‖) u

theorem integral_compactKernelField_pow
    (W : Finset ℝ) (lo hi : ℝ) (p : ℕ) (hp : 0 < p) :
    (∫ u, compactKernelField W lo hi u ^ p) =
      ∫ u in Set.Icc lo hi,
        ‖GuthMaynardRatioKernelIdentity.pointMassFourierKernel W u‖ ^ p := by
  rw [← MeasureTheory.integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ Set.Icc lo hi
  · simp [compactKernelField, hu]
  · simp [compactKernelField, hu, hp.ne']

set_option maxHeartbeats 1200000 in
/-- Complete small-gcd sample estimate before summing over gcd scales.  This
joins the repaired cubic Lemma 11.7 directly to reduced-fraction packing in
log-frequency.  The interval `[lo,hi]` is the literal compact avatar of
`v asymp 1`; the two center inequalities say every radius-`A/(3T)` collar is
inside it. -/
theorem sum_ratioKernel_cube_le_logPacking_add_tail
    (W : Finset ℝ) (P : Finset (ℕ × ℕ))
    {x0 T A B lo hi : ℝ} (k : ℕ)
    (hT : 0 < T) (hA : 0 < A) (hB : 0 < B)
    (hinterval : ∀ t ∈ W, x0 ≤ t ∧ t ≤ x0+T)
    (hnumden : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
      (p.2:ℝ) ≤ B ∧ (p.1:ℝ)/(p.2:ℝ) ≤ 2)
    (hcross : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      p.1*q.2 ≠ q.1*p.2)
    (hcenter : ∀ p ∈ P,
      lo + A/(3*T) ≤ Real.log ((p.1:ℝ)/(p.2:ℝ))/(-2*Real.pi) ∧
      Real.log ((p.1:ℝ)/(p.2:ℝ))/(-2*Real.pi) ≤ hi-A/(3*T)) :
    (∑ p ∈ P,
      ‖GuthMaynardRatioKernelIdentity.ratioDirichletKernel W
        ((p.1:ℝ)/(p.2:ℝ))‖^3) ≤
      (sourceBumpFourierConstant 1 zero_lt_one 0 * (3*T)) *
        ((⌊(8*Real.pi*(A/(3*T)))*B^2⌋₊+1:ℕ):ℝ) *
          (∫ u in Set.Icc lo hi,
            ‖GuthMaynardRatioKernelIdentity.pointMassFourierKernel W u‖^3) +
      (P.card:ℝ) * ((W.card:ℝ)^3 * (A^k)⁻¹ *
        ∫ xi : ℝ, |xi|^k *
          ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ,ℂ)) xi‖) := by
  let r : ℝ := A/(3*T)
  let xf : ℕ × ℕ → ℝ := fun p =>
    Real.log ((p.1:ℝ)/(p.2:ℝ))/(-2*Real.pi)
  let F : ℝ → ℝ := compactCubicField W lo hi
  let C : ℝ := sourceBumpFourierConstant 1 zero_lt_one 0 * (3*T)
  let Tail : ℝ := (W.card:ℝ)^3*(A^k)⁻¹ *
    ∫ xi : ℝ, |xi|^k *
      ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ,ℂ)) xi‖
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hδ : 0 < (1:ℝ)/(4*Real.pi*B^2) := by positivity
  have hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      (1:ℝ)/(4*Real.pi*B^2) ≤ |xf p-xf q| := by
    intro p hp q hq hpq
    exact distinct_nat_fraction_logFrequency_separation
      (hnumden p hp).1 (hnumden p hp).2.1
      (hnumden q hq).1 (hnumden q hq).2.1 hB
      (hnumden p hp).2.2.1 (hnumden q hq).2.2.1
      (hcross p hp q hq hpq)
      (hnumden p hp).2.2.2 (hnumden q hq).2.2.2
  have hFnonneg : ∀ u, 0 ≤ F u := by
    intro u
    dsimp [F, compactCubicField]
    exact Set.indicator_nonneg (fun _ _ => by positivity) _
  have hFint : Integrable F := by
    change Integrable ((Set.Icc lo hi).indicator
      (fun u => ‖GuthMaynardRatioKernelIdentity.pointMassFourierKernel W u‖^3))
    have hc : Continuous (fun u : ℝ =>
        ‖GuthMaynardRatioKernelIdentity.pointMassFourierKernel W u‖^3) := by
      unfold GuthMaynardRatioKernelIdentity.pointMassFourierKernel
      fun_prop
    apply (integrable_indicator_iff measurableSet_Icc).2
    exact hc.continuousOn.integrableOn_compact (μ:=volume) isCompact_Icc
  have hcollarSubset : ∀ p ∈ P,
      sampleCollar xf r p ⊆ Set.Icc lo hi := by
    intro p hp u hu
    have hu' : |xf p-u| ≤ r := hu
    have habs := abs_le.mp hu'
    have hc := hcenter p hp
    dsimp only [xf,r] at habs hc ⊢
    constructor <;> linarith
  have hlocal : ∀ p ∈ P,
      F (xf p) ≤ C * (∫ u, (sampleCollar xf r p).indicator F u) + Tail := by
    intro p hp
    have hcub := GuthMaynardLemma117.pointMassFourierKernel_cube_localConstancy_explicit
      W k hT hA hinterval (tau:=xf p)
    have hxp : xf p ∈ Set.Icc lo hi := by
      have hc := hcenter p hp
      dsimp only [xf,r] at hc ⊢
      constructor <;> linarith [hr]
    have hleft : F (xf p) =
        ‖GuthMaynardRatioKernelIdentity.pointMassFourierKernel W (xf p)‖^3 := by
      simp [F, compactCubicField, hxp]
    have hset : sampleCollar xf r p = Set.Icc (xf p-r) (xf p+r) := by
      ext u
      simp only [sampleCollar, Set.mem_setOf_eq, Set.mem_Icc]
      rw [abs_le]
      constructor <;> intro h <;> constructor <;> linarith
    have hint :
        (∫ u in Set.Icc (xf p-r) (xf p+r),
          ‖GuthMaynardRatioKernelIdentity.pointMassFourierKernel W u‖^3) =
        ∫ u, (sampleCollar xf r p).indicator F u := by
      rw [← MeasureTheory.integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with u
      by_cases hu : u ∈ sampleCollar xf r p
      · have hui : u ∈ Set.Icc lo hi := hcollarSubset p hp hu
        have huI : u ∈ Set.Icc (xf p-r) (xf p+r) := by simpa [←hset] using hu
        rw [Set.indicator_of_mem huI, Set.indicator_of_mem hu]
        simp [F, compactCubicField, hui]
      · have huI : u ∉ Set.Icc (xf p-r) (xf p+r) := by simpa [←hset] using hu
        rw [Set.indicator_of_notMem huI, Set.indicator_of_notMem hu]
    rw [hleft]
    rw [show A/(3*T)=r by rfl, hint] at hcub
    simpa only [C,Tail,mul_assoc] using hcub
  have hsumLocal :
      (∑ p ∈ P, F (xf p)) ≤
        C * (∑ p ∈ P, (∫ u, (sampleCollar xf r p).indicator F u)) +
          (P.card:ℝ)*Tail := by
    calc
      (∑ p ∈ P, F (xf p)) ≤
          (∑ p ∈ P, (C * (∫ u, (sampleCollar xf r p).indicator F u) + Tail)) :=
        Finset.sum_le_sum fun p hp => hlocal p hp
      _ = C * (∑ p ∈ P, ∫ u, (sampleCollar xf r p).indicator F u) +
          (P.card:ℝ)*Tail := by
        calc
          (∑ p ∈ P, (C * (∫ u, (sampleCollar xf r p).indicator F u) + Tail)) =
              (∑ p ∈ P, C * (∫ u, (sampleCollar xf r p).indicator F u)) +
                ∑ _p ∈ P, Tail := Finset.sum_add_distrib
          _ = _ := by rw [Finset.mul_sum]; simp
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (sourceBumpFourierConstant_nonneg 1 zero_lt_one 0)
      (by positivity)
  have hpack := sum_integral_sampleCollar_le P xf hr hδ hsep F hFint hFnonneg
  have hscale : (2*r)/((1:ℝ)/(4*Real.pi*B^2)) =
      (8*Real.pi*r)*B^2 := by
    field_simp [Real.pi_ne_zero,hB.ne']
    ring
  have hbound := hsumLocal.trans (add_le_add
    (mul_le_mul_of_nonneg_left hpack hC) le_rfl)
  have hFmass : (∫ u, F u) =
      ∫ u in Set.Icc lo hi,
        ‖GuthMaynardRatioKernelIdentity.pointMassFourierKernel W u‖^3 := by
    dsimp [F,compactCubicField]
    exact MeasureTheory.integral_indicator measurableSet_Icc
  have hsumRatio :
      (∑ p ∈ P, ‖ratioDirichletKernel W ((p.1:ℝ)/(p.2:ℝ))‖^3) =
        ∑ p ∈ P, F (xf p) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [ratioDirichletKernel_eq_pointMassFourierKernel]
    have hp1 : (0:ℝ) < p.1 := by exact_mod_cast (hnumden p hp).1
    have hp2 : (0:ℝ) < p.2 := by exact_mod_cast (hnumden p hp).2.1
    rw [abs_of_pos (div_pos hp1 hp2)]
    have hxmem : xf p ∈ Set.Icc lo hi := by
      have hc := hcenter p hp
      dsimp only [xf,r] at hc ⊢
      constructor <;> linarith [hr]
    change ‖pointMassFourierKernel W (xf p)‖^3 = F (xf p)
    dsimp only [F,compactCubicField]
    rw [Set.indicator_of_mem hxmem]
  rw [hsumRatio]
  rw [hFmass] at hbound
  rw [hscale] at hbound
  simpa only [r,C,Tail,hscale, mul_assoc] using hbound

set_option maxHeartbeats 1200000 in
/-- The complete analytic/geometric sample bound used in Lemma 11.8.  The
cubic sample mass is controlled by the geometric mean of the literal compact
second and fourth moments, with one bandwidth factor and the exact rational
packing multiplicity. -/
theorem sum_ratioKernel_cube_le_logPacking_mul_sqrtMoments_add_tail
    (W : Finset ℝ) (P : Finset (ℕ × ℕ))
    {x0 T A B lo hi : ℝ} (k : ℕ)
    (hT : 0 < T) (hA : 0 < A) (hB : 0 < B)
    (hinterval : ∀ t ∈ W, x0 ≤ t ∧ t ≤ x0+T)
    (hnumden : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
      (p.2:ℝ) ≤ B ∧ (p.1:ℝ)/(p.2:ℝ) ≤ 2)
    (hcross : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      p.1*q.2 ≠ q.1*p.2)
    (hcenter : ∀ p ∈ P,
      lo + A/(3*T) ≤ Real.log ((p.1:ℝ)/(p.2:ℝ))/(-2*Real.pi) ∧
      Real.log ((p.1:ℝ)/(p.2:ℝ))/(-2*Real.pi) ≤ hi-A/(3*T)) :
    (∑ p ∈ P,
      ‖GuthMaynardRatioKernelIdentity.ratioDirichletKernel W
        ((p.1:ℝ)/(p.2:ℝ))‖^3) ≤
      (sourceBumpFourierConstant 1 zero_lt_one 0 * (3*T)) *
        ((⌊(8*Real.pi*(A/(3*T)))*B^2⌋₊+1:ℕ):ℝ) *
          Real.sqrt (∫ u in Set.Icc lo hi,
            ‖GuthMaynardRatioKernelIdentity.pointMassFourierKernel W u‖^2) *
          Real.sqrt (∫ u in Set.Icc lo hi,
            ‖GuthMaynardRatioKernelIdentity.pointMassFourierKernel W u‖^4) +
      (P.card:ℝ) * ((W.card:ℝ)^3 * (A^k)⁻¹ *
        ∫ xi : ℝ, |xi|^k *
          ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ,ℂ)) xi‖) := by
  let G : ℝ → ℝ := compactKernelField W lo hi
  have hGc : Continuous (fun u : ℝ =>
      ‖GuthMaynardRatioKernelIdentity.pointMassFourierKernel W u‖) := by
    unfold GuthMaynardRatioKernelIdentity.pointMassFourierKernel
    fun_prop
  have hGmeas : AEStronglyMeasurable G := by
    dsimp [G, compactKernelField]
    exact hGc.aestronglyMeasurable.indicator measurableSet_Icc
  have hGpowInt (p : ℕ) (hp : 0 < p) : Integrable (fun u => G u ^ p) := by
    have heq : (fun u => G u ^ p) = (Set.Icc lo hi).indicator
        (fun u => ‖GuthMaynardRatioKernelIdentity.pointMassFourierKernel W u‖ ^ p) := by
      funext u
      by_cases hu : u ∈ Set.Icc lo hi
      · simp [G, compactKernelField, hu]
      · simp [G, compactKernelField, hu, hp.ne']
    rw [heq]
    apply (integrable_indicator_iff measurableSet_Icc).2
    exact (hGc.pow p).continuousOn.integrableOn_compact
      (μ:=volume) isCompact_Icc
  have hGnonneg : ∀ u, 0 ≤ G u := by
    intro u
    dsimp [G, compactKernelField]
    exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
  have hholder := integral_cube_le_sqrt_mul_sqrt G hGmeas
    (hGpowInt 2 (by norm_num)) (hGpowInt 4 (by norm_num)) hGnonneg
  have hpow (p : ℕ) (hp : 0 < p) :
      (∫ u, G u ^ p) =
        ∫ u in Set.Icc lo hi,
          ‖GuthMaynardRatioKernelIdentity.pointMassFourierKernel W u‖ ^ p := by
    simpa only [G] using integral_compactKernelField_pow W lo hi p hp
  rw [hpow 2 (by norm_num), hpow 3 (by norm_num), hpow 4 (by norm_num)] at hholder
  have hsample := sum_ratioKernel_cube_le_logPacking_add_tail
    W P k hT hA hB hinterval hnumden hcross hcenter
  let C : ℝ :=
    (sourceBumpFourierConstant 1 zero_lt_one 0 * (3*T)) *
      ((⌊(8*Real.pi*(A/(3*T)))*B^2⌋₊+1:ℕ):ℝ)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (sourceBumpFourierConstant_nonneg 1 zero_lt_one 0)
        (mul_nonneg (by norm_num) hT.le))
      (Nat.cast_nonneg _)
  calc
    (∑ p ∈ P, ‖ratioDirichletKernel W
        ((p.1:ℝ)/(p.2:ℝ))‖^3) ≤
        C * (∫ u in Set.Icc lo hi,
          ‖pointMassFourierKernel W u‖^3) +
        (P.card:ℝ) * ((W.card:ℝ)^3 * (A^k)⁻¹ *
          ∫ xi : ℝ, |xi|^k *
            ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ,ℂ)) xi‖) := by
      simpa only [C, mul_assoc] using hsample
    _ ≤ C * (Real.sqrt (∫ u in Set.Icc lo hi,
          ‖pointMassFourierKernel W u‖^2) *
        Real.sqrt (∫ u in Set.Icc lo hi,
          ‖pointMassFourierKernel W u‖^4)) +
        (P.card:ℝ) * ((W.card:ℝ)^3 * (A^k)⁻¹ *
          ∫ xi : ℝ, |xi|^k *
            ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ,ℂ)) xi‖) := by
      gcongr
    _ = _ := by ring

end
end GuthMaynardLemma118

#print axioms GuthMaynardLemma118.half_abs_sub_le_abs_log_sub
#print axioms GuthMaynardLemma118.distinct_nat_fraction_logFrequency_separation
#print axioms GuthMaynardLemma118.sum_rational_logFrequency_samples_le_packing_mul_integral
#print axioms GuthMaynardLemma118.sum_ratioKernel_cube_le_logPacking_add_tail
#print axioms GuthMaynardLemma118.sum_ratioKernel_cube_le_logPacking_mul_sqrtMoments_add_tail
