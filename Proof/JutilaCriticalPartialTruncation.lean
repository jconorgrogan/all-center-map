import JutilaPrincipalResidueBound
import JutilaReflectedFunctionalEquationIntegrand
import HuxleyGammaExactNorm
import PrimitiveRootNumberNorm
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Critical-line truncation of Jutila's partial dual sum

After splitting the dual series in the proof of Jutila (1977), Lemma 1,
p. 58, the partial-sum contribution is moved to `Re(s+w)=1/2`.  Jutila
then cuts that integral at `|Im w|=h^2`.  This file certifies the exact
critical-line multiplier, the finite partial-sum bound, and the exponential
tail envelope used in that truncation.
-/

namespace JutilaCriticalPartialTruncation

open Complex Real MeasureTheory Set Filter Topology DirichletCharacter
open scoped BigOperators LSeries.notation
open JutilaTwoScaleSmoothing
open JutilaTwoScaleHorizontalDecay
open JutilaReflectedFunctionalEquationIntegrand
open JutilaPrimitiveFunctionalEquation
open MAPGammaCompactStripSharp

noncomputable section

variable {q : ℕ} [NeZero q]

def criticalPoint (u : ℝ) : ℂ := (1 / 2 : ℂ) + u * I

def reflectedDualMultiplier
    (chi : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  ((q : ℂ) ^ ((1 : ℂ) / 2 - z) * rootNumber chi) *
    (gammaFactor chi⁻¹ (1 - z) / gammaFactor chi z)

def dualPartialSum
    (chi : DirichletCharacter ℂ q) (z : ℂ) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.range M,
    LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - z) n

private theorem inv_even {chi : DirichletCharacter ℂ q} (hchi : chi.Even) :
    chi⁻¹.Even := by
  simpa only [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', inv_one] using
    congrArg (fun z : ℂ => z⁻¹) hchi

private theorem inv_odd {chi : DirichletCharacter ℂ q} (hchi : chi.Odd) :
    chi⁻¹.Odd := by
  simpa only [DirichletCharacter.Odd, MulChar.inv_apply_eq_inv', inv_neg,
    inv_one] using congrArg (fun z : ℂ => z⁻¹) hchi

theorem one_sub_criticalPoint_eq_conj (u : ℝ) :
    1 - criticalPoint u = starRingEnd ℂ (criticalPoint u) := by
  apply Complex.ext <;> simp [criticalPoint] <;> norm_num

/-- The parity-dependent archimedean quotient has exact norm one on the
critical line. -/
theorem norm_gammaFactor_quotient_criticalPoint_eq_one
    (chi : DirichletCharacter ℂ q) (u : ℝ) :
    ‖gammaFactor chi⁻¹ (1 - criticalPoint u) /
        gammaFactor chi (criticalPoint u)‖ = 1 := by
  have hzre : 0 < (criticalPoint u).re := by simp [criticalPoint]
  have hden : gammaFactor chi (criticalPoint u) ≠ 0 :=
    gammaFactor_ne_zero_of_re_pos chi hzre
  have hnormDen : ‖gammaFactor chi (criticalPoint u)‖ ≠ 0 := norm_ne_zero_iff.mpr hden
  have hconj := one_sub_criticalPoint_eq_conj u
  have hnorm : ‖gammaFactor chi⁻¹ (1 - criticalPoint u)‖ =
      ‖gammaFactor chi (criticalPoint u)‖ := by
    rcases chi.even_or_odd with heven | hodd
    · rw [(inv_even heven).gammaFactor_def, heven.gammaFactor_def, hconj]
      exact MAPHuxleyGammaExactNorm.norm_GammaR_conj (criticalPoint u)
    · rw [(inv_odd hodd).gammaFactor_def, hodd.gammaFactor_def, hconj]
      have hshift : starRingEnd ℂ (criticalPoint u) + 1 =
          starRingEnd ℂ (criticalPoint u + 1) := by simp
      rw [hshift]
      exact MAPHuxleyGammaExactNorm.norm_GammaR_conj (criticalPoint u + 1)
  rw [norm_div, hnorm, div_self hnormDen]

/-- The full primitive functional-equation multiplier has exact norm one on
the critical line. -/
theorem norm_reflectedDualMultiplier_criticalPoint_eq_one
    (chi : DirichletCharacter ℂ q) (hprim : chi.IsPrimitive) (u : ℝ) :
    ‖reflectedDualMultiplier chi (criticalPoint u)‖ = 1 := by
  unfold reflectedDualMultiplier
  rw [norm_mul, norm_mul,
    FixedCharacterPrimitiveRootNumber.primitive_rootNumber_norm_eq_one chi hprim,
    mul_one, norm_gammaFactor_quotient_criticalPoint_eq_one, mul_one]
  rw [Complex.norm_natCast_cpow_of_pos (NeZero.pos q)]
  simp [criticalPoint]

/-- Every finite dual partial sum is bounded by its literal number of terms
on the critical line. -/
theorem norm_dualPartialSum_criticalPoint_le
    (chi : DirichletCharacter ℂ q) (u : ℝ) (M : ℕ) :
    ‖dualPartialSum chi (criticalPoint u) M‖ ≤ M := by
  unfold dualPartialSum
  calc
    ‖∑ n ∈ Finset.range M,
        LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - criticalPoint u) n‖ ≤
      ∑ n ∈ Finset.range M,
        ‖LSeries.term (fun m : ℕ => chi⁻¹ m)
          (1 - criticalPoint u) n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range M, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [LSeries.norm_term_eq]
      split_ifs with hn0
      · norm_num
      · have hn1 : (1 : ℝ) ≤ n := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
        have hre : (1 - criticalPoint u).re = (1 / 2 : ℝ) := by
          simp [criticalPoint]
          norm_num
        rw [hre]
        have hden : 1 ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
          Real.one_le_rpow hn1 (by norm_num)
        exact (div_le_one (by positivity)).2
          ((chi⁻¹.norm_le_one (n : ZMod q)).trans hden)
    _ = M := by simp

def criticalPartialIntegrand
    (chi : DirichletCharacter ℂ q) (s : ℂ)
    (N h : ℝ) (M : ℕ) (v : ℝ) : ℂ :=
  let w : ℂ := ((1 / 2 - s.re : ℝ) : ℂ) + v * I
  let z : ℂ := s + w
  Complex.Gamma (1 + w / (h : ℂ)) *
    twoScaleRemovableQuotient N w *
      reflectedDualMultiplier chi z * dualPartialSum chi z M

/-- Exact pointwise critical-line bound before absorbing the linear Gamma
factor into half of its exponential. -/
theorem norm_criticalPartialIntegrand_le
    (chi : DirichletCharacter ℂ q) (hprim : chi.IsPrimitive)
    (s : ℂ) {N h : ℝ} (hN : 0 < N) (hh : 2 ≤ h)
    (hsigma0 : 0 ≤ s.re) (hsigma1 : s.re < 1)
    (M : ℕ) {v : ℝ} (hv : 1 ≤ |v|) :
    ‖criticalPartialIntegrand chi s N h M v‖ ≤
      12 * M * twoScaleCpowEndpointBound N (1 / 2 - s.re) (1 / 2 - s.re) *
        (1 + |v| / h) *
          Real.exp (-(Real.pi / 2) * (|v| / h)) := by
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num) hh
  let x : ℝ := 1 / 2 - s.re
  let w : ℂ := (x : ℂ) + v * I
  let z : ℂ := s + w
  have hz : z = criticalPoint (s.im + v) := by
    apply Complex.ext <;> simp [z, w, x, criticalPoint]
  have hxlo : -(h / 2) ≤ x := by dsimp [x]; nlinarith
  have hxhi : x ≤ h / 2 := by dsimp [x]; nlinarith
  have hGammaLo : (1 / 2 : ℝ) ≤ 1 + x / h := by
    have hxdiv : -(1 / 2 : ℝ) ≤ x / h := by
      apply (le_div_iff₀ hh0).2
      nlinarith
    linarith
  have hGammaHi : 1 + x / h ≤ (3 / 2 : ℝ) := by
    have hxdiv : x / h ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ hh0).2
      nlinarith
    linarith
  have hGammaPoint :
      1 + w / (h : ℂ) =
        GammaCompactStripScratch.stripPoint (1 + x / h) (v / h) := by
    apply Complex.ext <;> simp [w, GammaCompactStripScratch.stripPoint]
  have hGamma := norm_Gamma_positive_strip_le_exp_pi_half
    hGammaLo hGammaHi (t := v / h)
  rw [← hGammaPoint] at hGamma
  have habs : |v / h| = |v| / h := by rw [abs_div, abs_of_pos hh0]
  rw [habs] at hGamma
  have hQ := norm_twoScaleRemovableQuotient_horizontal_le
    hN (a := x) (b := x) (x := x) le_rfl le_rfl hv
  have hmult : ‖reflectedDualMultiplier chi z‖ = 1 := by
    rw [hz]
    exact norm_reflectedDualMultiplier_criticalPoint_eq_one chi hprim _
  have hpartial : ‖dualPartialSum chi z M‖ ≤ M := by
    rw [hz]
    exact norm_dualPartialSum_criticalPoint_le chi _ M
  have hQ0 : 0 ≤ twoScaleCpowEndpointBound N x x :=
    twoScaleCpowEndpointBound_nonneg hN _ _
  unfold criticalPartialIntegrand
  dsimp only
  change ‖Complex.Gamma (1 + w / (h : ℂ)) *
    twoScaleRemovableQuotient N w * reflectedDualMultiplier chi z *
      dualPartialSum chi z M‖ ≤ _
  repeat' rw [norm_mul]
  rw [hmult, mul_one]
  calc
    ‖Complex.Gamma (1 + w / (h : ℂ))‖ *
          ‖twoScaleRemovableQuotient N w‖ *
          ‖dualPartialSum chi z M‖ ≤
      (12 * (1 + |v| / h) *
          Real.exp (-(Real.pi / 2) * (|v| / h))) *
        twoScaleCpowEndpointBound N x x * M := by gcongr
    _ = 12 * M * twoScaleCpowEndpointBound N (1 / 2 - s.re)
        (1 / 2 - s.re) * (1 + |v| / h) *
          Real.exp (-(Real.pi / 2) * (|v| / h)) := by
      dsimp [x]
      ring

def criticalPartialTailEnvelope
    (N h : ℝ) (s : ℂ) (M : ℕ) (v : ℝ) : ℝ :=
  12 * M * twoScaleCpowEndpointBound N (1 / 2 - s.re) (1 / 2 - s.re) *
    Real.exp (-((Real.pi / 2 - 1) * (|v| / h)))

/-- The source integrand is dominated by a pure exponential tail. -/
theorem norm_criticalPartialIntegrand_le_tailEnvelope
    (chi : DirichletCharacter ℂ q) (hprim : chi.IsPrimitive)
    (s : ℂ) {N h : ℝ} (hN : 0 < N) (hh : 2 ≤ h)
    (hsigma0 : 0 ≤ s.re) (hsigma1 : s.re < 1)
    (M : ℕ) {v : ℝ} (hv : 1 ≤ |v|) :
    ‖criticalPartialIntegrand chi s N h M v‖ ≤
      criticalPartialTailEnvelope N h s M v := by
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num) hh
  have hu0 : 0 ≤ |v| / h := div_nonneg (abs_nonneg _) hh0.le
  have hone := Real.add_one_le_exp (|v| / h)
  have hraw := norm_criticalPartialIntegrand_le
    chi hprim s hN hh hsigma0 hsigma1 M hv
  have hK0 : 0 ≤ 12 * (M : ℝ) *
      twoScaleCpowEndpointBound N (1 / 2 - s.re) (1 / 2 - s.re) := by
    exact mul_nonneg (by positivity)
      (twoScaleCpowEndpointBound_nonneg hN _ _)
  calc
    ‖criticalPartialIntegrand chi s N h M v‖ ≤
      12 * M * twoScaleCpowEndpointBound N (1 / 2 - s.re) (1 / 2 - s.re) *
        (1 + |v| / h) *
          Real.exp (-(Real.pi / 2) * (|v| / h)) := hraw
    _ ≤ 12 * M * twoScaleCpowEndpointBound N (1 / 2 - s.re) (1 / 2 - s.re) *
        Real.exp (|v| / h) *
          Real.exp (-(Real.pi / 2) * (|v| / h)) := by
      gcongr
      simpa [add_comm] using hone
    _ = criticalPartialTailEnvelope N h s M v := by
      unfold criticalPartialTailEnvelope
      have hExp : Real.exp (|v| / h) *
          Real.exp (-(Real.pi / 2) * (|v| / h)) =
          Real.exp (-((Real.pi / 2 - 1) * (|v| / h))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        12 * (M : ℝ) *
              twoScaleCpowEndpointBound N (1 / 2 - s.re) (1 / 2 - s.re) *
              Real.exp (|v| / h) *
              Real.exp (-(Real.pi / 2) * (|v| / h)) =
            (12 * (M : ℝ) *
              twoScaleCpowEndpointBound N (1 / 2 - s.re) (1 / 2 - s.re)) *
              (Real.exp (|v| / h) *
                Real.exp (-(Real.pi / 2) * (|v| / h))) := by ring
        _ = (12 * (M : ℝ) *
              twoScaleCpowEndpointBound N (1 / 2 - s.re) (1 / 2 - s.re)) *
              Real.exp (-((Real.pi / 2 - 1) * (|v| / h))) := by rw [hExp]

/-- Exact mass of the pure exponential upper-tail envelope. -/
theorem integral_Ioi_criticalPartialTailEnvelope
    {N h R : ℝ} (s : ℂ) (M : ℕ) (hh : 0 < h) (hR : 0 ≤ R) :
    (∫ v : ℝ in Set.Ioi R, criticalPartialTailEnvelope N h s M v) =
      (12 * M * twoScaleCpowEndpointBound N (1 / 2 - s.re) (1 / 2 - s.re)) *
        (h / (Real.pi / 2 - 1)) *
          Real.exp (-((Real.pi / 2 - 1) * (R / h))) := by
  let d : ℝ := Real.pi / 2 - 1
  have hd : 0 < d := by dsimp [d]; nlinarith [Real.pi_gt_three]
  have ha : -(d / h) < 0 := neg_neg_of_pos (div_pos hd hh)
  have habs : ∀ᵐ v : ℝ ∂volume.restrict (Set.Ioi R), |v| = v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [abs_of_nonneg (hR.trans hv.le)]
  rw [show (∫ v : ℝ in Set.Ioi R, criticalPartialTailEnvelope N h s M v) =
      (12 * M * twoScaleCpowEndpointBound N (1 / 2 - s.re) (1 / 2 - s.re)) *
        ∫ v : ℝ in Set.Ioi R, Real.exp (-(d / h) * v) by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [habs] with v hv
    unfold criticalPartialTailEnvelope
    rw [hv]
    congr 2
    dsimp [d]
    ring]
  rw [integral_exp_mul_Ioi ha R]
  dsimp [d]
  field_simp
  <;> ring

/-- Quantitative upper-tail truncation of the *actual* critical-line partial
integrand. -/
theorem norm_integral_Ioi_criticalPartialIntegrand_le
    (chi : DirichletCharacter ℂ q) (hprim : chi.IsPrimitive)
    (s : ℂ) {N h R : ℝ} (hN : 0 < N) (hh : 2 ≤ h)
    (hsigma0 : 0 ≤ s.re) (hsigma1 : s.re < 1)
    (M : ℕ) (hR : 1 ≤ R) :
    ‖∫ v : ℝ in Set.Ioi R, criticalPartialIntegrand chi s N h M v‖ ≤
      (12 * M * twoScaleCpowEndpointBound N (1 / 2 - s.re) (1 / 2 - s.re)) *
        (h / (Real.pi / 2 - 1)) *
          Real.exp (-((Real.pi / 2 - 1) * (R / h))) := by
  let d : ℝ := Real.pi / 2 - 1
  let K : ℝ := 12 * M *
    twoScaleCpowEndpointBound N (1 / 2 - s.re) (1 / 2 - s.re)
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num) hh
  have hd : 0 < d := by dsimp [d]; nlinarith [Real.pi_gt_three]
  have ha : -(d / h) < 0 := neg_neg_of_pos (div_pos hd hh0)
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hExp : IntegrableOn (fun v : ℝ => Real.exp (-(d / h) * v))
      (Set.Ioi R) := integrableOn_exp_mul_Ioi ha R
  have hMajorRaw : IntegrableOn (fun v : ℝ => K * Real.exp (-(d / h) * v))
      (Set.Ioi R) := hExp.const_mul K
  have hMajor : Integrable
      (criticalPartialTailEnvelope N h s M) (volume.restrict (Set.Ioi R)) := by
    apply hMajorRaw.congr_fun
    · intro v hv
      have hv0 : 0 ≤ v := hR0.trans hv.le
      unfold criticalPartialTailEnvelope
      rw [abs_of_nonneg hv0]
      dsimp [K, d]
      congr 2
      ring
    · exact measurableSet_Ioi
  calc
    ‖∫ v : ℝ in Set.Ioi R, criticalPartialIntegrand chi s N h M v‖ ≤
        ∫ v : ℝ in Set.Ioi R, criticalPartialTailEnvelope N h s M v := by
      apply norm_integral_le_of_norm_le hMajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      apply norm_criticalPartialIntegrand_le_tailEnvelope
        chi hprim s hN hh hsigma0 hsigma1 M
      have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) (hR.trans hv.le)
      rw [abs_of_pos hv0]
      exact hR.trans hv.le
    _ = (12 * M *
          twoScaleCpowEndpointBound N (1 / 2 - s.re) (1 / 2 - s.re)) *
        (h / (Real.pi / 2 - 1)) *
          Real.exp (-((Real.pi / 2 - 1) * (R / h))) :=
      integral_Ioi_criticalPartialTailEnvelope s M hh0 hR0

/-- Matching lower-tail truncation, by the exact reflection `v ↦ -v`. -/
theorem norm_integral_Iic_criticalPartialIntegrand_le
    (chi : DirichletCharacter ℂ q) (hprim : chi.IsPrimitive)
    (s : ℂ) {N h R : ℝ} (hN : 0 < N) (hh : 2 ≤ h)
    (hsigma0 : 0 ≤ s.re) (hsigma1 : s.re < 1)
    (M : ℕ) (hR : 1 ≤ R) :
    ‖∫ v : ℝ in Set.Iic (-R), criticalPartialIntegrand chi s N h M v‖ ≤
      (12 * M * twoScaleCpowEndpointBound N (1 / 2 - s.re) (1 / 2 - s.re)) *
        (h / (Real.pi / 2 - 1)) *
          Real.exp (-((Real.pi / 2 - 1) * (R / h))) := by
  rw [← integral_comp_neg_Ioi]
  let F : ℝ → ℂ := fun v => criticalPartialIntegrand chi s N h M (-v)
  let E : ℝ → ℝ := fun v => criticalPartialTailEnvelope N h s M v
  -- The positive-tail proof applies verbatim because the envelope is even.
  let d : ℝ := Real.pi / 2 - 1
  let K : ℝ := 12 * M *
    twoScaleCpowEndpointBound N (1 / 2 - s.re) (1 / 2 - s.re)
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num) hh
  have hd : 0 < d := by dsimp [d]; nlinarith [Real.pi_gt_three]
  have ha : -(d / h) < 0 := neg_neg_of_pos (div_pos hd hh0)
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hExp : IntegrableOn (fun v : ℝ => Real.exp (-(d / h) * v))
      (Set.Ioi R) := integrableOn_exp_mul_Ioi ha R
  have hMajorRaw : IntegrableOn (fun v : ℝ => K * Real.exp (-(d / h) * v))
      (Set.Ioi R) := hExp.const_mul K
  have hMajor : Integrable E (volume.restrict (Set.Ioi R)) := by
    apply hMajorRaw.congr_fun
    · intro v hv
      have hv0 : 0 ≤ v := hR0.trans hv.le
      dsimp [E]
      unfold criticalPartialTailEnvelope
      rw [abs_of_nonneg hv0]
      dsimp [K, d]
      congr 2
      ring
    · exact measurableSet_Ioi
  calc
    ‖∫ v : ℝ in Set.Ioi R, F v‖ ≤ ∫ v : ℝ in Set.Ioi R, E v := by
      apply norm_integral_le_of_norm_le hMajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      dsimp [F, E]
      have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) (hR.trans hv.le)
      have hvabs : 1 ≤ |-v| := by
        rw [abs_neg, abs_of_pos hv0]
        exact hR.trans hv.le
      have hbound := norm_criticalPartialIntegrand_le_tailEnvelope
        chi hprim s hN hh hsigma0 hsigma1 M
        (v := -v) hvabs
      have henvEven : criticalPartialTailEnvelope N h s M (-v) =
          criticalPartialTailEnvelope N h s M v := by
        unfold criticalPartialTailEnvelope
        rw [abs_neg]
      exact hbound.trans_eq henvEven
    _ = (12 * M *
          twoScaleCpowEndpointBound N (1 / 2 - s.re) (1 / 2 - s.re)) *
        (h / (Real.pi / 2 - 1)) *
          Real.exp (-((Real.pi / 2 - 1) * (R / h))) := by
      dsimp [E]
      exact integral_Ioi_criticalPartialTailEnvelope s M hh0 hR0

/-- The total discarded contribution at the literal source cutoff
`|Im w| = h²`. -/
theorem norm_twoSided_criticalPartial_cut_h_sq_le
    (chi : DirichletCharacter ℂ q) (hprim : chi.IsPrimitive)
    (s : ℂ) {N h : ℝ} (hN : 0 < N) (hh : 2 ≤ h)
    (hsigma0 : 0 ≤ s.re) (hsigma1 : s.re < 1)
    (M : ℕ) :
    ‖(∫ v : ℝ in Set.Iic (-(h ^ 2)),
          criticalPartialIntegrand chi s N h M v) +
        ∫ v : ℝ in Set.Ioi (h ^ 2),
          criticalPartialIntegrand chi s N h M v‖ ≤
      2 * ((12 * M *
          twoScaleCpowEndpointBound N (1 / 2 - s.re) (1 / 2 - s.re)) *
        (h / (Real.pi / 2 - 1)) *
          Real.exp (-((Real.pi / 2 - 1) * h))) := by
  have hR : 1 ≤ h ^ 2 := by nlinarith [sq_nonneg (h - 2)]
  have hneg := norm_integral_Iic_criticalPartialIntegrand_le
    chi hprim s hN hh hsigma0 hsigma1 M hR
  have hpos := norm_integral_Ioi_criticalPartialIntegrand_le
    chi hprim s hN hh hsigma0 hsigma1 M hR
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num) hh
  have hsimplify : h ^ 2 / h = h := by
    field_simp [hh0.ne']
  rw [hsimplify] at hneg hpos
  exact (norm_add_le _ _).trans (by linarith)

theorem twoScaleCpowEndpointBound_critical_le_three_mul
    {N Q x : ℝ} (hN : 1 ≤ N) (hNQ : N ≤ Q) (hx : x ≤ 1) :
    twoScaleCpowEndpointBound N x x ≤ 3 * Q := by
  have h2N : 1 ≤ 2 * N := by nlinarith
  have h2pow : (2 * N) ^ x ≤ 2 * N := by
    calc
      (2 * N) ^ x ≤ (2 * N) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h2N hx
      _ = 2 * N := Real.rpow_one _
  have hNpow : N ^ x ≤ N := by
    calc
      N ^ x ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN hx
      _ = N := Real.rpow_one _
  unfold twoScaleCpowEndpointBound
  rw [max_self, max_self]
  nlinarith

/-- With Jutila's literal size conditions `M ≤ (qT)^2`, `N ≤ qT`, and
`h=log^2(qT)`, the discarded critical-line tail is strictly smaller than
one.  The explicit threshold `log(qT) ≥ 3888` is deliberately crude; it
formalizes the source phrase "qT sufficiently large" without hiding a
constant. -/
theorem norm_twoSided_criticalPartial_cut_h_sq_lt_one_sourceRange
    (chi : DirichletCharacter ℂ q) (hprim : chi.IsPrimitive)
    (s : ℂ) {N Q ell h : ℝ} (hN : 1 ≤ N) (hNQ : N ≤ Q)
    (hQ : Q = Real.exp ell) (hh : h = ell ^ 2) (hL : 3888 ≤ ell)
    (hsigma0 : 0 ≤ s.re) (hsigma1 : s.re < 1)
    (M : ℕ) (hM : (M : ℝ) ≤ Q ^ 2) :
    ‖(∫ v : ℝ in Set.Iic (-(h ^ 2)),
          criticalPartialIntegrand chi s N h M v) +
        ∫ v : ℝ in Set.Ioi (h ^ 2),
          criticalPartialIntegrand chi s N h M v‖ < 1 := by
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hh2 : 2 ≤ h := by rw [hh]; nlinarith
  have hraw := norm_twoSided_criticalPartial_cut_h_sq_le
    chi hprim s hN0 hh2 hsigma0 hsigma1 M
  let x : ℝ := 1 / 2 - s.re
  have hx : x ≤ 1 := by dsimp [x]; linarith
  have hB := twoScaleCpowEndpointBound_critical_le_three_mul hN hNQ hx
  have hQ0 : 0 < Q := by rw [hQ]; exact Real.exp_pos ell
  let d : ℝ := Real.pi / 2 - 1
  have hdHalf : (1 / 2 : ℝ) < d := by
    dsimp [d]
    nlinarith [Real.pi_gt_three]
  have hd : 0 < d := lt_trans (by norm_num) hdHalf
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num) hh2
  have hhdiv : h / d ≤ 2 * h := by
    apply (div_le_iff₀ hd).2
    nlinarith
  have hexp : Real.exp (-d * h) ≤ Real.exp (-(h / 2)) := by
    exact Real.exp_monotone (by nlinarith)
  have hcoarse :
      2 * ((12 * (M : ℝ) *
          twoScaleCpowEndpointBound N x x) *
        (h / d) * Real.exp (-(d * h))) ≤
      144 * Q ^ 3 * h * Real.exp (-(h / 2)) := by
    have hB0 : 0 ≤ twoScaleCpowEndpointBound N x x :=
      twoScaleCpowEndpointBound_nonneg hN0 _ _
    have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    have hQnonneg : 0 ≤ Q := hQ0.le
    calc
      2 * ((12 * (M : ℝ) * twoScaleCpowEndpointBound N x x) *
            (h / d) * Real.exp (-(d * h))) ≤
          2 * ((12 * Q ^ 2 * (3 * Q)) *
            (2 * h) * Real.exp (-(h / 2))) := by
        gcongr
        nlinarith [hdHalf, hh0]
      _ = 144 * Q ^ 3 * h * Real.exp (-(h / 2)) := by ring
  have hL0 : 0 ≤ ell := by linarith
  have hLdiv : 0 ≤ ell / 3 := by positivity
  have hlinExp : ell / 3 ≤ Real.exp (ell / 3) := by
    exact (by linarith [Real.add_one_le_exp (ell / 3)])
  have hcube : (ell / 3) ^ 3 ≤ Real.exp ell := by
    calc
      (ell / 3) ^ 3 ≤ (Real.exp (ell / 3)) ^ 3 :=
        pow_le_pow_left₀ hLdiv hlinExp 3
      _ = Real.exp ell := by
        rw [show (Real.exp (ell / 3)) ^ 3 =
            Real.exp (ell / 3) * Real.exp (ell / 3) * Real.exp (ell / 3) by ring,
          ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hpoly : 144 * ell ^ 2 ≤ Real.exp ell := by
    calc
      144 * ell ^ 2 ≤ (ell / 3) ^ 3 := by
        have : 3888 * ell ^ 2 ≤ ell * ell ^ 2 :=
          mul_le_mul_of_nonneg_right hL (sq_nonneg ell)
        nlinarith
      _ ≤ Real.exp ell := hcube
  have hrewrite :
      144 * Q ^ 3 * h * Real.exp (-(h / 2)) =
        (144 * ell ^ 2) * Real.exp (3 * ell) * Real.exp (-(ell ^ 2 / 2)) := by
    rw [hQ, hh, ← Real.exp_nat_mul]
    ring
  have hfinalExp :
      Real.exp ell * Real.exp (3 * ell) * Real.exp (-(ell ^ 2 / 2)) =
        Real.exp (4 * ell - ell ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hnegative : 4 * ell - ell ^ 2 / 2 < 0 := by nlinarith
  calc
    ‖(∫ v : ℝ in Set.Iic (-(h ^ 2)),
          criticalPartialIntegrand chi s N h M v) +
        ∫ v : ℝ in Set.Ioi (h ^ 2),
          criticalPartialIntegrand chi s N h M v‖ ≤
      2 * ((12 * M *
          twoScaleCpowEndpointBound N (1 / 2 - s.re) (1 / 2 - s.re)) *
        (h / (Real.pi / 2 - 1)) *
          Real.exp (-((Real.pi / 2 - 1) * h))) := hraw
    _ ≤ 144 * Q ^ 3 * h * Real.exp (-(h / 2)) := by
      simpa [x, d] using hcoarse
    _ = (144 * ell ^ 2) * Real.exp (3 * ell) *
          Real.exp (-(ell ^ 2 / 2)) := hrewrite
    _ ≤ Real.exp ell * Real.exp (3 * ell) *
          Real.exp (-(ell ^ 2 / 2)) := by gcongr
    _ = Real.exp (4 * ell - ell ^ 2 / 2) := hfinalExp
    _ < 1 := Real.exp_lt_one_iff.mpr hnegative

end

end JutilaCriticalPartialTruncation

#print axioms JutilaCriticalPartialTruncation.norm_gammaFactor_quotient_criticalPoint_eq_one
#print axioms JutilaCriticalPartialTruncation.norm_reflectedDualMultiplier_criticalPoint_eq_one
#print axioms JutilaCriticalPartialTruncation.norm_dualPartialSum_criticalPoint_le
#print axioms JutilaCriticalPartialTruncation.norm_criticalPartialIntegrand_le_tailEnvelope
#print axioms JutilaCriticalPartialTruncation.integral_Ioi_criticalPartialTailEnvelope
#print axioms JutilaCriticalPartialTruncation.norm_integral_Ioi_criticalPartialIntegrand_le
#print axioms JutilaCriticalPartialTruncation.norm_integral_Iic_criticalPartialIntegrand_le
#print axioms JutilaCriticalPartialTruncation.norm_twoSided_criticalPartial_cut_h_sq_le
#print axioms JutilaCriticalPartialTruncation.norm_twoSided_criticalPartial_cut_h_sq_lt_one_sourceRange
