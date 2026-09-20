import RamachandraShiftedHeadFiniteContour
import RamachandraFunctionalFactorEnvelope
import RamachandraShiftedGammaPoleContour

/-!
# Quantitative tails for the shifted reflected-head contour

The functional-equation multiplier has only polynomial vertical growth on
the head-deformation strip.  Combined with the exact finiteness of the head
and exponential Gamma decay, this makes both horizontal edges vanish.
-/

namespace RamachandraShiftedHeadContourTails

open Complex MeasureTheory Set Filter
open scoped BigOperators LSeries.notation Interval Topology
open BHPRamachandraMeanValueFromDyadicAFE
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedCoefficientEnergy
open RamachandraShiftedHeadFiniteContour
open RamachandraFunctionalFactorEnvelope
open RamachandraShiftedGammaPoleContour
open CGLProofDAG
open FinitePoleRectangle

noncomputable section

set_option maxHeartbeats 800000

/-- A reflected coefficient on `Re z ≤ 1` is bounded by the elementary
majorant `n`.  This intentionally crude bound is used only to certify
horizontal decay of a fixed finite polynomial. -/
theorem norm_ramachandraReflectedTerm_le_nat
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : z.re ≤ 1) :
    ‖ramachandraReflectedTerm psi z n‖ ≤ (n : ℝ) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold ramachandraReflectedTerm
  rw [LSeries.term_of_ne_zero hn0, norm_div,
    Complex.norm_natCast_cpow_of_pos hn]
  have hden : 1 ≤ (n : ℝ) ^ (1 - z).re := by
    apply Real.one_le_rpow hn1
    simp only [sub_re, one_re]
    linarith
  have hdenPos : 0 < (n : ℝ) ^ (1 - z).re :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  have hnum : ‖ramachandraDivisorCoeff psi⁻¹ n‖ ≤ (n : ℝ) := by
    unfold ramachandraDivisorCoeff
    rw [norm_mul]
    rw [show ‖(orderedDivisorCount 2 n : ℂ)‖ =
        (orderedDivisorCount 2 n : ℝ) by exact Complex.norm_natCast _]
    have hchi := psi⁻¹.norm_le_one (n : ZMod d)
    have hdivNat := orderedDivisorCount_two_le_self hn
    have hdiv : (orderedDivisorCount 2 n : ℝ) ≤ n := by
      exact_mod_cast hdivNat
    calc
      ‖psi⁻¹ (n : ZMod d)‖ * (orderedDivisorCount 2 n : ℝ) ≤
          1 * (n : ℝ) := by gcongr
      _ = (n : ℝ) := one_mul _
  apply (div_le_iff₀ hdenPos).2
  calc
    ‖ramachandraDivisorCoeff psi⁻¹ n‖ ≤ (n : ℝ) := hnum
    _ ≤ (n : ℝ) * (n : ℝ) ^ (1 - z).re := by
      exact le_mul_of_one_le_right (Nat.cast_nonneg n) hden

/-- Uniform elementary norm bound for the entire finite head. -/
theorem norm_ramachandraReflectedHead_le_floor_sq
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    {X : ℝ} (hX : 0 ≤ X) {z : ℂ} (hz : z.re ≤ 1) :
    ‖ramachandraReflectedHead psi X z‖ ≤
      ((⌊X⌋₊ + 1 : ℕ) : ℝ) ^ 2 := by
  rw [ramachandraReflectedHead_eq_finset psi hX z]
  let K : ℕ := ⌊X⌋₊ + 1
  calc
    ‖∑ n ∈ Finset.range K, ramachandraReflectedTerm psi z n‖ ≤
        ∑ n ∈ Finset.range K, ‖ramachandraReflectedTerm psi z n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range K, (n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hnmem
      by_cases hn0 : n = 0
      · subst n
        simp [ramachandraReflectedTerm, LSeries.term_zero]
      · exact norm_ramachandraReflectedTerm_le_nat psi
          (Nat.pos_of_ne_zero hn0) hz
    _ ≤ ∑ _n ∈ Finset.range K, (K : ℝ) := by
      apply Finset.sum_le_sum
      intro n hnmem
      exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hnmem))
    _ = (K : ℝ) * K := by simp
    _ = (((⌊X⌋₊ + 1 : ℕ) : ℝ) ^ 2) := by
      dsimp [K]
      ring

/-- Explicit horizontal-edge envelope for the finite head. -/
def shiftedHeadHorizontalEnvelope
    (d : ℕ) (s : ℂ) (X a b B : ℝ) : ℝ :=
  248832 * Real.rpow (d : ℝ) (3 / 2) *
    ((⌊X⌋₊ + 1 : ℕ) : ℝ) ^ 2 *
      (1 + |s.im| + B) ^ 6 * (1 + B) ^ 2 * Real.exp (-B) *
        max (X ^ a) (X ^ b)

/-- Pointwise head-integrand bound on a high horizontal edge. -/
theorem norm_shiftedHeadIntegrand_horizontal_le
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hprim : psi.IsPrimitive) (s : ℂ)
    {X a b x B : ℝ} (hX : 0 < X) (hab : a ≤ x) (hxb : x ≤ b)
    (haLo : -(3 / 2 : ℝ) ≤ a) (hbHi : b ≤ 2)
    (hzlo : -(1 / 4 : ℝ) ≤ s.re + a)
    (hzhi : s.re + b ≤ 1 / 2)
    (hB : 2 + |s.im| ≤ |B|) (hB1 : 1 ≤ |B|) :
    ‖shiftedHeadIntegrand psi s X ((x : ℂ) + B * I)‖ ≤
      248832 * Real.rpow (d : ℝ) (3 / 2) *
        ((⌊X⌋₊ + 1 : ℕ) : ℝ) ^ 2 *
          (1 + |s.im| + |B|) ^ 6 * (1 + |B|) ^ 2 *
            Real.exp (-|B|) * max (X ^ a) (X ^ b) := by
  let z : ℂ := s + ((x : ℂ) + B * I)
  have hzre : z.re = s.re + x := by simp [z]
  have hzim : z.im = s.im + B := by simp [z]
  have hzlo' : -(1 / 4 : ℝ) ≤ z.re := by rw [hzre]; linarith
  have hzhi' : z.re ≤ 1 / 2 := by rw [hzre]; linarith
  have hzim2 : 2 ≤ |z.im| := by
    rw [hzim]
    have hrev := abs_sub_abs_le_abs_sub B (-s.im)
    rw [abs_neg, sub_neg_eq_add] at hrev
    have hrev' : |B| - |s.im| ≤ |s.im + B| := by
      simpa [add_comm] using hrev
    linarith
  have hfactor := norm_ramachandraFunctionalFactor_le
    psi hprim hzlo' hzhi' hzim2
  have hhead := norm_ramachandraReflectedHead_le_floor_sq
    psi hX.le (z := z) (by linarith)
  have hgamma := norm_Gamma_ramachandraHorizontalStrip_le_exp
    (a := x) (t := B) (by linarith) (by linarith) hB1
  have hscale := norm_posReal_cpow_horizontal_le_max hX hab hxb (t := B)
  have hshiftAbs : |z.im| ≤ |s.im| + |B| := by
    rw [hzim]
    exact abs_add_le _ _
  have hpoly : (1 + |z.im|) ^ 6 ≤
      (1 + |s.im| + |B|) ^ 6 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hfactorSq :
      (Real.rpow (d : ℝ) (3 / 4) *
          (144 * (1 + |z.im|) ^ 3)) ^ 2 ≤
        (Real.rpow (d : ℝ) (3 / 4) * 144) ^ 2 *
          (1 + |s.im| + |B|) ^ 6 := by
    calc
      (Real.rpow (d : ℝ) (3 / 4) *
          (144 * (1 + |z.im|) ^ 3)) ^ 2 =
        (Real.rpow (d : ℝ) (3 / 4) * 144) ^ 2 *
          (1 + |z.im|) ^ 6 := by ring
      _ ≤ (Real.rpow (d : ℝ) (3 / 4) * 144) ^ 2 *
          (1 + |s.im| + |B|) ^ 6 :=
        mul_le_mul_of_nonneg_left hpoly (sq_nonneg _)
  unfold shiftedHeadIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_pow]
  calc
    ‖ramachandraFunctionalFactor psi z‖ ^ 2 *
          ‖ramachandraReflectedHead psi X z‖ *
          ‖Complex.Gamma ((x : ℂ) + B * I)‖ *
          ‖(X : ℂ) ^ ((x : ℂ) + B * I)‖ ≤
        (Real.rpow (d : ℝ) (3 / 4) *
            (144 * (1 + |z.im|) ^ 3)) ^ 2 *
          (((⌊X⌋₊ + 1 : ℕ) : ℝ) ^ 2) *
          (12 * (1 + |B|) ^ 2 * Real.exp (-|B|)) *
          max (X ^ a) (X ^ b) := by gcongr
    _ ≤ (Real.rpow (d : ℝ) (3 / 4) * 144) ^ 2 *
          (1 + |s.im| + |B|) ^ 6 *
          (((⌊X⌋₊ + 1 : ℕ) : ℝ) ^ 2) *
          (12 * (1 + |B|) ^ 2 * Real.exp (-|B|)) *
          max (X ^ a) (X ^ b) := by
      gcongr
    _ = 248832 * Real.rpow (d : ℝ) (3 / 2) *
        ((⌊X⌋₊ + 1 : ℕ) : ℝ) ^ 2 *
          (1 + |s.im| + |B|) ^ 6 * (1 + |B|) ^ 2 *
            Real.exp (-|B|) * max (X ^ a) (X ^ b) := by
      have hd : (Real.rpow (d : ℝ) (3 / 4)) ^ 2 =
          Real.rpow (d : ℝ) (3 / 2) := by
        calc
          (Real.rpow (d : ℝ) (3 / 4)) ^ 2 =
              Real.rpow (Real.rpow (d : ℝ) (3 / 4)) (2 : ℝ) := by
            exact (Real.rpow_natCast (Real.rpow (d : ℝ) (3 / 4)) 2).symm
          _ = Real.rpow (d : ℝ) ((3 / 4 : ℝ) * 2) := by
            exact (Real.rpow_mul (Nat.cast_nonneg d) (3 / 4 : ℝ) 2).symm
          _ = Real.rpow (d : ℝ) (3 / 2) := by norm_num
      have hconst : (144 : ℝ) ^ 2 * 12 = 248832 := by norm_num
      rw [show (Real.rpow (d : ℝ) (3 / 4) * 144) ^ 2 =
          (Real.rpow (d : ℝ) (3 / 4)) ^ 2 * 144 ^ 2 by ring, hd]
      rw [← hconst]
      ring

/-- The explicit head-edge envelope tends to zero. -/
theorem tendsto_shiftedHeadHorizontalEnvelope_zero
    (d : ℕ) (s : ℂ) {X : ℝ} (hX : 0 < X) (a b : ℝ) :
    Tendsto (shiftedHeadHorizontalEnvelope d s X a b) atTop (𝓝 0) := by
  let C : ℝ := 1 + |s.im|
  let K : ℝ := 248832 * Real.rpow (d : ℝ) (3 / 2) *
    (((⌊X⌋₊ + 1 : ℕ) : ℝ) ^ 2) * max (X ^ a) (X ^ b)
  let G : ℝ → ℝ := fun B =>
    K * Real.exp C * ((B + C) ^ 8 * Real.exp (-(B + C)))
  have hshift : Tendsto (fun B : ℝ => B + C) atTop atTop :=
    tendsto_atTop_add_const_right atTop C tendsto_id
  have hpoly : Tendsto (fun B : ℝ =>
      (B + C) ^ 8 * Real.exp (-(B + C))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 8).comp hshift
  have hG : Tendsto G atTop (𝓝 0) := by
    simpa [G] using hpoly.const_mul (K * Real.exp C)
  apply squeeze_zero' (g := G)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    unfold shiftedHeadHorizontalEnvelope
    have hd0 : 0 ≤ Real.rpow (d : ℝ) (3 / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg d) _
    have hmax : 0 ≤ max (X ^ a) (X ^ b) :=
      le_max_of_le_left (Real.rpow_nonneg hX.le _)
    positivity
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    have hC : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg s.im]
    have hone : 1 + B ≤ B + C := by linarith
    have h6 : (1 + |s.im| + B) ^ 6 = (B + C) ^ 6 := by
      congr 1
      dsimp [C]
      ring
    have h2 : (1 + B) ^ 2 ≤ (B + C) ^ 2 := by gcongr
    have h8 : (1 + |s.im| + B) ^ 6 * (1 + B) ^ 2 ≤
        (B + C) ^ 8 := by
      rw [h6]
      calc
        (B + C) ^ 6 * (1 + B) ^ 2 ≤
            (B + C) ^ 6 * (B + C) ^ 2 := by gcongr
        _ = (B + C) ^ 8 := by ring
    have hrewrite : Real.exp C * Real.exp (-(B + C)) =
        Real.exp (-B) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hK : 0 ≤ K := by dsimp [K]; positivity
    calc
      shiftedHeadHorizontalEnvelope d s X a b B =
          K * ((1 + |s.im| + B) ^ 6 * (1 + B) ^ 2 *
            Real.exp (-B)) := by
        dsimp [shiftedHeadHorizontalEnvelope, K]
        ring
      _ ≤ K * ((B + C) ^ 8 * Real.exp (-B)) := by
        gcongr
      _ = G B := by
        rw [← hrewrite]
        dsimp [G]
        ring
  · exact hG

theorem tendsto_shiftedHead_upperHorizontal_zero
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hprim : psi.IsPrimitive) (s : ℂ)
    {X a b : ℝ} (hX : 0 < X) (hab : a ≤ b)
    (haLo : -(3 / 2 : ℝ) ≤ a) (hbHi : b ≤ 2)
    (hzlo : -(1 / 4 : ℝ) ≤ s.re + a)
    (hzhi : s.re + b ≤ 1 / 2) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in a..b, shiftedHeadIntegrand psi s X ((x : ℂ) + B * I))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have henv :=
    (tendsto_shiftedHeadHorizontalEnvelope_zero d s hX a b).mul_const
      |b - a|
  apply squeeze_zero'
    (g := fun B => shiftedHeadHorizontalEnvelope d s X a b B * |b - a|)
  · exact Filter.Eventually.of_forall fun B => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (2 + |s.im|)] with B hB
    have hB0 : 0 ≤ B := by linarith [abs_nonneg s.im]
    have hBabs : 2 + |s.im| ≤ |B| := by
      simpa [abs_of_nonneg hB0] using hB
    have hBabs1 : 1 ≤ |B| := by
      rw [abs_of_nonneg hB0]
      linarith [abs_nonneg s.im]
    apply MAPAppendixA4Detector.horizontal_segment_norm_le
      (shiftedHeadIntegrand psi s X)
      (B := B) (M := shiftedHeadHorizontalEnvelope d s X a b B)
    intro x hx
    have hx' : x ∈ Set.Ioc a b := by
      simpa [Set.uIoc_of_le hab] using hx
    have hpoint := norm_shiftedHeadIntegrand_horizontal_le
      psi hprim s hX hx'.1.le hx'.2 haLo hbHi hzlo hzhi
        hBabs hBabs1
    simpa [shiftedHeadHorizontalEnvelope,
      abs_of_nonneg hB0] using hpoint
  · simpa only [zero_mul] using henv

theorem tendsto_shiftedHead_lowerHorizontal_zero
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hprim : psi.IsPrimitive) (s : ℂ)
    {X a b : ℝ} (hX : 0 < X) (hab : a ≤ b)
    (haLo : -(3 / 2 : ℝ) ≤ a) (hbHi : b ≤ 2)
    (hzlo : -(1 / 4 : ℝ) ≤ s.re + a)
    (hzhi : s.re + b ≤ 1 / 2) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in a..b, shiftedHeadIntegrand psi s X ((x : ℂ) - B * I))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have henv :=
    (tendsto_shiftedHeadHorizontalEnvelope_zero d s hX a b).mul_const
      |b - a|
  apply squeeze_zero'
    (g := fun B => shiftedHeadHorizontalEnvelope d s X a b B * |b - a|)
  · exact Filter.Eventually.of_forall fun B => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (2 + |s.im|)] with B hB
    have hB0 : 0 ≤ B := by linarith [abs_nonneg s.im]
    have hBabs : 2 + |s.im| ≤ |B| := by
      simpa [abs_of_nonneg hB0] using hB
    have hBabs1 : 1 ≤ |B| := by
      rw [abs_of_nonneg hB0]
      linarith [abs_nonneg s.im]
    simpa [sub_eq_add_neg, shiftedHeadHorizontalEnvelope,
      abs_of_nonneg hB0] using
      (MAPAppendixA4Detector.horizontal_segment_norm_le
        (shiftedHeadIntegrand psi s X)
        (B := -B) (M := shiftedHeadHorizontalEnvelope d s X a b B)
        (fun x hx => by
          have hx' : x ∈ Set.Ioc a b := by
            simpa [Set.uIoc_of_le hab] using hx
          have hpoint := norm_shiftedHeadIntegrand_horizontal_le
            psi hprim s (X := X) (a := a) (b := b) (x := x) (B := -B)
              hX hx'.1.le hx'.2 haLo hbHi hzlo hzhi
              (by simpa [abs_neg] using hBabs)
              (by simpa [abs_neg] using hBabs1)
          simpa [shiftedHeadHorizontalEnvelope, abs_neg,
            abs_of_nonneg hB0] using hpoint))
  · simpa only [zero_mul] using henv

/-! ## Full-line integrability and infinite deformation -/

theorem integrable_one_add_abs_pow_eight_mul_exp_neg_abs :
    Integrable (fun t : ℝ => (1 + |t|) ^ 8 * Real.exp (-|t|)) := by
  let f : ℝ → ℝ := fun t => (1 + |t|) ^ 8 * Real.exp (-|t|)
  have hposRaw : IntegrableOn
      (fun t : ℝ => (1 + t) ^ 8 * Real.exp (-t)) (Set.Ioi 0) := by
    have h0 := integrableOn_exp_neg_Ioi 0
    have h8 : IntegrableOn
        (fun t : ℝ => Real.exp (-t) * t ^ 8) (Set.Ioi 0) := by
      have h := Real.GammaIntegral_convergent
        (s := (9 : ℝ)) (by norm_num)
      convert h using 1
      ext t
      norm_num [Real.rpow_natCast]
    have hmajor : IntegrableOn
        (fun t : ℝ =>
          128 * (Real.exp (-t) + Real.exp (-t) * t ^ 8)) (Set.Ioi 0) :=
      (h0.add h8).const_mul 128
    apply hmajor.mono'
    · exact (by fun_prop : Continuous
        (fun t : ℝ => (1 + t) ^ 8 * Real.exp (-t))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 ≤ t := ht.le
      have hp := add_pow_le (by norm_num : (0 : ℝ) ≤ 1) ht0 8
      norm_num at hp
      rw [Real.norm_of_nonneg
        (mul_nonneg (by positivity) (Real.exp_pos _).le)]
      calc
        (1 + t) ^ 8 * Real.exp (-t) ≤
            (128 * (1 + t ^ 8)) * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
        _ = 128 * (Real.exp (-t) + Real.exp (-t) * t ^ 8) := by ring
  have hpos : IntegrableOn f (Set.Ioi 0) := by
    apply hposRaw.congr_fun
    · intro t ht
      have ht' : 0 < t := ht
      simp [f, abs_of_pos ht']
    · exact measurableSet_Ioi
  have hneg0 := hpos.comp_neg
  rw [Set.neg_Ioi, neg_zero] at hneg0
  have hneg : IntegrableOn f (Set.Iio 0) := by
    apply hneg0.congr_fun
    · intro t ht
      simp [f]
    · exact measurableSet_Iio
  have hzero : IntegrableOn f ({0} : Set ℝ) :=
    integrableOn_singleton (f := f) (hx := by simp)
  have hnonneg : IntegrableOn f (Set.Ici 0) := by
    have h := hpos.union hzero
    convert h using 1
    ext t
    simp [le_iff_lt_or_eq, or_comm]
  have hall := hneg.union hnonneg
  rw [Set.Iio_union_Ici] at hall
  exact integrableOn_univ.mp hall

theorem continuous_shiftedHead_vertical
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (s : ℂ) {X c : ℝ} (hX : 0 < X)
    (hcLo : -1 < c) (hcHi : c < 0) (hz : s.re + c < 1) :
    Continuous (fun v : ℝ =>
      shiftedHeadIntegrand psi s X ((c : ℂ) + v * I)) := by
  rw [continuous_iff_continuousAt]
  intro v
  have hinner : ContinuousAt (fun y : ℝ => (c : ℂ) + y * I) v := by
    fun_prop
  have hdiff := differentiableAt_shiftedHeadIntegrand psi s hX
    (w := (c : ℂ) + v * I) (by simpa using hcLo) (by simpa using hcHi)
      (by simpa using hz)
  change ContinuousAt
    ((shiftedHeadIntegrand psi s X) ∘ (fun y : ℝ => (c : ℂ) + y * I)) v
  exact ContinuousAt.comp
    (f := fun y : ℝ => (c : ℂ) + y * I)
    (g := shiftedHeadIntegrand psi s X) hdiff.continuousAt hinner

theorem integrable_shiftedHead_vertical
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hprim : psi.IsPrimitive) (s : ℂ) {X c : ℝ} (hX : 0 < X)
    (hcLo : -1 < c) (hcHi : c < 0)
    (hzlo : -(1 / 4 : ℝ) ≤ s.re + c)
    (hzhi : s.re + c ≤ 1 / 2) :
    Integrable (fun v : ℝ =>
      shiftedHeadIntegrand psi s X ((c : ℂ) + v * I)) := by
  let F : ℝ → ℂ := fun v =>
    shiftedHeadIntegrand psi s X ((c : ℂ) + v * I)
  let C : ℝ := 1 + |s.im|
  let K : ℝ := 248832 * Real.rpow (d : ℝ) (3 / 2) *
    (((⌊X⌋₊ + 1 : ℕ) : ℝ) ^ 2) * C ^ 6 * X ^ c
  let E : ℝ → ℝ := fun v =>
    K * ((1 + |v|) ^ 8 * Real.exp (-|v|))
  let S : Set ℝ := {v | 2 + |s.im| ≤ |v|}
  have hcont : Continuous F := by
    simpa [F] using continuous_shiftedHead_vertical psi s hX hcLo hcHi
      (by linarith)
  have hE : Integrable E :=
    integrable_one_add_abs_pow_eight_mul_exp_neg_abs.const_mul K
  have htail : IntegrableOn F S := by
    apply hE.integrableOn.mono'
    · exact hcont.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (by
          dsimp [S]
          exact measurableSet_le measurable_const measurable_abs)] with v hv
      change 2 + |s.im| ≤ |v| at hv
      have hpoint := norm_shiftedHeadIntegrand_horizontal_le
        psi hprim s (X := X) (a := c) (b := c) (x := c) (B := v)
          hX le_rfl le_rfl (by linarith) (by linarith) hzlo hzhi hv
            (by linarith [abs_nonneg s.im])
      have hC : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg s.im]
      have hbase : 1 + |s.im| + |v| ≤ C * (1 + |v|) := by
        dsimp [C]
        nlinarith [abs_nonneg s.im, abs_nonneg v]
      have hpow : (1 + |s.im| + |v|) ^ 6 ≤
          C ^ 6 * (1 + |v|) ^ 6 := by
        calc
          (1 + |s.im| + |v|) ^ 6 ≤ (C * (1 + |v|)) ^ 6 :=
            pow_le_pow_left₀ (by positivity) hbase 6
          _ = C ^ 6 * (1 + |v|) ^ 6 := by ring
      have hnonneg : 0 ≤
          (1 + |v|) ^ 2 * Real.exp (-|v|) * X ^ c := by positivity
      have hpref : 0 ≤ 248832 * Real.rpow (d : ℝ) (3 / 2) *
          (((⌊X⌋₊ + 1 : ℕ) : ℝ) ^ 2) := by
        exact mul_nonneg
          (mul_nonneg (by norm_num)
            (Real.rpow_nonneg (Nat.cast_nonneg d) _)) (sq_nonneg _)
      calc
        ‖F v‖ ≤ 248832 * Real.rpow (d : ℝ) (3 / 2) *
            (((⌊X⌋₊ + 1 : ℕ) : ℝ) ^ 2) *
              (1 + |s.im| + |v|) ^ 6 * (1 + |v|) ^ 2 *
                Real.exp (-|v|) * X ^ c := by
          simpa [F, max_self] using hpoint
        _ ≤ 248832 * Real.rpow (d : ℝ) (3 / 2) *
            (((⌊X⌋₊ + 1 : ℕ) : ℝ) ^ 2) *
              (C ^ 6 * (1 + |v|) ^ 6) * (1 + |v|) ^ 2 *
                Real.exp (-|v|) * X ^ c := by
          gcongr
        _ = E v := by
          dsimp [E, K]
          ring
  let R : ℝ := 2 + |s.im|
  have hcentral : IntegrableOn F (Set.Icc (-R) R) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hcover : Set.Icc (-R) R ∪ S = Set.univ := by
    have hRpos : 0 < R := by
      dsimp [R]
      linarith [abs_nonneg s.im]
    ext v
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_setOf_eq, Set.mem_univ,
      iff_true]
    by_cases h : -R ≤ v ∧ v ≤ R
    · exact Or.inl h
    · right
      rw [not_and_or] at h
      rcases h with h | h
      · have hv : v < -R := lt_of_not_ge h
        dsimp [S, R]
        rw [abs_of_neg (show v < 0 by linarith)]
        linarith [abs_nonneg s.im]
      · have hv : R < v := lt_of_not_ge h
        dsimp [S, R]
        rw [abs_of_pos (show 0 < v by linarith)]
        linarith [abs_nonneg s.im]
  have hall := hcentral.union htail
  rw [hcover] at hall
  exact integrableOn_univ.mp hall

/-- Premise-free infinite deformation of the finite reflected head from one
vertical line to another inside `-1 < Re w < 0`. -/
theorem full_shiftedHead_vertical_integral_eq
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hprim : psi.IsPrimitive) (s : ℂ)
    {X a b : ℝ} (hX : 0 < X) (hab : a ≤ b)
    (ha : -1 < a) (hb : b < 0)
    (hzlo : -(1 / 4 : ℝ) ≤ s.re + a)
    (hzhi : s.re + b ≤ 1 / 2) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, shiftedHeadIntegrand psi s X ((b : ℂ) + v * I)) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, shiftedHeadIntegrand psi s X ((a : ℂ) + v * I)) := by
  let rightTrunc : ℝ → ℂ := fun B => ∫ v : ℝ in -B..B,
    shiftedHeadIntegrand psi s X ((b : ℂ) + v * I)
  let leftTrunc : ℝ → ℂ := fun B => ∫ v : ℝ in -B..B,
    shiftedHeadIntegrand psi s X ((a : ℂ) + v * I)
  let Hminus : ℝ → ℂ := fun B => ∫ x : ℝ in a..b,
    shiftedHeadIntegrand psi s X ((x : ℂ) - B * I)
  let Hplus : ℝ → ℂ := fun B => ∫ x : ℝ in a..b,
    shiftedHeadIntegrand psi s X ((x : ℂ) + B * I)
  have hleft := integrable_shiftedHead_vertical psi hprim s hX ha
    (lt_of_le_of_lt hab hb) hzlo (by linarith)
  have hright := integrable_shiftedHead_vertical psi hprim s hX
    (lt_of_lt_of_le ha hab) hb (by linarith) hzhi
  have hR : Tendsto rightTrunc atTop
      (𝓝 (∫ v : ℝ, shiftedHeadIntegrand psi s X ((b : ℂ) + v * I))) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral hright
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hL : Tendsto leftTrunc atTop
      (𝓝 (∫ v : ℝ, shiftedHeadIntegrand psi s X ((a : ℂ) + v * I))) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral hleft
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hminus : Tendsto Hminus atTop (𝓝 0) := by
    simpa [Hminus] using tendsto_shiftedHead_lowerHorizontal_zero
      psi hprim s hX hab (by linarith) (by linarith) hzlo hzhi
  have hplus : Tendsto Hplus atTop (𝓝 0) := by
    simpa [Hplus] using tendsto_shiftedHead_upperHorizontal_zero
      psi hprim s hX hab (by linarith) (by linarith) hzlo hzhi
  have hbalance : ∀ B : ℝ,
      I * (rightTrunc B - leftTrunc B) = Hplus B - Hminus B := by
    intro B
    have hrect := rectangleBoundaryIntegral_shiftedHead_eq_zero
      psi s hX hab ha hb (by linarith)
        (u := -B) (v := B)
    unfold rectangleBoundaryIntegral at hrect
    have hminusInt :
        (∫ x : ℝ in a..b,
          shiftedHeadIntegrand psi s X
            ((x : ℂ) + ((-B : ℝ) : ℂ) * I)) =
          ∫ x : ℝ in a..b,
            shiftedHeadIntegrand psi s X ((x : ℂ) - (B : ℂ) * I) := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply congrArg (shiftedHeadIntegrand psi s X)
      push_cast
      ring
    rw [hminusInt] at hrect
    change Hminus B - Hplus B + I * rightTrunc B - I * leftTrunc B = 0 at hrect
    linear_combination hrect
  have hlhs : Tendsto (fun B => I * (rightTrunc B - leftTrunc B)) atTop
      (𝓝 (I * ((∫ v : ℝ,
          shiftedHeadIntegrand psi s X ((b : ℂ) + v * I)) -
        ∫ v : ℝ,
          shiftedHeadIntegrand psi s X ((a : ℂ) + v * I)))) :=
    tendsto_const_nhds.mul (hR.sub hL)
  have hrhs : Tendsto (fun B => Hplus B - Hminus B) atTop (𝓝 0) := by
    simpa using hplus.sub hminus
  have hlhs0 : Tendsto (fun B => I * (rightTrunc B - leftTrunc B)) atTop (𝓝 0) :=
    hrhs.congr' (Filter.Eventually.of_forall fun B => (hbalance B).symm)
  have heq := tendsto_nhds_unique hlhs hlhs0
  have hraw :
      (∫ v : ℝ, shiftedHeadIntegrand psi s X ((b : ℂ) + v * I)) =
        ∫ v : ℝ, shiftedHeadIntegrand psi s X ((a : ℂ) + v * I) := by
    apply sub_eq_zero.mp
    apply mul_left_cancel₀ I_ne_zero
    simpa using heq
  rw [hraw]

end
end RamachandraShiftedHeadContourTails

#print axioms RamachandraShiftedHeadContourTails.norm_ramachandraReflectedHead_le_floor_sq
#print axioms RamachandraShiftedHeadContourTails.norm_shiftedHeadIntegrand_horizontal_le
#print axioms RamachandraShiftedHeadContourTails.tendsto_shiftedHead_upperHorizontal_zero
#print axioms RamachandraShiftedHeadContourTails.tendsto_shiftedHead_lowerHorizontal_zero
