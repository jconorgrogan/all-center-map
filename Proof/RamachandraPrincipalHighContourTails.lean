import RamachandraPrincipalHighContourIdentity
import PrincipalZetaContourTails

/-!
# Infinite principal contour in shifted Ramachandra Lemma 3

This module supplies the limiting estimates omitted from the finite
conductor-one rectangle.  The translated zeta pole is retained throughout;
its double principal part has zero contour integral, while its first
difference gives the displayed simple residue.
-/

namespace RamachandraPrincipalHighContourTails

open Complex MeasureTheory Set Filter
open scoped Interval Topology LSeries.notation
open RamachandraShiftedGammaPoleContour
open RamachandraPrincipalHighContourIdentity
open MAPPrincipalZetaPoleContour

noncomputable section

set_option maxHeartbeats 800000

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

/-- Away from the pole, a unit lower bound on the imaginary part lets the
regularized fixed-strip estimate be divided by `z-1` without loss. -/
theorem norm_LFunction_one_fixedStrip_le_of_one_le_abs_im
    {z : ℂ} (hzlo : -1 ≤ z.re) (hzhi : z.re ≤ 2)
    (hzim : 1 ≤ |z.im|) :
    ‖DirichletCharacter.LFunction chiOne z‖ ≤
      1600 * ‖z + 3‖ ^ 6 := by
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hzim
  have hden : 1 ≤ ‖z - 1‖ := by
    have him : |z.im| ≤ ‖z - 1‖ := by
      simpa using Complex.abs_im_le_norm (z - 1)
    exact hzim.trans him
  have hreg :=
    MAPPrincipalZetaFixedStrip.norm_principalRegularized_fixedStrip_le
      (z := z) hzlo hzhi
  have heq : principalF z =
      (z - 1) * DirichletCharacter.LFunction chiOne z := by
    rw [DirichletCharacter.LFunction_modOne_eq]
    exact MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hz1
  calc
    ‖DirichletCharacter.LFunction chiOne z‖ ≤
        ‖z - 1‖ * ‖DirichletCharacter.LFunction chiOne z‖ := by
      nlinarith [norm_nonneg (DirichletCharacter.LFunction chiOne z)]
    _ = ‖principalF z‖ := by rw [heq, norm_mul]
    _ ≤ 1600 * ‖z + 3‖ ^ 6 := hreg

/-- A real-part gap from the zeta pole gives the corresponding uniform
division estimate on a vertical line. -/
theorem norm_LFunction_one_fixedStrip_le_of_quarter_re_gap
    {z : ℂ} (hzlo : -1 ≤ z.re) (hzhi : z.re ≤ 2)
    (hgap : (1 / 4 : ℝ) ≤ |z.re - 1|) :
    ‖DirichletCharacter.LFunction chiOne z‖ ≤
      6400 * ‖z + 3‖ ^ 6 := by
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hgap
  have hden : (1 / 4 : ℝ) ≤ ‖z - 1‖ := by
    have hre : |z.re - 1| ≤ ‖z - 1‖ := by
      simpa using Complex.abs_re_le_norm (z - 1)
    exact hgap.trans hre
  have hreg :=
    MAPPrincipalZetaFixedStrip.norm_principalRegularized_fixedStrip_le
      (z := z) hzlo hzhi
  have heq : principalF z =
      (z - 1) * DirichletCharacter.LFunction chiOne z := by
    rw [DirichletCharacter.LFunction_modOne_eq]
    exact MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hz1
  calc
    ‖DirichletCharacter.LFunction chiOne z‖ ≤
        4 * (‖z - 1‖ * ‖DirichletCharacter.LFunction chiOne z‖) := by
      nlinarith [norm_nonneg (DirichletCharacter.LFunction chiOne z)]
    _ = 4 * ‖principalF z‖ := by rw [heq, norm_mul]
    _ ≤ 4 * (1600 * ‖z + 3‖ ^ 6) := by gcongr
    _ = 6400 * ‖z + 3‖ ^ 6 := by ring

/-- The degree-fourteen exponential majorant needed for the principal raw
vertical and horizontal tails. -/
theorem integrable_one_add_abs_pow_fourteen_mul_exp_neg_abs :
    Integrable (fun t : ℝ =>
      (1 + |t|) ^ 14 * Real.exp (-|t|)) := by
  let f : ℝ → ℝ := fun t => (1 + |t|) ^ 14 * Real.exp (-|t|)
  have hposRaw : IntegrableOn
      (fun t : ℝ => (1 + t) ^ 14 * Real.exp (-t)) (Set.Ioi 0) := by
    have h0 := integrableOn_exp_neg_Ioi 0
    have h14 : IntegrableOn
        (fun t : ℝ => Real.exp (-t) * t ^ 14) (Set.Ioi 0) := by
      have h := Real.GammaIntegral_convergent
        (s := (15 : ℝ)) (by norm_num)
      convert h using 1
      ext t
      norm_num [Real.rpow_natCast]
    have hmajor : IntegrableOn
        (fun t : ℝ =>
          8192 * (Real.exp (-t) + Real.exp (-t) * t ^ 14))
        (Set.Ioi 0) := (h0.add h14).const_mul 8192
    apply hmajor.mono'
    · exact (by fun_prop : Continuous
        (fun t : ℝ => (1 + t) ^ 14 * Real.exp (-t))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 ≤ t := ht.le
      have hp := add_pow_le (by norm_num : (0 : ℝ) ≤ 1) ht0 14
      norm_num at hp
      rw [Real.norm_of_nonneg
        (mul_nonneg (by positivity) (Real.exp_pos _).le)]
      calc
        (1 + t) ^ 14 * Real.exp (-t) ≤
            (8192 * (1 + t ^ 14)) * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
        _ = 8192 * (Real.exp (-t) +
            Real.exp (-t) * t ^ 14) := by ring
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

/-- Continuity of a principal raw vertical slice when both its Gamma line
and its translated zeta line avoid their poles. -/
theorem continuous_shiftedGammaRaw_vertical_principal
    (s : ℂ) {X c : ℝ} (hX : 0 < X)
    (hcLo : -1 < c) (hc0 : c ≠ 0)
    (hzeta : s.re + c ≠ 1) :
    Continuous (fun t : ℝ =>
      shiftedGammaRawIntegrand chiOne s X ((c : ℂ) + t * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  unfold shiftedGammaRawIntegrand
  have hinner : ContinuousAt (fun u : ℝ => (c : ℂ) + u * I) t := by
    fun_prop
  have hz1 : s + ((c : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    exact hzeta hre
  have hLz : ContinuousAt (fun z : ℂ =>
      DirichletCharacter.LFunction chiOne z)
      (s + ((c : ℂ) + (t : ℂ) * I)) := by
    rw [DirichletCharacter.LFunction_modOne_eq]
    exact (differentiableAt_riemannZeta hz1).continuousAt
  have hL : ContinuousAt (fun u : ℝ =>
      DirichletCharacter.LFunction chiOne
        (s + ((c : ℂ) + u * I))) t := by
    have hcomp : ContinuousAt
        ((fun z : ℂ => DirichletCharacter.LFunction chiOne z) ∘
          (fun u : ℝ => s + ((c : ℂ) + u * I))) t :=
      ContinuousAt.comp
        (f := fun u : ℝ => s + ((c : ℂ) + u * I))
        (g := fun z : ℂ => DirichletCharacter.LFunction chiOne z)
        hLz (by fun_prop)
    simpa [Function.comp_def] using hcomp
  have hGammaPoint (m : ℕ) :
      ((c : ℂ) + (t : ℂ) * I) ≠ -(m : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hmLt : (m : ℝ) < 1 := by linarith
    have hm0 : m = 0 := Nat.lt_one_iff.mp (by exact_mod_cast hmLt)
    subst m
    norm_num at hre
    exact hc0 hre
  have hGamma : ContinuousAt (fun u : ℝ =>
      Complex.Gamma ((c : ℂ) + u * I)) t := by
    have hcomp : ContinuousAt
        (Complex.Gamma ∘ (fun u : ℝ => (c : ℂ) + u * I)) t :=
      ContinuousAt.comp
        (f := fun u : ℝ => (c : ℂ) + u * I)
        (g := Complex.Gamma)
        (Complex.continuousAt_Gamma _ hGammaPoint) hinner
    simpa [Function.comp_def] using hcomp
  have hpow : ContinuousAt (fun u : ℝ =>
      (X : ℂ) ^ ((c : ℂ) + u * I)) t := by
    letI : NeZero (X : ℂ) :=
      ⟨Complex.ofReal_ne_zero.mpr hX.ne'⟩
    exact (continuous_const_cpow (X : ℂ)).continuousAt.comp hinner
  exact ((hL.pow 2).mul hGamma).mul hpow

/-- Full-line integrability of a source principal vertical slice. -/
theorem integrable_shiftedGammaRaw_vertical_principal
    (s : ℂ) {X c : ℝ} (hX : 0 < X)
    (hcLo : -1 < c) (hcHi : c ≤ 2) (hc0 : c ≠ 0)
    (hLLo : -1 ≤ s.re + c) (hLHi : s.re + c ≤ 2)
    (hgap : (1 / 4 : ℝ) ≤ |s.re + c - 1|) :
    Integrable (fun t : ℝ =>
      shiftedGammaRawIntegrand chiOne s X ((c : ℂ) + t * I)) := by
  let F : ℝ → ℂ := fun t =>
    shiftedGammaRawIntegrand chiOne s X ((c : ℂ) + t * I)
  let C : ℝ := 5 + |s.im|
  let K : ℝ := 491520000 * C ^ 12 * X ^ c
  let E : ℝ → ℝ := fun t =>
    K * ((1 + |t|) ^ 14 * Real.exp (-|t|))
  have hzeta : s.re + c ≠ 1 := by
    intro h
    rw [h, sub_self, abs_zero] at hgap
    norm_num at hgap
  have hcont : Continuous F := by
    simpa [F] using continuous_shiftedGammaRaw_vertical_principal
      s hX hcLo hc0 hzeta
  have hE : Integrable E :=
    integrable_one_add_abs_pow_fourteen_mul_exp_neg_abs.const_mul K
  have htail : IntegrableOn F {t : ℝ | 1 ≤ |t|} := by
    apply hE.integrableOn.mono'
    · exact hcont.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem
          (measurableSet_le measurable_const measurable_abs)] with t ht
      let z : ℂ := s + ((c : ℂ) + t * I)
      have hzLo : -1 ≤ z.re := by simpa [z] using hLLo
      have hzHi : z.re ≤ 2 := by simpa [z] using hLHi
      have hzGap : (1 / 4 : ℝ) ≤ |z.re - 1| := by simpa [z] using hgap
      have hzNorm : ‖z + 3‖ ≤ C + |t| := by
        calc
          ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
            Complex.norm_le_abs_re_add_abs_im _
          _ ≤ 5 + (|s.im| + |t|) := by
            have hre : |(z + 3).re| ≤ 5 := by
              have hzre : z.re = s.re + c := by simp [z]
              rw [Complex.add_re, hzre]
              norm_num
              rw [abs_of_nonneg (by linarith)]
              linarith
            have him : |(z + 3).im| ≤ |s.im| + |t| := by
              simpa [z] using abs_add_le s.im t
            exact add_le_add hre him
          _ = C + |t| := by simp [C]; ring
      have hL0 := norm_LFunction_one_fixedStrip_le_of_quarter_re_gap
        hzLo hzHi hzGap
      have hL : ‖DirichletCharacter.LFunction chiOne z‖ ≤
          6400 * (C + |t|) ^ 6 :=
        hL0.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hzNorm 6) (by norm_num))
      have hG := norm_Gamma_ramachandraHorizontalStrip_le_exp
        (a := c) (t := t) (by linarith) hcHi ht
      have hP : ‖(X : ℂ) ^ ((c : ℂ) + t * I)‖ = X ^ c := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
        simp
      have hC : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg s.im]
      have hbase : C + |t| ≤ C * (1 + |t|) := by
        nlinarith [abs_nonneg t]
      have hpow : (C + |t|) ^ 12 ≤ C ^ 12 * (1 + |t|) ^ 12 := by
        calc
          (C + |t|) ^ 12 ≤ (C * (1 + |t|)) ^ 12 :=
            pow_le_pow_left₀ (by positivity) hbase 12
          _ = C ^ 12 * (1 + |t|) ^ 12 := by ring
      change ‖shiftedGammaRawIntegrand chiOne s X
        ((c : ℂ) + t * I)‖ ≤ E t
      unfold shiftedGammaRawIntegrand
      rw [norm_mul, norm_mul, norm_pow, hP]
      calc
        ‖DirichletCharacter.LFunction chiOne z‖ ^ 2 *
              ‖Complex.Gamma ((c : ℂ) + t * I)‖ * X ^ c ≤
            (6400 * (C + |t|) ^ 6) ^ 2 *
              (12 * (1 + |t|) ^ 2 * Real.exp (-|t|)) * X ^ c := by
          gcongr
        _ ≤ (6400 ^ 2 * (C ^ 12 * (1 + |t|) ^ 12)) *
              (12 * (1 + |t|) ^ 2 * Real.exp (-|t|)) * X ^ c := by
          have hsq : (6400 * (C + |t|) ^ 6) ^ 2 =
              6400 ^ 2 * (C + |t|) ^ 12 := by ring
          rw [hsq]
          gcongr
        _ = E t := by dsimp [E, K]; ring
  have hcentral : IntegrableOn F (Set.Icc (-1) 1) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hcover : Set.Icc (-1 : ℝ) 1 ∪ {t : ℝ | 1 ≤ |t|} = Set.univ := by
    ext t
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_setOf_eq, Set.mem_univ,
      iff_true]
    by_cases h : -1 ≤ t ∧ t ≤ 1
    · exact Or.inl h
    · right
      rw [not_and_or] at h
      rcases h with h | h
      · rw [abs_of_neg (by linarith [lt_of_not_ge h])]
        linarith
      · rw [abs_of_pos (by linarith [lt_of_not_ge h])]
        linarith
  have hall := hcentral.union htail
  rw [hcover] at hall
  exact integrableOn_univ.mp hall

/-- Common principal horizontal envelope. -/
def principalShiftedGammaHorizontalEnvelope
    (s : ℂ) (X a b B : ℝ) : ℝ :=
  30720000 * (5 + |s.im| + B) ^ 12 *
    (1 + B) ^ 2 * Real.exp (-B) * max (X ^ a) (X ^ b)

theorem norm_shiftedGammaRaw_principal_upper_le_envelope
    (s : ℂ) {X a b x B : ℝ} (hX : 0 < X)
    (haLo : -(3 / 2 : ℝ) ≤ a) (hbHi : b ≤ 2)
    (hax : a ≤ x) (hxb : x ≤ b)
    (hLLo : -1 ≤ s.re + a) (hLHi : s.re + b ≤ 2)
    (hB : 1 + |s.im| ≤ B) :
    ‖shiftedGammaRawIntegrand chiOne s X ((x : ℂ) + B * I)‖ ≤
      principalShiftedGammaHorizontalEnvelope s X a b B := by
  let z : ℂ := s + ((x : ℂ) + B * I)
  have hzLo : -1 ≤ z.re := by simp [z]; linarith
  have hzHi : z.re ≤ 2 := by simp [z]; linarith
  have hzim : 1 ≤ |z.im| := by
    have hsum : 1 ≤ s.im + B := by linarith [neg_abs_le s.im]
    have hzIm : z.im = s.im + B := by simp [z]
    rw [hzIm, abs_of_nonneg (by linarith)]
    exact hsum
  have hzNorm : ‖z + 3‖ ≤ 5 + |s.im| + B := by
    have hB0 : 0 ≤ B :=
      (by positivity : 0 ≤ 1 + |s.im|).trans hB
    calc
      ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 5 + (|s.im| + B) := by
        have hre : |(z + 3).re| ≤ 5 := by
          have hzre : z.re = s.re + x := by simp [z]
          rw [Complex.add_re, hzre]
          norm_num
          rw [abs_of_nonneg (by linarith)]
          linarith
        have him : |(z + 3).im| ≤ |s.im| + B := by
          have himEq : (z + 3).im = s.im + B := by simp [z]
          rw [himEq]
          calc
            |s.im + B| ≤ |s.im| + |B| := abs_add_le _ _
            _ = |s.im| + B := by
              rw [abs_of_nonneg hB0]
        linarith
      _ = 5 + |s.im| + B := by ring
  have hL0 := norm_LFunction_one_fixedStrip_le_of_one_le_abs_im
    hzLo hzHi hzim
  have hL : ‖DirichletCharacter.LFunction chiOne z‖ ≤
      1600 * (5 + |s.im| + B) ^ 6 :=
    hL0.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hzNorm 6) (by norm_num))
  have hG := norm_Gamma_ramachandraHorizontalStrip_le_exp
    (a := x) (t := B) (haLo.trans hax) (hxb.trans hbHi)
      (by
        have hB0 : 0 ≤ B :=
          (by positivity : 0 ≤ 1 + |s.im|).trans hB
        have hB1 : 1 ≤ B :=
          (by linarith [abs_nonneg s.im] : 1 ≤ 1 + |s.im|).trans hB
        rw [abs_of_nonneg hB0]
        exact hB1)
  have hP := norm_posReal_cpow_horizontal_le_max hX hax hxb (t := B)
  change ‖DirichletCharacter.LFunction chiOne z ^ 2 *
      Complex.Gamma ((x : ℂ) + B * I) *
        (X : ℂ) ^ ((x : ℂ) + B * I)‖ ≤
    principalShiftedGammaHorizontalEnvelope s X a b B
  unfold principalShiftedGammaHorizontalEnvelope
  rw [norm_mul, norm_mul, norm_pow]
  calc
    ‖DirichletCharacter.LFunction chiOne z‖ ^ 2 *
          ‖Complex.Gamma ((x : ℂ) + B * I)‖ *
          ‖(X : ℂ) ^ ((x : ℂ) + B * I)‖ ≤
        (1600 * (5 + |s.im| + B) ^ 6) ^ 2 *
          (12 * (1 + |B|) ^ 2 * Real.exp (-|B|)) *
            max (X ^ a) (X ^ b) := by gcongr
    _ = 30720000 * (5 + |s.im| + B) ^ 12 *
        (1 + B) ^ 2 * Real.exp (-B) * max (X ^ a) (X ^ b) := by
      have hB0 : 0 ≤ B :=
        (by positivity : 0 ≤ 1 + |s.im|).trans hB
      rw [abs_of_nonneg hB0]
      ring

theorem norm_shiftedGammaRaw_principal_lower_le_envelope
    (s : ℂ) {X a b x B : ℝ} (hX : 0 < X)
    (haLo : -(3 / 2 : ℝ) ≤ a) (hbHi : b ≤ 2)
    (hax : a ≤ x) (hxb : x ≤ b)
    (hLLo : -1 ≤ s.re + a) (hLHi : s.re + b ≤ 2)
    (hB : 1 + |s.im| ≤ B) :
    ‖shiftedGammaRawIntegrand chiOne s X ((x : ℂ) - B * I)‖ ≤
      principalShiftedGammaHorizontalEnvelope s X a b B := by
  let z : ℂ := s + ((x : ℂ) - B * I)
  have hzLo : -1 ≤ z.re := by simp [z]; linarith
  have hzHi : z.re ≤ 2 := by simp [z]; linarith
  have hzim : 1 ≤ |z.im| := by
    have hsum : s.im - B ≤ -1 := by linarith [le_abs_self s.im]
    have hzIm : z.im = s.im - B := by
      simp [z]
      ring
    rw [hzIm]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hzNorm : ‖z + 3‖ ≤ 5 + |s.im| + B := by
    have hB0 : 0 ≤ B :=
      (by positivity : 0 ≤ 1 + |s.im|).trans hB
    calc
      ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 5 + (|s.im| + B) := by
        have hre : |(z + 3).re| ≤ 5 := by
          have hzre : z.re = s.re + x := by simp [z]
          rw [Complex.add_re, hzre]
          norm_num
          rw [abs_of_nonneg (by linarith)]
          linarith
        have him : |(z + 3).im| ≤ |s.im| + B := by
          have himEq : (z + 3).im = s.im - B := by
            simp [z]
            ring
          rw [himEq]
          calc
            |s.im - B| ≤ |s.im| + |B| := abs_sub _ _
            _ = |s.im| + B := by
              rw [abs_of_nonneg hB0]
        linarith
      _ = 5 + |s.im| + B := by ring
  have hL0 := norm_LFunction_one_fixedStrip_le_of_one_le_abs_im
    hzLo hzHi hzim
  have hL : ‖DirichletCharacter.LFunction chiOne z‖ ≤
      1600 * (5 + |s.im| + B) ^ 6 :=
    hL0.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hzNorm 6) (by norm_num))
  have hG := norm_Gamma_ramachandraHorizontalStrip_le_exp
    (a := x) (t := -B) (haLo.trans hax) (hxb.trans hbHi)
      (by
        have hB0 : 0 ≤ B :=
          (by positivity : 0 ≤ 1 + |s.im|).trans hB
        have hB1 : 1 ≤ B :=
          (by linarith [abs_nonneg s.im] : 1 ≤ 1 + |s.im|).trans hB
        rw [abs_neg, abs_of_nonneg hB0]
        exact hB1)
  have hP := norm_posReal_cpow_horizontal_le_max hX hax hxb (t := -B)
  have hw : ((x : ℂ) - B * I) = (x : ℂ) + (-B : ℝ) * I := by
    push_cast
    ring
  change ‖DirichletCharacter.LFunction chiOne z ^ 2 *
      Complex.Gamma ((x : ℂ) - B * I) *
        (X : ℂ) ^ ((x : ℂ) - B * I)‖ ≤
    principalShiftedGammaHorizontalEnvelope s X a b B
  unfold principalShiftedGammaHorizontalEnvelope
  rw [norm_mul, norm_mul, norm_pow]
  have hG' : ‖Complex.Gamma ((x : ℂ) - B * I)‖ ≤
      12 * (1 + |-B|) ^ 2 * Real.exp (-|-B|) := by
    rw [hw]
    exact hG
  have hP' : ‖(X : ℂ) ^ ((x : ℂ) - B * I)‖ ≤
      max (X ^ a) (X ^ b) := by
    rw [hw]
    exact hP
  calc
    ‖DirichletCharacter.LFunction chiOne z‖ ^ 2 *
          ‖Complex.Gamma ((x : ℂ) - B * I)‖ *
          ‖(X : ℂ) ^ ((x : ℂ) - B * I)‖ ≤
        (1600 * (5 + |s.im| + B) ^ 6) ^ 2 *
          (12 * (1 + |-B|) ^ 2 * Real.exp (-|-B|)) *
            max (X ^ a) (X ^ b) := by
      gcongr
    _ = 30720000 * (5 + |s.im| + B) ^ 12 *
        (1 + B) ^ 2 * Real.exp (-B) * max (X ^ a) (X ^ b) := by
      have hB0 : 0 ≤ B :=
        (by positivity : 0 ≤ 1 + |s.im|).trans hB
      rw [abs_neg, abs_of_nonneg hB0]
      ring

theorem tendsto_principalShiftedGammaHorizontalEnvelope_zero
    (s : ℂ) {X : ℝ} (hX : 0 < X) (a b : ℝ) :
    Tendsto (principalShiftedGammaHorizontalEnvelope s X a b)
      atTop (𝓝 0) := by
  let C : ℝ := 5 + |s.im|
  let K : ℝ := 30720000 * max (X ^ a) (X ^ b)
  have hshift : Tendsto (fun B : ℝ => B + C) atTop atTop :=
    tendsto_atTop_add_const_right atTop C tendsto_id
  have hpoly : Tendsto (fun B : ℝ =>
      (B + C) ^ 14 * Real.exp (-(B + C))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 14).comp hshift
  have htarget := hpoly.const_mul (K * Real.exp C)
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    unfold principalShiftedGammaHorizontalEnvelope
    positivity
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    have hC : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg s.im]
    have hbase : 0 ≤ B + C := by linarith
    have h1B : 1 + B ≤ B + C := by linarith
    have h12 : (5 + |s.im| + B) ^ 12 = (B + C) ^ 12 := by
      congr 1
      dsimp [C]
      ring
    have h2 : (1 + B) ^ 2 ≤ (B + C) ^ 2 :=
      pow_le_pow_left₀ (by linarith) h1B 2
    have hcombine :
        (5 + |s.im| + B) ^ 12 * (1 + B) ^ 2 ≤
          (B + C) ^ 14 := by
      rw [h12]
      calc
        (B + C) ^ 12 * (1 + B) ^ 2 ≤
            (B + C) ^ 12 * (B + C) ^ 2 := by gcongr
        _ = (B + C) ^ 14 := by ring
    have hexp : Real.exp C * Real.exp (-(B + C)) = Real.exp (-B) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      principalShiftedGammaHorizontalEnvelope s X a b B =
          K * ((5 + |s.im| + B) ^ 12 * (1 + B) ^ 2 *
            Real.exp (-B)) := by dsimp [K, principalShiftedGammaHorizontalEnvelope]; ring
      _ ≤ K * ((B + C) ^ 14 * Real.exp (-B)) := by gcongr
      _ = (K * Real.exp C) *
          ((B + C) ^ 14 * Real.exp (-(B + C))) := by
        calc
          K * ((B + C) ^ 14 * Real.exp (-B)) =
              K * ((B + C) ^ 14 *
                (Real.exp C * Real.exp (-(B + C)))) := by rw [hexp]
          _ = _ := by ring
  · simpa using htarget

theorem tendsto_shiftedGammaRaw_principal_upperHorizontal_zero
    (s : ℂ) {X a b : ℝ} (hX : 0 < X)
    (hab : a ≤ b) (haLo : -(3 / 2 : ℝ) ≤ a) (hbHi : b ≤ 2)
    (hLLo : -1 ≤ s.re + a) (hLHi : s.re + b ≤ 2) :
    Tendsto (fun B : ℝ => ∫ x : ℝ in a..b,
      shiftedGammaRawIntegrand chiOne s X ((x : ℂ) + B * I))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have henv :=
    (tendsto_principalShiftedGammaHorizontalEnvelope_zero s hX a b).mul_const
      |b - a|
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun B => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (1 + |s.im|)] with B hB
    apply MAPAppendixA4Detector.horizontal_segment_norm_le
      (shiftedGammaRawIntegrand chiOne s X)
      (B := B) (M := principalShiftedGammaHorizontalEnvelope s X a b B)
    intro x hx
    have hx' : x ∈ Set.Ioc a b := by
      simpa [Set.uIoc_of_le hab] using hx
    exact norm_shiftedGammaRaw_principal_upper_le_envelope s hX haLo hbHi
      hx'.1.le hx'.2 hLLo hLHi hB
  · simpa using henv

theorem tendsto_shiftedGammaRaw_principal_lowerHorizontal_zero
    (s : ℂ) {X a b : ℝ} (hX : 0 < X)
    (hab : a ≤ b) (haLo : -(3 / 2 : ℝ) ≤ a) (hbHi : b ≤ 2)
    (hLLo : -1 ≤ s.re + a) (hLHi : s.re + b ≤ 2) :
    Tendsto (fun B : ℝ => ∫ x : ℝ in a..b,
      shiftedGammaRawIntegrand chiOne s X ((x : ℂ) - B * I))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have henv :=
    (tendsto_principalShiftedGammaHorizontalEnvelope_zero s hX a b).mul_const
      |b - a|
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun B => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (1 + |s.im|)] with B hB
    have hbound := MAPAppendixA4Detector.horizontal_segment_norm_le
      (shiftedGammaRawIntegrand chiOne s X)
      (a := a) (c := b) (B := -B)
      (M := principalShiftedGammaHorizontalEnvelope s X a b B)
      (fun x hx => by
        have hx' : x ∈ Set.Ioc a b := by
          simpa [Set.uIoc_of_le hab] using hx
        simpa [sub_eq_add_neg] using
          norm_shiftedGammaRaw_principal_lower_le_envelope s hX haLo hbHi
            hx'.1.le hx'.2 hLLo hLHi hB)
    simpa [sub_eq_add_neg] using hbound
  · simpa [sub_eq_add_neg] using henv

/-- Infinite principal contour displacement with both the Gamma residue and
the translated zeta simple residue retained exactly. -/
theorem full_shiftedGamma_principal_vertical_integral_eq
    (s : ℂ) {X a b r0 rp : ℝ}
    (hX : 0 < X) (hs : s ≠ 1) (haStrip : -1 < a)
    (hr0 : 0 < r0) (ha0 : a < -r0) (hb0 : r0 < b)
    (hrp : 0 < rp)
    (hap : a < (principalTranslatedPole s).re - rp)
    (hbp : (principalTranslatedPole s).re + rp < b)
    (haLo : -(3 / 2 : ℝ) ≤ a) (hbHi : b ≤ 2)
    (hLLo : -1 ≤ s.re + a) (hLHi : s.re + b ≤ 2)
    (hgapA : (1 / 4 : ℝ) ≤ |s.re + a - 1|)
    (hgapB : (1 / 4 : ℝ) ≤ |s.re + b - 1|) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ,
        shiftedGammaRawIntegrand chiOne s X ((b : ℂ) + t * I)) =
      DirichletCharacter.LFunction chiOne s ^ 2 +
        principalTranslatedFirstDifference s X (principalTranslatedPole s) +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ,
            shiftedGammaRawIntegrand chiOne s X ((a : ℂ) + t * I)) := by
  have hab : a ≤ b := by linarith
  have ha0ne : a ≠ 0 := by linarith
  have hb0ne : b ≠ 0 := by linarith
  have hleft := integrable_shiftedGammaRaw_vertical_principal s hX
    haStrip (le_trans hab hbHi) ha0ne hLLo (by linarith) hgapA
  have hright := integrable_shiftedGammaRaw_vertical_principal s hX
    (by linarith) hbHi hb0ne (by linarith) hLHi hgapB
  have hminus := tendsto_shiftedGammaRaw_principal_lowerHorizontal_zero
    s hX hab haLo hbHi hLLo hLHi
  have hplus := tendsto_shiftedGammaRaw_principal_upperHorizontal_zero
    s hX hab haLo hbHi hLLo hLHi
  have hinfinite := full_vertical_integrals_eq_add_residue_of_boundary
    (shiftedGammaRawIntegrand chiOne s X)
    (DirichletCharacter.LFunction chiOne s ^ 2 +
      principalTranslatedFirstDifference s X (principalTranslatedPole s))
    hleft hright hminus hplus (by
      filter_upwards [eventually_gt_atTop
        (max r0 (|((principalTranslatedPole s).im)| + rp))] with B hB
      have hBr0 : r0 < B :=
        lt_of_le_of_lt (le_max_left r0
          (|((principalTranslatedPole s).im)| + rp)) hB
      have hBpole : |((principalTranslatedPole s).im)| + rp < B :=
        lt_of_le_of_lt (le_max_right r0
          (|((principalTranslatedPole s).im)| + rp)) hB
      exact rectangleBoundaryIntegral_shiftedGammaRaw_principal
        s hX hs haStrip hr0 ha0 hb0
          (by linarith) hBr0
          hrp hap hbp
          (by linarith [neg_abs_le (principalTranslatedPole s).im])
          (by linarith [le_abs_self (principalTranslatedPole s).im]))
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [hinfinite]
  have hscalar : (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ((2 : ℂ) * (Real.pi : ℂ))) = 1 := by
    push_cast
    field_simp [hpi]
  let R : ℂ := DirichletCharacter.LFunction chiOne s ^ 2 +
    principalTranslatedFirstDifference s X (principalTranslatedPole s)
  have hresidueScalar :
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((2 : ℂ) * (Real.pi : ℂ) * R)) = R := by
    calc
      _ = ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ((2 : ℂ) * (Real.pi : ℂ))) *
            R) := by ring
      _ = _ := by rw [hscalar, one_mul]
  change (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ((∫ t : ℝ, shiftedGammaRawIntegrand chiOne s X
        ((a : ℂ) + t * I)) + (2 : ℂ) * (Real.pi : ℂ) * R)) =
    R + (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, shiftedGammaRawIntegrand chiOne s X
        ((a : ℂ) + t * I))
  rw [mul_add, hresidueScalar]
  ring

end
end RamachandraPrincipalHighContourTails

#print axioms RamachandraPrincipalHighContourTails.norm_LFunction_one_fixedStrip_le_of_one_le_abs_im
#print axioms RamachandraPrincipalHighContourTails.integrable_shiftedGammaRaw_vertical_principal
#print axioms RamachandraPrincipalHighContourTails.full_shiftedGamma_principal_vertical_integral_eq
