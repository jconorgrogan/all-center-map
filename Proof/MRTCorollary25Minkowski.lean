import MRTCorollary25Certified
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The pp. 57--58 cutoff-removal Minkowski layer
-/

namespace MAPMRTCorollary25Minkowski

open scoped BigOperators
open MeasureTheory

noncomputable section

/-- The exact positive Perron cutoff weight used in Corollary 2.5. -/
def perronWeight (u : ℝ) : ℝ := 1 / (1 + |u|)

theorem continuous_perronWeight : Continuous perronWeight := by
  unfold perronWeight
  exact continuous_const.div (continuous_const.add continuous_abs)
    (fun u ↦ by positivity)

theorem perronWeight_pos (u : ℝ) : 0 < perronWeight u := by
  unfold perronWeight
  positivity

/-- The cutoff weight has exactly logarithmic mass. -/
theorem integral_perronWeight {T : ℝ} (hT : 0 ≤ T) :
    (∫ u in (-T)..T, perronWeight u) = 2 * Real.log (1 + T) := by
  have hpos :
      (∫ u in (0 : ℝ)..T, perronWeight u) = Real.log (1 + T) := by
    calc
      (∫ u in (0 : ℝ)..T, perronWeight u) =
          ∫ u in (0 : ℝ)..T, 1 / (1 + u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le hT] at hu
        rw [perronWeight, abs_of_nonneg hu.1]
      _ = ∫ y in (1 : ℝ)..(T + 1), 1 / y := by
        have hshift := intervalIntegral.integral_comp_add_right
          (fun y : ℝ ↦ 1 / y) 1 (a := 0) (b := T)
        simpa [add_comm] using hshift
      _ = Real.log ((T + 1) / 1) :=
        integral_one_div_of_pos (by norm_num) (by linarith)
      _ = Real.log (1 + T) := by ring_nf
  have hneg :
      (∫ u in (-T)..(0 : ℝ), perronWeight u) =
        ∫ u in (0 : ℝ)..T, perronWeight u := by
    have hs := intervalIntegral.integral_comp_neg perronWeight
      (a := 0) (b := T)
    have heven : (fun u : ℝ ↦ perronWeight (-u)) = perronWeight := by
      funext u
      simp [perronWeight]
    rw [heven] at hs
    simpa using hs.symm
  have hleft : IntervalIntegrable perronWeight volume (-T) 0 :=
    continuous_perronWeight.intervalIntegrable _ _
  have hright : IntervalIntegrable perronWeight volume 0 T :=
    continuous_perronWeight.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright,
    hneg, hpos]
  ring

/-- Cauchy--Schwarz on a compact real interval, in a form avoiding any
abstract `Lp` packaging. -/
theorem intervalIntegral_sq_le_length_mul_integral_sq
    {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b) :
    (∫ x in a..b, f x) ^ 2 ≤
      (b - a) * ∫ x in a..b, (f x) ^ 2 := by
  let W := b - a
  let J := ∫ x in a..b, f x
  let Q := ∫ x in a..b, (f x) ^ 2
  have hW : 0 < W := by dsimp only [W]; linarith
  have hnonneg : 0 ≤ ∫ x in a..b, (W * f x - J) ^ 2 := by
    apply intervalIntegral.integral_nonneg hab.le
    intro x hx
    positivity
  have hfI : IntervalIntegrable f volume a b := hf.intervalIntegrable a b
  have hf2I : IntervalIntegrable (fun x ↦ (f x) ^ 2) volume a b :=
    (hf.pow 2).intervalIntegrable a b
  have hconstI : IntervalIntegrable (fun _x : ℝ ↦ J ^ 2) volume a b :=
    intervalIntegrable_const
  have hexpand :
      (∫ x in a..b, (W * f x - J) ^ 2) = W * (W * Q - J ^ 2) := by
    have hfun : (fun x : ℝ ↦ (W * f x - J) ^ 2) =
        fun x ↦ W ^ 2 * (f x) ^ 2 - 2 * W * J * f x + J ^ 2 := by
      funext x
      ring
    have hfirstI : IntervalIntegrable (fun x ↦ W ^ 2 * (f x) ^ 2)
        volume a b := hf2I.const_mul (W ^ 2)
    have hsecondI : IntervalIntegrable (fun x ↦ 2 * W * J * f x)
        volume a b := hfI.const_mul (2 * W * J)
    have hsubI := hfirstI.sub hsecondI
    rw [hfun]
    rw [intervalIntegral.integral_add hsubI hconstI]
    rw [intervalIntegral.integral_sub hfirstI hsecondI]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    dsimp only [W, J, Q]
    ring
  rw [hexpand] at hnonneg
  have := (mul_nonneg_iff_of_pos_left hW).mp hnonneg
  dsimp only [W, J, Q] at this ⊢
  linarith

/-- Weighted Cauchy--Schwarz on a compact interval.  Keeping the weight's
actual mass is what preserves the logarithmic, rather than linear, cutoff
cost in MRT pp. 57--58. -/
theorem intervalIntegral_weighted_sq_le
    {w g : ℝ → ℝ} (hw : Continuous w) (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b)
    (hw0 : ∀ x, 0 ≤ w x)
    (hW : 0 < ∫ x in a..b, w x) :
    (∫ x in a..b, w x * g x) ^ 2 ≤
      (∫ x in a..b, w x) * ∫ x in a..b, w x * (g x) ^ 2 := by
  let W := ∫ x in a..b, w x
  let J := ∫ x in a..b, w x * g x
  let Q := ∫ x in a..b, w x * (g x) ^ 2
  have hwI : IntervalIntegrable w volume a b := hw.intervalIntegrable a b
  have hwgI : IntervalIntegrable (fun x ↦ w x * g x) volume a b :=
    (hw.mul hg).intervalIntegrable a b
  have hwg2I : IntervalIntegrable (fun x ↦ w x * (g x) ^ 2) volume a b :=
    (hw.mul (hg.pow 2)).intervalIntegrable a b
  have hnonneg : 0 ≤ ∫ x in a..b, w x * (W * g x - J) ^ 2 := by
    apply intervalIntegral.integral_nonneg hab
    intro x hx
    exact mul_nonneg (hw0 x) (sq_nonneg _)
  have hexpand :
      (∫ x in a..b, w x * (W * g x - J) ^ 2) =
        W * (W * Q - J ^ 2) := by
    have hfun : (fun x : ℝ ↦ w x * (W * g x - J) ^ 2) =
        fun x ↦ W ^ 2 * (w x * (g x) ^ 2) -
          2 * W * J * (w x * g x) + J ^ 2 * w x := by
      funext x
      ring
    have hfirstI : IntervalIntegrable
        (fun x ↦ W ^ 2 * (w x * (g x) ^ 2)) volume a b :=
      hwg2I.const_mul (W ^ 2)
    have hsecondI : IntervalIntegrable
        (fun x ↦ 2 * W * J * (w x * g x)) volume a b :=
      hwgI.const_mul (2 * W * J)
    have hthirdI : IntervalIntegrable
        (fun x ↦ J ^ 2 * w x) volume a b := hwI.const_mul (J ^ 2)
    have hsubI := hfirstI.sub hsecondI
    rw [hfun]
    rw [intervalIntegral.integral_add hsubI hthirdI]
    rw [intervalIntegral.integral_sub hfirstI hsecondI]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    dsimp only [W, J, Q]
    ring
  rw [hexpand] at hnonneg
  have hW' : 0 < W := by simpa only [W] using hW
  have hdiff := (mul_nonneg_iff_of_pos_left hW').mp hnonneg
  dsimp only [W, J, Q] at hdiff ⊢
  linarith

/-- Weighted Holder at exponent four on a compact interval, obtained by two
applications of the preceding weighted Cauchy inequality. -/
theorem intervalIntegral_weighted_fourth_le
    {w g : ℝ → ℝ} (hw : Continuous w) (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b)
    (hw0 : ∀ x, 0 ≤ w x)
    (hW : 0 < ∫ x in a..b, w x) :
    (∫ x in a..b, w x * g x) ^ 4 ≤
      (∫ x in a..b, w x) ^ 3 *
        ∫ x in a..b, w x * (g x) ^ 4 := by
  let W : ℝ := ∫ x in a..b, w x
  let P₂ : ℝ := ∫ x in a..b, w x * (g x) ^ 2
  let P₄ : ℝ := ∫ x in a..b, w x * (g x) ^ 4
  have hW0 : 0 ≤ W := hW.le
  have hP₂ : 0 ≤ P₂ := by
    dsimp [P₂]
    exact intervalIntegral.integral_nonneg hab
      (fun x hx => mul_nonneg (hw0 x) (sq_nonneg (g x)))
  have hfirst : (∫ x in a..b, w x * g x) ^ 2 ≤ W * P₂ := by
    simpa [W, P₂] using intervalIntegral_weighted_sq_le
      hw hg hab hw0 hW
  have hfirstSq : (∫ x in a..b, w x * g x) ^ 4 ≤
      (W * P₂) ^ 2 := by
    have hsquare := pow_le_pow_left₀
      (sq_nonneg (∫ x in a..b, w x * g x)) hfirst 2
    convert hsquare using 1 <;> ring
  have hsecond : P₂ ^ 2 ≤ W * P₄ := by
    have hs := intervalIntegral_weighted_sq_le hw (hg.pow 2) hab hw0 hW
    simpa [W, P₂, P₄, ← pow_mul] using hs
  calc
    (∫ x in a..b, w x * g x) ^ 4 ≤ (W * P₂) ^ 2 := hfirstSq
    _ = W ^ 2 * P₂ ^ 2 := by ring
    _ ≤ W ^ 2 * (W * P₄) :=
      mul_le_mul_of_nonneg_left hsecond (sq_nonneg W)
    _ = W ^ 3 * P₄ := by ring
    _ = (∫ x in a..b, w x) ^ 3 *
        ∫ x in a..b, w x * (g x) ^ 4 := rfl

/-- Convolution with the finite Perron cutoff kernel. -/
def perronConvolution (G : ℝ → ℝ) (V t : ℝ) : ℝ :=
  ∫ u in (-V)..V, perronWeight u * G (t + u)

theorem continuous_perronConvolution
    {G : ℝ → ℝ} (hG : Continuous G) {V : ℝ} (hV : 0 ≤ V) :
    Continuous (perronConvolution G V) := by
  have hparam : Continuous (fun t : ℝ ↦
      ∫ u in Set.Icc (-V) V, perronWeight u * G (t + u)) := by
    apply continuous_parametric_integral_of_continuous
    · exact (continuous_perronWeight.comp continuous_snd).mul
        (hG.comp (continuous_fst.add continuous_snd))
    · exact isCompact_Icc
  have heq : perronConvolution G V = fun t : ℝ ↦
      ∫ u in Set.Icc (-V) V, perronWeight u * G (t + u) := by
    funext t
    rw [perronConvolution, intervalIntegral.integral_of_le (by linarith),
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [heq]
  exact hparam

theorem perronConvolution_nonneg
    {G : ℝ → ℝ} (hG0 : ∀ t, 0 ≤ G t) {V t : ℝ} (hV : 0 ≤ V) :
    0 ≤ perronConvolution G V t := by
  unfold perronConvolution
  apply intervalIntegral.integral_nonneg (by linarith)
  intro u hu
  exact mul_nonneg (perronWeight_pos u).le (hG0 _)

/-- Pointwise weighted Cauchy for the Perron convolution. -/
theorem perronConvolution_sq_le_weightMass_mul
    {G : ℝ → ℝ} (hG : Continuous G) {V t : ℝ} (hV : 0 < V) :
    (perronConvolution G V t) ^ 2 ≤
      (∫ u in (-V)..V, perronWeight u) *
        perronConvolution (fun x ↦ (G x) ^ 2) V t := by
  have hW : 0 < ∫ u in (-V)..V, perronWeight u := by
    apply intervalIntegral.integral_pos (by linarith)
    · exact continuous_perronWeight.continuousOn
    · intro u hu
      exact (perronWeight_pos u).le
    · refine ⟨0, ?_, perronWeight_pos 0⟩
      constructor <;> linarith
  simpa only [perronConvolution] using
    (intervalIntegral_weighted_sq_le continuous_perronWeight
      (hG.comp (continuous_const.add continuous_id)) (by linarith)
      (fun u ↦ (perronWeight_pos u).le) hW)

/-- Weighted Holder at exponent four for the Perron convolution.  It is
obtained by applying the certified weighted Cauchy inequality twice, so the
kernel pays exactly the cube of its `L¹` mass. -/
theorem perronConvolution_fourth_le_cubeWeightMass_mul
    {G : ℝ → ℝ} (hG : Continuous G) {V t : ℝ} (hV : 0 < V) :
    (perronConvolution G V t) ^ 4 ≤
      (∫ u in (-V)..V, perronWeight u) ^ 3 *
        perronConvolution (fun x => (G x) ^ 4) V t := by
  let W : ℝ := ∫ u in (-V)..V, perronWeight u
  let P₂ : ℝ := perronConvolution (fun x => (G x) ^ 2) V t
  let P₄ : ℝ := perronConvolution (fun x => (G x) ^ 4) V t
  have hW : 0 ≤ W := by
    dsimp [W]
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun u hu => (perronWeight_pos u).le)
  have hP₂ : 0 ≤ P₂ := by
    dsimp [P₂]
    exact perronConvolution_nonneg (fun x => sq_nonneg (G x)) hV.le
  have hfirst : (perronConvolution G V t) ^ 2 ≤ W * P₂ := by
    simpa [W, P₂] using perronConvolution_sq_le_weightMass_mul hG hV
  have hfirstSq : (perronConvolution G V t) ^ 4 ≤ (W * P₂) ^ 2 := by
    have hsquare := pow_le_pow_left₀ (sq_nonneg (perronConvolution G V t))
      hfirst 2
    convert hsquare using 1 <;> ring
  have hsecond : P₂ ^ 2 ≤ W * P₄ := by
    have hs := perronConvolution_sq_le_weightMass_mul
      (t := t) (hG.pow 2) hV
    simpa [W, P₂, P₄, ← pow_mul] using hs
  calc
    (perronConvolution G V t) ^ 4 ≤ (W * P₂) ^ 2 := hfirstSq
    _ = W ^ 2 * P₂ ^ 2 := by ring
    _ ≤ W ^ 2 * (W * P₄) :=
      mul_le_mul_of_nonneg_left hsecond (sq_nonneg W)
    _ = W ^ 3 * P₄ := by ring
    _ = (∫ u in (-V)..V, perronWeight u) ^ 3 *
        perronConvolution (fun x => (G x) ^ 4) V t := rfl

/-- Fubini plus translated-interval inclusion.  This is the precise source
of the second cutoff-weight mass on MRT p. 58. -/
theorem integral_perronConvolution_le_weightMass_mul_enlarged
    {G : ℝ → ℝ} (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t)
    {a b V : ℝ} (hab : a ≤ b) (hV : 0 ≤ V) :
    (∫ t in a..b, perronConvolution G V t) ≤
      (∫ u in (-V)..V, perronWeight u) *
        ∫ s in (a - V)..(b + V), G s := by
  have hrect : MeasureTheory.Integrable
      (Function.uncurry (fun t u : ℝ ↦ perronWeight u * G (t + u)))
      ((volume.restrict (Set.Ioc a b)).prod
        (volume.restrict (Set.Ioc (-V) V))) := by
    rw [MeasureTheory.Measure.prod_restrict]
    have hcompact : IsCompact
        (Set.Icc a b ×ˢ Set.Icc (-V) V) := isCompact_Icc.prod isCompact_Icc
    have hcont : Continuous (fun p : ℝ × ℝ ↦
        perronWeight p.2 * G (p.1 + p.2)) :=
      (continuous_perronWeight.comp continuous_snd).mul
        (hG.comp (continuous_fst.add continuous_snd))
    exact (ContinuousOn.integrableOn_compact hcompact hcont.continuousOn).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  have hswap :
      (∫ t in a..b, ∫ u in (-V)..V, perronWeight u * G (t + u)) =
        ∫ u in (-V)..V, ∫ t in a..b, perronWeight u * G (t + u) := by
    simp_rw [intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_of_le (by linarith : -V ≤ V)]
    exact MeasureTheory.integral_integral_swap hrect
  unfold perronConvolution
  rw [hswap]
  have houter :
      (∫ u in (-V)..V, ∫ t in a..b, perronWeight u * G (t + u)) ≤
        ∫ u in (-V)..V,
          perronWeight u * (∫ s in (a - V)..(b + V), G s) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · have hinnerCont : Continuous (fun u : ℝ ↦
          ∫ t in a..b, perronWeight u * G (t + u)) := by
        have hparam : Continuous (fun u : ℝ ↦
            ∫ t in Set.Icc a b, perronWeight u * G (t + u)) := by
          apply continuous_parametric_integral_of_continuous
          · exact (continuous_perronWeight.comp continuous_fst).mul
              (hG.comp (continuous_snd.add continuous_fst))
          · exact isCompact_Icc
        have heq : (fun u : ℝ ↦
            ∫ t in a..b, perronWeight u * G (t + u)) =
            fun u : ℝ ↦ ∫ t in Set.Icc a b,
              perronWeight u * G (t + u) := by
          funext u
          rw [intervalIntegral.integral_of_le hab,
            MeasureTheory.integral_Icc_eq_integral_Ioc]
        rw [heq]
        exact hparam
      exact hinnerCont.intervalIntegrable _ _
    · exact (continuous_perronWeight.mul continuous_const).intervalIntegrable _ _
    · intro u hu
      have hu' : u ∈ Set.Icc (-V) V := by
        simpa [Set.uIcc_of_le (by linarith : -V ≤ V)] using hu
      rw [intervalIntegral.integral_const_mul]
      apply mul_le_mul_of_nonneg_left _ (perronWeight_pos u).le
      rw [intervalIntegral.integral_comp_add_right]
      apply intervalIntegral.integral_mono_interval
      · linarith [hu'.1]
      · simpa [add_comm] using add_le_add_right hab u
      · linarith [hu'.2]
      · exact Filter.Eventually.of_forall fun x ↦ hG0 x
      · exact hG.intervalIntegrable _ _
  calc
    (∫ u in (-V)..V, ∫ t in a..b, perronWeight u * G (t + u)) ≤
        ∫ u in (-V)..V,
          perronWeight u * (∫ s in (a - V)..(b + V), G s) := houter
    _ = (∫ u in (-V)..V, perronWeight u) *
        ∫ s in (a - V)..(b + V), G s := by
      rw [intervalIntegral.integral_mul_const]

/-- The exact Minkowski/Cauchy consequence used on MRT p. 58: cutoff
convolution costs the square of the logarithmic kernel mass and enlarges the
outer interval by `V` on each side. -/
theorem integral_sq_perronConvolution_le_sqWeightMass_mul_enlarged
    {G : ℝ → ℝ} (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t)
    {a b V : ℝ} (hab : a ≤ b) (hV : 0 < V) :
    (∫ t in a..b, (perronConvolution G V t) ^ 2) ≤
      (∫ u in (-V)..V, perronWeight u) ^ 2 *
        ∫ s in (a - V)..(b + V), (G s) ^ 2 := by
  let W := ∫ u in (-V)..V, perronWeight u
  have hW0 : 0 ≤ W := by
    dsimp only [W]
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun u hu ↦ (perronWeight_pos u).le)
  have hconvCont : Continuous (perronConvolution G V) :=
    continuous_perronConvolution hG hV.le
  have hsqCont : Continuous (fun t ↦ (perronConvolution G V t) ^ 2) :=
    hconvCont.pow 2
  have hrightCont : Continuous (fun t ↦
      W * perronConvolution (fun x ↦ (G x) ^ 2) V t) :=
    continuous_const.mul
      (continuous_perronConvolution (hG.pow 2) hV.le)
  have hfirst :
      (∫ t in a..b, (perronConvolution G V t) ^ 2) ≤
        ∫ t in a..b,
          W * perronConvolution (fun x ↦ (G x) ^ 2) V t := by
    apply intervalIntegral.integral_mono_on hab
    · exact hsqCont.intervalIntegrable _ _
    · exact hrightCont.intervalIntegrable _ _
    · intro t ht
      dsimp only [W]
      exact perronConvolution_sq_le_weightMass_mul hG hV
  have hsweep := integral_perronConvolution_le_weightMass_mul_enlarged
    (hG.pow 2) (fun t ↦ sq_nonneg (G t)) hab hV.le
  calc
    (∫ t in a..b, (perronConvolution G V t) ^ 2) ≤
        ∫ t in a..b,
          W * perronConvolution (fun x ↦ (G x) ^ 2) V t := hfirst
    _ = W * ∫ t in a..b,
          perronConvolution (fun x ↦ (G x) ^ 2) V t := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ W * (W * ∫ s in (a - V)..(b + V), (G s) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hsweep hW0
    _ = W ^ 2 * ∫ s in (a - V)..(b + V), (G s) ^ 2 := by ring

/-- Full compact-component transfer after pointwise cutoff removal, including
the ordinary constant error.  This is the scalar core of the passage from the
display before (95) to the p. 58 enlarged untruncated mean. -/
theorem component_square_transfer_of_pointwise_cutoff
    {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G)
    (hF0 : ∀ t, 0 ≤ F t) (hG0 : ∀ t, 0 ≤ G t)
    {a b V K E : ℝ} (hab : a ≤ b) (hV : 0 < V)
    (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hpoint : ∀ t, F t ≤ K * (perronConvolution G V t + E)) :
    (∫ t in a..b, (F t) ^ 2) ≤
      2 * K ^ 2 *
        ((∫ u in (-V)..V, perronWeight u) ^ 2 *
            (∫ s in (a - V)..(b + V), (G s) ^ 2) +
          (b - a) * E ^ 2) := by
  have hconv0 (t : ℝ) : 0 ≤ perronConvolution G V t :=
    perronConvolution_nonneg hG0 hV.le
  have hpointSq (t : ℝ) :
      (F t) ^ 2 ≤
        2 * K ^ 2 * ((perronConvolution G V t) ^ 2 + E ^ 2) := by
    have hright0 : 0 ≤ K * (perronConvolution G V t + E) :=
      mul_nonneg hK (add_nonneg (hconv0 t) hE)
    have hsquare : (F t) ^ 2 ≤
        (K * (perronConvolution G V t + E)) ^ 2 := by
      exact (sq_le_sq₀ (hF0 t) hright0).2 (hpoint t)
    calc
      (F t) ^ 2 ≤ (K * (perronConvolution G V t + E)) ^ 2 := hsquare
      _ ≤ 2 * K ^ 2 * ((perronConvolution G V t) ^ 2 + E ^ 2) := by
        nlinarith [sq_nonneg (perronConvolution G V t - E), sq_nonneg K]
  have hleftI : IntervalIntegrable (fun t ↦ (F t) ^ 2) volume a b :=
    (hF.pow 2).intervalIntegrable _ _
  have hrightCont : Continuous (fun t ↦
      2 * K ^ 2 * ((perronConvolution G V t) ^ 2 + E ^ 2)) :=
    continuous_const.mul
      ((continuous_perronConvolution hG hV.le).pow 2 |>.add continuous_const)
  have hintegrated :
      (∫ t in a..b, (F t) ^ 2) ≤
        ∫ t in a..b,
          2 * K ^ 2 * ((perronConvolution G V t) ^ 2 + E ^ 2) := by
    apply intervalIntegral.integral_mono_on hab hleftI
      (hrightCont.intervalIntegrable _ _)
    intro t ht
    exact hpointSq t
  have hmink := integral_sq_perronConvolution_le_sqWeightMass_mul_enlarged
    hG hG0 hab hV
  calc
    (∫ t in a..b, (F t) ^ 2) ≤
        ∫ t in a..b,
          2 * K ^ 2 * ((perronConvolution G V t) ^ 2 + E ^ 2) := hintegrated
    _ = 2 * K ^ 2 *
        ((∫ t in a..b, (perronConvolution G V t) ^ 2) +
          (b - a) * E ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_add
        ((continuous_perronConvolution hG hV.le).pow 2 |>.intervalIntegrable _ _)
        intervalIntegrable_const]
      simp only [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ 2 * K ^ 2 *
        ((∫ u in (-V)..V, perronWeight u) ^ 2 *
            (∫ s in (a - V)..(b + V), (G s) ^ 2) +
          (b - a) * E ^ 2) := by
      gcongr

/-- Symmetric moving window used in (95). -/
def movingIntegral (F : ℝ → ℝ) (U t : ℝ) : ℝ :=
  ∫ s in (t - U)..(t + U), F s

theorem continuous_movingIntegral
    {F : ℝ → ℝ} (hF : Continuous F) (U : ℝ) :
    Continuous (movingIntegral F U) := by
  let A : ℝ → ℝ := fun x ↦ ∫ s in 0..x, F s
  have hA : Continuous A := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hF.integral_hasStrictDerivAt 0 x).hasDerivAt.continuousAt
  have heq : movingIntegral F U = fun t ↦ A (t + U) - A (t - U) := by
    funext t
    unfold movingIntegral
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (μ := volume) 0 (t - U))
      (hF.intervalIntegrable (μ := volume) (t - U) (t + U))
    dsimp only [A]
    linarith
  rw [heq]
  exact (hA.comp (continuous_id.add continuous_const)).sub
    (hA.comp (continuous_id.sub continuous_const))

theorem movingIntegral_nonneg
    {F : ℝ → ℝ} (hF0 : ∀ t, 0 ≤ F t) {U t : ℝ} (hU : 0 ≤ U) :
    0 ≤ movingIntegral F U t := by
  unfold movingIntegral
  exact intervalIntegral.integral_nonneg (by linarith)
    (fun s hs ↦ hF0 s)

/-- Compact Fubini identity commuting the Perron cutoff with the symmetric
moving window. -/
theorem movingIntegral_perronConvolution_comm
    {F : ℝ → ℝ} (hF : Continuous F)
    {U V t : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) :
    movingIntegral (perronConvolution F V) U t =
      perronConvolution (movingIntegral F U) V t := by
  have hrect : MeasureTheory.Integrable
      (Function.uncurry (fun s u : ℝ ↦ perronWeight u * F (s + u)))
      ((volume.restrict (Set.Ioc (t - U) (t + U))).prod
        (volume.restrict (Set.Ioc (-V) V))) := by
    rw [MeasureTheory.Measure.prod_restrict]
    have hcompact : IsCompact
        (Set.Icc (t - U) (t + U) ×ˢ Set.Icc (-V) V) :=
      isCompact_Icc.prod isCompact_Icc
    have hcont : Continuous (fun p : ℝ × ℝ ↦
        perronWeight p.2 * F (p.1 + p.2)) :=
      (continuous_perronWeight.comp continuous_snd).mul
        (hF.comp (continuous_fst.add continuous_snd))
    exact (ContinuousOn.integrableOn_compact hcompact hcont.continuousOn).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  unfold movingIntegral perronConvolution
  have hswap :
      (∫ s in (t - U)..(t + U),
          ∫ u in (-V)..V, perronWeight u * F (s + u)) =
        ∫ u in (-V)..V,
          ∫ s in (t - U)..(t + U), perronWeight u * F (s + u) := by
    simp_rw [intervalIntegral.integral_of_le (by linarith : t - U ≤ t + U),
      intervalIntegral.integral_of_le (by linarith : -V ≤ V)]
    exact MeasureTheory.integral_integral_swap hrect
  rw [hswap]
  apply intervalIntegral.integral_congr
  intro u hu
  change (∫ s in (t - U)..(t + U), perronWeight u * F (s + u)) =
    perronWeight u * ∫ s in ((t + u) - U)..((t + u) + U), F s
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have hshift := intervalIntegral.integral_comp_add_right F u
    (a := t - U) (b := t + U)
  simpa [add_assoc, add_comm, add_left_comm, sub_eq_add_neg] using hshift

/-- Sum of moving windows over a finite character family. -/
def characterMovingMass {Chi : Type*} [Fintype Chi]
    (F : Chi → ℝ → ℝ) (U t : ℝ) : ℝ :=
  ∑ chi : Chi, movingIntegral (F chi) U t

theorem continuous_characterMovingMass
    {Chi : Type*} [Fintype Chi] {F : Chi → ℝ → ℝ}
    (hF : ∀ chi, Continuous (F chi)) (U : ℝ) :
    Continuous (characterMovingMass F U) := by
  unfold characterMovingMass
  apply continuous_finset_sum
  intro chi hchi
  exact continuous_movingIntegral (hF chi) U

theorem characterMovingMass_nonneg
    {Chi : Type*} [Fintype Chi] {F : Chi → ℝ → ℝ}
    (hF0 : ∀ chi t, 0 ≤ F chi t) {U t : ℝ} (hU : 0 ≤ U) :
    0 ≤ characterMovingMass F U t := by
  unfold characterMovingMass
  exact Finset.sum_nonneg fun chi hchi ↦ movingIntegral_nonneg (hF0 chi) hU

/-- Finite character sums commute exactly with the Perron convolution and
moving window. -/
theorem sum_movingIntegral_perronConvolution_eq
    {Chi : Type*} [Fintype Chi] {F : Chi → ℝ → ℝ}
    (hF : ∀ chi, Continuous (F chi))
    {U V t : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) :
    (∑ chi : Chi, movingIntegral (perronConvolution (F chi) V) U t) =
      perronConvolution (characterMovingMass F U) V t := by
  simp_rw [movingIntegral_perronConvolution_comm (hF _) hU hV]
  unfold perronConvolution characterMovingMass
  rw [← intervalIntegral.integral_finset_sum]
  · apply intervalIntegral.integral_congr
    intro u hu
    change (∑ i : Chi, perronWeight u * movingIntegral (F i) U (t + u)) =
      perronWeight u * ∑ i : Chi, movingIntegral (F i) U (t + u)
    rw [Finset.mul_sum]
  · intro chi hchi
    exact (continuous_perronWeight.mul
      ((continuous_movingIntegral (hF chi) U).comp
        (continuous_const.add continuous_id))).intervalIntegrable _ _

/-- Pointwise Corollary 2.5 summed over a finite character family and then
integrated over the inner window.  The Perron and moving-window integrals are
commuted by the preceding certified compact Fubini identity. -/
theorem characterMovingMass_le_of_pointwiseCutoff
    {Chi : Type*} [Fintype Chi]
    {clip full : Chi → ℝ → ℝ}
    (hclip : ∀ chi, Continuous (clip chi))
    (hfull : ∀ chi, Continuous (full chi))
    {U V K E₀ t : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hK : 0 ≤ K) (hE₀ : 0 ≤ E₀)
    (hpoint : ∀ chi s,
      clip chi s ≤ K * (perronConvolution (full chi) V s + E₀)) :
    characterMovingMass clip U t ≤
      K * (perronConvolution (characterMovingMass full U) V t +
        2 * U * (Fintype.card Chi : ℝ) * E₀) := by
  have hone (chi : Chi) :
      movingIntegral (clip chi) U t ≤
        K * (movingIntegral (perronConvolution (full chi) V) U t +
          2 * U * E₀) := by
    have hrightCont : Continuous (fun s ↦
        K * (perronConvolution (full chi) V s + E₀)) :=
      continuous_const.mul
        ((continuous_perronConvolution (hfull chi) hV).add continuous_const)
    have hint : movingIntegral (clip chi) U t ≤
        movingIntegral
          (fun s ↦ K * (perronConvolution (full chi) V s + E₀)) U t := by
      unfold movingIntegral
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact (hclip chi).intervalIntegrable _ _
      · exact hrightCont.intervalIntegrable _ _
      · intro s hs
        exact hpoint chi s
    calc
      movingIntegral (clip chi) U t ≤
          movingIntegral
            (fun s ↦ K * (perronConvolution (full chi) V s + E₀)) U t := hint
      _ = K * (movingIntegral (perronConvolution (full chi) V) U t +
          2 * U * E₀) := by
        unfold movingIntegral
        rw [intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_add
          ((continuous_perronConvolution (hfull chi) hV).intervalIntegrable _ _)
          intervalIntegrable_const]
        simp only [intervalIntegral.integral_const, smul_eq_mul]
        ring
  unfold characterMovingMass
  calc
    (∑ chi : Chi, movingIntegral (clip chi) U t) ≤
        ∑ chi : Chi,
          K * (movingIntegral (perronConvolution (full chi) V) U t +
            2 * U * E₀) := Finset.sum_le_sum fun chi hchi ↦ hone chi
    _ = K * ((∑ chi : Chi,
          movingIntegral (perronConvolution (full chi) V) U t) +
        2 * U * (Fintype.card Chi : ℝ) * E₀) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ = K * (perronConvolution
          (characterMovingMass full U) V t +
        2 * U * (Fintype.card Chi : ℝ) * E₀) := by
      rw [sum_movingIntegral_perronConvolution_eq hfull hU hV]

/-- The complete p. 57--58 transfer for one connected outer component and a
finite character family.  It exposes both losses: the square of the exact
Perron weight mass and the constant cutoff-error contribution. -/
theorem character_component_square_cutoff_transfer
    {Chi : Type*} [Fintype Chi]
    {clip full : Chi → ℝ → ℝ}
    (hclip : ∀ chi, Continuous (clip chi))
    (hfull : ∀ chi, Continuous (full chi))
    (hclip0 : ∀ chi t, 0 ≤ clip chi t)
    (hfull0 : ∀ chi t, 0 ≤ full chi t)
    {a b U V K E₀ : ℝ} (hab : a ≤ b) (hU : 0 ≤ U) (hV : 0 < V)
    (hK : 0 ≤ K) (hE₀ : 0 ≤ E₀)
    (hpoint : ∀ chi s,
      clip chi s ≤ K * (perronConvolution (full chi) V s + E₀)) :
    (∫ t in a..b, (characterMovingMass clip U t) ^ 2) ≤
      2 * K ^ 2 *
        ((∫ u in (-V)..V, perronWeight u) ^ 2 *
            (∫ s in (a - V)..(b + V),
              (characterMovingMass full U s) ^ 2) +
          (b - a) *
            (2 * U * (Fintype.card Chi : ℝ) * E₀) ^ 2) := by
  let F := characterMovingMass clip U
  let G := characterMovingMass full U
  let E := 2 * U * (Fintype.card Chi : ℝ) * E₀
  have hFcont : Continuous F := continuous_characterMovingMass hclip U
  have hGcont : Continuous G := continuous_characterMovingMass hfull U
  have hF0 : ∀ t, 0 ≤ F t := fun t ↦
    characterMovingMass_nonneg hclip0 hU
  have hG0 : ∀ t, 0 ≤ G t := fun t ↦
    characterMovingMass_nonneg hfull0 hU
  have hE : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hmass : ∀ t, F t ≤ K * (perronConvolution G V t + E) := by
    intro t
    dsimp only [F, G, E]
    exact characterMovingMass_le_of_pointwiseCutoff hclip hfull hU hV.le
      hK hE₀ hpoint
  simpa only [F, G, E] using
    component_square_transfer_of_pointwise_cutoff hFcont hGcont hF0 hG0
      hab hV hK hE hmass

end
end MAPMRTCorollary25Minkowski

#print axioms MAPMRTCorollary25Minkowski.intervalIntegral_sq_le_length_mul_integral_sq
#print axioms MAPMRTCorollary25Minkowski.intervalIntegral_weighted_sq_le
#print axioms MAPMRTCorollary25Minkowski.intervalIntegral_weighted_fourth_le
#print axioms MAPMRTCorollary25Minkowski.perronConvolution_fourth_le_cubeWeightMass_mul
#print axioms MAPMRTCorollary25Minkowski.integral_perronWeight
#print axioms MAPMRTCorollary25Minkowski.movingIntegral_perronConvolution_comm
#print axioms MAPMRTCorollary25Minkowski.character_component_square_cutoff_transfer
