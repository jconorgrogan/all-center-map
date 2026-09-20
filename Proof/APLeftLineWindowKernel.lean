import APAlignedComponentSource
import ComplexMonomialAverage

/-!
# Difference-level Perron bounds on the left line

The endpoint subtraction is kept inside the contour integral.  The resulting
factor `(b^s-a^s)/(Y*s)` is the complex average of `t^(s-1)`, so the window
length cancels before any norm is taken.  This avoids the artificial `X/Y`
loss of separate endpoint estimates.
-/

namespace MAPAPLeftLineWindowKernel

open MeasureTheory Set
open PrimitiveTruncatedExplicitFormulaBridge TruncatedTwistedPerron
open MAPPaperWindowVKBypass
open MAPAPCorrectedPaperEdgeComponentSource
open PaperEdgePrimitiveComponents

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Exact pointwise Perron-window identity. -/
theorem perronContourIntegrand_window_div_eq_logDeriv_mul_average
    (chi : DirichletCharacter ℂ q)
    {x Y : ℝ} (hx : 0 < x) (hY : 0 < Y)
    {s : ℂ} (hs : 0 < s.re) :
    (perronContourIntegrand chi (x + Y) s -
        perronContourIntegrand chi x s) / (Y : ℂ) =
      (-logDeriv (DirichletCharacter.LFunction chi) s) *
        complexRightAverage (fun t : ℝ => (t : ℂ) ^ (s - 1)) Y x := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  rw [complexRightAverage_cpow_sub_one_eq hx hY hs]
  unfold perronContourIntegrand
  field_simp [hs0, hY.ne']
  ring

/-- On a left line `0 < Re s ≤ 1`, endpoint subtraction before norms removes
the full `X/Y` loss. -/
theorem norm_perronContourIntegrand_window_div_le
    (chi : DirichletCharacter ℂ q)
    {x Y M : ℝ} (hx : 0 < x) (hY : 0 < Y)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re ≤ 1)
    (hlog : ‖logDeriv (DirichletCharacter.LFunction chi) s‖ ≤ M) :
    ‖(perronContourIntegrand chi (x + Y) s -
        perronContourIntegrand chi x s) / (Y : ℂ)‖ ≤
      M * Real.rpow x (s.re - 1) := by
  rw [perronContourIntegrand_window_div_eq_logDeriv_mul_average
    chi hx hY hs0, norm_mul, norm_neg]
  exact mul_le_mul hlog
    (norm_complexRightAverage_cpow_sub_one_le_trivial hx hY hs1)
    (norm_nonneg _) (le_trans (norm_nonneg _) hlog)

/-- The literal normalized left-line window, with subtraction inside the
vertical contour integral. -/
def normalizedLeftLineWindow
    (chi : DirichletCharacter ℂ q)
    (x Y sigma T : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ u in (-T)..T,
      (perronContourIntegrand chi (x + Y)
          ((sigma : ℂ) + Complex.I * u) -
        perronContourIntegrand chi x
          ((sigma : ℂ) + Complex.I * u)) / (Y : ℂ)

/-- Under the ordinary endpoint integrability hypotheses, the normalized
left-line window is exactly the difference of the two left-line components
divided by `Y`. -/
theorem leftLineIntegral_window_div_eq_normalizedLeftLineWindow
    (chi : DirichletCharacter ℂ q)
    {x Y sigma T : ℝ}
    (hxyInt : IntervalIntegrable
      (fun u : ℝ => perronContourIntegrand chi (x + Y)
        ((sigma : ℂ) + Complex.I * u)) volume (-T) T)
    (hxInt : IntervalIntegrable
      (fun u : ℝ => perronContourIntegrand chi x
        ((sigma : ℂ) + Complex.I * u)) volume (-T) T) :
    (leftLineIntegral chi (x + Y) sigma T -
        leftLineIntegral chi x sigma T) / (Y : ℂ) =
      normalizedLeftLineWindow chi x Y sigma T := by
  unfold leftLineIntegral normalizedLeftLineWindow
  rw [← mul_sub, ← intervalIntegral.integral_sub hxyInt hxInt,
    intervalIntegral.integral_div]
  ring

/-- Difference-level left-line estimate.  Its scale is `T * M * X^(sigma-1)`
rather than `T * M * X^sigma / Y`. -/
theorem norm_normalizedLeftLineWindow_le_of_logDeriv
    (chi : DirichletCharacter ℂ q)
    {x Y sigma T M : ℝ} (hx : 0 < x) (hY : 0 < Y)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma ≤ 1) (hT : 0 ≤ T)
    (hlog : ∀ u ∈ Set.Icc (-T) T,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((sigma : ℂ) + Complex.I * u)‖ ≤ M) :
    ‖normalizedLeftLineWindow chi x Y sigma T‖ ≤
      T / Real.pi * (M * Real.rpow x (sigma - 1)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold normalizedLeftLineWindow
  rw [norm_mul]
  have hconst : norm ((((2 * Real.pi : ℝ) : ℂ)⁻¹)) =
      (2 * Real.pi)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) hpi)]
  rw [hconst]
  have hint :
      ‖∫ u in (-T)..T,
          (perronContourIntegrand chi (x + Y)
              ((sigma : ℂ) + Complex.I * u) -
            perronContourIntegrand chi x
              ((sigma : ℂ) + Complex.I * u)) / (Y : ℂ)‖ ≤
        (M * Real.rpow x (sigma - 1)) * |T - (-T)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu => by
      have hu' : u ∈ Set.Icc (-T) T := by
        have huu : u ∈ Set.uIcc (-T) T := Set.uIoc_subset_uIcc hu
        simpa [Set.uIcc_of_le (neg_le_self hT)] using huu
      have hsre : (((sigma : ℂ) + Complex.I * u)).re = sigma := by simp
      simpa [hsre] using
        (norm_perronContourIntegrand_window_div_le chi hx hY
          (s := (sigma : ℂ) + Complex.I * u) (by simpa [hsre])
          (by simpa [hsre]) (hlog u hu')))
  calc
    (2 * Real.pi)⁻¹ *
        ‖∫ u in (-T)..T,
          (perronContourIntegrand chi (x + Y)
              ((sigma : ℂ) + Complex.I * u) -
            perronContourIntegrand chi x
              ((sigma : ℂ) + Complex.I * u)) / (Y : ℂ)‖
        ≤ (2 * Real.pi)⁻¹ *
          ((M * Real.rpow x (sigma - 1)) * |T - (-T)|) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = T / Real.pi * (M * Real.rpow x (sigma - 1)) := by
      have habs : |T - (-T)| = 2 * T := by
        rw [sub_neg_eq_add, ← two_mul,
          abs_of_nonneg (mul_nonneg (by norm_num) hT)]
      rw [habs]
      field_simp [ne_of_gt hpi]

/-- Literal aligned-component consequence.  The half-integer interval has
length at most `Y+1`; for every legal `Y ≥ 1` this costs only the constant
factor two.  The endpoint integrability assumptions are deterministic
contour regularity obligations, not an estimate. -/
theorem norm_leftComponent_window_div_le_two
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {x Y sigma T M : ℝ} (hx : 0 ≤ x) (hY : 1 ≤ Y)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma ≤ 1) (hT : 0 ≤ T)
    (hxyInt : IntervalIntegrable
      (fun u : ℝ => perronContourIntegrand chi.primitiveCharacter
        (halfIntegerPoint ⌊x + Y⌋₊)
          ((sigma : ℂ) + Complex.I * u)) volume (-T) T)
    (hxInt : IntervalIntegrable
      (fun u : ℝ => perronContourIntegrand chi.primitiveCharacter
        (halfIntegerPoint ⌊x⌋₊)
          ((sigma : ℂ) + Complex.I * u)) volume (-T) T)
    (hlog : ∀ u ∈ Set.Icc (-T) T,
      ‖logDeriv (DirichletCharacter.LFunction chi.primitiveCharacter)
        ((sigma : ℂ) + Complex.I * u)‖ ≤ M) :
    ‖(leftComponent chi sigma T (x + Y) -
        leftComponent chi sigma T x) / (Y : ℂ)‖ ≤
      2 * (T / Real.pi *
        (M * Real.rpow (halfIntegerPoint ⌊x⌋₊) (sigma - 1))) := by
  let a := halfIntegerPoint ⌊x⌋₊
  let b := halfIntegerPoint ⌊x + Y⌋₊
  let d := b - a
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hfloor : ⌊x⌋₊ ≤ ⌊x + Y⌋₊ :=
    Nat.floor_mono (by linarith)
  have hab : a ≤ b := by
    have hfloorReal : (⌊x⌋₊ : ℝ) ≤ (⌊x + Y⌋₊ : ℝ) := by
      exact_mod_cast hfloor
    dsimp only [a, b, halfIntegerPoint]
    linarith
  have hd0 : 0 ≤ d := sub_nonneg.mpr hab
  have ha0 : 0 < a := by
    dsimp only [a]
    exact halfIntegerPoint_pos _
  have hdle : d ≤ Y + 1 := by
    have hdisp :=
      MAPAPHalfIntegerAlignedTail.abs_halfInteger_window_sub_length_le_one hx
        (zero_le_one.trans hY)
    change |d - Y| ≤ 1 at hdisp
    linarith [le_abs_self (d - Y)]
  have hdY : d / Y ≤ 2 := by
    apply (div_le_iff₀ hY0).2
    calc
      d ≤ Y + 1 := hdle
      _ ≤ 2 * Y := by linarith
  have hM : 0 ≤ M := by
    have hz := hlog 0 (by simp [hT])
    exact (norm_nonneg _).trans hz
  have hboundnonneg :
      0 ≤ T / Real.pi *
        (M * Real.rpow a (sigma - 1)) := by
    exact mul_nonneg (div_nonneg hT Real.pi_pos.le)
      (mul_nonneg hM (Real.rpow_nonneg ha0.le _))
  by_cases hd : d = 0
  · have habEq : b = a := by linarith
    have hcomp : leftComponent chi sigma T (x + Y) =
        leftComponent chi sigma T x := by
      simp only [leftComponent]
      change leftLineIntegral chi.primitiveCharacter b sigma T =
        leftLineIntegral chi.primitiveCharacter a sigma T
      rw [habEq]
    rw [hcomp, sub_self, zero_div, norm_zero]
    positivity
  · have hdpos : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hd)
    have hIntB : IntervalIntegrable
        (fun u : ℝ => perronContourIntegrand chi.primitiveCharacter
          (a + d) ((sigma : ℂ) + Complex.I * u)) volume (-T) T := by
      convert hxyInt using 1 <;> dsimp only [a, b, d] <;> ring
    have heq := leftLineIntegral_window_div_eq_normalizedLeftLineWindow
      chi.primitiveCharacter (x := a) (Y := d) (sigma := sigma) (T := T)
        hIntB hxInt
    have hnorm := norm_normalizedLeftLineWindow_le_of_logDeriv
      chi.primitiveCharacter (x := a) (Y := d) ha0 hdpos
        hsigma0 hsigma1 hT hlog
    have hline :
        ‖(leftLineIntegral chi.primitiveCharacter b sigma T -
            leftLineIntegral chi.primitiveCharacter a sigma T) / (d : ℂ)‖ ≤
          T / Real.pi * (M * Real.rpow a (sigma - 1)) := by
      have habAdd : a + d = b := by dsimp only [d]; ring
      rw [← habAdd]
      rw [heq]
      exact hnorm
    simp only [leftComponent]
    change ‖(leftLineIntegral chi.primitiveCharacter b sigma T -
        leftLineIntegral chi.primitiveCharacter a sigma T) / (Y : ℂ)‖ ≤ _
    have hfactor :
        (leftLineIntegral chi.primitiveCharacter b sigma T -
            leftLineIntegral chi.primitiveCharacter a sigma T) / (Y : ℂ) =
          ((d : ℂ) / (Y : ℂ)) *
            ((leftLineIntegral chi.primitiveCharacter b sigma T -
              leftLineIntegral chi.primitiveCharacter a sigma T) / (d : ℂ)) := by
      field_simp [hd, hY0.ne']
    rw [hfactor, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hd0,
      abs_of_pos hY0]
    calc
      d / Y *
          ‖(leftLineIntegral chi.primitiveCharacter b sigma T -
              leftLineIntegral chi.primitiveCharacter a sigma T) / (d : ℂ)‖
          ≤ d / Y *
              (T / Real.pi * (M * Real.rpow a (sigma - 1))) :=
        mul_le_mul_of_nonneg_left hline (div_nonneg hd0 hY0.le)
      _ ≤ 2 * (T / Real.pi *
            (M * Real.rpow a (sigma - 1))) :=
        mul_le_mul_of_nonneg_right hdY hboundnonneg

/-! ## Fixed-edge horizontal difference

The actual paper edge moves slightly with the endpoint.  The next lemmas
close the common-edge part exactly; the remaining edge-change strip is left
visible rather than hidden in an endpointwise norm.
-/

/-- A nonoscillatory complex-monomial average bound valid up to a right-edge
exponent `c ≥ 1`. -/
theorem norm_complexRightAverage_cpow_sub_one_le_upper
    {x Y U c : ℝ} (hx : 1 ≤ x) (hY : 0 < Y)
    (hxyU : x + Y ≤ U) (hc : 1 ≤ c)
    {s : ℂ} (hsc : s.re ≤ c) :
    ‖complexRightAverage (fun t : ℝ => (t : ℂ) ^ (s - 1)) Y x‖ ≤
      Real.rpow U (c - 1) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hU : 1 ≤ U := hx.trans (le_trans (le_add_of_nonneg_right hY.le) hxyU)
  have hint :
      ‖∫ t : ℝ in x..x + Y, (t : ℂ) ^ (s - 1)‖ ≤
        Real.rpow U (c - 1) * |(x + Y) - x| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => by
      have ht' : t ∈ Set.Ioc x (x + Y) := by
        rw [Set.uIoc_of_le (le_add_of_nonneg_right hY.le)] at ht
        exact ht
      have ht1 : 1 ≤ t := hx.trans (le_of_lt ht'.1)
      have htU : t ≤ U := ht'.2.trans hxyU
      rw [Complex.norm_cpow_eq_rpow_re_of_pos
        (zero_lt_one.trans_le ht1)]
      simp only [Complex.sub_re, Complex.one_re]
      calc
        Real.rpow t (s.re - 1) ≤ Real.rpow t (c - 1) :=
          Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
        _ ≤ Real.rpow U (c - 1) :=
          Real.rpow_le_rpow (zero_le_one.trans ht1) htU (by linarith))
  unfold complexRightAverage
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hY]
  have habs : |(x + Y) - x| = Y := by simp [abs_of_pos hY]
  rw [habs] at hint
  calc
    Y⁻¹ * ‖∫ t : ℝ in x..x + Y, (t : ℂ) ^ (s - 1)‖ ≤
        Y⁻¹ * (Real.rpow U (c - 1) * Y) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hY.le)
    _ = Real.rpow U (c - 1) := by field_simp

/-- Pointwise common-edge horizontal kernel bound after window
normalization. -/
theorem norm_perronContourIntegrand_window_div_le_upper
    (chi : DirichletCharacter ℂ q)
    {x Y U c M : ℝ} (hx : 1 ≤ x) (hY : 0 < Y)
    (hxyU : x + Y ≤ U) (hc : 1 ≤ c)
    {s : ℂ} (hs0 : 0 < s.re) (hsc : s.re ≤ c)
    (hlog : ‖logDeriv (DirichletCharacter.LFunction chi) s‖ ≤ M) :
    ‖(perronContourIntegrand chi (x + Y) s -
        perronContourIntegrand chi x s) / (Y : ℂ)‖ ≤
      M * Real.rpow U (c - 1) := by
  rw [perronContourIntegrand_window_div_eq_logDeriv_mul_average
    chi (zero_lt_one.trans_le hx) hY hs0, norm_mul, norm_neg]
  exact mul_le_mul hlog
    (norm_complexRightAverage_cpow_sub_one_le_upper hx hY hxyU hc hsc)
    (norm_nonneg _) (le_trans (norm_nonneg _) hlog)

/-- The horizontal-pair window with a single fixed right edge `c`. -/
def normalizedFixedEdgeHorizontalWindow
    (chi : DirichletCharacter ℂ q)
    (x Y sigma c T : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹ * Complex.I) *
      (∫ r in sigma..c,
        (perronContourIntegrand chi (x + Y)
            ((r : ℂ) + Complex.I * T) -
          perronContourIntegrand chi x
            ((r : ℂ) + Complex.I * T)) / (Y : ℂ)) -
    (((2 * Real.pi : ℝ) : ℂ)⁻¹ * Complex.I) *
      (∫ r in sigma..c,
        (perronContourIntegrand chi (x + Y)
            ((r : ℂ) - Complex.I * T) -
          perronContourIntegrand chi x
            ((r : ℂ) - Complex.I * T)) / (Y : ℂ))

/-- Exact fixed-edge horizontal window identity. -/
theorem horizontalBoundaryIntegral_window_div_eq_fixedEdge
    (chi : DirichletCharacter ℂ q)
    {x Y sigma c T : ℝ}
    (htopXY : IntervalIntegrable
      (fun r : ℝ => perronContourIntegrand chi (x + Y)
        ((r : ℂ) + Complex.I * T)) volume sigma c)
    (htopX : IntervalIntegrable
      (fun r : ℝ => perronContourIntegrand chi x
        ((r : ℂ) + Complex.I * T)) volume sigma c)
    (hbotXY : IntervalIntegrable
      (fun r : ℝ => perronContourIntegrand chi (x + Y)
        ((r : ℂ) - Complex.I * T)) volume sigma c)
    (hbotX : IntervalIntegrable
      (fun r : ℝ => perronContourIntegrand chi x
        ((r : ℂ) - Complex.I * T)) volume sigma c) :
    (horizontalBoundaryIntegral chi (x + Y) sigma c T -
        horizontalBoundaryIntegral chi x sigma c T) / (Y : ℂ) =
      normalizedFixedEdgeHorizontalWindow chi x Y sigma c T := by
  unfold horizontalBoundaryIntegral normalizedFixedEdgeHorizontalWindow
  rw [intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_sub htopXY htopX,
    intervalIntegral.integral_sub hbotXY hbotX]
  ring

/-- Common-edge horizontal estimate with endpoint cancellation preserved.
The moving-edge strip is not included in this theorem. -/
theorem norm_normalizedFixedEdgeHorizontalWindow_le
    (chi : DirichletCharacter ℂ q)
    {x Y U sigma c T M : ℝ}
    (hx : 1 ≤ x) (hY : 0 < Y) (hxyU : x + Y ≤ U)
    (hsigma0 : 0 < sigma) (hsigmaC : sigma ≤ c) (hc : 1 ≤ c)
    (htop : ∀ r ∈ Set.Icc sigma c,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * T)‖ ≤ M)
    (hbottom : ∀ r ∈ Set.Icc sigma c,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) - Complex.I * T)‖ ≤ M) :
    ‖normalizedFixedEdgeHorizontalWindow chi x Y sigma c T‖ ≤
      (c - sigma) / Real.pi * (M * Real.rpow U (c - 1)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have htopint :
      ‖∫ r in sigma..c,
          (perronContourIntegrand chi (x + Y)
              ((r : ℂ) + Complex.I * T) -
            perronContourIntegrand chi x
              ((r : ℂ) + Complex.I * T)) / (Y : ℂ)‖ ≤
        (M * Real.rpow U (c - 1)) * |c - sigma| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun r hr => by
      have hr' : r ∈ Set.Icc sigma c := by
        have hru : r ∈ Set.uIcc sigma c := Set.uIoc_subset_uIcc hr
        simpa [Set.uIcc_of_le hsigmaC] using hru
      apply norm_perronContourIntegrand_window_div_le_upper chi hx hY
        hxyU hc (s := (r : ℂ) + Complex.I * T)
      · simpa using hsigma0.trans_le hr'.1
      · simpa using hr'.2
      · exact htop r hr')
  have hbotint :
      ‖∫ r in sigma..c,
          (perronContourIntegrand chi (x + Y)
              ((r : ℂ) - Complex.I * T) -
            perronContourIntegrand chi x
              ((r : ℂ) - Complex.I * T)) / (Y : ℂ)‖ ≤
        (M * Real.rpow U (c - 1)) * |c - sigma| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun r hr => by
      have hr' : r ∈ Set.Icc sigma c := by
        have hru : r ∈ Set.uIcc sigma c := Set.uIoc_subset_uIcc hr
        simpa [Set.uIcc_of_le hsigmaC] using hru
      apply norm_perronContourIntegrand_window_div_le_upper chi hx hY
        hxyU hc (s := (r : ℂ) - Complex.I * T)
      · simpa using hsigma0.trans_le hr'.1
      · simpa using hr'.2
      · exact hbottom r hr')
  let A : ℂ := ((2 * Real.pi : ℝ) : ℂ)⁻¹ * Complex.I
  let Itop : ℂ := ∫ r in sigma..c,
    (perronContourIntegrand chi (x + Y) ((r : ℂ) + Complex.I * T) -
      perronContourIntegrand chi x ((r : ℂ) + Complex.I * T)) / (Y : ℂ)
  let Ibot : ℂ := ∫ r in sigma..c,
    (perronContourIntegrand chi (x + Y) ((r : ℂ) - Complex.I * T) -
      perronContourIntegrand chi x ((r : ℂ) - Complex.I * T)) / (Y : ℂ)
  have hA : ‖A‖ = (2 * Real.pi)⁻¹ := by
    dsimp [A]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) hpi), Complex.norm_I, mul_one]
  change ‖A * Itop - A * Ibot‖ ≤ _
  calc
    ‖A * Itop - A * Ibot‖ ≤ ‖A * Itop‖ + ‖A * Ibot‖ :=
      norm_sub_le _ _
    _ = (2 * Real.pi)⁻¹ * ‖Itop‖ +
        (2 * Real.pi)⁻¹ * ‖Ibot‖ := by
      rw [norm_mul A Itop, norm_mul A Ibot, hA]
    _ ≤ (2 * Real.pi)⁻¹ *
          ((M * Real.rpow U (c - 1)) * |c - sigma|) +
        (2 * Real.pi)⁻¹ *
          ((M * Real.rpow U (c - 1)) * |c - sigma|) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (by simpa [Itop] using htopint)
          (by positivity))
        (mul_le_mul_of_nonneg_left (by simpa [Ibot] using hbotint)
          (by positivity))
    _ = (c - sigma) / Real.pi *
        (M * Real.rpow U (c - 1)) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hsigmaC)]
      field_simp [ne_of_gt hpi]
      ring

/-- Exact split of the literal aligned horizontal component into a
common-edge endpoint window and one moving-edge correction strip.  This is
the release-path shape: the first term is controlled by
`norm_normalizedFixedEdgeHorizontalWindow_le`; the second is the sole
remaining deterministic horizontal correction. -/
theorem horizontalComponent_window_eq_neg_commonEdge_sub_edgeChange
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    (sigma T x Y : ℝ) :
    horizontalComponent chi sigma T (x + Y) -
        horizontalComponent chi sigma T x =
      -(horizontalBoundaryIntegral chi.primitiveCharacter
          (halfIntegerPoint ⌊x + Y⌋₊) sigma (standardEdge ⌊x⌋₊) T -
        horizontalBoundaryIntegral chi.primitiveCharacter
          (halfIntegerPoint ⌊x⌋₊) sigma (standardEdge ⌊x⌋₊) T) -
      (horizontalBoundaryIntegral chi.primitiveCharacter
          (halfIntegerPoint ⌊x + Y⌋₊) sigma
            (standardEdge ⌊x + Y⌋₊) T -
        horizontalBoundaryIntegral chi.primitiveCharacter
          (halfIntegerPoint ⌊x + Y⌋₊) sigma (standardEdge ⌊x⌋₊) T) := by
  simp only [horizontalComponent]
  ring

end

end MAPAPLeftLineWindowKernel
