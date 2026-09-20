import KoukExercise12TwoContourAperture
import APZeroFieldEnergy28Grouping
import PrincipalFullStripA5Source

/-!
# Local horizontal aperture for Exercise 12.2(a)

The horizontal height is selected only against zeros whose ordinates can lie
within distance one of `(H,H+1)`.  This is the source-local selection needed
to retain the Perron factor `1/T`; charging every zero below `H` would cancel
that decay.
-/

namespace MAPKoukExercise12TwoLocalHorizontalAperture

open Complex Set DirichletZeros PrimitiveExplicitFormulaSpine
open QuantitativeFiniteAperture
open MAPKoukExercise12TwoContourAperture
open MAPLocalZeroWindow
open WideDiskBlaschkeAssembly

noncomputable section

private def sliceImagCoordinates
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (T a : ℝ) : Finset ℝ :=
  (MAPPaperWindowVKBypass.globalUnitWindowSupport chi 0 T a).image Complex.im

private def sliceNegImagCoordinates
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (T a : ℝ) : Finset ℝ :=
  (MAPPaperWindowVKBypass.globalUnitWindowSupport chi 0 T a).image
    (fun rho => -rho.im)

/-- The six unit slices which can approach the top or bottom horizontal side. -/
def exerciseLocalImagCoordinates
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (H : ℝ) : Finset ℝ :=
  let T := H + 4
  (((sliceImagCoordinates chi T (H - 1) ∪
      sliceImagCoordinates chi T H) ∪
      sliceImagCoordinates chi T (H + 1)) ∪
    ((sliceNegImagCoordinates chi T (-H - 2) ∪
      sliceNegImagCoordinates chi T (-H - 1)) ∪
      sliceNegImagCoordinates chi T (-H)))

def exerciseHorizontalClearance
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (H : ℝ) : ℝ :=
  1 / (4 * ((exerciseLocalImagCoordinates chi H).card + 1))

def exerciseRealClearance
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (H : ℝ) : ℝ :=
  (1 / 2 : ℝ) /
    (4 * ((exerciseBufferedRealCoordinates chi H).card + 1))

theorem exerciseHorizontalClearance_pos
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (H : ℝ) :
    0 < exerciseHorizontalClearance chi H := by
  unfold exerciseHorizontalClearance
  positivity

theorem exerciseRealClearance_pos
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (H : ℝ) :
    0 < exerciseRealClearance chi H := by
  unfold exerciseRealClearance
  positivity

private theorem card_slice_le_mass
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (T a : ℝ) :
    ((MAPPaperWindowVKBypass.globalUnitWindowSupport chi 0 T a).card : ℝ) ≤
      ∑ rho ∈ MAPPaperWindowVKBypass.globalUnitWindowSupport chi 0 T a,
        (zeroMultiplicity chi 0 T rho : ℝ) := by
  rw [Finset.card_eq_sum_ones]
  push_cast
  apply Finset.sum_le_sum
  intro rho hrho
  have hmem : rho ∈ zeroSupport chi 0 T := (Finset.mem_filter.mp hrho).1
  have hpos := MAPZeroFreeSiegelSpine.zeroMultiplicity_pos_of_mem
    chi 0 T hmem
  exact_mod_cast hpos

private theorem card_sliceImagCoordinates_le_uniform
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {H : ℝ} (hH : 0 ≤ H) (a : ℝ) :
    ((sliceImagCoordinates chi (H + 4) a).card : ℝ) ≤
      1 + 306 * Real.log ((q : ℝ) * (H + 8)) := by
  have himage := Finset.card_image_le
    (s := MAPPaperWindowVKBypass.globalUnitWindowSupport chi 0 (H + 4) a)
    (f := Complex.im)
  have himageR : ((sliceImagCoordinates chi (H + 4) a).card : ℝ) ≤
      ((MAPPaperWindowVKBypass.globalUnitWindowSupport chi 0 (H + 4) a).card : ℝ) := by
    exact_mod_cast himage
  exact himageR.trans ((card_slice_le_mass chi (H + 4) a).trans (by
    have hmass :=
      MAPAPZeroFieldEnergy28Grouping.globalUnitWindowMass_le_uniform
        chi hprim hchi (show 0 ≤ H + 4 by linarith) a
    convert hmass using 1 <;> ring))

private theorem card_sliceNegImagCoordinates_le_uniform
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {H : ℝ} (hH : 0 ≤ H) (a : ℝ) :
    ((sliceNegImagCoordinates chi (H + 4) a).card : ℝ) ≤
      1 + 306 * Real.log ((q : ℝ) * (H + 8)) := by
  have himage := Finset.card_image_le
    (s := MAPPaperWindowVKBypass.globalUnitWindowSupport chi 0 (H + 4) a)
    (f := fun rho : ℂ => -rho.im)
  have himageR : ((sliceNegImagCoordinates chi (H + 4) a).card : ℝ) ≤
      ((MAPPaperWindowVKBypass.globalUnitWindowSupport chi 0 (H + 4) a).card : ℝ) := by
    exact_mod_cast himage
  exact himageR.trans ((card_slice_le_mass chi (H + 4) a).trans (by
    have hmass :=
      MAPAPZeroFieldEnergy28Grouping.globalUnitWindowMass_le_uniform
        chi hprim hchi (show 0 ≤ H + 4 by linarith) a
    convert hmass using 1 <;> ring))

/-- Six certified A.5 unit-window counts pay for the local horizontal
clearance. -/
theorem card_exerciseLocalImagCoordinates_le_uniform
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {H : ℝ} (hH : 0 ≤ H) :
    ((exerciseLocalImagCoordinates chi H).card : ℝ) ≤
      6 * (1 + 306 * Real.log ((q : ℝ) * (H + 8))) := by
  let U := 1 + 306 * Real.log ((q : ℝ) * (H + 8))
  have h1 := card_sliceImagCoordinates_le_uniform chi hprim hchi hH (H - 1)
  have h2 := card_sliceImagCoordinates_le_uniform chi hprim hchi hH H
  have h3 := card_sliceImagCoordinates_le_uniform chi hprim hchi hH (H + 1)
  have h4 := card_sliceNegImagCoordinates_le_uniform chi hprim hchi hH (-H - 2)
  have h5 := card_sliceNegImagCoordinates_le_uniform chi hprim hchi hH (-H - 1)
  have h6 := card_sliceNegImagCoordinates_le_uniform chi hprim hchi hH (-H)
  have hc12 := Finset.card_union_le
    (sliceImagCoordinates chi (H + 4) (H - 1))
    (sliceImagCoordinates chi (H + 4) H)
  have hc123 := Finset.card_union_le
    (sliceImagCoordinates chi (H + 4) (H - 1) ∪
      sliceImagCoordinates chi (H + 4) H)
    (sliceImagCoordinates chi (H + 4) (H + 1))
  have hc45 := Finset.card_union_le
    (sliceNegImagCoordinates chi (H + 4) (-H - 2))
    (sliceNegImagCoordinates chi (H + 4) (-H - 1))
  have hc456 := Finset.card_union_le
    (sliceNegImagCoordinates chi (H + 4) (-H - 2) ∪
      sliceNegImagCoordinates chi (H + 4) (-H - 1))
    (sliceNegImagCoordinates chi (H + 4) (-H))
  have hcall := Finset.card_union_le
    ((sliceImagCoordinates chi (H + 4) (H - 1) ∪
      sliceImagCoordinates chi (H + 4) H) ∪
      sliceImagCoordinates chi (H + 4) (H + 1))
    ((sliceNegImagCoordinates chi (H + 4) (-H - 2) ∪
      sliceNegImagCoordinates chi (H + 4) (-H - 1)) ∪
      sliceNegImagCoordinates chi (H + 4) (-H))
  have hc12R : (((sliceImagCoordinates chi (H + 4) (H - 1) ∪
      sliceImagCoordinates chi (H + 4) H).card : ℕ) : ℝ) ≤
      (sliceImagCoordinates chi (H + 4) (H - 1)).card +
        (sliceImagCoordinates chi (H + 4) H).card := by exact_mod_cast hc12
  have hc123R : ((((sliceImagCoordinates chi (H + 4) (H - 1) ∪
      sliceImagCoordinates chi (H + 4) H) ∪
      sliceImagCoordinates chi (H + 4) (H + 1)).card : ℕ) : ℝ) ≤
      ((sliceImagCoordinates chi (H + 4) (H - 1) ∪
        sliceImagCoordinates chi (H + 4) H).card : ℝ) +
        (sliceImagCoordinates chi (H + 4) (H + 1)).card := by exact_mod_cast hc123
  have hc45R : (((sliceNegImagCoordinates chi (H + 4) (-H - 2) ∪
      sliceNegImagCoordinates chi (H + 4) (-H - 1)).card : ℕ) : ℝ) ≤
      (sliceNegImagCoordinates chi (H + 4) (-H - 2)).card +
        (sliceNegImagCoordinates chi (H + 4) (-H - 1)).card := by exact_mod_cast hc45
  have hc456R : ((((sliceNegImagCoordinates chi (H + 4) (-H - 2) ∪
      sliceNegImagCoordinates chi (H + 4) (-H - 1)) ∪
      sliceNegImagCoordinates chi (H + 4) (-H)).card : ℕ) : ℝ) ≤
      ((sliceNegImagCoordinates chi (H + 4) (-H - 2) ∪
        sliceNegImagCoordinates chi (H + 4) (-H - 1)).card : ℝ) +
        (sliceNegImagCoordinates chi (H + 4) (-H)).card := by exact_mod_cast hc456
  have hcallR : ((exerciseLocalImagCoordinates chi H).card : ℝ) ≤
      (((sliceImagCoordinates chi (H + 4) (H - 1) ∪
        sliceImagCoordinates chi (H + 4) H) ∪
        sliceImagCoordinates chi (H + 4) (H + 1)).card : ℝ) +
      (((sliceNegImagCoordinates chi (H + 4) (-H - 2) ∪
        sliceNegImagCoordinates chi (H + 4) (-H - 1)) ∪
        sliceNegImagCoordinates chi (H + 4) (-H)).card : ℝ) := by
    unfold exerciseLocalImagCoordinates
    exact_mod_cast hcall
  linarith

/-- The inverse horizontal aperture costs only one local A.5 logarithm. -/
theorem inv_exerciseHorizontalClearance_le_uniform
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {H : ℝ} (hH : 0 ≤ H) :
    (exerciseHorizontalClearance chi H)⁻¹ ≤
      28 * (1 + 306 * Real.log ((q : ℝ) * (H + 8))) := by
  have hcard := card_exerciseLocalImagCoordinates_le_uniform chi hprim hchi hH
  have hU1 : 1 ≤ 1 + 306 * Real.log ((q : ℝ) * (H + 8)) := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
    have hscale : 1 ≤ (q : ℝ) * (H + 8) := by nlinarith
    have hlog := Real.log_nonneg hscale
    nlinarith
  unfold exerciseHorizontalClearance
  have heq :
      (1 / (4 * (((exerciseLocalImagCoordinates chi H).card : ℝ) + 1)))⁻¹ =
        4 * (((exerciseLocalImagCoordinates chi H).card : ℝ) + 1) := by
    field_simp
  rw [heq]
  nlinarith

/-- The vertical-line clearance may spend the full divisor count; unlike the
horizontal clearance, it is multiplied only by the square-root-sized left
edge contribution. -/
theorem inv_exerciseRealClearance_le_count
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (H : ℝ) :
    (exerciseRealClearance chi H)⁻¹ ≤
      8 * ((dirichletZeroCount chi 0 (H + 4) : ℝ) + 2) := by
  classical
  let S := zeroSupport chi 0 (H + 4)
  let Z := dirichletZeroCount chi 0 (H + 4)
  have hSZ : S.card ≤ Z := by
    dsimp [S, Z]
    exact zeroSupport_card_le_dirichletZeroCount chi 0 (H + 4)
  have hrealCard : (exerciseBufferedRealCoordinates chi H).card ≤ Z + 1 := by
    calc
      (exerciseBufferedRealCoordinates chi H).card ≤
          (zeroRealCoordinates chi (H + 3)).card + 1 := by
        unfold exerciseBufferedRealCoordinates
        exact Finset.card_insert_le _ _
      _ ≤ S.card + 1 := by
        apply Nat.add_le_add_right
        unfold zeroRealCoordinates
        have heq : zeroSupport chi 0 (H + 3 + 1) = S := by
          dsimp [S]
          congr 1
          ring
        rw [heq]
        exact Finset.card_image_le
      _ ≤ Z + 1 := Nat.add_le_add_right hSZ 1
  have hrealCast :
      ((exerciseBufferedRealCoordinates chi H).card : ℝ) ≤ (Z : ℝ) + 1 := by
    exact_mod_cast hrealCard
  unfold exerciseRealClearance
  have heq :
      (((1 / 2 : ℝ) /
        (4 * (((exerciseBufferedRealCoordinates chi H).card : ℝ) + 1)))⁻¹) =
        8 * (((exerciseBufferedRealCoordinates chi H).card : ℝ) + 1) := by
    field_simp
    ring
  rw [heq]
  nlinarith

private theorem mem_localCoords_of_mem_global_top
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {H : ℝ} {rho : ℂ} (hrho : rho ∈ zeroSupport chi 0 (H + 4))
    (hrange : rho.im ∈ Set.Icc (H - 1) (H + 2)) :
    rho.im ∈ exerciseLocalImagCoordinates chi H := by
  unfold exerciseLocalImagCoordinates
  by_cases h₀ : rho.im ≤ H
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨rho, Finset.mem_filter.mpr ⟨hrho, hrange.1, by linarith⟩, rfl⟩
  by_cases h₁ : rho.im ≤ H + 1
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨rho, Finset.mem_filter.mpr ⟨hrho, by linarith,
      by convert h₁ using 1 <;> ring⟩, rfl⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨rho, Finset.mem_filter.mpr ⟨hrho, by linarith,
      by convert hrange.2 using 1 <;> ring⟩, rfl⟩

private theorem mem_localCoords_of_mem_global_bottom
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {H : ℝ} {rho : ℂ} (hrho : rho ∈ zeroSupport chi 0 (H + 4))
    (hrange : -rho.im ∈ Set.Icc (H - 1) (H + 2)) :
    -rho.im ∈ exerciseLocalImagCoordinates chi H := by
  unfold exerciseLocalImagCoordinates
  have him : rho.im ∈ Set.Icc (-H - 2) (-H + 1) := by
    constructor <;> linarith [hrange.1, hrange.2]
  by_cases h₀ : rho.im ≤ -H - 1
  · apply Finset.mem_union_right
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨rho, Finset.mem_filter.mpr ⟨hrho, him.1, by linarith⟩, rfl⟩
  by_cases h₁ : rho.im ≤ -H
  · apply Finset.mem_union_right
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨rho, Finset.mem_filter.mpr ⟨hrho, by linarith, by linarith⟩, rfl⟩
  · apply Finset.mem_union_right
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨rho, Finset.mem_filter.mpr ⟨hrho, by linarith, him.2⟩, rfl⟩

/-- Public membership adapter for a global zero whose ordinate can approach
the selected top edge. -/
theorem mem_exerciseLocalImagCoordinates_of_mem_global_top
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {H : ℝ} {rho : ℂ} (hrho : rho ∈ zeroSupport chi 0 (H + 4))
    (hrange : rho.im ∈ Set.Icc (H - 1) (H + 2)) :
    rho.im ∈ exerciseLocalImagCoordinates chi H :=
  mem_localCoords_of_mem_global_top chi hrho hrange

/-- Public membership adapter for a global zero whose reflected ordinate can
approach the selected bottom edge. -/
theorem mem_exerciseLocalImagCoordinates_of_mem_global_bottom
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {H : ℝ} {rho : ℂ} (hrho : rho ∈ zeroSupport chi 0 (H + 4))
    (hrange : -rho.im ∈ Set.Icc (H - 1) (H + 2)) :
    -rho.im ∈ exerciseLocalImagCoordinates chi H :=
  mem_localCoords_of_mem_global_bottom chi hrho hrange

/-- Source-local two-clearance aperture: global real-coordinate avoidance for
the left line, and six-unit-window ordinate avoidance for the horizontal
sides. -/
theorem exists_exerciseLocalHorizontalAperture
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {H c : ℝ} :
    ∃ sigma ∈ Set.Ioo (0 : ℝ) (1 / 2),
      ∃ T ∈ Set.Ioo H (H + 1),
        exerciseRealClearance chi H ≤ sigma ∧
        (∀ u ∈ Set.Icc (-T) T,
          ∀ rho ∈ zeroSupport chi 0 (H + 4),
            exerciseRealClearance chi H ≤
              ‖((sigma : ℂ) + (u : ℂ) * Complex.I) - rho‖) ∧
        (∀ r ∈ Set.Icc sigma c,
          ∀ rho ∈ zeroSupport chi 0 (H + 4),
            exerciseHorizontalClearance chi H ≤
              ‖((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho‖) ∧
        (∀ r ∈ Set.Icc sigma c,
          ∀ rho ∈ zeroSupport chi 0 (H + 4),
            exerciseHorizontalClearance chi H ≤
              ‖((r : ℂ) + (T : ℂ) * Complex.I) - rho‖) := by
  classical
  let R := exerciseBufferedRealCoordinates chi H
  let A := exerciseLocalImagCoordinates chi H
  obtain ⟨sigma, hsigma, hsigmaClear⟩ :=
    exists_mem_Ioo_with_finset_clearance R
      (a := 0) (b := 1 / 2) (by norm_num)
  obtain ⟨T, hT, hTClear⟩ :=
    exists_mem_Ioo_with_finset_clearance A
      (a := H) (b := H + 1) (by linarith)
  have hzeroR : (0 : ℝ) ∈ R := by
    simp [R, exerciseBufferedRealCoordinates]
  have hsigmaRaw := hsigmaClear 0 hzeroR
  have hdSigma : exerciseRealClearance chi H ≤ sigma := by
    unfold exerciseRealClearance
    dsimp [R] at hsigmaRaw
    norm_num [abs_of_pos hsigma.1] at hsigmaRaw
    exact hsigmaRaw
  have hleft : ∀ u ∈ Set.Icc (-T) T, ∀ rho ∈ zeroSupport chi 0 (H + 4),
      exerciseRealClearance chi H ≤
        ‖((sigma : ℂ) + (u : ℂ) * Complex.I) - rho‖ := by
    intro u hu rho hrho
    have hrho' : rho ∈ zeroSupport chi 0 (H + 3 + 1) := by
      convert hrho using 1 <;> ring
    have hrhoR : rho.re ∈ R := by
      simp only [R, exerciseBufferedRealCoordinates, Finset.mem_insert]
      right
      exact Finset.mem_image.mpr ⟨rho, hrho', rfl⟩
    have hcoord := hsigmaClear rho.re hrhoR
    calc
      exerciseRealClearance chi H ≤ |sigma - rho.re| := by
        simpa [exerciseRealClearance, R] using hcoord
      _ ≤ ‖((sigma : ℂ) + (u : ℂ) * Complex.I) - rho‖ := by
        simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
          Complex.ofReal_im, zero_mul, sub_zero, add_zero] using
            Complex.abs_re_le_norm (((sigma : ℂ) + (u : ℂ) * Complex.I) - rho)
  have hdHleOne : exerciseHorizontalClearance chi H ≤ 1 := by
    unfold exerciseHorizontalClearance
    have hden : (4 : ℝ) ≤
        4 * (((exerciseLocalImagCoordinates chi H).card : ℝ) + 1) := by
      have hc : 0 ≤ ((exerciseLocalImagCoordinates chi H).card : ℝ) := by positivity
      nlinarith
    exact (one_div_le_one_div_of_le (by norm_num) hden).trans (by norm_num)
  have htop : ∀ r ∈ Set.Icc sigma c, ∀ rho ∈ zeroSupport chi 0 (H + 4),
      exerciseHorizontalClearance chi H ≤
        ‖((r : ℂ) + (T : ℂ) * Complex.I) - rho‖ := by
    intro r hr rho hrho
    by_cases hrange : rho.im ∈ Set.Icc (H - 1) (H + 2)
    · have hmem : rho.im ∈ A := by
        dsimp [A]
        exact mem_localCoords_of_mem_global_top chi hrho hrange
      have hc := hTClear rho.im hmem
      calc
        exerciseHorizontalClearance chi H ≤ |T - rho.im| := by
          simpa [exerciseHorizontalClearance, A] using hc
        _ ≤ _ := by
          simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
            Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
            mul_one, zero_mul, add_zero, zero_add] using
              Complex.abs_im_le_norm (((r : ℂ) + (T : ℂ) * Complex.I) - rho)
    · have hfar : 1 ≤ |T - rho.im| := by
        rw [Set.mem_Icc, not_and_or] at hrange
        rcases hrange with hlo | hhi
        · rw [abs_of_nonneg (by linarith [hT.1])]
          linarith [hT.1]
        · rw [abs_of_nonpos (by linarith [hT.2])]
          linarith [hT.2]
      exact hdHleOne.trans (hfar.trans (by
        simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          mul_one, zero_mul, add_zero, zero_add] using
            Complex.abs_im_le_norm (((r : ℂ) + (T : ℂ) * Complex.I) - rho)))
  have hbottom : ∀ r ∈ Set.Icc sigma c, ∀ rho ∈ zeroSupport chi 0 (H + 4),
      exerciseHorizontalClearance chi H ≤
        ‖((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho‖ := by
    intro r hr rho hrho
    by_cases hrange : -rho.im ∈ Set.Icc (H - 1) (H + 2)
    · have hmem : -rho.im ∈ A := by
        dsimp [A]
        exact mem_localCoords_of_mem_global_bottom chi hrho hrange
      have hc := hTClear (-rho.im) hmem
      have hdist : exerciseHorizontalClearance chi H ≤ |(-T) - rho.im| := by
        calc
          _ ≤ |T - (-rho.im)| := by
            simpa [exerciseHorizontalClearance, A] using hc
          _ = _ := by rw [show (-T) - rho.im = -(T - (-rho.im)) by ring, abs_neg]
      exact hdist.trans (by
        simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          mul_one, zero_mul, add_zero, zero_add] using
            Complex.abs_im_le_norm
              (((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho))
    · have hfar : 1 ≤ |T - (-rho.im)| := by
        rw [Set.mem_Icc, not_and_or] at hrange
        rcases hrange with hlo | hhi
        · rw [abs_of_nonneg (by linarith [hT.1])]
          linarith [hT.1]
        · rw [abs_of_nonpos (by linarith [hT.2])]
          linarith [hT.2]
      have hdist : exerciseHorizontalClearance chi H ≤ |(-T) - rho.im| :=
        hdHleOne.trans (hfar.trans_eq (by
          rw [show (-T) - rho.im = -(T - (-rho.im)) by ring, abs_neg]))
      exact hdist.trans (by
        simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          mul_one, zero_mul, add_zero, zero_add] using
            Complex.abs_im_le_norm
              (((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho))
  exact ⟨sigma, hsigma, T, hT, hdSigma, hleft, hbottom, htop⟩

/-- Arbitrary positive global-buffer clearance transports to the local
radius-three zero disk. -/
theorem localClearance_le_norm_sub_wide
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {H t r delta : ℝ} (hdelta : 0 < delta) (ht : |t| ≤ H + 1)
    (hdSigma : delta ≤ r)
    {rho : ℂ} (hrho : rho ∈ wideZeroSupport chi t)
    (hdGlobal : ∀ z ∈ zeroSupport chi 0 (H + 4),
      delta ≤ ‖((r : ℂ) + Complex.I * t) - z‖) :
    delta ≤ ‖((r : ℂ) + Complex.I * t) - rho‖ := by
  by_cases hre : 0 ≤ rho.re
  · exact hdGlobal rho
      (mem_globalBufferedSupport_of_mem_wide_of_nonneg_re chi ht hrho hre)
  · have hr0 : 0 < r := hdelta.trans_le hdSigma
    have hreal : r ≤ |r - rho.re| := by
      rw [abs_of_pos (by linarith)]
      linarith
    exact hdSigma.trans (hreal.trans (by
      simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
        Complex.ofReal_im, zero_mul, sub_zero, add_zero] using
          Complex.abs_re_le_norm (((r : ℂ) + Complex.I * t) - rho)))

/-! ## Conductor-one principal horizontal aperture -/

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩

private theorem principal_fullStrip_family_bound :
    ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi.IsPrimitive → chi = 1 → ∀ t : ℝ,
        (MAPLocalZeroWindow.closedUnitWindowCount chi 0 t : ℝ) ≤
          5050 * Real.log (MAPLocalZeroWindow.arithmeticScale q t) := by
  intro q _inst chi hprim hchi t
  have hcond : chi.conductor = q := hprim
  rw [hchi, DirichletCharacter.conductor_one] at hcond
  subst q
  subst chi
  have hbase := MAPPrincipalZetaFullStrip.principal_fullStrip_count_le_log t
  have hlog0 : 0 ≤ Real.log (MAPLocalZeroWindow.arithmeticScale 1 t) := by
    apply Real.log_nonneg
    unfold MAPLocalZeroWindow.arithmeticScale
    norm_num
    linarith [abs_nonneg t]
  nlinarith

private theorem card_sliceImagCoordinates_le_principal
    {H : ℝ} (hH : 0 ≤ H) (a : ℝ) :
    ((sliceImagCoordinates (1 : DirichletCharacter ℂ 1) (H + 4) a).card : ℝ) ≤
      5050 * Real.log (H + 8) := by
  have himage := Finset.card_image_le
    (s := MAPPaperWindowVKBypass.globalUnitWindowSupport
      (1 : DirichletCharacter ℂ 1) 0 (H + 4) a)
    (f := Complex.im)
  have himageR :
      ((sliceImagCoordinates (1 : DirichletCharacter ℂ 1) (H + 4) a).card : ℝ) ≤
        ((MAPPaperWindowVKBypass.globalUnitWindowSupport
          (1 : DirichletCharacter ℂ 1) 0 (H + 4) a).card : ℝ) := by
    exact_mod_cast himage
  have hprim : (1 : DirichletCharacter ℂ 1).IsPrimitive := by
    show (1 : DirichletCharacter ℂ 1).conductor = 1
    rw [DirichletCharacter.conductor_one]
  exact himageR.trans
    ((card_slice_le_mass (1 : DirichletCharacter ℂ 1) (H + 4) a).trans
      (by
        simpa only [Nat.cast_one, one_mul, add_assoc,
          show H + 4 + 4 = H + 8 by ring] using
          MAPPrincipalFullStripA5Source.principal_globalUnitWindowMass_le_uniform
            5050 (by norm_num) principal_fullStrip_family_bound
              (1 : DirichletCharacter ℂ 1) hprim rfl
              (show 0 ≤ H + 4 by linarith) a))

private theorem card_sliceNegImagCoordinates_le_principal
    {H : ℝ} (hH : 0 ≤ H) (a : ℝ) :
    ((sliceNegImagCoordinates (1 : DirichletCharacter ℂ 1) (H + 4) a).card : ℝ) ≤
      5050 * Real.log (H + 8) := by
  have himage := Finset.card_image_le
    (s := MAPPaperWindowVKBypass.globalUnitWindowSupport
      (1 : DirichletCharacter ℂ 1) 0 (H + 4) a)
    (f := fun rho : ℂ => -rho.im)
  have himageR :
      ((sliceNegImagCoordinates (1 : DirichletCharacter ℂ 1) (H + 4) a).card : ℝ) ≤
        ((MAPPaperWindowVKBypass.globalUnitWindowSupport
          (1 : DirichletCharacter ℂ 1) 0 (H + 4) a).card : ℝ) := by
    exact_mod_cast himage
  have hprim : (1 : DirichletCharacter ℂ 1).IsPrimitive := by
    show (1 : DirichletCharacter ℂ 1).conductor = 1
    rw [DirichletCharacter.conductor_one]
  exact himageR.trans
    ((card_slice_le_mass (1 : DirichletCharacter ℂ 1) (H + 4) a).trans
      (by
        simpa only [Nat.cast_one, one_mul, add_assoc,
          show H + 4 + 4 = H + 8 by ring] using
          MAPPrincipalFullStripA5Source.principal_globalUnitWindowMass_le_uniform
            5050 (by norm_num) principal_fullStrip_family_bound
              (1 : DirichletCharacter ℂ 1) hprim rfl
              (show 0 ≤ H + 4 by linarith) a))

/-- The conductor-one local horizontal coordinate set has logarithmic size,
proved from the certified full-strip zeta unit-window count. -/
theorem card_exerciseLocalImagCoordinates_le_principal
    {H : ℝ} (hH : 0 ≤ H) :
    ((exerciseLocalImagCoordinates (1 : DirichletCharacter ℂ 1) H).card : ℝ) ≤
      6 * (5050 * Real.log (H + 8)) := by
  let chi : DirichletCharacter ℂ 1 := 1
  have h1 := card_sliceImagCoordinates_le_principal hH (H - 1)
  have h2 := card_sliceImagCoordinates_le_principal hH H
  have h3 := card_sliceImagCoordinates_le_principal hH (H + 1)
  have h4 := card_sliceNegImagCoordinates_le_principal hH (-H - 2)
  have h5 := card_sliceNegImagCoordinates_le_principal hH (-H - 1)
  have h6 := card_sliceNegImagCoordinates_le_principal hH (-H)
  have hc12 := Finset.card_union_le
    (sliceImagCoordinates chi (H + 4) (H - 1))
    (sliceImagCoordinates chi (H + 4) H)
  have hc123 := Finset.card_union_le
    (sliceImagCoordinates chi (H + 4) (H - 1) ∪
      sliceImagCoordinates chi (H + 4) H)
    (sliceImagCoordinates chi (H + 4) (H + 1))
  have hc45 := Finset.card_union_le
    (sliceNegImagCoordinates chi (H + 4) (-H - 2))
    (sliceNegImagCoordinates chi (H + 4) (-H - 1))
  have hc456 := Finset.card_union_le
    (sliceNegImagCoordinates chi (H + 4) (-H - 2) ∪
      sliceNegImagCoordinates chi (H + 4) (-H - 1))
    (sliceNegImagCoordinates chi (H + 4) (-H))
  have hcall := Finset.card_union_le
    ((sliceImagCoordinates chi (H + 4) (H - 1) ∪
      sliceImagCoordinates chi (H + 4) H) ∪
      sliceImagCoordinates chi (H + 4) (H + 1))
    ((sliceNegImagCoordinates chi (H + 4) (-H - 2) ∪
      sliceNegImagCoordinates chi (H + 4) (-H - 1)) ∪
      sliceNegImagCoordinates chi (H + 4) (-H))
  have hc12R : (((sliceImagCoordinates chi (H + 4) (H - 1) ∪
      sliceImagCoordinates chi (H + 4) H).card : ℕ) : ℝ) ≤
      (sliceImagCoordinates chi (H + 4) (H - 1)).card +
        (sliceImagCoordinates chi (H + 4) H).card := by exact_mod_cast hc12
  have hc123R : ((((sliceImagCoordinates chi (H + 4) (H - 1) ∪
      sliceImagCoordinates chi (H + 4) H) ∪
      sliceImagCoordinates chi (H + 4) (H + 1)).card : ℕ) : ℝ) ≤
      ((sliceImagCoordinates chi (H + 4) (H - 1) ∪
        sliceImagCoordinates chi (H + 4) H).card : ℝ) +
        (sliceImagCoordinates chi (H + 4) (H + 1)).card := by exact_mod_cast hc123
  have hc45R : (((sliceNegImagCoordinates chi (H + 4) (-H - 2) ∪
      sliceNegImagCoordinates chi (H + 4) (-H - 1)).card : ℕ) : ℝ) ≤
      (sliceNegImagCoordinates chi (H + 4) (-H - 2)).card +
        (sliceNegImagCoordinates chi (H + 4) (-H - 1)).card := by exact_mod_cast hc45
  have hc456R : ((((sliceNegImagCoordinates chi (H + 4) (-H - 2) ∪
      sliceNegImagCoordinates chi (H + 4) (-H - 1)) ∪
      sliceNegImagCoordinates chi (H + 4) (-H)).card : ℕ) : ℝ) ≤
      ((sliceNegImagCoordinates chi (H + 4) (-H - 2) ∪
        sliceNegImagCoordinates chi (H + 4) (-H - 1)).card : ℝ) +
        (sliceNegImagCoordinates chi (H + 4) (-H)).card := by exact_mod_cast hc456
  have hcallR : ((exerciseLocalImagCoordinates chi H).card : ℝ) ≤
      (((sliceImagCoordinates chi (H + 4) (H - 1) ∪
        sliceImagCoordinates chi (H + 4) H) ∪
        sliceImagCoordinates chi (H + 4) (H + 1)).card : ℝ) +
      (((sliceNegImagCoordinates chi (H + 4) (-H - 2) ∪
        sliceNegImagCoordinates chi (H + 4) (-H - 1)) ∪
        sliceNegImagCoordinates chi (H + 4) (-H)).card : ℝ) := by
    unfold exerciseLocalImagCoordinates
    exact_mod_cast hcall
  dsimp only [chi] at h1 h2 h3 h4 h5 h6 hcallR ⊢
  linarith

/-- Principal conductor-one inverse horizontal aperture with one logarithmic
cost and no unproved source leaf. -/
theorem inv_exerciseHorizontalClearance_le_principal
    {H : ℝ} (hH : 0 ≤ H) :
    (exerciseHorizontalClearance (1 : DirichletCharacter ℂ 1) H)⁻¹ ≤
      121204 * Real.log (H + 8) := by
  have hcard := card_exerciseLocalImagCoordinates_le_principal hH
  have hlog0 : 0 ≤ Real.log (H + 8) :=
    Real.log_nonneg (by linarith)
  unfold exerciseHorizontalClearance
  have heq :
      (1 / (4 * (((exerciseLocalImagCoordinates
        (1 : DirichletCharacter ℂ 1) H).card : ℝ) + 1)))⁻¹ =
        4 * (((exerciseLocalImagCoordinates
          (1 : DirichletCharacter ℂ 1) H).card : ℝ) + 1) := by
    field_simp
  rw [heq]
  have hlogLower : 1 ≤ Real.log (H + 8) := by
    have hlog8 : 1 < Real.log (8 : ℝ) := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 8)]
      exact Real.exp_one_lt_three.trans (by norm_num)
    exact hlog8.le.trans (Real.log_le_log (by norm_num) (by linarith))
  nlinarith

#print axioms MAPKoukExercise12TwoLocalHorizontalAperture.card_exerciseLocalImagCoordinates_le_uniform
#print axioms MAPKoukExercise12TwoLocalHorizontalAperture.inv_exerciseHorizontalClearance_le_uniform
#print axioms MAPKoukExercise12TwoLocalHorizontalAperture.inv_exerciseRealClearance_le_count
#print axioms MAPKoukExercise12TwoLocalHorizontalAperture.exists_exerciseLocalHorizontalAperture
#print axioms MAPKoukExercise12TwoLocalHorizontalAperture.localClearance_le_norm_sub_wide
#print axioms MAPKoukExercise12TwoLocalHorizontalAperture.card_exerciseLocalImagCoordinates_le_principal
#print axioms MAPKoukExercise12TwoLocalHorizontalAperture.inv_exerciseHorizontalClearance_le_principal

end

end MAPKoukExercise12TwoLocalHorizontalAperture
