import APZeroFieldEnergy28Core
import HarmonicRowGrouping
import FiniteWeightedSchur
import FullStripA5Family
import LocalZeroCountSlice

/-!
# Full-strip harmonic grouping for equation (2.8)

This file instantiates the generic harmonic row estimate on the literal
divisor-backed zero support.  It first treats primitive nonprincipal
characters; the conductor-one principal branch is kept separate.
-/

namespace MAPAPZeroFieldEnergy28Grouping

open Complex MeasureTheory Set
open scoped BigOperators ENNReal
open DirichletZeros MAPLocalZeroWindow
open APExplicitFormulaMajorantAdapter

noncomputable section

variable {q : ℕ} [NeZero q]

theorem globalUnitWindowMass_le_fullStrip
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (T a : ℝ) :
    (∑ ρ ∈ MAPPaperWindowVKBypass.globalUnitWindowSupport χ 0 T a,
        (zeroMultiplicity χ 0 T ρ : ℝ)) ≤
      1 + 153 * Real.log (arithmeticScale q a) +
        153 * Real.log (arithmeticScale q (-a - 1)) := by
  have hnat := MAPPaperWindowVKBypass.globalUnitWindowCount_le_closed χ 0 T a
  have hcast :
      (∑ ρ ∈ MAPPaperWindowVKBypass.globalUnitWindowSupport χ 0 T a,
          (zeroMultiplicity χ 0 T ρ : ℝ)) ≤
        (closedUnitWindowCount χ 0 a : ℝ) := by
    exact_mod_cast hnat
  exact hcast.trans
    (MAPFullStripA5Family.certifiedFullStripClosedLocalZeroCount
      χ hprim hχ a)

private theorem zeroSupport_im_abs_le
    (χ : DirichletCharacter ℂ q) {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport χ 0 T) : |ρ.im| ≤ T := by
  have hrect := PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
    χ 0 T hρ
  rw [zeroRectangle, Complex.mem_reProdIm] at hrect
  exact abs_le.mpr hrect.2

private theorem arithmeticScale_le_global
    {T a : ℝ} (hT : 0 ≤ T) (ha : |a| ≤ T + 2) :
    arithmeticScale q a ≤ (q : ℝ) * (T + 4) := by
  unfold arithmeticScale
  have hq : (0 : ℝ) ≤ q := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hq

private theorem global_scale_one_le {T : ℝ} (hT : 0 ≤ T) :
    1 ≤ (q : ℝ) * (T + 4) := by
  have hqnat : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast hqnat
  nlinarith

theorem globalUnitWindowMass_le_uniform
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {T : ℝ} (hT : 0 ≤ T) (a : ℝ) :
    (∑ ρ ∈ MAPPaperWindowVKBypass.globalUnitWindowSupport χ 0 T a,
        (zeroMultiplicity χ 0 T ρ : ℝ)) ≤
      1 + 306 * Real.log ((q : ℝ) * (T + 4)) := by
  classical
  let S := MAPPaperWindowVKBypass.globalUnitWindowSupport χ 0 T a
  by_cases hS : S.Nonempty
  · obtain ⟨ρ, hρ⟩ := hS
    have hρglobal : ρ ∈ zeroSupport χ 0 T := (Finset.mem_filter.mp hρ).1
    have hρim := zeroSupport_im_abs_le χ hρglobal
    have hρwindow := (Finset.mem_filter.mp hρ).2
    have haLo : -T - 1 ≤ a := by
      have hlow : -T ≤ ρ.im := (abs_le.mp hρim).1
      linarith
    have haHi : a ≤ T := by
      have hhigh : ρ.im ≤ T := (abs_le.mp hρim).2
      linarith
    have habsa : |a| ≤ T + 1 := (abs_le.mpr ⟨by linarith, by linarith⟩)
    have habsinv : |-a - 1| ≤ T + 2 := by
      rw [show -a - 1 = -(a + 1) by ring, abs_neg]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hscaleA : arithmeticScale q a ≤ (q : ℝ) * (T + 4) :=
      arithmeticScale_le_global hT (habsa.trans (by linarith))
    have hscaleInv : arithmeticScale q (-a - 1) ≤ (q : ℝ) * (T + 4) :=
      arithmeticScale_le_global hT habsinv
    have hscaleApos : 0 < arithmeticScale q a := by
      unfold arithmeticScale
      exact mul_pos (by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q)))
        (by linarith [abs_nonneg a])
    have hscaleInvPos : 0 < arithmeticScale q (-a - 1) := by
      unfold arithmeticScale
      exact mul_pos (by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q)))
        (by linarith [abs_nonneg (-a - 1)])
    have hlogA := Real.log_le_log hscaleApos hscaleA
    have hlogInv := Real.log_le_log hscaleInvPos hscaleInv
    have hbase := globalUnitWindowMass_le_fullStrip χ hprim hχ T a
    nlinarith
  · have hSempt : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hlog : 0 ≤ Real.log ((q : ℝ) * (T + 4)) :=
      Real.log_nonneg (global_scale_one_le hT)
    simpa [S, hSempt] using (show (0 : ℝ) ≤
      1 + 306 * Real.log ((q : ℝ) * (T + 4)) by positivity)

theorem reciprocalRow_le_nonprincipal
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {T : ℝ} (hT : 0 ≤ T) (ρ : ℂ) (hρ : ρ ∈ zeroSupport χ 0 T) :
    (∑ ρ' ∈ zeroSupport χ 0 T,
        (zeroMultiplicity χ 0 T ρ' : ℝ) /
          (1 + |ρ'.im - ρ.im|)) ≤
      2 * (1 + 306 * Real.log ((q : ℝ) * (T + 4))) *
        (harmonic (⌊2 * T⌋₊ + 1) : ℝ) := by
  classical
  apply MAPHarmonicRowGrouping.finite_reciprocal_row_le_harmonic
    (zeroSupport χ 0 T)
    (fun z => (zeroMultiplicity χ 0 T z : ℝ))
    (fun z => z.im) hT
      (show 0 ≤ 1 + 306 * Real.log ((q : ℝ) * (T + 4)) by
        have hlog : 0 ≤ Real.log ((q : ℝ) * (T + 4)) :=
          Real.log_nonneg (global_scale_one_le (q := q) hT)
        positivity)
  · intro z hz
    positivity
  · intro z hz
    exact zeroSupport_im_abs_le χ hz
  · intro a
    exact globalUnitWindowMass_le_uniform χ hprim hχ hT a
  · exact hρ

private theorem zeroSupport_re_mem_unit
    (χ : DirichletCharacter ℂ q) {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport χ 0 T) : 0 ≤ ρ.re ∧ ρ.re ≤ 1 := by
  have hrect := PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
    χ 0 T hρ
  exact (Complex.mem_reProdIm.mp hrect).1

private theorem rpow_pair_factor
    {X : ℝ} (hX : 0 < X) (ρ ρ' : ℂ) :
    Real.rpow X (ρ.re + ρ'.re - 1) =
      X * Real.rpow X (ρ.re - 1) * Real.rpow X (ρ'.re - 1) := by
  rw [show ρ.re + ρ'.re - 1 = 1 + (ρ.re - 1) + (ρ'.re - 1) by ring]
  have houter : Real.rpow X (1 + (ρ.re - 1) + (ρ'.re - 1)) =
      Real.rpow X (1 + (ρ.re - 1)) * Real.rpow X (ρ'.re - 1) :=
    Real.rpow_add hX _ _
  have hinner : Real.rpow X (1 + (ρ.re - 1)) =
      Real.rpow X 1 * Real.rpow X (ρ.re - 1) := Real.rpow_add hX _ _
  have hone : Real.rpow X 1 = X := Real.rpow_one X
  rw [houter, hinner, hone]

private theorem rpow_weight_sq
    {X : ℝ} (hX : 0 < X) (ρ : ℂ) :
    (Real.rpow X (ρ.re - 1)) ^ 2 =
      Real.rpow X (2 * (ρ.re - 1)) := by
  rw [pow_two]
  have hadd : Real.rpow X (ρ.re - 1) * Real.rpow X (ρ.re - 1) =
      Real.rpow X ((ρ.re - 1) + (ρ.re - 1)) :=
    (Real.rpow_add hX _ _).symm
  calc
    Real.rpow X (ρ.re - 1) * Real.rpow X (ρ.re - 1) =
        Real.rpow X ((ρ.re - 1) + (ρ.re - 1)) := hadd
    _ = Real.rpow X (2 * (ρ.re - 1)) := by congr 1; ring

/-- Schur reduction with the row estimate exposed as the only input. -/
theorem zeroPairQuadraticForm_le_of_row
    (χ : DirichletCharacter ℂ q) {X T H : ℝ} (hX : 0 < X)
    (hrow : ∀ ρ ∈ zeroSupport χ 0 T,
      (∑ ρ' ∈ zeroSupport χ 0 T,
        (zeroMultiplicity χ 0 T ρ' : ℝ) /
          (1 + |ρ'.im - ρ.im|)) ≤ H) :
    (∑ ρ ∈ zeroSupport χ 0 T, ∑ ρ' ∈ zeroSupport χ 0 T,
        (zeroMultiplicity χ 0 T ρ : ℝ) *
          (zeroMultiplicity χ 0 T ρ' : ℝ) *
          Real.rpow X (ρ.re + ρ'.re - 1) /
          (1 + |ρ.im - ρ'.im|)) ≤
      X * H *
        (∑ ρ ∈ zeroSupport χ 0 T,
          (zeroMultiplicity χ 0 T ρ : ℝ) *
            Real.rpow X (2 * (ρ.re - 1))) := by
  classical
  let S := zeroSupport χ 0 T
  let m : ℂ → ℝ := fun z => (zeroMultiplicity χ 0 T z : ℝ)
  let w : ℂ → ℝ := fun z => Real.rpow X (z.re - 1)
  let K : ℂ → ℂ → ℝ := fun z z' => 1 / (1 + |z.im - z'.im|)
  have hrow' : ∀ z ∈ S, ∑ z' ∈ S, m z' * K z z' ≤ H := by
    intro z hz
    have hr := hrow z hz
    simpa [S, m, K, div_eq_mul_inv, abs_sub_comm] using hr
  have hschur := MAPPaperWindowVKBypass.finite_weighted_schur
    S m w K H
    (fun z hz => by simp [m])
    (fun z hz z' hz' => by simp [K]; positivity)
    (fun z hz z' hz' => by simp [K, abs_sub_comm])
    hrow'
  calc
    (∑ ρ ∈ zeroSupport χ 0 T, ∑ ρ' ∈ zeroSupport χ 0 T,
        (zeroMultiplicity χ 0 T ρ : ℝ) *
          (zeroMultiplicity χ 0 T ρ' : ℝ) *
          Real.rpow X (ρ.re + ρ'.re - 1) /
          (1 + |ρ.im - ρ'.im|)) =
      X * (∑ ρ ∈ S, ∑ ρ' ∈ S,
        m ρ * m ρ' * w ρ * w ρ' * K ρ ρ') := by
        simp only [S, m, w, K]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ρ hρ
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ρ' hρ'
        rw [rpow_pair_factor hX ρ ρ']
        field_simp <;> ring
    _ ≤ X * (H * ∑ ρ ∈ S, m ρ * (w ρ) ^ 2) :=
      mul_le_mul_of_nonneg_left hschur hX.le
    _ = X * H *
        (∑ ρ ∈ zeroSupport χ 0 T,
          (zeroMultiplicity χ 0 T ρ : ℝ) *
            Real.rpow X (2 * (ρ.re - 1))) := by
      simp only [S, m, w]
      rw [show
        (∑ ρ ∈ zeroSupport χ 0 T,
          (zeroMultiplicity χ 0 T ρ : ℝ) *
            (Real.rpow X (ρ.re - 1)) ^ 2) =
        ∑ ρ ∈ zeroSupport χ 0 T,
          (zeroMultiplicity χ 0 T ρ : ℝ) *
            Real.rpow X (2 * (ρ.re - 1)) by
          apply Finset.sum_congr rfl
          intro ρ hρ
          rw [rpow_weight_sq hX ρ]]
      ring

/-- Pair expansion and the constant-192 kernel bound, before any local-zero
grouping is inserted. -/
theorem intervalIntegral_norm_actualZeroField_sq_le_pairForm
    (χ : DirichletCharacter ℂ q) {X T : ℝ} (hX : 0 < X) :
    (∫ t : ℝ in X / 4..6 * X, ‖actualZeroField χ 0 T t‖ ^ 2) ≤
      192 * (∑ ρ ∈ zeroSupport χ 0 T,
        ∑ ρ' ∈ zeroSupport χ 0 T,
          (zeroMultiplicity χ 0 T ρ : ℝ) *
            (zeroMultiplicity χ 0 T ρ' : ℝ) *
            Real.rpow X (ρ.re + ρ'.re - 1) /
            (1 + |ρ.im - ρ'.im|)) := by
  classical
  let S := zeroSupport χ 0 T
  let mult := zeroMultiplicity χ 0 T
  have hab : X / 4 ≤ 6 * X := by linarith
  have hnonneg : 0 ≤
      ∫ t : ℝ in X / 4..6 * X, ‖actualZeroField χ 0 T t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg _)
  have hexact :=
    MAPAPZeroFieldEnergy28Core.integral_norm_finiteZeroField_sq_eq_pairIntegrals
      S mult (a := X / 4) (b := 6 * X) (by positivity) (by positivity)
  calc
    (∫ t : ℝ in X / 4..6 * X, ‖actualZeroField χ 0 T t‖ ^ 2) =
        ‖(((∫ t : ℝ in X / 4..6 * X,
          ‖actualZeroField χ 0 T t‖ ^ 2) : ℝ) : ℂ)‖ := by
            simp [abs_of_nonneg hnonneg]
    _ = ‖∑ ρ ∈ S, ∑ ρ' ∈ S,
        ∫ t : ℝ in X / 4..6 * X,
          MAPAPZeroFieldEnergy28Core.zeroPairKernel mult ρ ρ' t‖ := by
          simpa [S, mult, actualZeroField] using congrArg norm hexact
    _ ≤ ∑ ρ ∈ S, ‖∑ ρ' ∈ S,
        ∫ t : ℝ in X / 4..6 * X,
          MAPAPZeroFieldEnergy28Core.zeroPairKernel mult ρ ρ' t‖ :=
            norm_sum_le _ _
    _ ≤ ∑ ρ ∈ S, ∑ ρ' ∈ S,
        ‖∫ t : ℝ in X / 4..6 * X,
          MAPAPZeroFieldEnergy28Core.zeroPairKernel mult ρ ρ' t‖ := by
            apply Finset.sum_le_sum
            intro ρ hρ
            exact norm_sum_le _ _
    _ ≤ ∑ ρ ∈ S, ∑ ρ' ∈ S,
        192 * ((mult ρ : ℝ) * (mult ρ' : ℝ)) *
          Real.rpow X (ρ.re + ρ'.re - 1) /
          (1 + |ρ.im - ρ'.im|) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      apply Finset.sum_le_sum
      intro ρ' hρ'
      have hre := zeroSupport_re_mem_unit χ hρ
      have hre' := zeroSupport_re_mem_unit χ hρ'
      exact MAPAPZeroFieldEnergy28Core.norm_integral_zeroPairKernel_le_manuscript
        mult ρ ρ' hX hre.1 hre.2 hre'.1 hre'.2
    _ = 192 * (∑ ρ ∈ zeroSupport χ 0 T,
        ∑ ρ' ∈ zeroSupport χ 0 T,
          (zeroMultiplicity χ 0 T ρ : ℝ) *
            (zeroMultiplicity χ 0 T ρ' : ℝ) *
            Real.rpow X (ρ.re + ρ'.re - 1) /
            (1 + |ρ.im - ρ'.im|)) := by
      simp only [S, mult]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ' hρ'
      ring

/-- Complete real interval-energy estimate from an arbitrary certified row
bound. -/
theorem intervalIntegral_norm_actualZeroField_sq_le_of_row
    (χ : DirichletCharacter ℂ q) {X T H : ℝ} (hX : 0 < X)
    (hrow : ∀ ρ ∈ zeroSupport χ 0 T,
      (∑ ρ' ∈ zeroSupport χ 0 T,
        (zeroMultiplicity χ 0 T ρ' : ℝ) /
          (1 + |ρ'.im - ρ.im|)) ≤ H) :
    (∫ t : ℝ in X / 4..6 * X, ‖actualZeroField χ 0 T t‖ ^ 2) ≤
      192 * X * H *
        (∑ ρ ∈ zeroSupport χ 0 T,
          (zeroMultiplicity χ 0 T ρ : ℝ) *
            Real.rpow X (2 * (ρ.re - 1))) := by
  refine (intervalIntegral_norm_actualZeroField_sq_le_pairForm χ hX).trans ?_
  calc
    192 * (∑ ρ ∈ zeroSupport χ 0 T,
        ∑ ρ' ∈ zeroSupport χ 0 T,
          (zeroMultiplicity χ 0 T ρ : ℝ) *
            (zeroMultiplicity χ 0 T ρ' : ℝ) *
            Real.rpow X (ρ.re + ρ'.re - 1) /
            (1 + |ρ.im - ρ'.im|)) ≤
      192 * (X * H *
        (∑ ρ ∈ zeroSupport χ 0 T,
          (zeroMultiplicity χ 0 T ρ : ℝ) *
            Real.rpow X (2 * (ρ.re - 1)))) := by
      gcongr
      exact zeroPairQuadraticForm_le_of_row χ hX hrow
    _ = _ := by ring

/-- The finite weighted Schur estimate on the literal full-strip zero list. -/
theorem zeroPairQuadraticForm_le_nonprincipal
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {X T : ℝ} (hX : 0 < X) (hT : 0 ≤ T) :
    (∑ ρ ∈ zeroSupport χ 0 T, ∑ ρ' ∈ zeroSupport χ 0 T,
        (zeroMultiplicity χ 0 T ρ : ℝ) *
          (zeroMultiplicity χ 0 T ρ' : ℝ) *
          Real.rpow X (ρ.re + ρ'.re - 1) /
          (1 + |ρ.im - ρ'.im|)) ≤
      X *
        (2 * (1 + 306 * Real.log ((q : ℝ) * (T + 4))) *
          (harmonic (⌊2 * T⌋₊ + 1) : ℝ)) *
        (∑ ρ ∈ zeroSupport χ 0 T,
          (zeroMultiplicity χ 0 T ρ : ℝ) *
            Real.rpow X (2 * (ρ.re - 1))) := by
  classical
  let S := zeroSupport χ 0 T
  let m : ℂ → ℝ := fun z => (zeroMultiplicity χ 0 T z : ℝ)
  let w : ℂ → ℝ := fun z => Real.rpow X (z.re - 1)
  let K : ℂ → ℂ → ℝ := fun z z' => 1 / (1 + |z.im - z'.im|)
  let H := 2 * (1 + 306 * Real.log ((q : ℝ) * (T + 4))) *
    (harmonic (⌊2 * T⌋₊ + 1) : ℝ)
  have hrow : ∀ z ∈ S, ∑ z' ∈ S, m z' * K z z' ≤ H := by
    intro z hz
    have hr := reciprocalRow_le_nonprincipal χ hprim hχ hT z hz
    simpa [S, m, K, H, div_eq_mul_inv, abs_sub_comm] using hr
  have hschur := MAPPaperWindowVKBypass.finite_weighted_schur
    S m w K H
    (fun z hz => by simp [m])
    (fun z hz z' hz' => by simp [K]; positivity)
    (fun z hz z' hz' => by simp [K, abs_sub_comm])
    hrow
  calc
    (∑ ρ ∈ zeroSupport χ 0 T, ∑ ρ' ∈ zeroSupport χ 0 T,
        (zeroMultiplicity χ 0 T ρ : ℝ) *
          (zeroMultiplicity χ 0 T ρ' : ℝ) *
          Real.rpow X (ρ.re + ρ'.re - 1) /
          (1 + |ρ.im - ρ'.im|)) =
      X * (∑ ρ ∈ S, ∑ ρ' ∈ S,
        m ρ * m ρ' * w ρ * w ρ' * K ρ ρ') := by
        simp only [S, m, w, K]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ρ hρ
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ρ' hρ'
        rw [rpow_pair_factor hX ρ ρ']
        field_simp
        <;> ring
    _ ≤ X * (H * ∑ ρ ∈ S, m ρ * (w ρ) ^ 2) :=
      mul_le_mul_of_nonneg_left hschur hX.le
    _ = X *
        (2 * (1 + 306 * Real.log ((q : ℝ) * (T + 4))) *
          (harmonic (⌊2 * T⌋₊ + 1) : ℝ)) *
        (∑ ρ ∈ zeroSupport χ 0 T,
          (zeroMultiplicity χ 0 T ρ : ℝ) *
            Real.rpow X (2 * (ρ.re - 1))) := by
      simp only [H, S, m, w]
      rw [show
        (∑ ρ ∈ zeroSupport χ 0 T,
          (zeroMultiplicity χ 0 T ρ : ℝ) *
            (Real.rpow X (ρ.re - 1)) ^ 2) =
        ∑ ρ ∈ zeroSupport χ 0 T,
          (zeroMultiplicity χ 0 T ρ : ℝ) *
            Real.rpow X (2 * (ρ.re - 1)) by
          apply Finset.sum_congr rfl
          intro ρ hρ
          rw [rpow_weight_sq hX ρ]]
      ring

/-- Deterministic real interval-energy estimate for one primitive
nonprincipal character, before conversion to the literal ENNReal field. -/
theorem intervalIntegral_norm_actualZeroField_sq_le_nonprincipal
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {X T : ℝ} (hX : 0 < X) (hT : 0 ≤ T) :
    (∫ t : ℝ in X / 4..6 * X, ‖actualZeroField χ 0 T t‖ ^ 2) ≤
      192 * X *
        (2 * (1 + 306 * Real.log ((q : ℝ) * (T + 4))) *
          (harmonic (⌊2 * T⌋₊ + 1) : ℝ)) *
        (∑ ρ ∈ zeroSupport χ 0 T,
          (zeroMultiplicity χ 0 T ρ : ℝ) *
            Real.rpow X (2 * (ρ.re - 1))) := by
  classical
  let S := zeroSupport χ 0 T
  let mult := zeroMultiplicity χ 0 T
  have hab : X / 4 ≤ 6 * X := by linarith
  have hnonneg : 0 ≤
      ∫ t : ℝ in X / 4..6 * X, ‖actualZeroField χ 0 T t‖ ^ 2 := by
    exact intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg _)
  have hexact :=
    MAPAPZeroFieldEnergy28Core.integral_norm_finiteZeroField_sq_eq_pairIntegrals
      S mult (a := X / 4) (b := 6 * X) (by positivity) (by positivity)
  have htriangle :
      (∫ t : ℝ in X / 4..6 * X, ‖actualZeroField χ 0 T t‖ ^ 2) ≤
        ∑ ρ ∈ S, ∑ ρ' ∈ S,
          ‖∫ t : ℝ in X / 4..6 * X,
            MAPAPZeroFieldEnergy28Core.zeroPairKernel mult ρ ρ' t‖ := by
    calc
      (∫ t : ℝ in X / 4..6 * X, ‖actualZeroField χ 0 T t‖ ^ 2) =
          ‖(((∫ t : ℝ in X / 4..6 * X,
            ‖actualZeroField χ 0 T t‖ ^ 2) : ℝ) : ℂ)‖ := by
              simp [abs_of_nonneg hnonneg]
      _ = ‖∑ ρ ∈ S, ∑ ρ' ∈ S,
          ∫ t : ℝ in X / 4..6 * X,
            MAPAPZeroFieldEnergy28Core.zeroPairKernel mult ρ ρ' t‖ := by
            simpa [S, mult, actualZeroField] using congrArg norm hexact
      _ ≤ ∑ ρ ∈ S, ‖∑ ρ' ∈ S,
          ∫ t : ℝ in X / 4..6 * X,
            MAPAPZeroFieldEnergy28Core.zeroPairKernel mult ρ ρ' t‖ :=
              norm_sum_le _ _
      _ ≤ ∑ ρ ∈ S, ∑ ρ' ∈ S,
          ‖∫ t : ℝ in X / 4..6 * X,
            MAPAPZeroFieldEnergy28Core.zeroPairKernel mult ρ ρ' t‖ := by
              apply Finset.sum_le_sum
              intro ρ hρ
              exact norm_sum_le _ _
  refine htriangle.trans ?_
  calc
    (∑ ρ ∈ S, ∑ ρ' ∈ S,
        ‖∫ t : ℝ in X / 4..6 * X,
          MAPAPZeroFieldEnergy28Core.zeroPairKernel mult ρ ρ' t‖) ≤
      ∑ ρ ∈ S, ∑ ρ' ∈ S,
        192 * ((mult ρ : ℝ) * (mult ρ' : ℝ)) *
          Real.rpow X (ρ.re + ρ'.re - 1) /
          (1 + |ρ.im - ρ'.im|) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      apply Finset.sum_le_sum
      intro ρ' hρ'
      have hre := zeroSupport_re_mem_unit χ hρ
      have hre' := zeroSupport_re_mem_unit χ hρ'
      exact MAPAPZeroFieldEnergy28Core.norm_integral_zeroPairKernel_le_manuscript
        mult ρ ρ' hX hre.1 hre.2 hre'.1 hre'.2
    _ = 192 * (∑ ρ ∈ zeroSupport χ 0 T,
        ∑ ρ' ∈ zeroSupport χ 0 T,
          (zeroMultiplicity χ 0 T ρ : ℝ) *
            (zeroMultiplicity χ 0 T ρ' : ℝ) *
            Real.rpow X (ρ.re + ρ'.re - 1) /
            (1 + |ρ.im - ρ'.im|)) := by
      simp only [S, mult]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ' hρ'
      ring
    _ ≤ 192 * (X *
        (2 * (1 + 306 * Real.log ((q : ℝ) * (T + 4))) *
          (harmonic (⌊2 * T⌋₊ + 1) : ℝ)) *
        (∑ ρ ∈ zeroSupport χ 0 T,
          (zeroMultiplicity χ 0 T ρ : ℝ) *
            Real.rpow X (2 * (ρ.re - 1)))) := by
      gcongr
      exact zeroPairQuadraticForm_le_nonprincipal χ hprim hχ hX hT
    _ = _ := by ring

private theorem continuousOn_norm_actualZeroField_sq
    (χ : DirichletCharacter ℂ q) {X T : ℝ} (hX : 0 < X) :
    ContinuousOn (fun t : ℝ => ‖actualZeroField χ 0 T t‖ ^ 2)
      (Set.Icc (X / 4) (6 * X)) := by
  apply ContinuousOn.pow
  · apply ContinuousOn.norm
    unfold actualZeroField finiteZeroField
    apply continuousOn_finsetSum
    intro ρ hρ
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    exact (continuousAt_const.mul
      (Complex.continuousAt_ofReal_cpow_const t (ρ - 1)
        (Or.inr htpos.ne'))).continuousWithinAt

/-- Exact conversion between the literal indicator-valued ENNReal energy and
the real interval integral used by the pair expansion. -/
theorem lintegral_zeroNormField_sq_eq_intervalIntegral
    (χ : DirichletCharacter ℂ q) {X T : ℝ} (hX : 0 < X) :
    (∫⁻ t : ℝ,
      ((Set.Icc (X / 4) (6 * X)).indicator
        (fun u => ENNReal.ofReal ‖actualZeroField χ 0 T u‖) t) ^ 2) =
      ENNReal.ofReal
        (∫ t : ℝ in X / 4..6 * X, ‖actualZeroField χ 0 T t‖ ^ 2) := by
  let f : ℝ → ℝ := fun t => ‖actualZeroField χ 0 T t‖ ^ 2
  have hcont : ContinuousOn f (Set.Icc (X / 4) (6 * X)) :=
    continuousOn_norm_actualZeroField_sq χ hX
  have hint : IntegrableOn f (Set.Icc (X / 4) (6 * X)) :=
    hcont.integrableOn_Icc
  have hnonneg : 0 ≤ᶠ[ae (volume.restrict (Set.Icc (X / 4) (6 * X)))] f :=
    Filter.Eventually.of_forall (fun t => sq_nonneg _)
  have hpoint (t : ℝ) :
      ((Set.Icc (X / 4) (6 * X)).indicator
        (fun u => ENNReal.ofReal ‖actualZeroField χ 0 T u‖) t) ^ 2 =
      (Set.Icc (X / 4) (6 * X)).indicator
        (fun u => ENNReal.ofReal (f u)) t := by
    by_cases ht : t ∈ Set.Icc (X / 4) (6 * X)
    · simp only [Set.indicator_of_mem ht]
      rw [ENNReal.ofReal_pow (norm_nonneg _) 2]
    · simp [Set.indicator_of_notMem ht]
  calc
    (∫⁻ t : ℝ,
      ((Set.Icc (X / 4) (6 * X)).indicator
        (fun u => ENNReal.ofReal ‖actualZeroField χ 0 T u‖) t) ^ 2) =
      ∫⁻ t : ℝ, (Set.Icc (X / 4) (6 * X)).indicator
        (fun u => ENNReal.ofReal (f u)) t := by
          apply lintegral_congr
          intro t
          exact hpoint t
    _ = ∫⁻ t : ℝ in Set.Icc (X / 4) (6 * X),
        ENNReal.ofReal (f t) := lintegral_indicator measurableSet_Icc _
    _ = ENNReal.ofReal
        (∫ t : ℝ in Set.Icc (X / 4) (6 * X), f t) :=
      (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
    _ = ENNReal.ofReal
        (∫ t : ℝ in X / 4..6 * X, f t) := by
      congr 1
      rw [intervalIntegral.integral_of_le (by linarith),
        integral_Icc_eq_integral_Ioc]

/-- Literal ENNReal energy estimate from an arbitrary certified row bound. -/
theorem lintegral_zeroNormField_sq_le_of_row
    (χ : DirichletCharacter ℂ q) {X T H : ℝ} (hX : 0 < X)
    (hrow : ∀ ρ ∈ zeroSupport χ 0 T,
      (∑ ρ' ∈ zeroSupport χ 0 T,
        (zeroMultiplicity χ 0 T ρ' : ℝ) /
          (1 + |ρ'.im - ρ.im|)) ≤ H) :
    (∫⁻ t : ℝ,
      ((Set.Icc (X / 4) (6 * X)).indicator
        (fun u => ENNReal.ofReal ‖actualZeroField χ 0 T u‖) t) ^ 2) ≤
      ENNReal.ofReal
        (192 * X * H *
          (∑ ρ ∈ zeroSupport χ 0 T,
            (zeroMultiplicity χ 0 T ρ : ℝ) *
              Real.rpow X (2 * (ρ.re - 1)))) := by
  rw [lintegral_zeroNormField_sq_eq_intervalIntegral χ hX]
  exact ENNReal.ofReal_le_ofReal
    (intervalIntegral_norm_actualZeroField_sq_le_of_row χ hX hrow)

/-- Literal ENNReal energy estimate for one primitive nonprincipal
character. -/
theorem lintegral_zeroNormField_sq_le_nonprincipal
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {X T : ℝ} (hX : 0 < X) (hT : 0 ≤ T) :
    (∫⁻ t : ℝ,
      ((Set.Icc (X / 4) (6 * X)).indicator
        (fun u => ENNReal.ofReal ‖actualZeroField χ 0 T u‖) t) ^ 2) ≤
      ENNReal.ofReal
        (192 * X *
          (2 * (1 + 306 * Real.log ((q : ℝ) * (T + 4))) *
            (harmonic (⌊2 * T⌋₊ + 1) : ℝ)) *
          (∑ ρ ∈ zeroSupport χ 0 T,
            (zeroMultiplicity χ 0 T ρ : ℝ) *
              Real.rpow X (2 * (ρ.re - 1)))) := by
  rw [lintegral_zeroNormField_sq_eq_intervalIntegral χ hX]
  exact ENNReal.ofReal_le_ofReal
    (intervalIntegral_norm_actualZeroField_sq_le_nonprincipal
      χ hprim hχ hX hT)

#print axioms reciprocalRow_le_nonprincipal
#print axioms zeroPairQuadraticForm_le_nonprincipal
#print axioms intervalIntegral_norm_actualZeroField_sq_le_nonprincipal
#print axioms lintegral_zeroNormField_sq_eq_intervalIntegral
#print axioms lintegral_zeroNormField_sq_le_nonprincipal

end
end MAPAPZeroFieldEnergy28Grouping
