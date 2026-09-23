import GuthMaynardLemma295LineTwoFubini
import GoldfeldFourfoldContour

/-!
# Finite zeta-pole displacement for Lemma 29.5

The initial zeta--Mellin integrand has one pole, at `s = 1 + ig`.
This file removes that pole by the certified regularized zeta function and
applies the existing excised-rectangle residue theorem.  No limiting-height
or tail estimate is included in the finite identity.
-/

namespace GuthMaynardLemma295FiniteContour

open Set MeasureTheory Complex Filter Asymptotics
open FinitePoleRectangle
open GuthMaynardJutilaReflection2941
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295LineTwoFubini
open MAPGoldfeldSiegel
open scoped FourierTransform SchwartzMap

noncomputable section

theorem sourceHZero_isBigO_atTop (a : ℝ) :
    sourceHZero =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_gt_atTop (5 / 2 : ℝ)] with x hx
  rw [sourceHZero_support x (by
    intro hmem
    exact (not_lt_of_ge hmem.2) hx)]
  simp

theorem sourceHZero_isBigO_atZero (b : ℝ) :
    sourceHZero =O[nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun x : ℝ => x ^ (-b)) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with x hx
  rw [sourceHZero_support x (by
    intro hmem
    exact (not_lt_of_ge hmem.1) hx)]
  simp

/-- Compact support away from zero makes the cutoff Mellin transform entire. -/
theorem differentiableAt_mellin_sourceHZero (s : ℂ) :
    DifferentiableAt ℂ (mellin sourceHZero) s := by
  apply mellin_differentiableAt_of_isBigO_rpow
    (a := s.re + 1) (b := s.re - 1)
  · exact sourceHZero_contDiff.continuous.locallyIntegrable.locallyIntegrableOn _
  · exact sourceHZero_isBigO_atTop (s.re + 1)
  · linarith
  · exact sourceHZero_isBigO_atZero (s.re - 1)
  · linarith

theorem differentiable_mellin_sourceHZero :
    Differentiable ℂ (mellin sourceHZero) :=
  fun s => differentiableAt_mellin_sourceHZero s

def lemma295Pole (g : ℝ) : ℂ := 1 + g * Complex.I

def lemma295RawIntegrand (N g : ℝ) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (s - g * Complex.I) *
    riemannZeta (s - g * Complex.I) * mellin sourceHZero s

def lemma295PoleNumerator (N g : ℝ) (s : ℂ) : ℂ :=
  regularizedRiemannZeta (s - g * Complex.I) *
    (N : ℂ) ^ (s - g * Complex.I) * mellin sourceHZero s

def lemma295PoleResidue (N g : ℝ) : ℂ :=
  (N : ℂ) * mellin sourceHZero (lemma295Pole g)

def lemma295PoleRemainder (N g : ℝ) : ℂ → ℂ :=
  dslope (lemma295PoleNumerator N g) (lemma295Pole g)

theorem analyticAt_lemma295PoleNumerator
    {N : ℝ} (hN : 0 < N) (g : ℝ) (s : ℂ) :
    AnalyticAt ℂ (lemma295PoleNumerator N g) s := by
  unfold lemma295PoleNumerator
  have hpow : Differentiable ℂ (fun z : ℂ =>
      (N : ℂ) ^ (z - g * Complex.I)) :=
    (differentiable_id.sub_const _).const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hN.ne'))
  have hinner : AnalyticAt ℂ (fun z : ℂ => z - g * Complex.I) s :=
    analyticAt_id.sub analyticAt_const
  have hreg : AnalyticAt ℂ
      (fun z : ℂ => regularizedRiemannZeta (z - g * Complex.I)) s := by
    simpa only [Function.comp_apply] using!
      (analyticAt_regularizedRiemannZeta (s - g * Complex.I)).comp
        (f := fun z : ℂ => z - g * Complex.I) hinner
  exact (hreg.mul (hpow.analyticAt s)).mul
    (differentiable_mellin_sourceHZero.analyticAt s)

theorem analyticAt_lemma295PoleRemainder
    {N : ℝ} (hN : 0 < N) (g : ℝ) (s : ℂ) :
    AnalyticAt ℂ (lemma295PoleRemainder N g) s := by
  unfold lemma295PoleRemainder
  exact analyticAt_dslope_of_analyticAt
    (analyticAt_lemma295PoleNumerator hN g (lemma295Pole g))
    (analyticAt_lemma295PoleNumerator hN g s)

theorem lemma295PoleNumerator_at_pole
    (N g : ℝ) :
    lemma295PoleNumerator N g (lemma295Pole g) =
      lemma295PoleResidue N g := by
  unfold lemma295PoleNumerator lemma295PoleResidue lemma295Pole
  simp

/-- Quantitative residue decay from the already-certified arbitrary-order
Mellin bound on `Re s=1`.  This is the source's use of (29.30) at the zeta
pole; no contour estimate enters. -/
theorem norm_lemma295PoleResidue_le
    {N g : ℝ} (hN : 0 < N) {k : ℕ} (hg : g ≠ 0) :
    ‖lemma295PoleResidue N g‖ ≤
      N *
        (SchwartzMap.seminorm ℂ k 0
          (𝓕 (GuthMaynardMellinRapidDecay.mellinLogLiftSchwartz sourceHZero
            (GuthMaynardMellinRapidDecay.mellinLogLift_hasCompactSupport
              (by norm_num : (0 : ℝ) < 1 / 2)
              (by norm_num : (0 : ℝ) < 5 / 2) sourceHZero_support)
            (GuthMaynardMellinRapidDecay.mellinLogLift_contDiff
              sourceHZero_contDiff)) : 𝓢(ℝ, ℂ)) /
          |g / (2 * Real.pi)| ^ k) := by
  have hmellin :=
    GuthMaynardMellinRapidDecay.norm_mellin_line_one_le_seminorm_div_scaledPower
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 5 / 2) sourceHZero_support
      sourceHZero_contDiff k hg
  unfold lemma295PoleResidue lemma295Pole
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hN.le]
  exact mul_le_mul_of_nonneg_left (by simpa [mul_comm] using hmellin) hN.le

theorem lemma295RawIntegrand_eq_remainder_add_principal
    (N g : ℝ) {s : ℂ}
    (hsp : s ≠ lemma295Pole g) :
    lemma295RawIntegrand N g s =
      lemma295PoleRemainder N g s +
        lemma295PoleResidue N g * (s - lemma295Pole g)⁻¹ := by
  have hz : s - g * Complex.I ≠ 1 := by
    intro h
    apply hsp
    unfold lemma295Pole
    exact (sub_eq_iff_eq_add.mp h)
  have hreg := regularizedRiemannZeta_eq_mul hz
  have hds : lemma295PoleRemainder N g s =
      (lemma295PoleNumerator N g s -
        lemma295PoleNumerator N g (lemma295Pole g)) /
          (s - lemma295Pole g) := by
    rw [lemma295PoleRemainder, dslope_of_ne]
    · simp [slope, vsub_eq_sub, div_eq_inv_mul]
    · simpa using hsp
  rw [hds, lemma295PoleNumerator_at_pole]
  unfold lemma295RawIntegrand lemma295PoleNumerator lemma295Pole
  rw [hreg]
  have hpform : s - g * Complex.I - 1 =
      s - (1 + g * Complex.I) := by ring
  rw [hpform]
  have hden : s - (1 + g * Complex.I) ≠ 0 := by
    simpa [lemma295Pole] using sub_ne_zero.mpr hsp
  field_simp [hden]
  <;> ring

theorem lemma295RawIntegrand_lineTwo
    (N g r : ℝ) :
    lemma295RawIntegrand N g (lineTwoPoint r) =
      lineTwoZetaIntegrand N g r := by
  rfl

/-- Exact finite rectangle displacement across the sole zeta pole. -/
theorem finiteRectangle_lemma295_shift
    {N : ℝ} (hN : 0 < N) (g : ℝ)
    {a c u v rad : ℝ} (hrad : 0 < rad)
    (haleft : a < 1 - rad) (haright : 1 + rad < c)
    (hbelow : u < g - rad) (habove : g + rad < v) :
    rectangleBoundaryIntegral (lemma295RawIntegrand N g) a c u v =
      (2 * Real.pi * Complex.I) * lemma295PoleResidue N g := by
  let p : Unit → ℂ := fun _ => lemma295Pole g
  let R : Unit → ℂ := fun _ => lemma295PoleResidue N g
  let radius : Unit → ℝ := fun _ => rad
  let rem := lemma295PoleRemainder N g
  have hsum : (∑ i ∈ ({()} : Finset Unit), R i) =
      lemma295PoleResidue N g := by simp [R]
  rw [← hsum]
  apply rectangleBoundaryIntegral_eq_two_pi_I_mul_sum_residue
    ({()} : Finset Unit) p R radius (lemma295RawIntegrand N g) rem a c u v
  · intro i hi; simpa [radius] using hrad
  · intro i hi; simpa [p, lemma295Pole, radius] using haleft
  · intro i hi; simpa [p, lemma295Pole, radius] using haright
  · intro i hi; simpa [p, lemma295Pole, radius] using hbelow
  · intro i hi; simpa [p, lemma295Pole, radius] using habove
  · apply boundaryIntervalIntegrable_of_differentiableOn
    intro z hz
    exact (analyticAt_lemma295PoleRemainder hN g z).differentiableWithinAt
  · intro z hz
    exact (analyticAt_lemma295PoleRemainder hN g z).differentiableWithinAt
  · intro x
    have hsp : (x : ℂ) + (u : ℂ) * Complex.I ≠ lemma295Pole g := by
      intro h
      have him := congrArg Complex.im h
      simp [lemma295Pole] at him
      linarith
    simpa [rem, p, R] using
      lemma295RawIntegrand_eq_remainder_add_principal N g hsp
  · intro x
    have hsp : (x : ℂ) + (v : ℂ) * Complex.I ≠ lemma295Pole g := by
      intro h
      have him := congrArg Complex.im h
      simp [lemma295Pole] at him
      linarith
    simpa [rem, p, R] using
      lemma295RawIntegrand_eq_remainder_add_principal N g hsp
  · intro y
    have hsp : (c : ℂ) + (y : ℂ) * Complex.I ≠ lemma295Pole g := by
      intro h
      have hre := congrArg Complex.re h
      simp [lemma295Pole] at hre
      linarith
    simpa [rem, p, R] using
      lemma295RawIntegrand_eq_remainder_add_principal N g hsp
  · intro y
    have hsp : (a : ℂ) + (y : ℂ) * Complex.I ≠ lemma295Pole g := by
      intro h
      have hre := congrArg Complex.re h
      simp [lemma295Pole] at hre
      linarith
    simpa [rem, p, R] using
      lemma295RawIntegrand_eq_remainder_add_principal N g hsp

end
end GuthMaynardLemma295FiniteContour

#print axioms GuthMaynardLemma295FiniteContour.differentiableAt_mellin_sourceHZero
#print axioms GuthMaynardLemma295FiniteContour.norm_lemma295PoleResidue_le
#print axioms GuthMaynardLemma295FiniteContour.finiteRectangle_lemma295_shift
