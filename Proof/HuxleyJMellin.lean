import HuxleyJVertical
import Mathlib.Analysis.MellinInversion

/-!
# Exact Mellin transform behind Huxley 1973 (2.5)

The source kernel is a linear combination of the Mellin transforms of a
one-sided unit cutoff and its two imaginary powers.  This module certifies
that transform identity.  Together with `HuxleyJVertical`, it supplies both
analytic inputs needed for pointwise Mellin inversion.
-/

namespace MAPHuxleyJMellin

open Complex Real Set MeasureTheory Filter
open scoped Topology

noncomputable section

private def p : ℂ := (Real.pi : ℂ) * I
private def n : ℂ := -((Real.pi : ℂ) * I)

/-- Unit cutoff on the Mellin half-line.  Values at nonpositive arguments do
not enter the Mellin transform. -/
def unitCutoff (x : ℝ) : ℂ := if 0 < x ∧ x ≤ 1 then 1 else 0

private theorem indicator_unitCutoff_integrand_eq
    (s : ℂ) (x : ℝ) :
    (Ioi (0 : ℝ)).indicator
        (fun x : ℝ => (x : ℂ) ^ (s - 1) • unitCutoff x) x =
      (Ioc (0 : ℝ) 1).indicator
        (fun x : ℝ => (x : ℂ) ^ (s - 1)) x := by
  by_cases hx : 0 < x
  · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
    by_cases hx1 : x ≤ 1
    · rw [indicator_of_mem (show x ∈ Ioc (0 : ℝ) 1 from ⟨hx, hx1⟩)]
      simp [unitCutoff, hx, hx1]
    · rw [indicator_of_notMem (show x ∉ Ioc (0 : ℝ) 1 by simp [hx, hx1])]
      simp [unitCutoff, hx, hx1]
  · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) by simpa using hx)]
    rw [indicator_of_notMem (show x ∉ Ioc (0 : ℝ) 1 by
      intro h; exact hx h.1)]

/-- The unit cutoff has Mellin transform `1/s` in the right half-plane. -/
theorem mellin_unitCutoff_eq {s : ℂ} (hs : 0 < s.re) :
    mellin unitCutoff s = 1 / s := by
  rw [mellin, ← integral_indicator measurableSet_Ioi]
  rw [show (Ioi (0 : ℝ)).indicator
        (fun x : ℝ => (x : ℂ) ^ (s - 1) • unitCutoff x) =
      (Ioc (0 : ℝ) 1).indicator
        (fun x : ℝ => (x : ℂ) ^ (s - 1)) by
      funext x; exact indicator_unitCutoff_integrand_eq s x]
  rw [integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  calc
    (∫ x : ℝ in 0..1, (x : ℂ) ^ (s - 1)) =
        Complex.betaIntegral s 1 := by
      simp [Complex.betaIntegral]
    _ = 1 / s := Complex.betaIntegral_eval_one_right hs

/-- Absolute convergence of the same elementary transform. -/
theorem mellinConvergent_unitCutoff {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent unitCutoff s := by
  rw [MellinConvergent, ← integrable_indicator_iff measurableSet_Ioi]
  rw [show (Ioi (0 : ℝ)).indicator
        (fun x : ℝ => (x : ℂ) ^ (s - 1) • unitCutoff x) =
      (Ioc (0 : ℝ) 1).indicator
        (fun x : ℝ => (x : ℂ) ^ (s - 1)) by
      funext x; exact indicator_unitCutoff_integrand_eq s x]
  rw [integrable_indicator_iff measurableSet_Ioc]
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  simpa only [sub_self, cpow_zero, mul_one] using
    (Complex.betaIntegral_convergent hs (by norm_num : 0 < ((1 : ℂ)).re))

/-- Complex-exponential presentation of the right side of Huxley (2.5). -/
def huxleyJWeight (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * unitCutoff x -
    (1 / 4 : ℂ) * ((x : ℂ) ^ p * unitCutoff x) -
    (1 / 4 : ℂ) * ((x : ℂ) ^ n * unitCutoff x)

private theorem shifted_re_pos {s : ℂ} (hs : 0 < s.re) :
    0 < (s + p).re ∧ 0 < (s + n).re := by
  unfold p n
  simpa using And.intro hs hs

private theorem mellin_shiftedCutoff_eq
    {s a : ℂ} (hsa : 0 < (s + a).re) :
    mellin (fun x : ℝ => (x : ℂ) ^ a * unitCutoff x) s =
      1 / (s + a) := by
  rw [show (fun x : ℝ => (x : ℂ) ^ a * unitCutoff x) =
      (fun x : ℝ => (x : ℂ) ^ a • unitCutoff x) by
        funext x; simp only [smul_eq_mul]]
  rw [mellin_cpow_smul, mellin_unitCutoff_eq hsa]

private theorem mellinConvergent_shiftedCutoff
    {s a : ℂ} (hsa : 0 < (s + a).re) :
    MellinConvergent (fun x : ℝ => (x : ℂ) ^ a * unitCutoff x) s := by
  rw [show (fun x : ℝ => (x : ℂ) ^ a * unitCutoff x) =
      (fun x : ℝ => (x : ℂ) ^ a • unitCutoff x) by
        funext x; simp only [smul_eq_mul],
    MellinConvergent.cpow_smul]
  exact mellinConvergent_unitCutoff hsa

/-- Exact transform identity: the Mellin transform of the source weight is
Huxley's rational kernel `J`. -/
theorem mellin_huxleyJWeight_eq {s : ℂ} (hs : 0 < s.re) :
    mellin huxleyJWeight s =
      MAPHuxleyReflectionKernelAlgebra.huxleyJ s := by
  obtain ⟨hsp, hsn⟩ := shifted_re_pos hs
  have h0c := mellinConvergent_unitCutoff hs
  have hpc := mellinConvergent_shiftedCutoff hsp
  have hnc := mellinConvergent_shiftedCutoff hsn
  have h0 := mellin_unitCutoff_eq hs
  have hp := mellin_shiftedCutoff_eq hsp
  have hn := mellin_shiftedCutoff_eq hsn
  unfold huxleyJWeight
  rw [show (fun x : ℝ =>
      (1 / 2 : ℂ) * unitCutoff x -
        (1 / 4 : ℂ) * ((x : ℂ) ^ p * unitCutoff x) -
        (1 / 4 : ℂ) * ((x : ℂ) ^ n * unitCutoff x)) =
      (fun x : ℝ =>
        (1 / 2 : ℂ) • unitCutoff x -
          (1 / 4 : ℂ) • ((x : ℂ) ^ p * unitCutoff x) -
          (1 / 4 : ℂ) • ((x : ℂ) ^ n * unitCutoff x)) by
      funext x; simp only [smul_eq_mul]]
  have hs0 := hasMellin_const_smul h0c (1 / 2 : ℂ)
  have hsp' := hasMellin_const_smul hpc (1 / 4 : ℂ)
  have hsn' := hasMellin_const_smul hnc (1 / 4 : ℂ)
  have hsub1 := hasMellin_sub hs0.1 hsp'.1
  have hsub2 := hasMellin_sub hsub1.1 hsn'.1
  rw [hsub2.2, hsub1.2, hs0.2, hsp'.2, hsn'.2, h0, hp, hn]
  rw [MAPHuxleyReflectionKernelAlgebra.huxleyJ_eq_partialFractions
    (Complex.ne_zero_of_re_pos hs)
    (Complex.ne_zero_of_re_pos (by simpa [p] using hsp))
    (Complex.ne_zero_of_re_pos (by simpa [p, n] using hsn))]
  unfold MAPHuxleyReflectionKernelAlgebra.huxleyJPartialFractions p n
  simp only [smul_eq_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Absolute convergence of the full source weight throughout the right
half-plane. -/
theorem mellinConvergent_huxleyJWeight {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent huxleyJWeight s := by
  obtain ⟨hsp, hsn⟩ := shifted_re_pos hs
  have h0c := mellinConvergent_unitCutoff hs
  have hpc := mellinConvergent_shiftedCutoff hsp
  have hnc := mellinConvergent_shiftedCutoff hsn
  have hs0 := (hasMellin_const_smul h0c (1 / 2 : ℂ)).1
  have hsp' := (hasMellin_const_smul hpc (1 / 4 : ℂ)).1
  have hsn' := (hasMellin_const_smul hnc (1 / 4 : ℂ)).1
  have hsub1 := (hasMellin_sub hs0 hsp').1
  have hsub2 := (hasMellin_sub hsub1 hsn').1
  simpa only [huxleyJWeight, smul_eq_mul] using! hsub2

/-- The transform itself is vertically integrable on the inversion line,
by the exact transform identity and the rational-kernel majorant. -/
theorem verticalIntegrable_mellin_huxleyJWeight :
    Complex.VerticalIntegrable (mellin huxleyJWeight) 2 := by
  unfold Complex.VerticalIntegrable
  have hJ := MAPHuxleyJVertical.verticalIntegrable_huxleyJ
  unfold Complex.VerticalIntegrable at hJ
  apply hJ.congr
  exact Filter.Eventually.of_forall (fun t =>
    (mellin_huxleyJWeight_eq (s := (2 : ℂ) + t * I) (by simp)).symm)

private def rawWeight (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) - (1 / 4 : ℂ) * (x : ℂ) ^ p -
    (1 / 4 : ℂ) * (x : ℂ) ^ n

private theorem continuousAt_rawWeight {x : ℝ} (hx : 0 < x) :
    ContinuousAt rawWeight x := by
  have hp : ContinuousAt (fun y : ℝ => (y : ℂ) ^ p) x :=
    Complex.continuousAt_ofReal_cpow_const x p (Or.inr hx.ne')
  have hn : ContinuousAt (fun y : ℝ => (y : ℂ) ^ n) x :=
    Complex.continuousAt_ofReal_cpow_const x n (Or.inr hx.ne')
  unfold rawWeight
  fun_prop

private def positiveBase (x : ℝ) : ℝ := max x (1 / 2)

private def boundarySurrogate (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) - (1 / 4 : ℂ) * ((positiveBase x : ℝ) : ℂ) ^ p -
    (1 / 4 : ℂ) * ((positiveBase x : ℝ) : ℂ) ^ n

private theorem continuous_boundarySurrogate : Continuous boundarySurrogate := by
  have hbase : Continuous positiveBase := by
    unfold positiveBase
    fun_prop
  have hpow (a : ℂ) :
      Continuous (fun x : ℝ => (((positiveBase x : ℝ) : ℂ) ^ a)) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hbpos : 0 < positiveBase x := by
      unfold positiveBase
      exact lt_of_lt_of_le (by norm_num : 0 < (1 / 2 : ℝ)) (le_max_right _ _)
    have houter := Complex.continuousAt_ofReal_cpow_const
      (positiveBase x) a (Or.inr hbpos.ne')
    simpa only [Function.comp_apply] using! houter.comp hbase.continuousAt
  unfold boundarySurrogate
  fun_prop

private theorem boundarySurrogate_one : boundarySurrogate 1 = 0 := by
  norm_num [boundarySurrogate, positiveBase]

private theorem continuous_boundaryPiecewise :
    Continuous (fun x : ℝ => if x ≤ 1 then boundarySurrogate x else 0) := by
  apply continuous_if
  · intro x hx
    have hx1 : x = 1 := by
      simpa only [show {y : ℝ | y ≤ 1} = Iic 1 from rfl,
        frontier_Iic, mem_singleton_iff] using hx
    subst x
    exact boundarySurrogate_one
  · exact continuous_boundarySurrogate.continuousOn
  · exact continuous_const.continuousOn

/-- The weight in (2.5) is continuous at every positive point, including
the cutoff `x=1` where all three Mellin components cancel. -/
theorem continuousAt_huxleyJWeight {x : ℝ} (hx : 0 < x) :
    ContinuousAt huxleyJWeight x := by
  rcases lt_trichotomy x 1 with hx1 | rfl | hx1
  · have heq : huxleyJWeight =ᶠ[𝓝 x] rawWeight := by
      filter_upwards [Ioi_mem_nhds hx, Iio_mem_nhds hx1] with y hy0 hy1
      have hy0' : 0 < y := hy0
      have hy1' : y < 1 := hy1
      simp [huxleyJWeight, rawWeight, unitCutoff, hy0', hy1'.le]
    exact (continuousAt_rawWeight hx).congr_of_eventuallyEq heq
  · let g : ℝ → ℂ := fun y => if y ≤ 1 then boundarySurrogate y else 0
    have hg : ContinuousAt g 1 := continuous_boundaryPiecewise.continuousAt
    have heq : huxleyJWeight =ᶠ[𝓝 (1 : ℝ)] g := by
      filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1),
        Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)] with y hy0 hyhalf
      have hy0' : 0 < y := hy0
      have hyhalf' : (1 / 2 : ℝ) < y := hyhalf
      by_cases hy1 : y ≤ 1
      · have hmax : max y (1 / 2 : ℝ) = y := max_eq_left hyhalf'.le
        have hsur : boundarySurrogate y = rawWeight y := by
          unfold boundarySurrogate rawWeight positiveBase
          rw [hmax]
        rw [show g y = boundarySurrogate y by simp [g, hy1], hsur]
        simp [huxleyJWeight, rawWeight, unitCutoff, hy0', hy1]
      · simp [g, huxleyJWeight, unitCutoff, hy0', hy1]
    exact hg.congr_of_eventuallyEq heq
  · have heq : huxleyJWeight =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
      filter_upwards [Ioi_mem_nhds hx1] with y hy1
      have hy1' : 1 < y := hy1
      simp [huxleyJWeight, unitCutoff, not_le.mpr hy1']
    exact continuousAt_const.congr_of_eventuallyEq heq

/-- Literal Mellin inversion of Huxley's rational kernel on the line
`Re w=2`, in the normalization used in (2.5). -/
theorem mellinInv_huxleyJ_eq_weight {x : ℝ} (hx : 0 < x) :
    mellinInv 2 MAPHuxleyReflectionKernelAlgebra.huxleyJ x =
      huxleyJWeight x := by
  calc
    mellinInv 2 MAPHuxleyReflectionKernelAlgebra.huxleyJ x =
        mellinInv 2 (mellin huxleyJWeight) x := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by
        exact congrArg
          (fun z : ℂ => (x : ℂ) ^ (-((2 : ℂ) + t * I)) • z)
          (mellin_huxleyJWeight_eq
            (s := (2 : ℂ) + t * I) (by simp)).symm)
    _ = huxleyJWeight x :=
      mellinInv_mellin_eq 2 huxleyJWeight hx
        (mellinConvergent_huxleyJWeight (by norm_num))
        verticalIntegrable_mellin_huxleyJWeight
        (continuousAt_huxleyJWeight hx)

/-- The real cosine presentation printed on the right side of Huxley (2.5). -/
def huxleyJSourceWeight (x : ℝ) : ℂ :=
  if x ≤ 1 then ((1 / 2 : ℝ) *
    (1 - Real.cos (Real.pi * Real.log x)) : ℝ) else 0

private theorem imaginary_cpow_add (x : ℝ) (hx : 0 < x) :
    (x : ℂ) ^ p + (x : ℂ) ^ n =
      (2 * Real.cos (Real.pi * Real.log x) : ℝ) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hp : (x : ℂ) ^ p =
      Complex.exp (((Real.pi * Real.log x : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le]
    unfold p
    congr 1
    push_cast
    ring
  have hn : (x : ℂ) ^ n =
      Complex.exp (-(((Real.pi * Real.log x : ℝ) : ℂ) * I)) := by
    rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le]
    unfold n
    congr 1
    push_cast
    ring
  rw [hp, hn]
  push_cast
  unfold Complex.cos
  ring

/-- The exponential and cosine presentations of (2.5) agree at every
positive argument, including the closed endpoint `x=1`. -/
theorem huxleyJWeight_eq_source {x : ℝ} (hx : 0 < x) :
    huxleyJWeight x = huxleyJSourceWeight x := by
  by_cases hx1 : x ≤ 1
  · have htrig := imaginary_cpow_add x hx
    have hcut : unitCutoff x = 1 := by simp [unitCutoff, hx, hx1]
    rw [huxleyJWeight, huxleyJSourceWeight, hcut, if_pos hx1]
    simp only [mul_one]
    calc
      (1 / 2 : ℂ) - (1 / 4 : ℂ) * (x : ℂ) ^ p -
          (1 / 4 : ℂ) * (x : ℂ) ^ n =
        (1 / 2 : ℂ) - (1 / 4 : ℂ) *
          ((x : ℂ) ^ p + (x : ℂ) ^ n) := by ring
      _ = ((1 / 2 : ℝ) *
          (1 - Real.cos (Real.pi * Real.log x)) : ℝ) := by
        rw [htrig]
        push_cast
        ring
  · unfold huxleyJWeight huxleyJSourceWeight
    simp [unitCutoff, hx, hx1]

/-- Huxley (2.5), now in its literal piecewise-cosine form. -/
theorem mellinInv_huxleyJ_eq_sourceWeight {x : ℝ} (hx : 0 < x) :
    mellinInv 2 MAPHuxleyReflectionKernelAlgebra.huxleyJ x =
      huxleyJSourceWeight x :=
  (mellinInv_huxleyJ_eq_weight hx).trans (huxleyJWeight_eq_source hx)

/-- Expanded real-line parametrization of the upward contour in Huxley
(2.5).  The source factor `1/(2*pi*i)` becomes `1/(2*pi)` because
`dw = i dt`. -/
theorem inverseMellin_integral_huxleyJ {x : ℝ} (hx : 0 < x) :
    (1 / (2 * Real.pi)) •
        ∫ t : ℝ, (x : ℂ) ^ (-((2 : ℂ) + t * I)) •
          MAPHuxleyReflectionKernelAlgebra.huxleyJ ((2 : ℂ) + t * I) =
      huxleyJSourceWeight x := by
  simpa only [mellinInv, Complex.ofReal_ofNat] using mellinInv_huxleyJ_eq_sourceWeight hx

end

end MAPHuxleyJMellin

#print axioms MAPHuxleyJMellin.mellin_unitCutoff_eq
#print axioms MAPHuxleyJMellin.mellinConvergent_unitCutoff
#print axioms MAPHuxleyJMellin.mellin_huxleyJWeight_eq
#print axioms MAPHuxleyJMellin.continuousAt_huxleyJWeight
#print axioms MAPHuxleyJMellin.mellinInv_huxleyJ_eq_weight
#print axioms MAPHuxleyJMellin.huxleyJWeight_eq_source
#print axioms MAPHuxleyJMellin.mellinInv_huxleyJ_eq_sourceWeight
#print axioms MAPHuxleyJMellin.inverseMellin_integral_huxleyJ
