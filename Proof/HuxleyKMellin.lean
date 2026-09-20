import HuxleyJMellin

/-!
# The compact Mellin weight in Huxley 1973 (2.6)--(2.7)

This module reconstructs the inverse Mellin weight attached to
`K(w) = (exp (4w) + exp (3w) - exp w - 1) J(w)`.
The four exponential factors are literal positive dilations of the already
certified inverse Mellin weight for `J`.  No contour shift, functional
equation, or density estimate enters this source segment.
-/

namespace MAPHuxleyKMellin

open Complex Real Set MeasureTheory Filter
open scoped Topology

noncomputable section

private def dilation (k : ℝ) : ℝ := Real.exp (-k)

/-- The compact weight whose Mellin transform is Huxley's kernel `K`. -/
def huxleyKWeight (x : ℝ) : ℂ :=
  MAPHuxleyJMellin.huxleyJWeight (dilation 4 * x) +
    MAPHuxleyJMellin.huxleyJWeight (dilation 3 * x) -
    MAPHuxleyJMellin.huxleyJWeight (dilation 1 * x) -
    MAPHuxleyJMellin.huxleyJWeight x

private theorem dilation_pos (k : ℝ) : 0 < dilation k := by
  exact Real.exp_pos (-k)

private theorem cpow_dilation_neg (k : ℝ) (s : ℂ) :
    ((dilation k : ℝ) : ℂ) ^ (-s) = Complex.exp ((k : ℂ) * s) := by
  have hk : (dilation k : ℝ) ≠ 0 := (dilation_pos k).ne'
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hk)]
  rw [← Complex.ofReal_log (dilation_pos k).le]
  simp only [dilation, Real.log_exp]
  congr 1
  push_cast
  ring

private theorem mellin_scaledJWeight_eq (k : ℝ) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x : ℝ =>
        MAPHuxleyJMellin.huxleyJWeight (dilation k * x)) s =
      Complex.exp ((k : ℂ) * s) *
        MAPHuxleyReflectionKernelAlgebra.huxleyJ s := by
  rw [mellin_comp_mul_left MAPHuxleyJMellin.huxleyJWeight s (dilation_pos k)]
  rw [MAPHuxleyJMellin.mellin_huxleyJWeight_eq hs]
  simp only [smul_eq_mul, cpow_dilation_neg]

private theorem mellinConvergent_scaledJWeight (k : ℝ) {s : ℂ}
    (hs : 0 < s.re) :
    MellinConvergent (fun x : ℝ =>
      MAPHuxleyJMellin.huxleyJWeight (dilation k * x)) s := by
  rw [MellinConvergent.comp_mul_left (dilation_pos k)]
  exact MAPHuxleyJMellin.mellinConvergent_huxleyJWeight hs

/-- Exact transform identity for the compact kernel in (2.6). -/
theorem mellin_huxleyKWeight_eq {s : ℂ} (hs : 0 < s.re) :
    mellin huxleyKWeight s =
      MAPHuxleyReflectionKernelAlgebra.huxleyK s := by
  have h4c := mellinConvergent_scaledJWeight 4 hs
  have h3c := mellinConvergent_scaledJWeight 3 hs
  have h1c := mellinConvergent_scaledJWeight 1 hs
  have h0c := MAPHuxleyJMellin.mellinConvergent_huxleyJWeight hs
  have h43 := hasMellin_add h4c h3c
  have h431 := hasMellin_sub h43.1 h1c
  have h4310 := hasMellin_sub h431.1 h0c
  rw [show huxleyKWeight = (fun x : ℝ =>
      (MAPHuxleyJMellin.huxleyJWeight (dilation 4 * x) +
        MAPHuxleyJMellin.huxleyJWeight (dilation 3 * x) -
        MAPHuxleyJMellin.huxleyJWeight (dilation 1 * x)) -
        MAPHuxleyJMellin.huxleyJWeight x) by rfl]
  rw [h4310.2, h431.2, h43.2]
  rw [mellin_scaledJWeight_eq 4 hs, mellin_scaledJWeight_eq 3 hs,
    mellin_scaledJWeight_eq 1 hs,
    MAPHuxleyJMellin.mellin_huxleyJWeight_eq hs]
  unfold MAPHuxleyReflectionKernelAlgebra.huxleyK
    MAPHuxleyReflectionKernelAlgebra.huxleyKernelNumerator
  have h4 : Complex.exp ((4 : ℂ) * s) = Complex.exp (s * 4) := by
    congr 1 <;> ring
  have h3 : Complex.exp ((3 : ℂ) * s) = Complex.exp (s * 3) := by
    congr 1 <;> ring
  rw [h4, h3]
  norm_num
  ring

/-- Absolute convergence of the compact source weight. -/
theorem mellinConvergent_huxleyKWeight {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent huxleyKWeight s := by
  have h4c := mellinConvergent_scaledJWeight 4 hs
  have h3c := mellinConvergent_scaledJWeight 3 hs
  have h1c := mellinConvergent_scaledJWeight 1 hs
  have h0c := MAPHuxleyJMellin.mellinConvergent_huxleyJWeight hs
  unfold MellinConvergent huxleyKWeight
  simpa only [smul_add, smul_sub] using ((h4c.add h3c).sub h1c).sub h0c

/-- Pointwise continuity needed for literal Mellin inversion. -/
theorem continuousAt_huxleyKWeight {x : ℝ} (hx : 0 < x) :
    ContinuousAt huxleyKWeight x := by
  have hscaled (k : ℝ) :
      ContinuousAt
        (fun y : ℝ => MAPHuxleyJMellin.huxleyJWeight (dilation k * y)) x := by
    exact (MAPHuxleyJMellin.continuousAt_huxleyJWeight
      (mul_pos (dilation_pos k) hx)).comp
        (continuousAt_const.mul continuousAt_id)
  unfold huxleyKWeight
  exact (((hscaled 4).add (hscaled 3)).sub (hscaled 1)).sub
    (MAPHuxleyJMellin.continuousAt_huxleyJWeight hx)

private theorem norm_huxleyKernelNumerator_vertical_le (t : ℝ) :
    ‖MAPHuxleyReflectionKernelAlgebra.huxleyKernelNumerator
        ((2 : ℂ) + (t : ℂ) * I)‖ ≤
      Real.exp 8 + Real.exp 6 + Real.exp 2 + 1 := by
  unfold MAPHuxleyReflectionKernelAlgebra.huxleyKernelNumerator
  calc
    ‖Complex.exp (4 * ((2 : ℂ) + (t : ℂ) * I)) +
        Complex.exp (3 * ((2 : ℂ) + (t : ℂ) * I)) -
        Complex.exp ((2 : ℂ) + (t : ℂ) * I) - 1‖ ≤
      ‖Complex.exp (4 * ((2 : ℂ) + (t : ℂ) * I))‖ +
        ‖Complex.exp (3 * ((2 : ℂ) + (t : ℂ) * I))‖ +
        ‖Complex.exp ((2 : ℂ) + (t : ℂ) * I)‖ + ‖(1 : ℂ)‖ := by
          calc
            ‖Complex.exp (4 * ((2 : ℂ) + (t : ℂ) * I)) +
                Complex.exp (3 * ((2 : ℂ) + (t : ℂ) * I)) -
                Complex.exp ((2 : ℂ) + (t : ℂ) * I) - 1‖ ≤
              ‖Complex.exp (4 * ((2 : ℂ) + (t : ℂ) * I)) +
                Complex.exp (3 * ((2 : ℂ) + (t : ℂ) * I)) -
                Complex.exp ((2 : ℂ) + (t : ℂ) * I)‖ + ‖(1 : ℂ)‖ :=
                  norm_sub_le _ _
            _ ≤ (‖Complex.exp (4 * ((2 : ℂ) + (t : ℂ) * I)) +
                Complex.exp (3 * ((2 : ℂ) + (t : ℂ) * I))‖ +
                ‖Complex.exp ((2 : ℂ) + (t : ℂ) * I)‖) + ‖(1 : ℂ)‖ := by
                  gcongr
                  exact norm_sub_le _ _
            _ ≤ (‖Complex.exp (4 * ((2 : ℂ) + (t : ℂ) * I))‖ +
                ‖Complex.exp (3 * ((2 : ℂ) + (t : ℂ) * I))‖) +
                ‖Complex.exp ((2 : ℂ) + (t : ℂ) * I)‖ + ‖(1 : ℂ)‖ := by
                  gcongr
                  exact norm_add_le _ _
    _ = Real.exp 8 + Real.exp 6 + Real.exp 2 + 1 := by
      norm_num [Complex.norm_exp, Complex.mul_re]

/-- The full kernel `K` is vertically integrable on Huxley's source line. -/
theorem verticalIntegrable_huxleyK :
    Complex.VerticalIntegrable
      MAPHuxleyReflectionKernelAlgebra.huxleyK 2 := by
  unfold Complex.VerticalIntegrable
  have hJ := MAPHuxleyJVertical.verticalIntegrable_huxleyJ
  unfold Complex.VerticalIntegrable at hJ
  unfold MAPHuxleyReflectionKernelAlgebra.huxleyK
  apply hJ.bdd_mul
  · apply Continuous.aestronglyMeasurable
    unfold MAPHuxleyReflectionKernelAlgebra.huxleyKernelNumerator
    fun_prop
  · exact Filter.Eventually.of_forall norm_huxleyKernelNumerator_vertical_le

/-- The Mellin transform of the reconstructed compact weight is vertically
integrable, by its exact identification with `K`. -/
theorem verticalIntegrable_mellin_huxleyKWeight :
    Complex.VerticalIntegrable (mellin huxleyKWeight) 2 := by
  unfold Complex.VerticalIntegrable
  have hK := verticalIntegrable_huxleyK
  unfold Complex.VerticalIntegrable at hK
  apply hK.congr
  exact Filter.Eventually.of_forall (fun t =>
    (mellin_huxleyKWeight_eq (s := (2 : ℂ) + t * I) (by simp)).symm)

/-- Literal inverse Mellin formula for Huxley's entire kernel `K`. -/
theorem mellinInv_huxleyK_eq_weight {x : ℝ} (hx : 0 < x) :
    mellinInv 2 MAPHuxleyReflectionKernelAlgebra.huxleyK x =
      huxleyKWeight x := by
  calc
    mellinInv 2 MAPHuxleyReflectionKernelAlgebra.huxleyK x =
        mellinInv 2 (mellin huxleyKWeight) x := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by
        exact congrArg
          (fun z : ℂ => (x : ℂ) ^ (-((2 : ℂ) + t * I)) • z)
          (mellin_huxleyKWeight_eq
            (s := (2 : ℂ) + t * I) (by simp)).symm)
    _ = huxleyKWeight x :=
      mellinInv_mellin_eq 2 huxleyKWeight hx
        (mellinConvergent_huxleyKWeight (by norm_num))
        verticalIntegrable_mellin_huxleyKWeight
        (continuousAt_huxleyKWeight hx)

end

end MAPHuxleyKMellin

#print axioms MAPHuxleyKMellin.mellin_huxleyKWeight_eq
#print axioms MAPHuxleyKMellin.mellinConvergent_huxleyKWeight
#print axioms MAPHuxleyKMellin.continuousAt_huxleyKWeight
#print axioms MAPHuxleyKMellin.verticalIntegrable_huxleyK
#print axioms MAPHuxleyKMellin.mellinInv_huxleyK_eq_weight
