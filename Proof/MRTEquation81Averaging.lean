import MRTEquation81Schur
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The averaging step in MRT equation (81)

This file formalizes the translation-invariant box averaging used between the
pointwise packet kernel (82) and Schur's test.  The radius is the manuscript's
literal `R = |β|H`; no enlargement of the frequency or half-range hypotheses is
hidden here.
-/

namespace MAPMRTEquation81Averaging

open MeasureTheory Set
open MAPMRTEquation81Kernel

noncomputable section

/-- The unnormalized symmetric moving integral printed immediately after (82). -/
def symmetricMovingIntegral (R : ℝ) (F : ℝ → ENNReal) (x : ℝ) : ENNReal :=
  ∫⁻ u in Icc (x - R) (x + R), F u

/-- Moving either endpoint by at most `R` costs at most the literal factor `9`
for the equation-(81) Cauchy-decay kernel. -/
theorem equation81Kernel_le_nine_of_mem_boxes
    {R u v x y : ℝ} (hR : 0 < R)
    (hx : x ∈ Icc (u - R) (u + R))
    (hy : y ∈ Icc (v - R) (v + R)) :
    equation81Kernel R u v ≤ 9 * equation81Kernel R x y := by
  have hxu : |x - u| ≤ R := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hyv : |y - v| ≤ R := by
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2]
  have hxy : |x - y| ≤ |u - v| + 2 * R := by
    calc
      |x - y| = |(x - u) + (u - v) + (v - y)| := by congr 1 <;> ring
      _ ≤ |x - u| + |u - v| + |v - y| := abs_add_three _ _ _
      _ ≤ R + |u - v| + R := by
        have hvy : |v - y| ≤ R := by simpa [abs_sub_comm] using hyv
        gcongr
      _ = |u - v| + 2 * R := by ring
  let a : ℝ := |u - v| / R
  let b : ℝ := |x - y| / R
  have ha : 0 ≤ a := by unfold a; positivity
  have hb : 0 ≤ b := by unfold b; positivity
  have hab : b ≤ a + 2 := by
    unfold a b
    rw [div_le_iff₀ hR]
    calc
      |x - y| ≤ |u - v| + 2 * R := hxy
      _ = (|u - v| / R + 2) * R := by field_simp
  have hden : (1 + b) ^ 2 ≤ 9 * (1 + a) ^ 2 := by
    have hlin : 1 + b ≤ 3 * (1 + a) := by nlinarith
    nlinarith [sq_nonneg ((1 + b) - 3 * (1 + a))]
  have hapos : 0 < (1 + a) ^ 2 := by positivity
  have hbpos : 0 < (1 + b) ^ 2 := by positivity
  unfold equation81Kernel
  rw [show |u - v| / R = a by rfl, show |x - y| / R = b by rfl]
  apply (div_le_iff₀ hapos).2
  have hrearrange : 9 * (1 / (1 + b) ^ 2) * (1 + a) ^ 2 =
      (9 * (1 + a) ^ 2) / (1 + b) ^ 2 := by ring
  rw [hrearrange]
  exact (le_div_iff₀ hbpos).2 (by simpa using hden)

/-- The averaged kernel over the two manuscript windows retains at least
`1/9` of its value at the two window centers.  This is the exact geometric
ingredient behind the prefactor `(|β|H)⁻²` in (81). -/
theorem box_lintegral_kernel_lower
    {R u v : ℝ} (hR : 0 < R) :
    (ENNReal.ofReal (2 * R)) ^ 2 *
        ENNReal.ofReal (equation81Kernel R u v) ≤
      9 * (∫⁻ x in Icc (u - R) (u + R),
        ∫⁻ y in Icc (v - R) (v + R),
          ENNReal.ofReal (equation81Kernel R x y)) := by
  have hpoint (x : ℝ) (hx : x ∈ Icc (u - R) (u + R))
      (y : ℝ) (hy : y ∈ Icc (v - R) (v + R)) :
      ENNReal.ofReal (equation81Kernel R u v) ≤
        9 * ENNReal.ofReal (equation81Kernel R x y) := by
    calc
      ENNReal.ofReal (equation81Kernel R u v) ≤
          ENNReal.ofReal (9 * equation81Kernel R x y) :=
        ENNReal.ofReal_le_ofReal
          (equation81Kernel_le_nine_of_mem_boxes hR hx hy)
      _ = 9 * ENNReal.ofReal (equation81Kernel R x y) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9)]
        norm_num
  have hmono :
      (∫⁻ x in Icc (u - R) (u + R),
        ∫⁻ y in Icc (v - R) (v + R),
          ENNReal.ofReal (equation81Kernel R u v)) ≤
      (∫⁻ x in Icc (u - R) (u + R),
        ∫⁻ y in Icc (v - R) (v + R),
          9 * ENNReal.ofReal (equation81Kernel R x y)) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact hpoint x hx y hy
  have hleft :
      (∫⁻ x in Icc (u - R) (u + R),
        ∫⁻ y in Icc (v - R) (v + R),
          ENNReal.ofReal (equation81Kernel R u v)) =
      (ENNReal.ofReal (2 * R)) ^ 2 *
        ENNReal.ofReal (equation81Kernel R u v) := by
    simp only [setLIntegral_const, Real.volume_Icc]
    rw [show u + R - (u - R) = 2 * R by ring,
      show v + R - (v - R) = 2 * R by ring]
    ring
  have hright :
      (∫⁻ x in Icc (u - R) (u + R),
        ∫⁻ y in Icc (v - R) (v + R),
          9 * ENNReal.ofReal (equation81Kernel R x y)) =
      9 * (∫⁻ x in Icc (u - R) (u + R),
        ∫⁻ y in Icc (v - R) (v + R),
          ENNReal.ofReal (equation81Kernel R x y)) := by
    have hinner : (fun x : ℝ ↦
        ∫⁻ y in Icc (v - R) (v + R),
          9 * ENNReal.ofReal (equation81Kernel R x y)) =
        fun x : ℝ ↦ 9 *
          (∫⁻ y in Icc (v - R) (v + R),
            ENNReal.ofReal (equation81Kernel R x y)) := by
      funext x
      exact lintegral_const_mul' 9 _ (by norm_num)
    rw [hinner]
    exact lintegral_const_mul' 9 _ (by norm_num)
  rw [hleft, hright] at hmono
  exact hmono

#print axioms equation81Kernel_le_nine_of_mem_boxes
#print axioms box_lintegral_kernel_lower

end
end MAPMRTEquation81Averaging
