import RieszKernelBoundary
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exact Mellin inversion for compact Riesz weights

This file connects the finite rational kernel in `RieszKernelBoundary` to
mathlib's Mellin inversion convention.  No analytic assertion is introduced as
an axiom.
-/

namespace MAPAppendixA4RieszInversion

open Complex Real Set MeasureTheory
open scoped Topology

noncomputable section

/-- The compact order-`k` Riesz weight, written with a positive part so it is
continuous at the cutoff when `k ≥ 1`. -/
def rieszWeight (k : ℕ) (x : ℝ) : ℂ :=
  (((max (1 - x) 0) ^ k : ℝ) : ℂ)

/-- The Riesz weight is continuous (the `k = 0` convention is also continuous
for this positive-part presentation, though it no longer represents an
indicator at the endpoint). -/
theorem continuous_rieszWeight (k : ℕ) : Continuous (rieszWeight k) := by
  unfold rieszWeight
  fun_prop

@[simp] theorem rieszWeight_eq_pow_of_le_one
    (k : ℕ) {x : ℝ} (hx : x ≤ 1) :
    rieszWeight k x = ((1 - x : ℝ) : ℂ) ^ k := by
  simp [rieszWeight, max_eq_left (sub_nonneg.mpr hx), Complex.ofReal_pow]

@[simp] theorem rieszWeight_eq_zero_of_one_le
    (k : ℕ) (hk : 1 ≤ k) {x : ℝ} (hx : 1 ≤ x) :
    rieszWeight k x = 0 := by
  have hk0 : k ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk)
  simp [rieszWeight, max_eq_right (sub_nonpos.mpr hx), hk0]

private lemma indicator_mellin_integrand_eq
    (k : ℕ) (hk : 1 ≤ k) (s : ℂ) (x : ℝ) :
    (Ioi (0 : ℝ)).indicator
        (fun x : ℝ => (x : ℂ) ^ (s - 1) • rieszWeight k x) x =
      (Ioc (0 : ℝ) 1).indicator
        (fun x : ℝ => (x : ℂ) ^ (s - 1) *
          (1 - (x : ℂ)) ^ k) x := by
  by_cases hx0 : 0 < x
  · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx0)]
    by_cases hx1 : x ≤ 1
    · rw [indicator_of_mem (show x ∈ Ioc (0 : ℝ) 1 from ⟨hx0, hx1⟩)]
      simp only [rieszWeight, max_eq_left (sub_nonneg.mpr hx1), smul_eq_mul,
        Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Complex.cpow_natCast,
        Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one]
    · rw [indicator_of_notMem (by simp [hx0, hx1])]
      have hk0 : k ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk)
      simp [rieszWeight, max_eq_right (sub_nonpos.mpr (le_of_not_ge hx1)), hk0]
  · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) by simpa using hx0)]
    rw [indicator_of_notMem (show x ∉ Ioc (0 : ℝ) 1 by
      intro h; exact hx0 h.1)]

/-- The defining Mellin integral of the compact Riesz weight is the Beta
integral. -/
theorem mellin_rieszWeight_eq_betaIntegral
    (k : ℕ) (hk : 1 ≤ k) (s : ℂ) :
    mellin (rieszWeight k) s = Complex.betaIntegral s (k + 1) := by
  rw [mellin, ← integral_indicator measurableSet_Ioi]
  rw [Complex.betaIntegral]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Complex.cpow_natCast]
  rw [intervalIntegral.integral_of_le zero_le_one,
    ← integral_indicator measurableSet_Ioc]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (indicator_mellin_integrand_eq k hk s))

/-- Exact Mellin transform: `k! / (s(s+1)...(s+k))`. -/
theorem mellin_rieszWeight_eq_kernel
    (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re) :
    mellin (rieszWeight k) s =
      MAPAppendixA4RieszKernel.rieszMellinKernel k s := by
  rw [mellin_rieszWeight_eq_betaIntegral k hk]
  exact MAPAppendixA4RieszKernel.betaIntegral_eq_rieszMellinKernel hs k

/-- Absolute convergence of the defining Mellin transform on every right
half-plane. -/
theorem mellinConvergent_rieszWeight
    (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (rieszWeight k) s := by
  rw [MellinConvergent, ← integrable_indicator_iff measurableSet_Ioi]
  rw [show (Ioi (0 : ℝ)).indicator
        (fun x : ℝ => (x : ℂ) ^ (s - 1) • rieszWeight k x) =
      (Ioc (0 : ℝ) 1).indicator
        (fun x : ℝ => (x : ℂ) ^ (s - 1) *
          (1 - (x : ℂ)) ^ k) by
        funext x; exact indicator_mellin_integrand_eq k hk s x]
  rw [integrable_indicator_iff measurableSet_Ioc]
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Complex.cpow_natCast] using
    (Complex.betaIntegral_convergent hs (by simp; positivity :
      0 < (((k + 1 : ℕ) : ℂ)).re))



/-- The rational kernel is continuous on a positive vertical line. -/
theorem continuous_rieszKernel_vertical
    (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Continuous (fun t : ℝ =>
      MAPAppendixA4RieszKernel.rieszMellinKernel k ((c : ℂ) + t * I)) := by
  unfold MAPAppendixA4RieszKernel.rieszMellinKernel
  apply Continuous.div continuous_const
  · apply continuous_finset_prod
    intro j hj
    fun_prop
  · intro t
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    apply Complex.ne_zero_of_re_pos
    simp
    positivity

/-- A global `L¹` majorant for the rational kernel on a positive vertical
line.  The constant is deliberately coarse; the key point is the certified
`(1+t²)⁻¹` decay, uniform in `t`. -/
theorem norm_rieszMellinKernel_vertical_le
    (k : ℕ) (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖MAPAppendixA4RieszKernel.rieszMellinKernel k ((c : ℂ) + t * I)‖ ≤
      (2 * (((2 : ℝ) ^ k / c) + (k.factorial : ℝ))) * (1 + t ^ 2)⁻¹ := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hzre :
      c ≤ ‖(c : ℂ) + t * I‖ := by
    have h := Complex.abs_re_le_norm ((c : ℂ) + t * I)
    simpa [abs_of_pos hc] using h
  have hzpos : 0 < ‖(c : ℂ) + t * I‖ :=
    lt_of_lt_of_le hc hzre
  rw [MAPAppendixA4RieszKernel.rieszMellinKernel_eq_div_regularized,
    norm_div]
  by_cases ht : |t| ≤ 1
  · have hreg := MAPAppendixA4RieszKernel.norm_regularizedRieszKernel_le_two_pow
        k c t (by linarith : -(1 : ℝ) / 2 ≤ c)
    have hraw :
        ‖MAPAppendixA4RieszKernel.regularizedRieszKernel k ((c : ℂ) + t * I)‖ /
            ‖(c : ℂ) + t * I‖ ≤ (2 : ℝ) ^ k / c := by
      exact div_le_div₀ (by positivity) hreg hc hzre
    calc
      ‖MAPAppendixA4RieszKernel.regularizedRieszKernel k ((c : ℂ) + t * I)‖ /
          ‖(c : ℂ) + t * I‖
          ≤ (2 : ℝ) ^ k / c := hraw
      _ ≤ (2 * (((2 : ℝ) ^ k / c) + (k.factorial : ℝ))) *
            (1 + t ^ 2)⁻¹ := by
        rw [inv_eq_one_div, mul_one_div]
        apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).2
        have ht2abs : |t| ^ 2 ≤ (1 : ℝ) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg t) ht 2
        have ht2 : t ^ 2 ≤ 1 := by simpa [sq_abs] using ht2abs
        have hnon : 0 ≤ (2 : ℝ) ^ k / c := by positivity
        have hfac : 0 ≤ (k.factorial : ℝ) := by positivity
        nlinarith
  · have htgt : 1 < |t| := lt_of_not_ge ht
    have habspos : 0 < |t| := lt_trans zero_lt_one htgt
    have ht0 : t ≠ 0 := abs_ne_zero.mp (ne_of_gt habspos)
    have him : |t| ≤ ‖(c : ℂ) + t * I‖ := by
      simpa using Complex.abs_im_le_norm ((c : ℂ) + t * I)
    have hreg := MAPAppendixA4RieszKernel.norm_regularizedRieszKernel_le
      k c t ht0
    have hraw :
        ‖MAPAppendixA4RieszKernel.regularizedRieszKernel k ((c : ℂ) + t * I)‖ /
            ‖(c : ℂ) + t * I‖ ≤
          (k.factorial : ℝ) / |t| ^ (k + 1) := by
      calc
        ‖MAPAppendixA4RieszKernel.regularizedRieszKernel k ((c : ℂ) + t * I)‖ /
            ‖(c : ℂ) + t * I‖
            ≤ ((k.factorial : ℝ) / |t| ^ k) / |t| := by
              exact div_le_div₀ (by positivity) hreg habspos him
        _ = (k.factorial : ℝ) / |t| ^ (k + 1) := by
              rw [pow_succ]
              field_simp
    have hpow : |t| ^ 2 ≤ |t| ^ (k + 1) := by
      apply pow_le_pow_right₀ (le_of_lt htgt)
      omega
    have hraw2 :
        (k.factorial : ℝ) / |t| ^ (k + 1) ≤
          (k.factorial : ℝ) / |t| ^ 2 := by
      exact div_le_div_of_nonneg_left (by positivity)
        (pow_pos habspos 2) hpow
    calc
      ‖MAPAppendixA4RieszKernel.regularizedRieszKernel k ((c : ℂ) + t * I)‖ /
          ‖(c : ℂ) + t * I‖
          ≤ (k.factorial : ℝ) / |t| ^ (k + 1) := hraw
      _ ≤ (k.factorial : ℝ) / |t| ^ 2 := hraw2
      _ ≤ (2 * (((2 : ℝ) ^ k / c) + (k.factorial : ℝ))) *
            (1 + t ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv]
        have habssq : |t| ^ 2 = t ^ 2 := sq_abs t
        rw [habssq]
        have ht2 : 1 < t ^ 2 := by
          nlinarith [sq_abs t, sq_nonneg t]
        apply (div_le_div_iff₀ (by positivity : 0 < t ^ 2)
          (by positivity : 0 < 1 + t ^ 2)).2
        have hnon : 0 ≤ (2 : ℝ) ^ k / c := by positivity
        have hfac : 0 ≤ (k.factorial : ℝ) := by positivity
        nlinarith

/-- The rational Mellin kernel is integrable on every positive vertical line
for every order `k ≥ 1`. -/
theorem verticalIntegrable_rieszMellinKernel
    (k : ℕ) (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    Complex.VerticalIntegrable
      (MAPAppendixA4RieszKernel.rieszMellinKernel k) c := by
  unfold Complex.VerticalIntegrable
  let C : ℝ := 2 * (((2 : ℝ) ^ k / c) + (k.factorial : ℝ))
  have hdom : Integrable (fun t : ℝ => C * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  apply hdom.mono'
  · exact (continuous_rieszKernel_vertical k hc).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      simpa [C] using norm_rieszMellinKernel_vertical_le k hk hc t)

/-- Vertical integrability of the actual Mellin transform, obtained by the
pointwise Beta/rational identity on the positive line. -/
theorem verticalIntegrable_mellin_rieszWeight
    (k : ℕ) (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    Complex.VerticalIntegrable (mellin (rieszWeight k)) c := by
  unfold Complex.VerticalIntegrable
  have hker := verticalIntegrable_rieszMellinKernel k hk hc
  unfold Complex.VerticalIntegrable at hker
  apply hker.congr
  exact Filter.Eventually.of_forall (fun t =>
    (mellin_rieszWeight_eq_kernel k hk (by simpa using hc :
      0 < ((c : ℂ) + t * I).re)).symm)

/-- **Exact inverse Mellin formula.**  In mathlib's convention the inverse is
`(1 / 2π) ∫_{t∈ℝ} x^{-(c+it)} K_k(c+it) dt`; there is no extra factor of `i`
because the vertical contour is parametrized by `s = c + it` and `ds = i dt`.
-/
theorem mellinInv_rieszKernel_eq_weight
    (k : ℕ) (hk : 1 ≤ k) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    mellinInv c (MAPAppendixA4RieszKernel.rieszMellinKernel k) x =
      rieszWeight k x := by
  calc
    mellinInv c (MAPAppendixA4RieszKernel.rieszMellinKernel k) x =
        mellinInv c (mellin (rieszWeight k)) x := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by
        change (x : ℂ) ^ (-(c + t * I)) •
            MAPAppendixA4RieszKernel.rieszMellinKernel k (c + t * I) =
          (x : ℂ) ^ (-(c + t * I)) • mellin (rieszWeight k) (c + t * I)
        congr 1
        exact (mellin_rieszWeight_eq_kernel k hk (by simpa using hc :
          0 < ((c : ℂ) + t * I).re)).symm)
    _ = rieszWeight k x :=
      mellinInv_mellin_eq c (rieszWeight k) hx
        (mellinConvergent_rieszWeight k hk (by simpa using hc))
        (verticalIntegrable_mellin_rieszWeight k hk hc)
        ((continuous_rieszWeight k).continuousAt)

/-- Literal interior form of the Riesz inversion formula. -/
theorem mellinInv_rieszKernel_eq_one_sub_pow
    (k : ℕ) (hk : 1 ≤ k) {c x : ℝ}
    (hc : 0 < c) (hx : 0 < x) (hx1 : x < 1) :
    mellinInv c (MAPAppendixA4RieszKernel.rieszMellinKernel k) x =
      ((1 - x : ℝ) : ℂ) ^ k := by
  rw [mellinInv_rieszKernel_eq_weight k hk hc hx,
    rieszWeight_eq_pow_of_le_one k hx1.le]

/-- Literal exterior form of the Riesz inversion formula. -/
theorem mellinInv_rieszKernel_eq_zero
    (k : ℕ) (hk : 1 ≤ k) {c x : ℝ}
    (hc : 0 < c) (hx : 0 < x) (hx1 : 1 ≤ x) :
    mellinInv c (MAPAppendixA4RieszKernel.rieszMellinKernel k) x = 0 := by
  rw [mellinInv_rieszKernel_eq_weight k hk hc hx,
    rieszWeight_eq_zero_of_one_le k hk hx1]

/-- Expanded real-line form, auditing the `1/(2π)` normalization and upward
vertical-line orientation. -/
theorem inverseMellin_integral_rieszKernel
    (k : ℕ) (hk : 1 ≤ k) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    (1 / (2 * Real.pi)) •
        ∫ t : ℝ, (x : ℂ) ^ (-(c + t * I)) •
          MAPAppendixA4RieszKernel.rieszMellinKernel k (c + t * I) =
      rieszWeight k x := by
  simpa only [mellinInv] using
    mellinInv_rieszKernel_eq_weight k hk hc hx


end

end MAPAppendixA4RieszInversion
