import GuthMaynardLemma295ThetaBounds
import GuthMaynardLemma295MellinAllLines
import JutilaDualTailPSeries

/-!
# The reflected Riemann-zeta tail in Lemma 29.5

This is the literal coefficient-one tail after retaining the first `K`
positive integers in the reflected Dirichlet series.  The bound keeps the
real exponent needed on the deep-left line.
-/

namespace GuthMaynardLemma295DualTail

open Complex Real
open JutilaDualTailPSeries
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295ThetaBounds
open GuthMaynardLemma295MellinAllLines

noncomputable section

def sourceDualPartialNat (K : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range K, 1 / ((n + 1 : ℕ) : ℂ) ^ (1 - z)

def sourceDualTailNat (K : ℕ) (z : ℂ) : ℂ :=
  riemannZeta (1 - z) - sourceDualPartialNat K z

theorem criticalDualTerm_eq_reflectedPhase
    {m : ℕ} (hm : 0 < m) (tau : ℝ) :
    1 / (m : ℂ) ^ (1 - (((1 / 2 : ℝ) : ℂ) - tau * I)) =
      (Real.rpow (m : ℝ) (-(1 / 2 : ℝ)) : ℂ) *
        GuthMaynardHeathBrownMajorant.dirichletPhase m (-tau) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hm.ne')]
  rw [div_eq_mul_inv, one_mul, ← Complex.exp_neg]
  unfold GuthMaynardHeathBrownMajorant.dirichletPhase
  have hrpow : (Real.rpow (m : ℝ) (-(1 / 2 : ℝ)) : ℂ) =
      Complex.exp (((-(1 / 2 : ℝ)) * Real.log m : ℝ) : ℂ) := by
    have hr := Real.rpow_def_of_pos hmR (-(1 / 2 : ℝ))
    calc
      (Real.rpow (m : ℝ) (-(1 / 2 : ℝ)) : ℂ) =
          (Real.exp (Real.log m * (-(1 / 2 : ℝ))) : ℂ) :=
        congrArg (fun x : ℝ => (x : ℂ)) hr
      _ = Complex.exp ((Real.log m * (-(1 / 2 : ℝ)) : ℝ) : ℂ) :=
        Complex.ofReal_exp _
      _ = Complex.exp (((-(1 / 2 : ℝ)) * Real.log m : ℝ) : ℂ) := by
        congr 1
        push_cast
        ring
  rw [hrpow, ← Complex.exp_add]
  congr 1
  rw [← Complex.natCast_log]
  push_cast
  ring

private theorem sum_Icc_one_eq_sum_range_succ_complex
    (f : ℕ → ℂ) (K : ℕ) :
    (∑ m ∈ Finset.Icc 1 K, f m) =
      ∑ n ∈ Finset.range K, f (n + 1) := by
  have hset : Finset.Icc 1 K =
      (Finset.range K).image (fun n => n + 1) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hm, hmK⟩
      refine ⟨m - 1, by omega, by omega⟩
    · rintro ⟨n, hn, rfl⟩
      omega
  rw [hset]
  have hinj : Function.Injective (fun n : ℕ => n + 1) := by
    intro a b hab
    exact Nat.add_right_cancel hab
  exact Finset.sum_image (f := f) (s := Finset.range K)
    (g := fun n => n + 1) hinj.injOn

/-- The finite reflected zeta prefix is exactly the source polynomial, with
the conjugate phase orientation forced by `zeta(1-z)`. -/
theorem sourceDualPartialNat_critical_eq_reflectedPolynomial_neg
    (K : ℕ) (tau : ℝ) :
    sourceDualPartialNat K (((1 / 2 : ℝ) : ℂ) - tau * I) =
      GuthMaynardJutilaReflection2941.lemma295ReflectedPolynomial K (-tau) := by
  let f : ℕ → ℂ := fun m =>
    (Real.rpow (m : ℝ) (-(1 / 2 : ℝ)) : ℂ) *
      GuthMaynardHeathBrownMajorant.dirichletPhase m (-tau)
  have hsupport : GuthMaynardJutilaTransference.natRealIoc 0 (K : ℝ) =
      Finset.Icc 1 K := by
    ext m
    rw [GuthMaynardJutilaTransference.mem_natRealIoc_iff
      (by positivity : (0 : ℝ) ≤ K)]
    simp only [Finset.mem_Icc]
    constructor
    · intro h
      constructor
      · exact_mod_cast h.1
      · exact_mod_cast h.2
    · intro h
      constructor
      · exact_mod_cast (Nat.zero_lt_of_lt h.1)
      · exact_mod_cast h.2
  unfold sourceDualPartialNat
  rw [show GuthMaynardJutilaReflection2941.lemma295ReflectedPolynomial K (-tau) =
      ∑ m ∈ Finset.Icc 1 K, f m by
    unfold GuthMaynardJutilaReflection2941.lemma295ReflectedPolynomial
    rw [hsupport]]
  rw [sum_Icc_one_eq_sum_range_succ_complex]
  apply Finset.sum_congr rfl
  intro n hn
  exact criticalDualTerm_eq_reflectedPhase (by omega) tau

private theorem summable_sourceDualSeries {z : ℂ} (hz : z.re < 0) :
    Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ (1 - z)) := by
  rw [← summable_norm_iff]
  have hreal := (Real.summable_one_div_nat_add_rpow 1 (1 - z.re)).2
    (by linarith)
  apply hreal.congr
  intro n
  have hn : 0 < n + 1 := by omega
  rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hn]
  simp only [Complex.sub_re, Complex.one_re, Nat.cast_add, Nat.cast_one]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]

/-- Exact tail as a shifted absolutely convergent series. -/
theorem sourceDualTailNat_eq_shifted_tsum
    {z : ℂ} (hz : z.re < 0) (K : ℕ) :
    sourceDualTailNat K z =
      ∑' n : ℕ, 1 / ((n + K + 1 : ℕ) : ℂ) ^ (1 - z) := by
  have hzeta := zeta_eq_tsum_one_div_nat_add_one_cpow
    (s := 1 - z) (by simp; linarith)
  have hs := summable_sourceDualSeries hz
  have hsplit := hs.sum_add_tsum_nat_add K
  unfold sourceDualTailNat sourceDualPartialNat
  rw [hzeta]
  simp only [Nat.cast_add, Nat.cast_one] at hsplit ⊢
  rw [← hsplit]
  ring

/-- Quantitative real-power tail used on the deep-left contour. -/
theorem norm_sourceDualTailNat_le
    {z : ℂ} (hz : z.re < 0) (K : ℕ) :
    ‖sourceDualTailNat K z‖ ≤
      (K + 1 : ℝ) ^ (z.re - 1) +
        (K + 1 : ℝ) ^ z.re / (-z.re) := by
  rw [sourceDualTailNat_eq_shifted_tsum hz]
  let f : ℕ → ℂ := fun n =>
    1 / ((n + K + 1 : ℕ) : ℂ) ^ (1 - z)
  let F : ℕ → ℝ := fun n => ((K + 1 + n : ℕ) : ℝ) ^ (z.re - 1)
  have hf : Summable f := by
    have hs := summable_sourceDualSeries hz
    simpa [f, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (summable_nat_add_iff K).2 hs
  have hF : Summable F := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (z.re - 1)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    rw [show F = fun n : ℕ => ((n + (K + 1) : ℕ) : ℝ) ^ (z.re - 1) by
      funext n
      simp [F, Nat.add_comm]]
    exact (summable_nat_add_iff (K + 1)).2 hbase
  have hpoint : ∀ n, ‖f n‖ = F n := by
    intro n
    have hn : 0 < n + K + 1 := by omega
    unfold f F
    rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hn]
    simp only [Complex.sub_re, Complex.one_re]
    rw [show z.re - 1 = -(1 - z.re) by ring]
    have hbase : ((n + K + 1 : ℕ) : ℝ) = ((K + 1 + n : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hbase]
    simpa only [one_div] using
      (Real.rpow_neg (x := ((K + 1 + n : ℕ) : ℝ))
        (by positivity) (1 - z.re)).symm
  calc
    ‖∑' n : ℕ, 1 / ((n + K + 1 : ℕ) : ℂ) ^ (1 - z)‖ =
        ‖∑' n : ℕ, f n‖ := rfl
    _ ≤ ∑' n : ℕ, ‖f n‖ := norm_tsum_le_tsum_norm hf.norm
    _ = ∑' n : ℕ, F n := tsum_congr hpoint
    _ ≤ (K + 1 : ℝ) ^ (z.re - 1) +
        (K + 1 : ℝ) ^ z.re / (-z.re) := by
      have h := tsum_real_rpow_nat_add_le
        (M := K + 1) (a := 1 - z.re) (by omega) (by linarith)
      simpa only [F, show -(1 - z.re) = z.re - 1 by ring,
        show 1 - (1 - z.re) = z.re by ring,
        show (1 - z.re) - 1 = -z.re by ring,
        Nat.cast_add, Nat.cast_one, Nat.add_comm] using h

def deepLeftSigma (n : ℕ) : ℝ := -(1 / 2 : ℝ) - 2 * n

def lemma295DeepLeftTailIntegrand
    (N g : ℝ) (K n : ℕ) (t : ℝ) : ℂ :=
  let s : ℂ := (deepLeftSigma n : ℝ) + t * I
  let z : ℂ := s - g * I
  sourceZetaTheta z * sourceDualTailNat K z *
    (N : ℂ) ^ (s - g * I) * mellin sourceHZero s

/-- Fully quantitative pointwise bound for the discarded reflected zeta
tail on the source deep-left line `Re s=-1/2-2n`. -/
theorem norm_lemma295DeepLeftTailIntegrand_le
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K n : ℕ) {t : ℝ}
    (htg : t ≠ g) (him : 2 ≤ |t - g|) :
    ‖lemma295DeepLeftTailIntegrand N g K n t‖ ≤
      (((1 + ‖((deepLeftSigma n : ℂ) + (t - g) * I)‖ + 2 * n) ^ 2) ^ n *
        (1152 * (1 + |t - g|) ^ 5)) *
      ((K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
        (K + 1 : ℝ) ^ (deepLeftSigma n) / (-deepLeftSigma n)) *
      (Real.rpow N (deepLeftSigma n) *
        (sourceMellinDecayConstant (deepLeftSigma n) / (1 + t ^ 2))) := by
  let s : ℂ := (deepLeftSigma n : ℝ) + t * I
  let z : ℂ := s - g * I
  have hzform : z = (deepLeftSigma n : ℂ) + (t - g) * I := by
    dsimp [z, s]
    ring
  have hzre : z.re = deepLeftSigma n := by simp [z, s]
  have hzim : z.im = t - g := by simp [z, s]
  have hzneg : z.re < 0 := by
    rw [hzre]
    unfold deepLeftSigma
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hzne : z.im ≠ 0 := by
    rw [hzim]
    exact sub_ne_zero.mpr htg
  have hshiftLo : -2 ≤ (JutilaMultiplierRecurrence.shiftTwo z n).re := by
    simp [JutilaMultiplierRecurrence.shiftTwo, hzre, deepLeftSigma]
    norm_num
  have hshiftHi : (JutilaMultiplierRecurrence.shiftTwo z n).re ≤ 0 := by
    simp [JutilaMultiplierRecurrence.shiftTwo, hzre, deepLeftSigma]
  have htheta := norm_sourceZetaTheta_deepLeft_le hzne
    (by simpa [hzim] using him) n hshiftLo hshiftHi
  rw [hzform] at htheta
  have htheta' :
      ‖sourceZetaTheta z‖ ≤
        ((1 + ‖((deepLeftSigma n : ℂ) + (t - g) * I)‖ + 2 * n) ^ 2) ^ n *
          (1152 * (1 + |t - g|) ^ 5) := by
    simpa [hzform] using htheta
  have htail := norm_sourceDualTailNat_le hzneg K
  rw [hzre] at htail
  have hscale : ‖(N : ℂ) ^ (s - g * I)‖ = Real.rpow N (deepLeftSigma n) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN]
    simp [s, deepLeftSigma]
  have hmellin := norm_mellin_sourceHZero_vertical_le_inv_one_add_sq
    (deepLeftSigma n) t
  unfold lemma295DeepLeftTailIntegrand
  dsimp only
  repeat' rw [norm_mul]
  rw [hscale]
  have htailNonneg : 0 ≤
      (K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
        (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n) :=
    (norm_nonneg _).trans htail
  have hthetaNonneg : 0 ≤
      ((1 + ‖((deepLeftSigma n : ℂ) + (t - g) * I)‖ + 2 * n) ^ 2) ^ n *
        (1152 * (1 + |t - g|) ^ 5) := (norm_nonneg _).trans htheta'
  have hscaleNonneg : 0 ≤ Real.rpow N (deepLeftSigma n) :=
    Real.rpow_nonneg hN.le _
  calc
    ‖sourceZetaTheta z‖ * ‖sourceDualTailNat K z‖ *
        Real.rpow N (deepLeftSigma n) * ‖mellin sourceHZero s‖ ≤
      (((1 + ‖((deepLeftSigma n : ℂ) + (t - g) * I)‖ + 2 * n) ^ 2) ^ n *
        (1152 * (1 + |t - g|) ^ 5)) *
      ((K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
        (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n)) *
      Real.rpow N (deepLeftSigma n) * ‖mellin sourceHZero s‖ := by
        gcongr
    _ ≤ (((1 + ‖((deepLeftSigma n : ℂ) + (t - g) * I)‖ + 2 * n) ^ 2) ^ n *
        (1152 * (1 + |t - g|) ^ 5)) *
      ((K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
        (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n)) *
      (Real.rpow N (deepLeftSigma n) *
        (sourceMellinDecayConstant (deepLeftSigma n) / (1 + t ^ 2))) := by
      rw [mul_assoc]
      gcongr

end
end GuthMaynardLemma295DualTail

#print axioms GuthMaynardLemma295DualTail.sourceDualTailNat_eq_shifted_tsum
#print axioms GuthMaynardLemma295DualTail.criticalDualTerm_eq_reflectedPhase
#print axioms GuthMaynardLemma295DualTail.sourceDualPartialNat_critical_eq_reflectedPolynomial_neg
#print axioms GuthMaynardLemma295DualTail.norm_sourceDualTailNat_le
#print axioms GuthMaynardLemma295DualTail.norm_lemma295DeepLeftTailIntegrand_le
