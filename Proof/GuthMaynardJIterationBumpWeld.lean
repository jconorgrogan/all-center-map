import GuthMaynardJIterationCanonicalSupremum
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open scoped BigOperators FourierTransform Real ContDiff SchwartzMap
open MeasureTheory Metric

noncomputable section
namespace GuthMaynardJIteration

/-!
# The concrete bump and negligible-tail weld in Guth--Maynard Lemma 9.2

This file supplies the regularity package used at TeX 1520 and 1637--1645
from mathlib's actual compactly supported smooth bump.  It also records the
quantitative absorption behind TeX 1518 without hiding the polynomial budget
in `O` notation.
-/

/-- A compactly supported smooth bump equal to one on `|x| ≤ R` and supported
in `|x| < 2R`. -/
def sourceBump (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : ℝ) where
  rIn := R
  rOut := 2 * R
  rIn_pos := hR
  rIn_lt_rOut := by linarith

@[simp] theorem sourceBump_rIn (R : ℝ) (hR : 0 < R) :
    (sourceBump R hR).rIn = R := rfl

@[simp] theorem sourceBump_rOut (R : ℝ) (hR : 0 < R) :
    (sourceBump R hR).rOut = 2 * R := rfl

theorem sourceBump_nonneg (R : ℝ) (hR : 0 < R) (x : ℝ) :
    0 ≤ sourceBump R hR x :=
  (sourceBump R hR).nonneg

theorem sourceBump_le_one (R : ℝ) (hR : 0 < R) (x : ℝ) :
    sourceBump R hR x ≤ 1 :=
  (sourceBump R hR).le_one

theorem sourceBump_eq_one_of_abs_le
    (R : ℝ) (hR : 0 < R) {x : ℝ} (hx : |x| ≤ R) :
    sourceBump R hR x = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simpa [Real.dist_eq] using hx

theorem sourceBump_one_le_of_abs_le
    (R : ℝ) (hR : 0 < R) {x : ℝ} (hx : |x| ≤ R) :
    1 ≤ sourceBump R hR x := by
  rw [sourceBump_eq_one_of_abs_le R hR hx]

theorem sourceBump_eq_zero_of_two_mul_le_abs
    (R : ℝ) (hR : 0 < R) {x : ℝ} (hx : 2 * R ≤ |x|) :
    sourceBump R hR x = 0 := by
  apply ContDiffBump.zero_of_le_dist
  simpa [Real.dist_eq] using hx

theorem sourceBump_hasCompactSupport (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (fun x : ℝ => sourceBump R hR x) :=
  ContDiffBump.hasCompactSupport _

theorem sourceBump_contDiff (R : ℝ) (hR : 0 < R) :
    ContDiff ℝ ∞ (fun x : ℝ => sourceBump R hR x) :=
  (sourceBump R hR).contDiff

theorem sourceBump_complex_hasCompactSupport (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (fun x : ℝ => (sourceBump R hR x : ℂ)) := by
  exact (sourceBump_hasCompactSupport R hR).comp_left Complex.ofReal_zero

theorem sourceBump_complex_contDiff (R : ℝ) (hR : 0 < R) :
    ContDiff ℝ ∞ (fun x : ℝ => (sourceBump R hR x : ℂ)) := by
  exact Complex.ofRealCLM.contDiff.comp (sourceBump_contDiff R hR)

/-- The concrete bump, bundled as a Schwartz function. -/
def sourceBumpSchwartz (R : ℝ) (hR : 0 < R) : 𝓢(ℝ, ℂ) :=
  (sourceBump_complex_hasCompactSupport R hR).toSchwartzMap
    (sourceBump_complex_contDiff R hR)

@[simp] theorem sourceBumpSchwartz_apply (R : ℝ) (hR : 0 < R) (x : ℝ) :
    sourceBumpSchwartz R hR x = sourceBump R hR x := rfl

/-- A single explicit Schwartz seminorm simultaneously gives the source's
uniform and order-`q` Fourier envelopes. -/
def sourceBumpFourierConstant (R : ℝ) (hR : 0 < R) (q : ℕ) : ℝ :=
  2 ^ q * (Finset.Iic (q, 0)).sup
    (fun m => SchwartzMap.seminorm ℂ m.1 m.2)
      (𝓕 (sourceBumpSchwartz R hR))

theorem sourceBumpFourierConstant_nonneg
    (R : ℝ) (hR : 0 < R) (q : ℕ) :
    0 ≤ sourceBumpFourierConstant R hR q := by
  unfold sourceBumpFourierConstant
  positivity

theorem sourceBump_fourier_decay
    (R : ℝ) (hR : 0 < R) (q : ℕ) (xi : ℝ) :
    ‖FourierTransform.fourier
        (fun x : ℝ => (sourceBump R hR x : ℂ)) xi‖ ≤
      sourceBumpFourierConstant R hR q / (1 + |xi|) ^ q := by
  let b : 𝓢(ℝ, ℂ) := sourceBumpSchwartz R hR
  let bhat : 𝓢(ℝ, ℂ) := 𝓕 b
  have hseminorm := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℂ) (m := (q, 0)) (k := q) (n := 0)
    le_rfl le_rfl bhat xi
  have hseminorm' :
      (1 + |xi|) ^ q * ‖bhat xi‖ ≤
        2 ^ q * (Finset.Iic (q, 0)).sup
          (fun m => SchwartzMap.seminorm ℂ m.1 m.2) bhat := by
    simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_zero] using hseminorm
  have hden : 0 < (1 + |xi|) ^ q := by positivity
  change ‖bhat xi‖ ≤
    sourceBumpFourierConstant R hR q / (1 + |xi|) ^ q
  apply (le_div_iff₀ hden).2
  rw [mul_comm]
  simpa only [bhat, b, sourceBumpFourierConstant] using hseminorm'

/-- Exact regularity and Fourier-seminorm package required by the second
Poisson theorem, now discharged by the concrete bump. -/
theorem exists_sourceBump_fourier_package (R : ℝ) (hR : 0 < R) (q : ℕ) :
    ∃ K0 Kdec Ksup : ℝ,
      0 ≤ Kdec ∧ 0 ≤ Ksup ∧
      (∀ xi, ‖FourierTransform.fourier
        (fun x : ℝ => (sourceBump R hR x : ℂ)) xi‖ ≤
          K0 / (1 + |xi|) ^ 2) ∧
      (∀ xi, ‖FourierTransform.fourier
        (fun x : ℝ => (sourceBump R hR x : ℂ)) xi‖ ≤
          Kdec / (1 + |xi|) ^ (q + 2)) ∧
      (∀ xi, ‖FourierTransform.fourier
        (fun x : ℝ => (sourceBump R hR x : ℂ)) xi‖ ≤ Ksup) := by
  refine ⟨sourceBumpFourierConstant R hR 2,
    sourceBumpFourierConstant R hR (q + 2),
    sourceBumpFourierConstant R hR 0,
    sourceBumpFourierConstant_nonneg R hR (q + 2),
    sourceBumpFourierConstant_nonneg R hR 0, ?_, ?_, ?_⟩
  · exact fun xi => sourceBump_fourier_decay R hR 2 xi
  · exact fun xi => sourceBump_fourier_decay R hR (q + 2) xi
  · intro xi
    simpa using sourceBump_fourier_decay R hR 0 xi

/-- If the third affine range lies in the inner plateau of the bump, the
weighted source `g` is exactly the complexification of that finite affine
branch.  This is the pointwise weld behind TeX 1520--1529. -/
theorem sourceGFinite_sourceBump_eq_ofReal_sourceFiniteAffineSum
    (m1Range m2Range m3Range : Finset ℤ) (f : ℝ → ℝ)
    {R M3 : ℝ} (hR : 0 < R)
    (hm3 : ∀ m3 ∈ m3Range, |(m3 : ℝ) / M3| ≤ R) (u : ℝ) :
    sourceGFinite m1Range m2Range m3Range
        (fun x : ℝ => (sourceBump R hR x : ℂ))
        (fun x : ℝ => (f x : ℂ)) M3 u =
      (sourceFiniteAffineSum m1Range m2Range m3Range f u : ℂ) := by
  unfold sourceGFinite sourceFiniteAffineSum sourceGSummand
  push_cast
  apply Finset.sum_congr rfl
  intro m1 hm1
  apply Finset.sum_congr rfl
  intro m2 hm2
  apply Finset.sum_congr rfl
  intro m3 hm3mem
  rw [sourceBump_eq_one_of_abs_le R hR (hm3 m3 hm3mem)]
  simp

/-- Squaring the preceding pointwise identity gives the exact nonnegative
bump domination used before Plancherel.  Equality is available because the
finite third range is already the source support range. -/
theorem sourceFiniteAffineEnergy_eq_integral_norm_sourceGFinite_sourceBump
    (m1Range m2Range m3Range : Finset ℤ) (f : ℝ → ℝ)
    {R M3 : ℝ} (hR : 0 < R)
    (hm3 : ∀ m3 ∈ m3Range, |(m3 : ℝ) / M3| ≤ R) :
    sourceFiniteAffineEnergy m1Range m2Range m3Range f =
      ∫ u : ℝ, ‖sourceGFinite m1Range m2Range m3Range
        (fun x : ℝ => (sourceBump R hR x : ℂ))
        (fun x : ℝ => (f x : ℂ)) M3 u‖ ^ 2 := by
  unfold sourceFiniteAffineEnergy
  apply integral_congr_ae
  filter_upwards with u
  rw [sourceGFinite_sourceBump_eq_ofReal_sourceFiniteAffineSum
    m1Range m2Range m3Range f hR hm3 u]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A plateau radius `R` discharges the varying source majorant
`|z| ≤ (M2/m2')B → 1 ≤ psi z` as soon as the dyadic ratios fit inside `R`. -/
theorem sourceBump_majorizes_dyadic_localization
    (mRange : Finset ℤ) {R M2 B : ℝ} (hR : 0 < R)
    (hradius : ∀ m2' ∈ mRange, (M2 / (m2' : ℝ)) * B ≤ R) :
    ∀ m2' ∈ mRange, ∀ z,
      |z| ≤ (M2 / (m2' : ℝ)) * B → 1 ≤ sourceBump R hR z := by
  intro m2' hm2' z hz
  exact sourceBump_one_le_of_abs_le R hR (hz.trans (hradius m2' hm2'))

/-- TeX 1518, in its exact reusable scalar form: after a polynomial factor
has been bounded by `T^a`, any exponent budget `a+4 ≤ 100` is absorbed by
the square of the mass lower bound `mass ≥ T⁻²`. -/
theorem time_pow_mul_time_neg100_le_mass_sq
    {T mass A : ℝ} (a : ℕ)
    (hT : 1 ≤ T) (hmass : T⁻¹ ^ 2 ≤ mass)
    (hAT : A ≤ T ^ a)
    (ha : a + 4 ≤ 100) :
    A / T ^ 100 ≤ mass ^ 2 := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hpow : T ^ (a + 4) ≤ T ^ 100 := by
    exact pow_le_pow_right₀ hT (by omega)
  have hA4 : A * T ^ 4 ≤ T ^ 100 := by
    calc
      A * T ^ 4 ≤ T ^ a * T ^ 4 :=
        mul_le_mul_of_nonneg_right hAT (by positivity)
      _ = T ^ (a + 4) := by rw [pow_add]
      _ ≤ T ^ 100 := hpow
  have htail : A / T ^ 100 ≤ T⁻¹ ^ 4 := by
    have hT100 : 0 < T ^ 100 := pow_pos hT0 _
    have hT4 : 0 < T ^ 4 := pow_pos hT0 _
    calc
      A / T ^ 100 ≤ 1 / T ^ 4 := by
        rw [div_le_div_iff₀ hT100 hT4]
        simpa [mul_comm] using hA4
      _ = T⁻¹ ^ 4 := by simp [one_div]
  have hmass0 : 0 ≤ T⁻¹ ^ 2 := sq_nonneg _
  have hmassSq : (T⁻¹ ^ 2) ^ 2 ≤ mass ^ 2 :=
    pow_le_pow_left₀ hmass0 hmass 2
  calc
    A / T ^ 100 ≤ T⁻¹ ^ 4 := htail
    _ = (T⁻¹ ^ 2) ^ 2 := by ring
    _ ≤ mass ^ 2 := hmassSq

/-- The source specialization `M ≤ T^4`: a factor bounded by `M^k` costs
at most `4k` powers of `T` in the explicit tail budget. -/
theorem M_pow_mul_time_neg100_le_mass_sq
    {T M mass A : ℝ} (k : ℕ)
    (hT : 1 ≤ T) (hM0 : 0 ≤ M) (hM : M ≤ T ^ 4)
    (hmass : T⁻¹ ^ 2 ≤ mass)
    (hApoly : A ≤ M ^ k)
    (hk : 4 * k + 4 ≤ 100) :
    A / T ^ 100 ≤ mass ^ 2 := by
  apply time_pow_mul_time_neg100_le_mass_sq (a := 4 * k)
    hT hmass
  · calc
      A ≤ M ^ k := hApoly
      _ ≤ (T ^ 4) ^ k := pow_le_pow_left₀ hM0 hM k
      _ = T ^ (4 * k) := by rw [pow_mul]
  · omega

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourceBump_eq_one_of_abs_le
#print axioms GuthMaynardJIteration.sourceBump_complex_hasCompactSupport
#print axioms GuthMaynardJIteration.sourceBump_complex_contDiff
#print axioms GuthMaynardJIteration.sourceBump_fourier_decay
#print axioms GuthMaynardJIteration.exists_sourceBump_fourier_package
#print axioms GuthMaynardJIteration.time_pow_mul_time_neg100_le_mass_sq
#print axioms GuthMaynardJIteration.M_pow_mul_time_neg100_le_mass_sq
