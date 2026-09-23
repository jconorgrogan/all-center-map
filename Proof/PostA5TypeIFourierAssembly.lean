import AppendixA4PostA5SetAdapter
import PostA5CrowdingDeterministic

/-!
# Deterministic Type-I Fourier extraction

This module isolates the finite and measure-theoretic part of the A.9
real-part removal.  Its hypotheses are the literal central Fourier mass and
tail integral; no large-value conclusion is assumed.
-/

namespace PostA5TypeIFourierAssembly

open Set MeasureTheory
open FixedCharacterPoweredBridge MAPAppendixA4PostA5SetAdapter SchwartzMap CGLProofDAG
open PostA5CrowdingDeterministic
open scoped FourierTransform

noncomputable section

/-- If a Fourier integral is large, its omitted tail costs at most half, and
the Fourier kernel has central `L¹` mass at most `A`, then the compact central
interval contains a point where the common polynomial is large. -/
theorem exists_large_point_of_central_fourier_mass
    (f P : ℝ → ℂ) {H A V : ℝ}
    (hA : 0 < A) (hV : 0 < V)
    (hprod : IntegrableOn (fun xi => f xi * P xi) (Set.Icc (-H) H))
    (hf : IntegrableOn f (Set.Icc (-H) H))
    (hmass : (∫ xi in Set.Icc (-H) H, ‖f xi‖) ≤ A)
    {E z : ℂ} (hsplit : z = (∫ xi in Set.Icc (-H) H, f xi * P xi) + E)
    (htail : ‖E‖ ≤ V / 2) (hlarge : V ≤ ‖z‖) :
    ∃ xi ∈ Set.Icc (-H) H, V / (4 * A) ≤ ‖P xi‖ := by
  by_contra h
  push Not at h
  have hpoint : ∀ xi ∈ Set.Icc (-H) H, ‖P xi‖ ≤ V / (4 * A) := by
    intro xi hxi
    exact (h xi hxi).le
  have hcentralNorm :
      ‖∫ xi in Set.Icc (-H) H, f xi * P xi‖ ≤ V / 4 := by
    calc
      ‖∫ xi in Set.Icc (-H) H, f xi * P xi‖ ≤
          ∫ xi in Set.Icc (-H) H, ‖f xi * P xi‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ xi in Set.Icc (-H) H,
          ‖f xi‖ * (V / (4 * A)) := by
        apply MeasureTheory.integral_mono_ae
        · exact hprod.norm
        · exact hf.norm.mul_const _
        · filter_upwards [ae_restrict_mem measurableSet_Icc] with xi hxi
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hpoint xi hxi) (norm_nonneg _)
      _ = (V / (4 * A)) *
          (∫ xi in Set.Icc (-H) H, ‖f xi‖) := by
        rw [← MeasureTheory.integral_const_mul]
        apply integral_congr_ae
        filter_upwards with xi
        ring
      _ ≤ (V / (4 * A)) * A := by
        exact mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = V / 4 := by field_simp
  have hz : ‖z‖ ≤ 3 * V / 4 := by
    rw [hsplit]
    calc
      ‖(∫ xi in Set.Icc (-H) H, f xi * P xi) + E‖ ≤
          ‖∫ xi in Set.Icc (-H) H, f xi * P xi‖ + ‖E‖ := norm_add_le _ _
      _ ≤ V / 4 + V / 2 := add_le_add hcentralNorm htail
      _ = 3 * V / 4 := by ring
  have hthree : 3 * V / 4 < V := by linarith
  exact (not_lt_of_ge hlarge) (hz.trans_lt hthree)

/-- Direct whole-line form.  The only tail premise is the norm of the literal
Fourier-product integral on the complement of the truncation interval. -/
theorem exists_large_point_of_fourier_integral
    (f P : ℝ → ℂ) {H A V : ℝ}
    (hA : 0 < A) (hV : 0 < V)
    (hprod : Integrable (fun xi => f xi * P xi))
    (hf : Integrable f)
    (hmass : (∫ xi in Set.Icc (-H) H, ‖f xi‖) ≤ A)
    (htail : ‖∫ xi in (Set.Icc (-H) H)ᶜ, f xi * P xi‖ ≤ V / 2)
    (hlarge : V ≤ ‖∫ xi, f xi * P xi‖) :
    ∃ xi ∈ Set.Icc (-H) H, V / (4 * A) ≤ ‖P xi‖ := by
  apply exists_large_point_of_central_fourier_mass f P hA hV
    hprod.integrableOn hf.integrableOn hmass
    (E := ∫ xi in (Set.Icc (-H) H)ᶜ, f xi * P xi)
    (z := ∫ xi, f xi * P xi)
  · exact (MeasureTheory.integral_add_compl measurableSet_Icc hprod).symm
  · exact htail
  · exact hlarge

/-- A finite Dirichlet polynomial is uniformly bounded by the `ℓ¹` mass of
its coefficient block. -/
theorem norm_dirichletPolynomial_le_coefficientMass
    (b : ℕ → ℂ) (D : ℕ) (t : ℝ) :
    ‖dirichletPolynomial b D t‖ ≤
      ∑ n ∈ Finset.Ioc D (2 * D), ‖b n‖ := by
  unfold dirichletPolynomial
  calc
    ‖∑ n ∈ Finset.Ioc D (2 * D),
        b n * Complex.exp (Complex.I * (t * Real.log n))‖ ≤
      ∑ n ∈ Finset.Ioc D (2 * D),
        ‖b n * Complex.exp (Complex.I * (t * Real.log n))‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.Ioc D (2 * D), ‖b n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, Complex.norm_exp]
      have hre :
          (Complex.I * ((t : ℂ) * ((Real.log n : ℝ) : ℂ))).re = 0 := by
        rw [Complex.mul_re]
        simp only [Complex.I_re, Complex.I_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [hre]
      simp

/-- The common A.9 coefficient has the source-faithful divisor majorant; in
particular the mollifier length `U` does not appear as a power-sized loss. -/
theorem norm_detectorCommonCoefficient_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (U N : ℕ) {Y : ℝ} (hY : 0 < Y) (sigma : ℝ)
    {n : ℕ} (hn : 0 < n) :
    ‖detectorCommonCoefficient chi U N Y sigma n‖ ≤
      Real.rpow n (-sigma) * orderedDivisorCount 2 n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hchi : ‖chi (n : ZMod q)‖ ≤ 1 := chi.norm_le_one _
  have hmoll := norm_mollifierCoeff_le_orderedDivisorCount_two U hn0
  have hdet : ‖MAPAppendixA4GammaEndpoint.detectorCoeff chi U n‖ ≤
      orderedDivisorCount 2 n := by
    unfold MAPAppendixA4GammaEndpoint.detectorCoeff
    simp only [Pi.mul_apply, norm_mul]
    calc
      ‖chi (n : ZMod q)‖ *
          ‖MAPMollifierCoefficientIdentity.mollifierCoeff U n‖ ≤
        1 * orderedDivisorCount 2 n :=
          mul_le_mul hchi hmoll (norm_nonneg _) (by positivity)
      _ = orderedDivisorCount 2 n := one_mul _
  have hexp : Real.exp (-((n : ℝ) / Y)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (n : ℝ) / Y := by positivity
    linarith
  have hrpow0 : 0 ≤ Real.rpow (n : ℝ) (-sigma) :=
    Real.rpow_nonneg (by positivity) _
  unfold detectorCommonCoefficient detectorFourierBaseCoefficient
  split_ifs with hsupp
  · rw [norm_mul, norm_mul]
    simp only [Real.norm_eq_abs, Complex.norm_real,
      abs_of_nonneg (Real.exp_pos _).le]
    rw [abs_of_nonneg hrpow0]
    calc
      Real.rpow n (-sigma) *
          (Real.exp (-((n : ℝ) / Y)) *
            ‖MAPAppendixA4GammaEndpoint.detectorCoeff chi U n‖) ≤
        Real.rpow n (-sigma) * (1 * orderedDivisorCount 2 n) := by
          gcongr
      _ = Real.rpow n (-sigma) * orderedDivisorCount 2 n := by ring
  · rw [mul_zero, norm_zero]
    exact mul_nonneg hrpow0 (Nat.cast_nonneg _)

/-- Explicit coefficient-mass bound on one dyadic block.  A pointwise
subpower divisor estimate is converted into the exact `D^(1-sigma+e)`-scale
mass, with no Fourier or zero-density input. -/
theorem detectorCommonCoefficientMass_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {U N D : ℕ} {Y sigma e K : ℝ}
    (hY : 0 < Y) (hD : 1 ≤ D) (hsigma : 0 ≤ sigma)
    (he : 0 ≤ e) (hK : 0 ≤ K)
    (hdiv : ∀ n ∈ Finset.Ioc D (2 * D),
      (orderedDivisorCount 2 n : ℝ) ≤ K * Real.rpow n e) :
    (∑ n ∈ Finset.Ioc D (2 * D),
        ‖detectorCommonCoefficient chi U N Y sigma n‖) ≤
      (D : ℝ) *
        (Real.rpow D (-sigma) *
          (K * Real.rpow (2 * D) e)) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  calc
    (∑ n ∈ Finset.Ioc D (2 * D),
        ‖detectorCommonCoefficient chi U N Y sigma n‖) ≤
      ∑ _n ∈ Finset.Ioc D (2 * D),
        Real.rpow D (-sigma) * (K * Real.rpow (2 * D) e) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnD : (D : ℝ) ≤ n := by
        exact_mod_cast (Finset.mem_Ioc.mp hn).1.le
      have hnUpper : (n : ℝ) ≤ 2 * D := by
        exact_mod_cast (Finset.mem_Ioc.mp hn).2
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have htwoD0 : (0 : ℝ) ≤ 2 * D := by positivity
      have hneg : -sigma ≤ 0 := neg_nonpos.mpr hsigma
      have hpowNeg : Real.rpow n (-sigma) ≤ Real.rpow D (-sigma) :=
        Real.rpow_le_rpow_of_nonpos hDpos hnD hneg
      have hpowPos : Real.rpow n e ≤ Real.rpow (2 * D) e :=
        Real.rpow_le_rpow hn0 hnUpper he
      calc
        ‖detectorCommonCoefficient chi U N Y sigma n‖ ≤
            Real.rpow n (-sigma) * orderedDivisorCount 2 n :=
          norm_detectorCommonCoefficient_le chi U N hY sigma
            (lt_of_lt_of_le (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1) le_rfl)
        _ ≤ Real.rpow D (-sigma) *
            (K * Real.rpow n e) := by
          calc
            Real.rpow n (-sigma) * orderedDivisorCount 2 n ≤
                Real.rpow D (-sigma) * orderedDivisorCount 2 n :=
              mul_le_mul_of_nonneg_right hpowNeg (Nat.cast_nonneg _)
            _ ≤ Real.rpow D (-sigma) * (K * Real.rpow n e) :=
              mul_le_mul_of_nonneg_left (hdiv n hn)
                (Real.rpow_nonneg hDpos.le _)
        _ ≤ Real.rpow D (-sigma) *
            (K * Real.rpow (2 * D) e) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpowPos hK)
            (Real.rpow_nonneg hDpos.le _)
    _ = (D : ℝ) *
        (Real.rpow D (-sigma) *
          (K * Real.rpow (2 * D) e)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
      congr 1
      norm_cast
      omega

/-! ## Uniform central Fourier mass -/

theorem detectorRealPartBump_translate (D : ℕ) (x : ℝ) :
    detectorRealPartBump D x =
      detectorRealPartBump 1 (x - Real.log D) := by
  simp [detectorRealPartBump, ContDiffBump.apply, Real.log_one]

/-- Exact physical-space scaling of the cutoff.  The dyadic center contributes
only the scalar `exp (-a log D)` and a translation. -/
theorem detectorRealPartCutoff_translate
    (a : ℝ) (D : ℕ) (x : ℝ) :
    detectorRealPartCutoff a D x =
      (Real.exp (-a * Real.log D) : ℂ) *
        detectorRealPartCutoff a 1 (x - Real.log D) := by
  change (((detectorRealPartBump D x : ℝ) : ℂ) *
      (Real.exp (-a * x) : ℂ)) = _
  change _ = (Real.exp (-a * Real.log D) : ℂ) *
    ((((detectorRealPartBump (1 : ℕ) (x - Real.log D) : ℝ) : ℂ) *
      (Real.exp (-a * (x - Real.log D)) : ℂ)))
  rw [detectorRealPartBump_translate]
  have he : Real.exp (-a * x) =
      Real.exp (-a * Real.log D) *
        Real.exp (-a * (x - Real.log D)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  push_cast
  ring

/-- Fourier translation is a unit phase, so the entire dyadic-center
dependence of the Fourier norm is the scalar `exp (-a log D)`. -/
theorem norm_fourier_detectorRealPartCutoff_eq
    (a : ℝ) (D : ℕ) (xi : ℝ) :
    ‖((𝓕 (detectorRealPartCutoff a D) : 𝓢(ℝ, ℂ)) xi)‖ =
      Real.exp (-a * Real.log D) *
        ‖((𝓕 (detectorRealPartCutoff a 1) : 𝓢(ℝ, ℂ)) xi)‖ := by
  let c : ℝ := Real.log D
  let r : ℂ := (Real.exp (-a * c) : ℂ)
  let f : ℝ → ℂ := fun x => detectorRealPartCutoff a 1 x
  have hfun : (fun x : ℝ => detectorRealPartCutoff a D x) =
      r • (f ∘ fun x : ℝ => x + (-c)) := by
    funext x
    dsimp [r, f, c]
    rw [detectorRealPartCutoff_translate]
    congr 2
  have hsmul :
      𝓕 (r • (f ∘ fun x : ℝ => x + (-c))) =
        r • 𝓕 (f ∘ fun x : ℝ => x + (-c)) := by
    exact VectorFourier.fourierIntegral_const_smul
      𝐞 volume (innerₗ ℝ) (f ∘ fun x : ℝ => x + (-c)) r
  have htrans :
      𝓕 (f ∘ fun x : ℝ => x + (-c)) =
        fun w => 𝐞 (((innerₗ ℝ) (-c)) w) • 𝓕 f w := by
    exact VectorFourier.fourierIntegral_comp_add_right
      𝐞 volume (innerₗ ℝ) f (-c)
  rw [SchwartzMap.fourier_coe]
  change ‖𝓕 (fun x : ℝ => detectorRealPartCutoff a D x) xi‖ = _
  rw [hfun, hsmul, Pi.smul_apply, htrans]
  change ‖r * (((𝐞 (((innerₗ ℝ) (-c)) xi) : Circle) : ℂ) * 𝓕 f xi)‖ = _
  have hr : ‖r‖ = Real.exp (-a * c) := by
    dsimp [r]
    calc
      ‖(Real.exp (-a * c) : ℂ)‖ = ‖Real.exp (-a * c)‖ := Complex.norm_real _
      _ = Real.exp (-a * c) := Real.norm_of_nonneg (Real.exp_pos _).le
  have hfFourier :
      𝓕 f xi = ((𝓕 (detectorRealPartCutoff a 1) : 𝓢(ℝ, ℂ)) xi) := by
    exact congrFun
      (SchwartzMap.fourier_coe (detectorRealPartCutoff a 1)).symm xi
  rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, hr, hfFourier]

/-- For nonnegative detector shift, moving the dyadic center can only decrease
the Fourier norm.  In particular there is no positive power (or logarithm) of
`D` hidden in the cutoff tail. -/
theorem norm_fourier_detectorRealPartCutoff_le_base
    {a : ℝ} {D : ℕ} (hD : 1 ≤ D) (ha0 : 0 ≤ a) (xi : ℝ) :
    ‖((𝓕 (detectorRealPartCutoff a D) : 𝓢(ℝ, ℂ)) xi)‖ ≤
      ‖((𝓕 (detectorRealPartCutoff a 1) : 𝓢(ℝ, ℂ)) xi)‖ := by
  rw [norm_fourier_detectorRealPartCutoff_eq]
  have hlog : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD)
  have hscale : Real.exp (-a * Real.log D) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg ha0 hlog)
  calc
    Real.exp (-a * Real.log D) *
          ‖((𝓕 (detectorRealPartCutoff a 1) : 𝓢(ℝ, ℂ)) xi)‖
        ≤ 1 * ‖((𝓕 (detectorRealPartCutoff a 1) : 𝓢(ℝ, ℂ)) xi)‖ :=
      mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
    _ = _ := one_mul _

/-- Every weighted Fourier moment at dyadic center `D ≥ 1` is bounded by the
same moment at center one.  Thus the exact center dependence is harmless; any
remaining uniformity question is solely the compact parameter `a`. -/
theorem integral_pow_mul_norm_fourier_detectorRealPartCutoff_le_base
    {a : ℝ} {D : ℕ} (hD : 1 ≤ D) (ha0 : 0 ≤ a) (k : ℕ) :
    (∫ xi : ℝ, |xi| ^ k *
        ‖((𝓕 (detectorRealPartCutoff a D) : 𝓢(ℝ, ℂ)) xi)‖) ≤
      ∫ xi : ℝ, |xi| ^ k *
        ‖((𝓕 (detectorRealPartCutoff a 1) : 𝓢(ℝ, ℂ)) xi)‖ := by
  have hIntD : Integrable (fun xi : ℝ => |xi| ^ k *
      ‖((𝓕 (detectorRealPartCutoff a D) : 𝓢(ℝ, ℂ)) xi)‖) := by
    simpa [Real.norm_eq_abs] using
      (𝓕 (detectorRealPartCutoff a D) : 𝓢(ℝ, ℂ)).integrable_pow_mul
        (volume : Measure ℝ) k
  have hInt1 : Integrable (fun xi : ℝ => |xi| ^ k *
      ‖((𝓕 (detectorRealPartCutoff a 1) : 𝓢(ℝ, ℂ)) xi)‖) := by
    simpa [Real.norm_eq_abs] using
      (𝓕 (detectorRealPartCutoff a 1) : 𝓢(ℝ, ℂ)).integrable_pow_mul
        (volume : Measure ℝ) k
  apply MeasureTheory.integral_mono_ae hIntD hInt1
  filter_upwards [] with xi
  exact mul_le_mul_of_nonneg_left
    (norm_fourier_detectorRealPartCutoff_le_base hD ha0 xi)
    (pow_nonneg (abs_nonneg xi) k)

def detectorBaseCutoff : 𝓢(ℝ, ℂ) :=
  detectorRealPartCutoff 0 1

def schwartzIteratedDerivative (n : ℕ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (SchwartzMap.derivCLM ℂ ℂ)^[n] f

theorem schwartzIteratedDerivative_apply (n : ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzIteratedDerivative n f x =
      iteratedDeriv n (fun y : ℝ => f y) x := by
  induction n generalizing x with
  | zero => simp [schwartzIteratedDerivative]
  | succ n ih =>
      rw [schwartzIteratedDerivative, Function.iterate_succ_apply']
      rw [SchwartzMap.derivCLM_apply]
      rw [iteratedDeriv_succ]
      congr 1
      funext y
      exact ih y

def detectorBaseDerivative (n : ℕ) : 𝓢(ℝ, ℂ) :=
  schwartzIteratedDerivative n detectorBaseCutoff

theorem detectorBaseDerivative_apply (n : ℕ) (x : ℝ) :
    detectorBaseDerivative n x =
      iteratedDeriv n (fun y : ℝ => detectorBaseCutoff y) x :=
  schwartzIteratedDerivative_apply n detectorBaseCutoff x

theorem detectorRealPartCutoff_base_factor (a x : ℝ) :
    detectorRealPartCutoff a 1 x =
      detectorBaseCutoff x * (Real.exp (-a * x) : ℂ) := by
  change (((detectorRealPartBump 1 x : ℝ) : ℂ) *
      (Real.exp (-a * x) : ℂ)) = _
  change _ =
    ((((detectorRealPartBump 1 x : ℝ) : ℂ) *
      (Real.exp (-(0 : ℝ) * x) : ℂ)) *
      (Real.exp (-a * x) : ℂ))
  simp

theorem iteratedDeriv_complex_exp_neg_mul (n : ℕ) (a : ℝ) :
    iteratedDeriv n (fun x : ℝ => (Real.exp (-a * x) : ℂ)) =
      fun x : ℝ => ((-a : ℝ) : ℂ) ^ n * (Real.exp (-a * x) : ℂ) := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
      rw [show n + 1 = n.succ by rfl, iteratedDeriv_succ, ih]
      funext x
      have hinner : HasDerivAt (fun x : ℝ => -a * x) (-a) x := by
        simpa using (hasDerivAt_id x).const_mul (-a)
      have hexpR : HasDerivAt (fun x : ℝ => Real.exp (-a * x))
          (Real.exp (-a * x) * (-a)) x := hinner.exp
      have hexpC : HasDerivAt (fun x : ℝ => (Real.exp (-a * x) : ℂ))
          ((Real.exp (-a * x) * (-a) : ℝ) : ℂ) x := by
        change HasDerivAt
          (Complex.ofRealCLM ∘ fun x : ℝ => Real.exp (-a * x)) _ x
        simpa using (Complex.ofRealCLM.hasFDerivAt.comp x
          hexpR.hasFDerivAt).hasDerivAt
      have hmul := hexpC.const_mul (((-a : ℝ) : ℂ) ^ n)
      simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmul.deriv

theorem iteratedDeriv_detectorRealPartCutoff_base (n : ℕ) (a x : ℝ) :
    iteratedDeriv n (fun y : ℝ => detectorRealPartCutoff a 1 y) x =
      ∑ r ∈ Finset.range (n + 1),
        (n.choose r : ℂ) * detectorBaseDerivative r x *
          (((-a : ℝ) : ℂ) ^ (n - r) * (Real.exp (-a * x) : ℂ)) := by
  have hbase : ContDiffAt ℝ (n : ℕ)
      (fun y : ℝ => detectorBaseCutoff y) x :=
    (detectorBaseCutoff.smooth (n : ℕ∞)).contDiffAt
  have hexp : ContDiffAt ℝ (n : ℕ)
      (fun y : ℝ => (Real.exp (-a * y) : ℂ)) x := by
    have heR : ContDiff ℝ (n : ℕ)
        (fun y : ℝ => Real.exp (-a * y)) := by fun_prop
    have heC : ContDiff ℝ (n : ℕ)
        (fun y : ℝ => (Real.exp (-a * y) : ℂ)) := by
      simpa only [Function.comp_def] using! Complex.ofRealCLM.contDiff.comp heR
    exact heC.contDiffAt
  have hfun : (fun y : ℝ => detectorRealPartCutoff a 1 y) =
      (fun y : ℝ => detectorBaseCutoff y) *
        (fun y : ℝ => (Real.exp (-a * y) : ℂ)) := by
    funext y
    exact detectorRealPartCutoff_base_factor a y
  rw [hfun, iteratedDeriv_mul hbase hexp]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← detectorBaseDerivative_apply]
  rw [congrFun (iteratedDeriv_complex_exp_neg_mul (n - r) a) x]

theorem detectorRealPartCutoff_eq_zero_of_not_mem_supportInterval
    {a x : ℝ} {D : ℕ}
    (hx : x ∉ Set.Icc (Real.log D - 2) (Real.log D + 2)) :
    detectorRealPartCutoff a D x = 0 := by
  have hdist : (2 : ℝ) ≤ dist x (Real.log D) := by
    rw [Real.dist_eq]
    by_contra h
    have habs : |x - Real.log D| < 2 := lt_of_not_ge h
    apply hx
    rw [abs_lt] at habs
    constructor <;> linarith
  let zeta : ContDiffBump (Real.log D) := detectorRealPartBump D
  change (zeta x : ℂ) * (Real.exp (-a * x) : ℂ) = 0
  have hz : zeta x = 0 := by
    apply zeta.zero_of_le_dist
    simpa [zeta, detectorRealPartBump] using hdist
  rw [hz]
  simp

theorem tsupport_detectorBaseCutoff_subset :
    tsupport (fun x : ℝ => detectorBaseCutoff x) ⊆ Set.Icc (-2 : ℝ) 2 := by
  apply closure_minimal
  · intro x hx
    by_contra hnot
    apply hx
    have hz : detectorRealPartCutoff (0 : ℝ) 1 x = 0 := by
      apply detectorRealPartCutoff_eq_zero_of_not_mem_supportInterval
      simpa using hnot
    simpa [detectorBaseCutoff] using hz
  · exact isClosed_Icc

theorem tsupport_detectorBaseDerivative_subset (n : ℕ) :
    tsupport (fun x : ℝ => detectorBaseDerivative n x) ⊆
      Set.Icc (-2 : ℝ) 2 := by
  induction n with
  | zero =>
      simpa [detectorBaseDerivative, schwartzIteratedDerivative] using
        tsupport_detectorBaseCutoff_subset
  | succ n ih =>
      change tsupport
        (fun x : ℝ =>
          ((SchwartzMap.derivCLM ℂ ℂ)^[n.succ] detectorBaseCutoff) x) ⊆ _
      rw [Function.iterate_succ_apply']
      exact (SchwartzMap.tsupport_derivCLM_subset ℂ
        ((SchwartzMap.derivCLM ℂ ℂ)^[n] detectorBaseCutoff)).trans ih

/-- On the support of every derivative of the fixed bump, the exponential
factor and all of its `a`-powers are uniformly bounded on `0 ≤ a ≤ 3/10`. -/
theorem norm_pow_mul_exp_le_uniform_of_baseDerivative_ne_zero
    {a x : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 3 / 10)
    (m r : ℕ) (hne : detectorBaseDerivative r x ≠ 0) :
    ‖(((-a : ℝ) : ℂ) ^ m * (Real.exp (-a * x) : ℂ))‖ ≤
      Real.exp (3 / 5) := by
  have hxTs : x ∈ tsupport (fun y : ℝ => detectorBaseDerivative r y) :=
    subset_tsupport _ hne
  have hx : x ∈ Set.Icc (-2 : ℝ) 2 :=
    tsupport_detectorBaseDerivative_subset r hxTs
  have ha1 : a ≤ 1 := by linarith
  have hpow : a ^ m ≤ 1 := pow_le_one₀ ha0 ha1
  have hxlow : -2 ≤ x := hx.1
  have hax : 0 ≤ a * (x + 2) :=
    mul_nonneg ha0 (by linarith)
  have h2a : 2 * a ≤ 3 / 5 := by linarith
  have hexponent : -a * x ≤ 3 / 5 := by
    nlinarith
  have hexp : Real.exp (-a * x) ≤ Real.exp (3 / 5) :=
    Real.exp_le_exp.mpr hexponent
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_neg, abs_of_nonneg ha0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le]
  calc
    a ^ m * Real.exp (-a * x) ≤ 1 * Real.exp (3 / 5) :=
      mul_le_mul hpow hexp (Real.exp_pos _).le (by norm_num)
    _ = Real.exp (3 / 5) := one_mul _

/-- Explicit fixed-bump constant controlling the `n`th physical derivative
uniformly for `0 ≤ a ≤ 3/10`. -/
def detectorDerivativeL1Constant (n : ℕ) : ℝ :=
  Real.exp (3 / 5) *
    ∑ r ∈ Finset.range (n + 1), (n.choose r : ℝ) *
      ∫ x : ℝ, ‖detectorBaseDerivative r x‖

theorem detectorDerivativeL1Constant_nonneg (n : ℕ) :
    0 ≤ detectorDerivativeL1Constant n := by
  unfold detectorDerivativeL1Constant
  positivity

theorem norm_iteratedDeriv_detectorRealPartCutoff_base_le
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 3 / 10) (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n
        (fun y : ℝ => detectorRealPartCutoff a 1 y) x‖ ≤
      ∑ r ∈ Finset.range (n + 1),
        Real.exp (3 / 5) * (n.choose r : ℝ) *
          ‖detectorBaseDerivative r x‖ := by
  rw [iteratedDeriv_detectorRealPartCutoff_base]
  apply norm_sum_le_of_le
  intro r hr
  by_cases hzero : detectorBaseDerivative r x = 0
  · simp [hzero]
  · rw [norm_mul, norm_mul]
    have hfactor :=
      norm_pow_mul_exp_le_uniform_of_baseDerivative_ne_zero
        ha0 ha (n - r) r hzero
    have hchoose : ‖(n.choose r : ℂ)‖ = (n.choose r : ℝ) := by simp
    rw [hchoose]
    calc
      (n.choose r : ℝ) * ‖detectorBaseDerivative r x‖ *
          ‖(((-a : ℝ) : ℂ) ^ (n - r) * (Real.exp (-a * x) : ℂ))‖ ≤
        (n.choose r : ℝ) * ‖detectorBaseDerivative r x‖ *
          Real.exp (3 / 5) :=
        mul_le_mul_of_nonneg_left hfactor
          (mul_nonneg (by positivity) (norm_nonneg _))
      _ = Real.exp (3 / 5) * (n.choose r : ℝ) *
          ‖detectorBaseDerivative r x‖ := by ring

/-- Uniform physical-space `L¹` derivative bound for the fixed-center cutoff.
All dependence on the smooth bump is retained in the explicit finite constant
`detectorDerivativeL1Constant n`; neither `a` nor `D` occurs in it. -/
theorem integral_norm_iteratedDeriv_detectorRealPartCutoff_base_le
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 3 / 10) (n : ℕ) :
    (∫ x : ℝ, ‖iteratedDeriv n
        (fun y : ℝ => detectorRealPartCutoff a 1 y) x‖) ≤
      detectorDerivativeL1Constant n := by
  let f : 𝓢(ℝ, ℂ) := detectorRealPartCutoff a 1
  have hleft : Integrable (fun x : ℝ =>
      ‖iteratedDeriv n (fun y : ℝ => detectorRealPartCutoff a 1 y) x‖) := by
    have h := (schwartzIteratedDerivative n f).integrable
      (μ := (volume : Measure ℝ)) |>.norm
    simpa [f, schwartzIteratedDerivative_apply] using h
  have hterm : ∀ r ∈ Finset.range (n + 1), Integrable (fun x : ℝ =>
      Real.exp (3 / 5) * (n.choose r : ℝ) *
        ‖detectorBaseDerivative r x‖) := by
    intro r hr
    exact ((detectorBaseDerivative r).integrable
      (μ := (volume : Measure ℝ))).norm.const_mul
      (Real.exp (3 / 5) * (n.choose r : ℝ))
  have hright : Integrable (fun x : ℝ =>
      ∑ r ∈ Finset.range (n + 1),
        Real.exp (3 / 5) * (n.choose r : ℝ) *
          ‖detectorBaseDerivative r x‖) :=
    integrable_finsetSum _ hterm
  calc
    (∫ x : ℝ, ‖iteratedDeriv n
        (fun y : ℝ => detectorRealPartCutoff a 1 y) x‖) ≤
      ∫ x : ℝ, ∑ r ∈ Finset.range (n + 1),
        Real.exp (3 / 5) * (n.choose r : ℝ) *
          ‖detectorBaseDerivative r x‖ := by
      exact MeasureTheory.integral_mono hleft hright
        (norm_iteratedDeriv_detectorRealPartCutoff_base_le ha0 ha n)
    _ = detectorDerivativeL1Constant n := by
      rw [MeasureTheory.integral_finsetSum _ hterm]
      simp_rw [MeasureTheory.integral_const_mul]
      unfold detectorDerivativeL1Constant
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

/-- Integration by parts, expressed through mathlib's exact Fourier theorem:
the `q`th Fourier seminorm is controlled by the uniform `L¹` norm of the
`q`th physical derivative. -/
theorem seminorm_fourier_detectorRealPartCutoff_base_le
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 3 / 10) (q : ℕ) :
    SchwartzMap.seminorm ℂ q 0
        (𝓕 (detectorRealPartCutoff a 1) : 𝓢(ℝ, ℂ)) ≤
      detectorDerivativeL1Constant q := by
  let f : 𝓢(ℝ, ℂ) := detectorRealPartCutoff a 1
  apply SchwartzMap.seminorm_le_bound' ℂ q 0
    (𝓕 f : 𝓢(ℝ, ℂ)) (detectorDerivativeL1Constant_nonneg q)
  intro xi
  rw [iteratedDeriv_zero]
  have hInt : ∀ m : ℕ, (m : ℕ∞) ≤ ⊤ →
      Integrable (iteratedDeriv m (fun x : ℝ => f x)) := by
    intro m hm
    have h := (schwartzIteratedDerivative m f).integrable
      (μ := (volume : Measure ℝ))
    apply h.congr
    filter_upwards with x
    exact schwartzIteratedDerivative_apply m f x
  have hfourier := Real.fourier_iteratedDeriv
    (f.smooth ⊤) hInt (show (q : ℕ∞) ≤ ⊤ from le_top)
  have hraw := VectorFourier.norm_fourierIntegral_le_integral_norm
    𝐞 volume (innerₗ ℝ)
      (iteratedDeriv q (fun x : ℝ => f x)) xi
  change ‖𝓕 (iteratedDeriv q (fun x : ℝ => f x)) xi‖ ≤ _ at hraw
  rw [congrFun hfourier xi] at hraw
  have hfFourier :
      𝓕 (fun x : ℝ => f x) xi = ((𝓕 f : 𝓢(ℝ, ℂ)) xi) := by
    exact congrFun (SchwartzMap.fourier_coe f).symm xi
  rw [hfFourier] at hraw
  have htwoPi : (1 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hscale : (1 : ℝ) ≤ (2 * Real.pi) ^ q := one_le_pow₀ htwoPi
  have hnormScale :
      ‖((2 * (Real.pi : ℂ) * Complex.I * (xi : ℂ)) ^ q) •
          ((𝓕 f : 𝓢(ℝ, ℂ)) xi)‖ =
        (2 * Real.pi) ^ q * |xi| ^ q *
          ‖((𝓕 f : 𝓢(ℝ, ℂ)) xi)‖ := by
    change ‖((2 * (Real.pi : ℂ) * Complex.I * (xi : ℂ)) ^ q) *
      ((𝓕 f : 𝓢(ℝ, ℂ)) xi)‖ = _
    rw [norm_mul, norm_pow]
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs]
    rw [abs_of_pos Real.pi_pos]
    have hnormTwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by
      calc
        ‖(2 : ℂ)‖ = ‖(2 : ℝ)‖ := Complex.norm_real _
        _ = |(2 : ℝ)| := Real.norm_eq_abs _
        _ = 2 := abs_of_nonneg (by norm_num)
    rw [hnormTwo]
    ring
  rw [hnormScale] at hraw
  calc
    |xi| ^ q * ‖((𝓕 f : 𝓢(ℝ, ℂ)) xi)‖ ≤
        (2 * Real.pi) ^ q *
          (|xi| ^ q * ‖((𝓕 f : 𝓢(ℝ, ℂ)) xi)‖) := by
      exact le_mul_of_one_le_left
        (mul_nonneg (pow_nonneg (abs_nonneg xi) q) (norm_nonneg _)) hscale
    _ = (2 * Real.pi) ^ q * |xi| ^ q *
          ‖((𝓕 f : 𝓢(ℝ, ℂ)) xi)‖ := by ring
    _ ≤ ∫ x : ℝ, ‖iteratedDeriv q
          (fun y : ℝ => detectorRealPartCutoff a 1 y) x‖ := by
      simpa [f] using hraw
    _ ≤ detectorDerivativeL1Constant q :=
      integral_norm_iteratedDeriv_detectorRealPartCutoff_base_le ha0 ha q

/-- Explicit constant for the `k`th weighted Fourier moment.  It depends only
on the fixed bump and `k`; in particular it is independent of `a` and `D`. -/
def detectorFourierMomentConstant (k : ℕ) : ℝ :=
  (2 ^ (volume : Measure ℝ).integrablePower *
      ∫ xi : ℝ,
        (1 + ‖xi‖) ^ (-((volume : Measure ℝ).integrablePower : ℝ))) *
    (detectorDerivativeL1Constant 0 +
      detectorDerivativeL1Constant
        (k + (volume : Measure ℝ).integrablePower))

theorem detectorFourierMomentConstant_nonneg (k : ℕ) :
    0 ≤ detectorFourierMomentConstant k := by
  unfold detectorFourierMomentConstant
  apply mul_nonneg
  · apply mul_nonneg (by positivity)
    exact integral_nonneg fun xi => Real.rpow_nonneg (by positivity) _
  · exact add_nonneg (detectorDerivativeL1Constant_nonneg 0)
      (detectorDerivativeL1Constant_nonneg _)

/-- Uniform weighted Fourier moment at center one, obtained by the explicit
physical derivative bounds and integration by parts. -/
theorem integral_pow_mul_norm_fourier_detectorRealPartCutoff_base_le
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 3 / 10) (k : ℕ) :
    (∫ xi : ℝ, |xi| ^ k *
        ‖((𝓕 (detectorRealPartCutoff a 1) : 𝓢(ℝ, ℂ)) xi)‖) ≤
      detectorFourierMomentConstant k := by
  let F : 𝓢(ℝ, ℂ) :=
    (𝓕 (detectorRealPartCutoff a 1) : 𝓢(ℝ, ℂ))
  have hgeneral :=
    SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℂ
      (volume : Measure ℝ) F k 0
  have hzero : SchwartzMap.seminorm ℂ 0 0 F ≤
      detectorDerivativeL1Constant 0 := by
    exact seminorm_fourier_detectorRealPartCutoff_base_le ha0 ha 0
  have hhigh : SchwartzMap.seminorm ℂ
      (k + (volume : Measure ℝ).integrablePower) 0 F ≤
      detectorDerivativeL1Constant
        (k + (volume : Measure ℝ).integrablePower) := by
    exact seminorm_fourier_detectorRealPartCutoff_base_le ha0 ha _
  have hpref : 0 ≤
      2 ^ (volume : Measure ℝ).integrablePower *
        ∫ xi : ℝ,
          (1 + ‖xi‖) ^ (-((volume : Measure ℝ).integrablePower : ℝ)) := by
    apply mul_nonneg (by positivity)
    exact integral_nonneg fun xi => Real.rpow_nonneg (by positivity) _
  calc
    (∫ xi : ℝ, |xi| ^ k *
        ‖((𝓕 (detectorRealPartCutoff a 1) : 𝓢(ℝ, ℂ)) xi)‖) ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ xi : ℝ,
          (1 + ‖xi‖) ^ (-((volume : Measure ℝ).integrablePower : ℝ))) *
        (SchwartzMap.seminorm ℂ 0 0 F +
          SchwartzMap.seminorm ℂ
            (k + (volume : Measure ℝ).integrablePower) 0 F) := by
      simpa [F, Real.norm_eq_abs, norm_iteratedFDeriv_zero] using hgeneral
    _ ≤ (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ xi : ℝ,
          (1 + ‖xi‖) ^ (-((volume : Measure ℝ).integrablePower : ℝ))) *
        (detectorDerivativeL1Constant 0 +
          detectorDerivativeL1Constant
            (k + (volume : Measure ℝ).integrablePower)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hzero hhigh) hpref
    _ = detectorFourierMomentConstant k := rfl

/-- The requested literal `D`-uniform weighted Fourier moment. -/
theorem integral_pow_mul_norm_fourier_detectorRealPartCutoff_le
    {a : ℝ} {D : ℕ} (hD : 1 ≤ D)
    (ha0 : 0 ≤ a) (ha : a ≤ 3 / 10) (k : ℕ) :
    (∫ xi : ℝ, |xi| ^ k *
        ‖((𝓕 (detectorRealPartCutoff a D) : 𝓢(ℝ, ℂ)) xi)‖) ≤
      detectorFourierMomentConstant k := by
  exact (integral_pow_mul_norm_fourier_detectorRealPartCutoff_le_base
    hD ha0 k).trans
      (integral_pow_mul_norm_fourier_detectorRealPartCutoff_base_le ha0 ha k)

theorem norm_detectorRealPartCutoff_le_three
    {a x : ℝ} {D : ℕ} (hD : 1 ≤ D)
    (ha0 : 0 ≤ a) (ha : a ≤ 3 / 10)
    (hx : x ∈ Set.Icc (Real.log D - 2) (Real.log D + 2)) :
    ‖detectorRealPartCutoff a D x‖ ≤ 3 := by
  let zeta : ContDiffBump (Real.log D) := detectorRealPartBump D
  have hlog : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD)
  have hxlow : -2 ≤ x := by linarith [hx.1]
  have hexponent : -a * x ≤ 1 := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ x + 2 by linarith)]
  have hexp : Real.exp (-a * x) ≤ 3 := by
    exact (Real.exp_le_exp.mpr hexponent).trans Real.exp_one_lt_three.le
  change ‖(zeta x : ℂ) * (Real.exp (-a * x) : ℂ)‖ ≤ 3
  have hzNorm : ‖(zeta x : ℂ)‖ = zeta x := by
    calc
      ‖(zeta x : ℂ)‖ = ‖(zeta x : ℝ)‖ := Complex.norm_real _
      _ = zeta x := Real.norm_of_nonneg zeta.nonneg
  have heNorm : ‖(Real.exp (-a * x) : ℂ)‖ = Real.exp (-a * x) := by
    calc
      ‖(Real.exp (-a * x) : ℂ)‖ = ‖Real.exp (-a * x)‖ := Complex.norm_real _
      _ = Real.exp (-a * x) := Real.norm_of_nonneg (Real.exp_pos _).le
  rw [norm_mul, hzNorm, heNorm]
  calc
    zeta x * Real.exp (-a * x) ≤ 1 * 3 :=
      mul_le_mul zeta.le_one hexp (Real.exp_pos _).le (by norm_num)
    _ = 3 := by ring

theorem integral_norm_detectorRealPartCutoff_le_twelve
    {a : ℝ} {D : ℕ} (hD : 1 ≤ D)
    (ha0 : 0 ≤ a) (ha : a ≤ 3 / 10) :
    (∫ x : ℝ, ‖detectorRealPartCutoff a D x‖) ≤ 12 := by
  let s : Set ℝ := Set.Icc (Real.log D - 2) (Real.log D + 2)
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := s) (fun x hx => by
      rw [detectorRealPartCutoff_eq_zero_of_not_mem_supportInterval hx]
      simp)]
  calc
    (∫ x in s, ‖detectorRealPartCutoff a D x‖) ≤
        ∫ _x : ℝ in s, (3 : ℝ) := by
      apply MeasureTheory.setIntegral_mono_on
      · exact (detectorRealPartCutoff a D).integrable.norm.integrableOn
      · exact integrableOn_const measure_Icc_lt_top.ne
      · exact measurableSet_Icc
      · intro x hx
        exact norm_detectorRealPartCutoff_le_three hD ha0 ha hx
    _ = 12 := by
      simp [s, MeasureTheory.integral_const]
      norm_num

set_option maxHeartbeats 800000 in
/-- Literal uniform truncated Fourier-kernel mass on the high strip.  The
bound is independent of the dyadic center `D`; only the truncation radius `H`
appears, with the explicit constant `24`. -/
theorem integral_norm_fourier_detectorRealPartCutoff_Icc_le
    {a H : ℝ} {D : ℕ} (hD : 1 ≤ D)
    (ha0 : 0 ≤ a) (ha : a ≤ 3 / 10) (hH : 0 ≤ H) :
    (∫ xi in Set.Icc (-H) H,
      ‖((𝓕 (detectorRealPartCutoff a D) : 𝓢(ℝ, ℂ)) xi)‖) ≤
        24 * H := by
  let psi : 𝓢(ℝ, ℂ) := detectorRealPartCutoff a D
  have hpoint : ∀ xi : ℝ, ‖((𝓕 psi : 𝓢(ℝ, ℂ)) xi)‖ ≤ 12 := by
    intro xi
    have hfourier := SchwartzMap.norm_fourier_apply_le_toLp_one psi xi
    rw [SchwartzMap.norm_toLp_one (μ := volume)] at hfourier
    exact hfourier.trans
      (integral_norm_detectorRealPartCutoff_le_twelve hD ha0 ha)
  calc
    (∫ xi in Set.Icc (-H) H, ‖((𝓕 psi : 𝓢(ℝ, ℂ)) xi)‖) ≤
        ∫ _xi : ℝ in Set.Icc (-H) H, (12 : ℝ) := by
      apply MeasureTheory.setIntegral_mono_on
      · exact (𝓕 psi : 𝓢(ℝ, ℂ)).integrable.norm.integrableOn
      · exact integrableOn_const measure_Icc_lt_top.ne
      · exact measurableSet_Icc
      · intro xi hxi
        exact hpoint xi
    _ = 24 * H := by
      simp [MeasureTheory.integral_const, hH]
      ring

/-- The complement of the symmetric compact interval is controlled by the
certified arbitrary-power Schwartz tail.  This converts the exact set used by
the finite extraction theorem to the canonical A.9 tail set. -/
theorem integral_compl_Icc_norm_fourier_le_inv_pow_mul
    (psi : 𝓢(ℝ, ℂ)) {H : ℝ} (k : ℕ) (hH : 0 < H) :
    (∫ xi in (Set.Icc (-H) H)ᶜ, ‖((𝓕 psi : 𝓢(ℝ, ℂ)) xi)‖) ≤
      (H ^ k)⁻¹ *
        (∫ xi : ℝ, |xi| ^ k * ‖((𝓕 psi : 𝓢(ℝ, ℂ)) xi)‖) := by
  apply le_trans ?_
    (FourierRealPartRemoval.fourier_tail_le_inv_pow_mul psi H k hH)
  apply MeasureTheory.setIntegral_mono_set
  · exact (𝓕 psi : 𝓢(ℝ, ℂ)).integrable.norm.integrableOn
  · filter_upwards with xi
    exact norm_nonneg _
  · filter_upwards with xi hxi
    change xi ∉ Set.Icc (-H) H at hxi
    simp only [Set.mem_Icc, not_and_or] at hxi
    dsimp [FourierRealPartRemoval.fourierTailSet]
    change H ≤ |xi|
    rcases hxi with hlo | hhi
    · have : xi < -H := lt_of_not_ge hlo
      rw [abs_of_neg (this.trans (neg_neg_of_pos hH))]
      linarith
    · have : H < xi := lt_of_not_ge hhi
      rw [abs_of_pos (hH.trans this)]
      exact this.le

/-- Fully uniform arbitrary-power tail for the literal detector cutoff. -/
theorem integral_compl_Icc_norm_fourier_detectorRealPartCutoff_le
    {a H : ℝ} {D : ℕ} (hD : 1 ≤ D)
    (ha0 : 0 ≤ a) (ha : a ≤ 3 / 10) (k : ℕ) (hH : 0 < H) :
    (∫ xi in (Set.Icc (-H) H)ᶜ,
        ‖((𝓕 (detectorRealPartCutoff a D) : 𝓢(ℝ, ℂ)) xi)‖) ≤
      (H ^ k)⁻¹ * detectorFourierMomentConstant k := by
  exact (integral_compl_Icc_norm_fourier_le_inv_pow_mul
    (detectorRealPartCutoff a D) k hH).trans
      (mul_le_mul_of_nonneg_left
        (integral_pow_mul_norm_fourier_detectorRealPartCutoff_le
          hD ha0 ha k)
        (inv_nonneg.mpr (pow_nonneg hH.le k)))

theorem continuous_dirichletPolynomial
    (b : ℕ → ℂ) (D : ℕ) :
    Continuous (fun t : ℝ => dirichletPolynomial b D t) := by
  unfold dirichletPolynomial
  fun_prop

/-- Multiplication by a finite Dirichlet polynomial preserves integrability
of a Schwartz kernel. -/
theorem integrable_schwartz_mul_dirichletPolynomial
    (f : 𝓢(ℝ, ℂ)) (b : ℕ → ℂ) (D : ℕ) (g : ℝ → ℝ)
    (hg : Continuous g) :
    Integrable (fun xi => f xi * dirichletPolynomial b D (g xi)) := by
  apply f.integrable.mul_bdd
  · exact (continuous_dirichletPolynomial b D).comp hg |>.aestronglyMeasurable
  · filter_upwards with xi
    exact norm_dirichletPolynomial_le_coefficientMass b D (g xi)

/-- The product tail is bounded by coefficient `ℓ¹` mass times the Fourier
tail.  This is the deterministic step that lets arbitrary-power Schwartz
decay absorb the trivial polynomial bound. -/
theorem norm_setIntegral_schwartz_mul_dirichletPolynomial_le
    (f : 𝓢(ℝ, ℂ)) (b : ℕ → ℂ) (D : ℕ) (g : ℝ → ℝ)
    (hg : Continuous g) (s : Set ℝ) :
    ‖∫ xi in s, f xi * dirichletPolynomial b D (g xi)‖ ≤
      (∑ n ∈ Finset.Ioc D (2 * D), ‖b n‖) *
        ∫ xi in s, ‖f xi‖ := by
  let C : ℝ := ∑ n ∈ Finset.Ioc D (2 * D), ‖b n‖
  have hprod := integrable_schwartz_mul_dirichletPolynomial f b D g hg
  calc
    ‖∫ xi in s, f xi * dirichletPolynomial b D (g xi)‖ ≤
        ∫ xi in s, ‖f xi * dirichletPolynomial b D (g xi)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ xi in s, C * ‖f xi‖ := by
      apply MeasureTheory.integral_mono_ae
      · exact hprod.norm.integrableOn
      · exact f.integrable.norm.const_mul C |>.integrableOn
      · filter_upwards with xi
        rw [norm_mul]
        simpa [C, mul_comm] using mul_le_mul_of_nonneg_left
          (norm_dirichletPolynomial_le_coefficientMass b D (g xi))
          (norm_nonneg (f xi))
    _ = C * ∫ xi in s, ‖f xi‖ := by
      rw [MeasureTheory.integral_const_mul]

/-- Exact specialization to the common dyadic detector block.  The two
remaining quantitative inputs are precisely the central Fourier `L¹` mass and
the Fourier-product tail; the conclusion is an actual common-polynomial
witness and the permitted frequency interval. -/
theorem exists_large_commonPolynomial_of_detectorBlock
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {U N : ℕ} (hU : 1 ≤ U) (rho : ℂ) (Y sigma : ℝ)
    (j : Fin (detectorDyadicCount N)) {H A V : ℝ}
    (hA : 0 < A) (hV : 0 < V)
    (hmass : (∫ xi in Set.Icc (-H) H,
        ‖((𝓕 (detectorRealPartCutoff (rho.re - sigma) (2 ^ (j : ℕ))) :
          𝓢(ℝ, ℂ)) xi)‖) ≤ A)
    (htail : ‖∫ xi in (Set.Icc (-H) H)ᶜ,
      ((𝓕 (detectorRealPartCutoff (rho.re - sigma) (2 ^ (j : ℕ))) :
          𝓢(ℝ, ℂ)) xi) *
        dirichletPolynomial
          (detectorCommonCoefficient chi U N Y sigma)
          (2 ^ (j : ℕ)) (-rho.im + 2 * Real.pi * xi)‖ ≤ V / 2)
    (hlarge : V ≤ ‖arithmeticDetectorDyadicBlock chi U N rho Y j‖) :
    ∃ xi ∈ Set.Icc (-H) H,
      V / (4 * A) ≤
        ‖dirichletPolynomial
          (detectorCommonCoefficient chi U N Y sigma)
          (2 ^ (j : ℕ)) (-rho.im + 2 * Real.pi * xi)‖ := by
  let f : ℝ → ℂ := fun xi =>
    (𝓕 (detectorRealPartCutoff (rho.re - sigma) (2 ^ (j : ℕ))) :
      𝓢(ℝ, ℂ)) xi
  let P : ℝ → ℂ := fun xi =>
    dirichletPolynomial
      (detectorCommonCoefficient chi U N Y sigma)
      (2 ^ (j : ℕ)) (-rho.im + 2 * Real.pi * xi)
  have hf : Integrable f := by
    exact (𝓕 (detectorRealPartCutoff
      (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)).integrable
  have hprod : Integrable (fun xi => f xi * P xi) := by
    dsimp [f, P]
    apply integrable_schwartz_mul_dirichletPolynomial
    fun_prop
  have hwhole :
      arithmeticDetectorDyadicBlock chi U N rho Y j =
        ∫ xi, f xi * P xi := by
    simpa [f, P] using arithmeticDetectorDyadicBlock_fourier_removal
      chi hU rho Y sigma j
  apply exists_large_point_of_fourier_integral f P hA hV hprod hf
  · simpa [f] using hmass
  · simpa [f, P] using htail
  · rw [← hwhole]
    exact hlarge

/-- Tail-input form of the detector-block extraction.  It asks only for a
tail estimate on the Fourier kernel itself; the common polynomial is bounded
internally by its explicit finite coefficient mass. -/
theorem exists_large_commonPolynomial_of_detectorBlock_of_kernelTail
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {U N : ℕ} (hU : 1 ≤ U) (rho : ℂ) (Y sigma : ℝ)
    (j : Fin (detectorDyadicCount N)) {H A V : ℝ}
    (hA : 0 < A) (hV : 0 < V)
    (hmass : (∫ xi in Set.Icc (-H) H,
        ‖((𝓕 (detectorRealPartCutoff (rho.re - sigma) (2 ^ (j : ℕ))) :
          𝓢(ℝ, ℂ)) xi)‖) ≤ A)
    (htail :
      (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
          ‖detectorCommonCoefficient chi U N Y sigma n‖) *
        (∫ xi in (Set.Icc (-H) H)ᶜ,
          ‖((𝓕 (detectorRealPartCutoff
            (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤ V / 2)
    (hlarge : V ≤ ‖arithmeticDetectorDyadicBlock chi U N rho Y j‖) :
    ∃ xi ∈ Set.Icc (-H) H,
      V / (4 * A) ≤
        ‖dirichletPolynomial
          (detectorCommonCoefficient chi U N Y sigma)
          (2 ^ (j : ℕ)) (-rho.im + 2 * Real.pi * xi)‖ := by
  apply exists_large_commonPolynomial_of_detectorBlock chi hU rho Y sigma j
    hA hV hmass
  · apply (norm_setIntegral_schwartz_mul_dirichletPolynomial_le
      (𝓕 (detectorRealPartCutoff
        (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ))
      (detectorCommonCoefficient chi U N Y sigma) (2 ^ (j : ℕ))
      (fun xi => -rho.im + 2 * Real.pi * xi) (by fun_prop)
      ((Set.Icc (-H) H)ᶜ)).trans
    exact htail
  · exact hlarge

/-- Simultaneous finite Type-I frequency selection after the common dyadic
block has been chosen.  The dyadic pigeonhole cost remains literal in both the
source block hypothesis and the final denominator. -/
theorem exists_typeI_fourier_assignment
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {U N : ℕ} (hU : 1 ≤ U) (Y sigma : ℝ)
    (j : Fin (detectorDyadicCount N)) (S : Finset ℂ)
    {H A V : ℝ} (hA : 0 < A) (hV : 0 < V)
    (hmass : ∀ rho ∈ S,
      (∫ xi in Set.Icc (-H) H,
        ‖((𝓕 (detectorRealPartCutoff (rho.re - sigma) (2 ^ (j : ℕ))) :
          𝓢(ℝ, ℂ)) xi)‖) ≤ A)
    (htail : ∀ rho ∈ S,
      (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
          ‖detectorCommonCoefficient chi U N Y sigma n‖) *
        (∫ xi in (Set.Icc (-H) H)ᶜ,
          ‖((𝓕 (detectorRealPartCutoff
            (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
          (V / (detectorDyadicCount N : ℝ)) / 2)
    (hblock : ∀ rho ∈ S,
      V ≤ detectorDyadicCount N *
        ‖arithmeticDetectorDyadicBlock chi U N rho Y j‖) :
    ∃ xi : ℂ → ℝ, ∀ rho ∈ S,
      xi rho ∈ Set.Icc (-H) H ∧
      V / (4 * A * detectorDyadicCount N) ≤
        ‖dirichletPolynomial
          (detectorCommonCoefficient chi U N Y sigma)
          (2 ^ (j : ℕ)) (-rho.im + 2 * Real.pi * xi rho)‖ := by
  classical
  have hJnat : 0 < detectorDyadicCount N := by
    unfold detectorDyadicCount
    omega
  have hJ : (0 : ℝ) < detectorDyadicCount N := by exact_mod_cast hJnat
  have hwitness : ∀ rho ∈ S, ∃ x ∈ Set.Icc (-H) H,
      V / (4 * A * detectorDyadicCount N) ≤
        ‖dirichletPolynomial
          (detectorCommonCoefficient chi U N Y sigma)
          (2 ^ (j : ℕ)) (-rho.im + 2 * Real.pi * x)‖ := by
    intro rho hrho
    have hblock' : V / (detectorDyadicCount N : ℝ) ≤
        ‖arithmeticDetectorDyadicBlock chi U N rho Y j‖ := by
      apply (div_le_iff₀ hJ).2
      simpa [mul_comm] using hblock rho hrho
    have hpoint :=
      exists_large_commonPolynomial_of_detectorBlock_of_kernelTail
        chi hU rho Y sigma j hA (div_pos hV hJ)
          (hmass rho hrho) (htail rho hrho) hblock'
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hpoint
  let xi : ℂ → ℝ := fun rho =>
    if hrho : rho ∈ S then Classical.choose (hwitness rho hrho) else 0
  refine ⟨xi, ?_⟩
  intro rho hrho
  dsimp [xi]
  rw [dif_pos hrho]
  exact Classical.choose_spec (hwitness rho hrho)

/-- A genuinely large selected detector shell cannot lie below the mollifier
cutoff.  This supplies the lower dyadic length needed by the powered bridge
without assuming it separately. -/
theorem dyadic_length_lower_of_detectorBlock_large
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {U N : ℕ} (hU : 1 ≤ U) (rho : ℂ) (Y : ℝ)
    (j : Fin (detectorDyadicCount N)) {V : ℝ} (hV : 0 < V)
    (hlarge : V ≤ detectorDyadicCount N *
      ‖arithmeticDetectorDyadicBlock chi U N rho Y j‖) :
    U < 2 * 2 ^ (j : ℕ) := by
  by_contra hnot
  have hupper : 2 * 2 ^ (j : ℕ) ≤ U := Nat.le_of_not_gt hnot
  have hzero : arithmeticDetectorDyadicBlock chi U N rho Y j = 0 := by
    unfold arithmeticDetectorDyadicBlock
    apply Finset.sum_eq_zero
    intro n hn
    have hnfilter := Finset.mem_filter.mp hn
    have hnrange := Finset.mem_Ico.mp hnfilter.1
    have hn2 : 2 ≤ n := by omega
    have hnshell :=
      (log2_sub_one_eq_iff_mem_Ioc hn2).mp hnfilter.2
    have hnupper := (Finset.mem_Ioc.mp hnshell).2
    omega
  rw [hzero, norm_zero, mul_zero] at hlarge
  linarith

/-! ## Weighted extraction for the shifted Type-I ordinates -/

/-- Embed a real ordinate on the imaginary axis, so the certified complex
floor-bin machinery reads the intended real coordinate. -/
def imaginaryLift (t : ℝ) : ℂ := (t : ℂ) * Complex.I

@[simp] theorem imaginaryLift_im (t : ℝ) : (imaginaryLift t).im = t := by
  simp [imaginaryLift]

def liftedOrdinateSet {α : Type*} [DecidableEq α]
    (S : Finset α) (ordinate : α → ℝ) : Finset ℂ :=
  S.image fun x => imaginaryLift (ordinate x)

def liftedOrdinateWeight {α : Type*} [DecidableEq α]
    (S : Finset α) (ordinate : α → ℝ) (weight : α → ℕ) (z : ℂ) : ℕ :=
  ∑ x ∈ S with imaginaryLift (ordinate x) = z, weight x

/-- Aggregating collisions of shifted ordinates loses no multiplicity. -/
theorem sum_liftedOrdinateWeight_eq
    {α : Type*} [DecidableEq α]
    (S : Finset α) (ordinate : α → ℝ) (weight : α → ℕ) :
    ∑ z ∈ liftedOrdinateSet S ordinate,
        liftedOrdinateWeight S ordinate weight z =
      ∑ x ∈ S, weight x := by
  classical
  have hmaps : ∀ x ∈ S,
      imaginaryLift (ordinate x) ∈ liftedOrdinateSet S ordinate := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  simpa [liftedOrdinateWeight] using
    (Finset.sum_fiberwise_of_maps_to hmaps weight)

/-- Collision aggregation also preserves the weight in every individual
shifted floor bin. -/
theorem sum_liftedOrdinateWeight_floorBin_eq
    {α : Type*} [DecidableEq α]
    (S : Finset α) (ordinate : α → ℝ) (weight : α → ℕ) (n : ℤ) :
    ∑ z ∈ liftedOrdinateSet S ordinate with Int.floor z.im = n,
        liftedOrdinateWeight S ordinate weight z =
      ∑ x ∈ S with Int.floor (ordinate x) = n, weight x := by
  classical
  let Sbin : Finset α := S.filter fun x => Int.floor (ordinate x) = n
  let Zbin : Finset ℂ :=
    (liftedOrdinateSet S ordinate).filter fun z => Int.floor z.im = n
  have hmaps : ∀ x ∈ Sbin, imaginaryLift (ordinate x) ∈ Zbin := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨x, hx'.1, rfl⟩, ?_⟩
    simpa using hx'.2
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps weight
  have hinter : ∀ z ∈ Zbin,
      (∑ x ∈ Sbin with imaginaryLift (ordinate x) = z, weight x) =
        liftedOrdinateWeight S ordinate weight z := by
    intro z hz
    have hzn : Int.floor z.im = n := (Finset.mem_filter.mp hz).2
    unfold liftedOrdinateWeight
    apply Finset.sum_subset
    · intro x hx
      have hx' := Finset.mem_filter.mp hx
      have hxbin := Finset.mem_filter.mp hx'.1
      exact Finset.mem_filter.mpr ⟨hxbin.1, hx'.2⟩
    · intro x hxS hxnot
      have hxeq : imaginaryLift (ordinate x) = z :=
        (Finset.mem_filter.mp hxS).2
      exfalso
      apply hxnot
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hxS).1, ?_⟩, hxeq⟩
      rw [← hxeq] at hzn
      simpa using hzn
  calc
    ∑ z ∈ liftedOrdinateSet S ordinate with Int.floor z.im = n,
        liftedOrdinateWeight S ordinate weight z =
      ∑ z ∈ Zbin, liftedOrdinateWeight S ordinate weight z := by
        rfl
    _ = ∑ z ∈ Zbin,
        ∑ x ∈ Sbin with imaginaryLift (ordinate x) = z, weight x := by
          apply Finset.sum_congr rfl
          intro z hz
          exact (hinter z hz).symm
    _ = ∑ x ∈ Sbin, weight x := hfiber
    _ = ∑ x ∈ S with Int.floor (ordinate x) = n, weight x := by rfl

/-- Integer floor bins in which an original ordinate can lie after a shift of
absolute value at most `C` lands in target floor bin `n`. -/
def shiftedFloorWindow (C : ℝ) (n : ℤ) : Finset ℤ :=
  Finset.Icc (Int.floor ((-C - 1) - (n : ℝ)))
    (Int.floor (C - (n : ℝ)))

def shiftedFloorWindowCount (C : ℝ) : ℕ :=
  (shiftedFloorWindow C 0).card

theorem shiftedFloorWindow_card (C : ℝ) (n : ℤ) :
    (shiftedFloorWindow C n).card = shiftedFloorWindowCount C := by
  simp [shiftedFloorWindow, shiftedFloorWindowCount,
    Int.floor_sub_intCast, Int.card_Icc]
  congr 1
  ring

theorem floor_source_mem_shiftedFloorWindow
    {gamma shift ordinate C : ℝ} {n : ℤ}
    (hordinate : ordinate = -gamma + shift)
    (hshift : |shift| ≤ C) (hfloor : Int.floor ordinate = n) :
    Int.floor gamma ∈ shiftedFloorWindow C n := by
  have htlow : (n : ℝ) ≤ ordinate := by
    rw [← hfloor]
    exact Int.floor_le ordinate
  have hthi : ordinate < (n : ℝ) + 1 := by
    rw [← hfloor]
    exact Int.lt_floor_add_one ordinate
  have hs := abs_le.mp hshift
  have hglow : (-C - 1) - (n : ℝ) ≤ gamma := by
    rw [hordinate] at htlow hthi
    linarith
  have hghi : gamma ≤ C - (n : ℝ) := by
    rw [hordinate] at htlow hthi
    linarith
  rw [shiftedFloorWindow, Finset.mem_Icc]
  exact ⟨Int.floor_mono hglow, Int.floor_mono hghi⟩

/-- A bounded shift enlarges a uniform source floor-bin weight cap only by
the explicit number of source bins intersecting one target bin. -/
theorem shifted_floorBin_weight_le
    {α : Type*} [DecidableEq α]
    (S : Finset α) (gamma shift : α → ℝ) (weight : α → ℕ)
    {C M : ℕ} (hshift : ∀ x ∈ S, |shift x| ≤ C)
    (hsource : ∀ m : ℤ,
      ∑ x ∈ S with Int.floor (gamma x) = m, weight x ≤ M)
    (n : ℤ) :
    ∑ x ∈ S with Int.floor (-gamma x + shift x) = n, weight x ≤
      shiftedFloorWindowCount C * M := by
  classical
  let Tbin : Finset α :=
    S.filter fun x => Int.floor (-gamma x + shift x) = n
  have hmaps : ∀ x ∈ Tbin,
      Int.floor (gamma x) ∈ shiftedFloorWindow C n := by
    intro x hx
    exact floor_source_mem_shiftedFloorWindow rfl
      (hshift x (Finset.mem_filter.mp hx).1)
      (Finset.mem_filter.mp hx).2
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps weight
  rw [← hfiber]
  calc
    ∑ m ∈ shiftedFloorWindow C n,
        ∑ x ∈ Tbin with Int.floor (gamma x) = m, weight x ≤
      ∑ _m ∈ shiftedFloorWindow C n, M := by
        apply Finset.sum_le_sum
        intro m hm
        apply (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_).trans (hsource m)
        · intro x hx
          have hx' := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp hx'.1).1, hx'.2⟩
        · intro x hxS hxnot
          positivity
    _ = (shiftedFloorWindow C n).card * M := by simp
    _ = shiftedFloorWindowCount C * M := by rw [shiftedFloorWindow_card]

/-- Weighted parity extraction for an arbitrary shifted-ordinate map.  The
floor-bin premise is stated after collision aggregation, exactly the quantity
that a crowding argument must bound. -/
theorem exists_oneSeparated_shiftedOrdinates_of_liftedFloorCap
    {α : Type*} [DecidableEq α]
    (S : Finset α) (ordinate : α → ℝ) (weight : α → ℕ) (L : ℕ)
    (hcap : ∀ n ∈ occupiedFloorBins (liftedOrdinateSet S ordinate),
      ∑ z ∈ liftedOrdinateSet S ordinate with Int.floor z.im = n,
        liftedOrdinateWeight S ordinate weight z ≤ L) :
    ∃ W : Finset ℝ,
      W ⊆ S.image ordinate ∧ OneSeparated W ∧
      ∑ x ∈ S, weight x ≤ 2 * L * W.card := by
  classical
  obtain ⟨Z', hZ', hsep, hcard, hweight⟩ :=
    exists_oneSeparated_ordinates_of_floorBin_weight_cap
      (liftedOrdinateSet S ordinate)
      (liftedOrdinateWeight S ordinate weight) L hcap
  let W : Finset ℝ := Z'.image Complex.im
  refine ⟨W, ?_, ?_, ?_⟩
  · intro t ht
    change t ∈ Z'.image Complex.im at ht
    rw [Finset.mem_image] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    have hzlift : z ∈ liftedOrdinateSet S ordinate := hZ' hz
    rw [liftedOrdinateSet, Finset.mem_image] at hzlift
    obtain ⟨x, hx, hxz⟩ := hzlift
    apply Finset.mem_image.mpr
    refine ⟨x, hx, ?_⟩
    rw [← hxz]
    exact (imaginaryLift_im _).symm
  · simpa [W] using hsep
  · rw [← sum_liftedOrdinateWeight_eq S ordinate weight]
    simpa [W, hcard] using hweight

/-- Complete weighted crowding adapter for bounded Type-I Fourier shifts.
A source unit-bin cap `M` becomes a target cap by the explicit interval-cover
factor `shiftedFloorWindowCount C`, after which parity thinning supplies an
actual one-separated set. -/
theorem exists_oneSeparated_boundedShiftedOrdinates
    {α : Type*} [DecidableEq α]
    (S : Finset α) (gamma shift : α → ℝ) (weight : α → ℕ)
    {C M : ℕ} (hshift : ∀ x ∈ S, |shift x| ≤ C)
    (hsource : ∀ m : ℤ,
      ∑ x ∈ S with Int.floor (gamma x) = m, weight x ≤ M) :
    ∃ W : Finset ℝ,
      W ⊆ S.image (fun x => -gamma x + shift x) ∧
      OneSeparated W ∧
      ∑ x ∈ S, weight x ≤
        2 * (shiftedFloorWindowCount C * M) * W.card := by
  apply exists_oneSeparated_shiftedOrdinates_of_liftedFloorCap
    S (fun x => -gamma x + shift x) weight
      (shiftedFloorWindowCount C * M)
  intro n hn
  rw [sum_liftedOrdinateWeight_floorBin_eq]
  exact shifted_floorBin_weight_le S gamma shift weight hshift hsource n

/-- End-to-end deterministic Type-I extraction: common-block Fourier
selection, bounded-shift crowding, and weighted parity thinning.  The output
is an actual one-separated common-polynomial witness set. -/
theorem exists_typeI_commonPolynomial_oneSeparated
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {U N : ℕ} (hU : 1 ≤ U) (Y sigma : ℝ)
    (j : Fin (detectorDyadicCount N)) (S : Finset ℂ)
    (weight : ℂ → ℕ) {H A V : ℝ} {C M : ℕ}
    (hC : 2 * Real.pi * H ≤ C)
    (hA : 0 < A) (hV : 0 < V)
    (hmass : ∀ rho ∈ S,
      (∫ xi in Set.Icc (-H) H,
        ‖((𝓕 (detectorRealPartCutoff (rho.re - sigma) (2 ^ (j : ℕ))) :
          𝓢(ℝ, ℂ)) xi)‖) ≤ A)
    (htail : ∀ rho ∈ S,
      (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
          ‖detectorCommonCoefficient chi U N Y sigma n‖) *
        (∫ xi in (Set.Icc (-H) H)ᶜ,
          ‖((𝓕 (detectorRealPartCutoff
            (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
          (V / (detectorDyadicCount N : ℝ)) / 2)
    (hblock : ∀ rho ∈ S,
      V ≤ detectorDyadicCount N *
        ‖arithmeticDetectorDyadicBlock chi U N rho Y j‖)
    (hsource : ∀ m : ℤ,
      ∑ rho ∈ S with Int.floor rho.im = m, weight rho ≤ M) :
    ∃ (xi : ℂ → ℝ) (W : Finset ℝ),
      (∀ rho ∈ S,
        xi rho ∈ Set.Icc (-H) H ∧
        V / (4 * A * detectorDyadicCount N) ≤
          ‖dirichletPolynomial
            (detectorCommonCoefficient chi U N Y sigma)
            (2 ^ (j : ℕ)) (-rho.im + 2 * Real.pi * xi rho)‖) ∧
      W ⊆ S.image (fun rho => -rho.im + 2 * Real.pi * xi rho) ∧
      OneSeparated W ∧
      (∀ t ∈ W,
        V / (4 * A * detectorDyadicCount N) ≤
          ‖dirichletPolynomial
            (detectorCommonCoefficient chi U N Y sigma)
            (2 ^ (j : ℕ)) t‖) ∧
      ∑ rho ∈ S, weight rho ≤
        2 * (shiftedFloorWindowCount C * M) * W.card := by
  classical
  obtain ⟨xi, hxi⟩ := exists_typeI_fourier_assignment
    chi hU Y sigma j S hA hV hmass htail hblock
  have hshift : ∀ rho ∈ S, |2 * Real.pi * xi rho| ≤ C := by
    intro rho hrho
    have hxabs : |xi rho| ≤ H := (abs_le).2 (hxi rho hrho).1
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos Real.pi_pos]
    exact (mul_le_mul_of_nonneg_left hxabs (by positivity)).trans hC
  obtain ⟨W, hWsub, hWsep, hWweight⟩ :=
    exists_oneSeparated_boundedShiftedOrdinates S Complex.im
      (fun rho => 2 * Real.pi * xi rho) weight hshift hsource
  refine ⟨xi, W, hxi, hWsub, hWsep, ?_, hWweight⟩
  intro t ht
  obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp (hWsub ht)
  exact (hxi rho hrho).2

end

end PostA5TypeIFourierAssembly

#print axioms PostA5TypeIFourierAssembly.exists_large_point_of_central_fourier_mass
#print axioms PostA5TypeIFourierAssembly.norm_detectorCommonCoefficient_le
#print axioms PostA5TypeIFourierAssembly.detectorCommonCoefficientMass_le
#print axioms PostA5TypeIFourierAssembly.detectorRealPartCutoff_translate
#print axioms PostA5TypeIFourierAssembly.norm_fourier_detectorRealPartCutoff_eq
#print axioms PostA5TypeIFourierAssembly.integral_norm_iteratedDeriv_detectorRealPartCutoff_base_le
#print axioms PostA5TypeIFourierAssembly.seminorm_fourier_detectorRealPartCutoff_base_le
#print axioms PostA5TypeIFourierAssembly.integral_pow_mul_norm_fourier_detectorRealPartCutoff_le
#print axioms PostA5TypeIFourierAssembly.integral_norm_fourier_detectorRealPartCutoff_Icc_le
#print axioms PostA5TypeIFourierAssembly.integral_compl_Icc_norm_fourier_le_inv_pow_mul
#print axioms PostA5TypeIFourierAssembly.integral_compl_Icc_norm_fourier_detectorRealPartCutoff_le
#print axioms PostA5TypeIFourierAssembly.exists_large_point_of_fourier_integral
#print axioms PostA5TypeIFourierAssembly.exists_large_commonPolynomial_of_detectorBlock
#print axioms PostA5TypeIFourierAssembly.exists_large_commonPolynomial_of_detectorBlock_of_kernelTail
#print axioms PostA5TypeIFourierAssembly.exists_typeI_fourier_assignment
#print axioms PostA5TypeIFourierAssembly.dyadic_length_lower_of_detectorBlock_large
#print axioms PostA5TypeIFourierAssembly.exists_oneSeparated_shiftedOrdinates_of_liftedFloorCap
#print axioms PostA5TypeIFourierAssembly.exists_oneSeparated_boundedShiftedOrdinates
#print axioms PostA5TypeIFourierAssembly.exists_typeI_commonPolynomial_oneSeparated
