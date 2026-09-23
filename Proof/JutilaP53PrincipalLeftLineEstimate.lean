import JutilaP53PrincipalDiagonalResidue
import BHPPrincipalNormalizedGaussian
import JutilaPolynomialExponentialIntegral

/-!
# Principal p.53 shifted-line envelope away from the crossed pole
-/

namespace MAPJutilaP53PrincipalLeftLineEstimate

open Complex Real MeasureTheory Set Filter Topology
open DirichletZeros
open MAPJutilaP53TwoScaleContour
open MAPJutilaP53LeftLineEstimate
open MAPJutilaP53PrincipalFinitePole
open MAPGammaCompactStripSharp
open MAPPrincipalZetaFixedStrip
open MAPBHPPrincipalNegativeEulerBound
open MAPPrimitiveLFixedStrip

noncomputable section

/-- On the nonnegative half-plane each missing Euler factor has norm at most
`2`. -/
theorem norm_trivialEulerCorrection_le_twoPow
    {q : ℕ} {z : ℂ} (hz : 0 ≤ z.re) :
    ‖trivialEulerCorrection q z‖ ≤ (2 : ℝ) ^ q.primeFactors.card := by
  unfold trivialEulerCorrection
  rw [norm_prod]
  calc
    _ ≤ ∏ _p ∈ q.primeFactors, (2 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro p hp
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
      have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_le
      have hpow : ‖(p : ℂ) ^ (-z)‖ = (p : ℝ) ^ (-z.re) := by
        change ‖((p : ℝ) : ℂ) ^ (-z)‖ = (p : ℝ) ^ (-z.re)
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hpPos]
        congr 1
      have hpowOne : (p : ℝ) ^ (-z.re) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hpOne (by linarith)
      calc
        ‖1 - (p : ℂ) ^ (-z)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-z)‖ :=
          norm_sub_le _ _
        _ = 1 + (p : ℝ) ^ (-z.re) := by rw [norm_one, hpow]
        _ ≤ 2 := by linarith
    _ = _ := by simp

/-- Exact conductor-one factorization of the ambient principal entire patch,
valid off the patched point. -/
theorem regularizedLFunction_principal_eq_zeta_mul_euler
    (q : ℕ) [NeZero q] {z : ℂ} (hz1 : z ≠ 1) :
    regularizedLFunction (1 : DirichletCharacter ℂ q) z =
      principalRegularized z * trivialEulerCorrection q z := by
  unfold regularizedLFunction principalRegularized
  simp only [if_pos]
  unfold DirichletCharacter.LFunctionTrivChar₁
  rw [Function.update_of_ne hz1, Function.update_of_ne hz1,
    DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hz1,
    DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hz1]
  simp only [Nat.primeFactors_one, Finset.prod_empty,
    one_mul]
  unfold trivialEulerCorrection
  ring

theorem norm_regularized_principal_fixedStrip_le_twoPow
    (q : ℕ) [NeZero q] {z : ℂ} (hzLo : 0 ≤ z.re) (hzHi : z.re ≤ 2) :
    ‖regularizedLFunction (1 : DirichletCharacter ℂ q) z‖ ≤
      1600 * ‖z + 3‖ ^ 6 * (2 : ℝ) ^ q.primeFactors.card := by
  by_cases hz1 : z = 1
  · subst z
    have h := MAPBHPPrincipalResidueBound.norm_regularized_principal_one_le_one q
    calc
      _ ≤ 1 := h
      _ ≤ 1600 * ‖(1 : ℂ) + 3‖ ^ 6 *
          (2 : ℝ) ^ q.primeFactors.card := by
        have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ q.primeFactors.card :=
          one_le_pow₀ (by norm_num)
        norm_num
        nlinarith
  · rw [regularizedLFunction_principal_eq_zeta_mul_euler q hz1, norm_mul]
    exact mul_le_mul
      (norm_principalRegularized_fixedStrip_le (by linarith) hzHi)
      (norm_trivialEulerCorrection_le_twoPow hzLo)
      (norm_nonneg _) (by positivity)

/-- Polynomial bound for the principal L-function on the p.53 left line.
The strict collar margin `Re s≤1/4` leaves distance at least `1/4` from the
pole. -/
theorem norm_principal_LFunction_leftHalf_le
    (q : ℕ) [NeZero q] {s : ℂ} (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 4)
    (t : ℝ) :
    ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
      (1 + s + (((-(1 / 2 : ℝ)) : ℂ) + t * I))‖ ≤
      6400 * (2 : ℝ) ^ q.primeFactors.card *
        (5 + |s.im| + |t|) ^ 6 := by
  let z : ℂ := 1 + s + (((-(1 / 2 : ℝ)) : ℂ) + t * I)
  have hzRe : z.re = 1 / 2 + s.re := by simp [z]; ring
  have hz1 : z ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hzRe] at hre
    norm_num at hre
    linarith
  have hregEq : regularizedLFunction (1 : DirichletCharacter ℂ q) z =
      (z - 1) * DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ q) z := by
    unfold regularizedLFunction
    simp only [if_pos]
    unfold DirichletCharacter.LFunctionTrivChar₁
    rw [Function.update_of_ne hz1]
  have hden : (1 / 4 : ℝ) ≤ ‖z - 1‖ := by
    have hzsubRe : (z - 1).re = s.re - 1 / 2 := by
      rw [Complex.sub_re, hzRe]
      norm_num
      ring
    calc
      (1 / 4 : ℝ) ≤ |(z - 1).re| := by
        rw [abs_of_nonpos]
        · rw [hzsubRe]
          linarith
        · rw [hzsubRe]
          linarith
      _ ≤ ‖z - 1‖ := Complex.abs_re_le_norm _
  have hregZeta := norm_principalRegularized_fixedStrip_le
    (z := z) (by rw [hzRe]; linarith) (by rw [hzRe]; linarith)
  have heuler := norm_trivialEulerCorrection_le_twoPow
    (q := q) (z := z) (by rw [hzRe]; linarith)
  have hreg := regularizedLFunction_principal_eq_zeta_mul_euler q hz1
  have hzNorm : ‖z + 3‖ ≤ 5 + |s.im| + |t| := by
    calc
      ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |7 / 2 + s.re| + |s.im + t| := by simp [z]; ring_nf
      _ ≤ 5 + (|s.im| + |t|) := by
        rw [abs_of_nonneg (by linarith)]
        exact add_le_add (by linarith) (abs_add_le _ _)
      _ = _ := by ring
  have hregBound : ‖regularizedLFunction
      (1 : DirichletCharacter ℂ q) z‖ ≤
      1600 * (5 + |s.im| + |t|) ^ 6 *
        (2 : ℝ) ^ q.primeFactors.card := by
    rw [hreg, norm_mul]
    calc
      _ ≤ (1600 * ‖z + 3‖ ^ 6) * (2 : ℝ) ^ q.primeFactors.card :=
        mul_le_mul hregZeta heuler (norm_nonneg _) (by positivity)
      _ ≤ _ := by gcongr
  rw [hregEq, norm_mul] at hregBound
  have hdenPos : 0 < ‖z - 1‖ := lt_of_lt_of_le (by norm_num) hden
  change ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z‖ ≤ _
  calc
    ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z‖ =
        4 * ((1 / 4 : ℝ) *
          ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z‖) := by ring
    _ ≤ 4 * (‖z - 1‖ *
          ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z‖) := by
      gcongr
    _ ≤ 4 * (1600 * (5 + |s.im| + |t|) ^ 6 *
        (2 : ℝ) ^ q.primeFactors.card) := by gcongr
    _ = _ := by ring

/-- Uniform principal L-bound along either high horizontal edge of the full
p.53 rectangle.  The lower bound on `B` separates the edge from the crossed
pole by at least one. -/
theorem norm_principal_LFunction_horizontal_le
    (q : ℕ) [NeZero q] {s : ℂ} (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 4)
    {x B epsilon : ℝ} (hxLo : -(1 / 2) ≤ x) (hxHi : x ≤ 1)
    (hB : 2 * (1 + |s.im|) ≤ B) (hepsilon : |epsilon| = 1) :
    ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
      (1 + s + ((x : ℂ) + (epsilon * B) * I))‖ ≤
      1600 * (2 : ℝ) ^ q.primeFactors.card *
        (7 + |s.im| + B) ^ 6 := by
  let z : ℂ := 1 + s + ((x : ℂ) + (epsilon * B) * I)
  have hB0 : 0 ≤ B := by linarith [abs_nonneg s.im]
  have hzRe : z.re = 1 + s.re + x := by simp [z]
  have hzIm : z.im = s.im + epsilon * B := by simp [z]
  have hzNorm : ‖z + 3‖ ≤ 7 + |s.im| + B := by
    calc
      ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |4 + s.re + x| + |s.im + epsilon * B| := by simp [z]; ring
      _ ≤ (6 : ℝ) + (|s.im| + B) := by
        have hre0 : 0 ≤ 4 + s.re + x := by linarith
        rw [abs_of_nonneg hre0]
        have him := abs_add_le s.im (epsilon * B)
        rw [abs_mul, hepsilon, one_mul, abs_of_nonneg hB0] at him
        linarith
      _ ≤ 7 + |s.im| + B := by linarith
  by_cases hzHi : z.re ≤ 2
  · have hzLo : 0 ≤ z.re := by rw [hzRe]; linarith
    have hz1 : z ≠ 1 := by
      intro hzOne
      have himOne := congrArg Complex.im hzOne
      rw [hzIm] at himOne
      simp only [one_im] at himOne
      have hsep : 1 ≤ |s.im + epsilon * B| := by
        have htri : B ≤ |s.im + epsilon * B| + |s.im| := by
          calc
            B = |epsilon * B| := by
              rw [abs_mul, hepsilon, one_mul, abs_of_nonneg hB0]
            _ = |(s.im + epsilon * B) - s.im| := by ring_nf
            _ ≤ |s.im + epsilon * B| + |s.im| := abs_sub _ _
        linarith
      rw [himOne, abs_zero] at hsep
      norm_num at hsep
    have hregEq : regularizedLFunction (1 : DirichletCharacter ℂ q) z =
        (z - 1) * DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ q) z := by
      unfold regularizedLFunction
      simp only [if_pos]
      unfold DirichletCharacter.LFunctionTrivChar₁
      rw [Function.update_of_ne hz1]
    have hden : 1 ≤ ‖z - 1‖ := by
      have him : 1 ≤ |z.im| := by
        rw [hzIm]
        have htri : B ≤ |s.im + epsilon * B| + |s.im| := by
          calc
            B = |epsilon * B| := by
              rw [abs_mul, hepsilon, one_mul, abs_of_nonneg hB0]
            _ = |(s.im + epsilon * B) - s.im| := by ring_nf
            _ ≤ |s.im + epsilon * B| + |s.im| := abs_sub _ _
        linarith
      exact him.trans (by simpa using Complex.abs_im_le_norm (z - 1))
    have hreg := norm_regularized_principal_fixedStrip_le_twoPow q hzLo hzHi
    rw [hregEq, norm_mul] at hreg
    change ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z‖ ≤ _
    calc
      _ ≤ ‖z - 1‖ * ‖DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ q) z‖ := by
        nlinarith [norm_nonneg (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ q) z)]
      _ ≤ 1600 * ‖z + 3‖ ^ 6 * (2 : ℝ) ^ q.primeFactors.card := hreg
      _ ≤ 1600 * (7 + |s.im| + B) ^ 6 *
          (2 : ℝ) ^ q.primeFactors.card := by gcongr
      _ = _ := by ring
  · have hL := (norm_LFunction_lt_three_of_two_le_re
        (1 : DirichletCharacter ℂ q) (le_of_not_ge hzHi)).le
    change ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z‖ ≤ _
    calc
      _ ≤ 3 := hL
      _ ≤ 1600 * (2 : ℝ) ^ q.primeFactors.card *
          (7 + |s.im| + B) ^ 6 := by
        have hbase : 1 ≤ 7 + |s.im| + B := by linarith [abs_nonneg s.im]
        have hpow : 1 ≤ (7 + |s.im| + B) ^ 6 := one_le_pow₀ hbase
        have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ q.primeFactors.card :=
          one_le_pow₀ (by norm_num)
        calc
          (3 : ℝ) ≤ 1600 := by norm_num
          _ ≤ 1600 * (2 : ℝ) ^ q.primeFactors.card := by nlinarith
          _ ≤ 1600 * (2 : ℝ) ^ q.primeFactors.card *
              (7 + |s.im| + B) ^ 6 := by
            have hcoef0 : 0 ≤ 1600 * (2 : ℝ) ^ q.primeFactors.card :=
              mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _)
            simpa using mul_le_mul_of_nonneg_left hpow hcoef0

theorem norm_p53PrincipalIntegrand_horizontal_le
    (q : ℕ) [NeZero q] (s : ℂ) {U V x B epsilon : ℝ}
    (hU : 0 < U) (hV : 0 < V)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 4)
    (hxLo : -(1 / 2) ≤ x) (hxHi : x ≤ 1)
    (hB : 2 * (1 + |s.im|) ≤ B) (hepsilon : |epsilon| = 1) :
    ‖p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
      ((x : ℂ) + (epsilon * B) * I)‖ ≤
      19200 * (2 : ℝ) ^ q.primeFactors.card * (1 + B) ^ 2 *
        (7 + |s.im| + B) ^ 6 * Real.exp (-(Real.pi / 2) * B) *
        p53CpowEndpointBound U V (-(1 / 2)) 1 := by
  let t := epsilon * B
  let w : ℂ := (x : ℂ) + t * I
  have hB0 : 0 ≤ B := by linarith [abs_nonneg s.im]
  have htAbs : |t| = B := by
    dsimp [t]
    rw [abs_mul, hepsilon, one_mul, abs_of_nonneg hB0]
  have ht : 1 ≤ |t| := by rw [htAbs]; linarith [abs_nonneg s.im]
  have hGamma : ‖Complex.Gamma (w + 1)‖ ≤
      12 * (1 + B) ^ 2 * Real.exp (-(Real.pi / 2) * B) := by
    by_cases hx : x ≤ 1 / 2
    · have hp := norm_Gamma_positive_strip_le_exp_pi_half
        (a := 1 + x) (t := t) (by linarith) (by linarith)
      have hpoint : w + 1 = GammaCompactStripScratch.stripPoint (1 + x) t := by
        apply Complex.ext <;> simp [w, GammaCompactStripScratch.stripPoint]
        ring
      rw [← hpoint, htAbs] at hp
      exact hp.trans (by
        have hfac : 1 + B ≤ (1 + B) ^ 2 := by nlinarith
        have hexp0 := (Real.exp_pos (-(Real.pi / 2) * B)).le
        nlinarith)
    · have hx' : 1 / 2 ≤ x := le_of_not_ge hx
      have hw : w ≠ 0 := by
        intro hw
        have hre := congrArg Complex.re hw
        simp [w] at hre
        linarith
      have hp := norm_Gamma_positive_strip_le_exp_pi_half
        (a := x) (t := t) hx' (hxHi.trans (by norm_num))
      have hpoint : w = GammaCompactStripScratch.stripPoint x t := by
        apply Complex.ext <;> simp [w, GammaCompactStripScratch.stripPoint]
      rw [← hpoint, htAbs] at hp
      have hwNorm : ‖w‖ ≤ 1 + B := by
        calc
          ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im _
          _ = |x| + B := by simp [w, htAbs]
          _ ≤ 1 + B := by
            have habsx : |x| ≤ 1 := abs_le.mpr ⟨by linarith, hxHi⟩
            linarith
      rw [Complex.Gamma_add_one w hw, norm_mul]
      calc
        ‖w‖ * ‖Complex.Gamma w‖ ≤
            (1 + B) * (12 * (1 + B) *
              Real.exp (-(Real.pi / 2) * B)) := by gcongr
        _ = _ := by ring
  have hQ := norm_p53ScaleRemovableQuotient_horizontal_le hU hV
    (a := -(1 / 2)) (b := 1) (x := x) (t := t) hxLo hxHi ht
  have hL := norm_principal_LFunction_horizontal_le q hsLo hsHi hxLo hxHi
    hB hepsilon
  have hGamma' : ‖Complex.Gamma
      ((x : ℂ) + (epsilon * B) * I + 1)‖ ≤
      12 * (1 + B) ^ 2 * Real.exp (-(Real.pi / 2) * B) := by
    simpa [w, t] using hGamma
  have hQ' : ‖p53ScaleRemovableQuotient U V
      ((x : ℂ) + (epsilon * B) * I)‖ ≤
      p53CpowEndpointBound U V (-(1 / 2)) 1 := by
    simpa [t] using hQ
  have hnonneg : 0 ≤
      12 * (1 + B) ^ 2 * Real.exp (-(Real.pi / 2) * B) *
        p53CpowEndpointBound U V (-(1 / 2)) 1 := by
    exact mul_nonneg (by positivity)
      (p53CpowEndpointBound_nonneg hU hV _ _)
  unfold p53TwoScaleContourIntegrand
  simp only [norm_mul]
  calc
    _ ≤ (12 * (1 + B) ^ 2 * Real.exp (-(Real.pi / 2) * B)) *
        p53CpowEndpointBound U V (-(1 / 2)) 1 *
        (1600 * (2 : ℝ) ^ q.primeFactors.card *
          (7 + |s.im| + B) ^ 6) := by
      exact mul_le_mul
        (mul_le_mul hGamma' hQ' (norm_nonneg _) (by positivity)) hL
        (norm_nonneg _) hnonneg
    _ = _ := by ring

theorem tendsto_p53PrincipalFullHorizontalIntegral_zero
    (q : ℕ) [NeZero q] (s : ℂ) {U V epsilon : ℝ}
    (hU : 0 < U) (hV : 0 < V)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 4)
    (hepsilon : |epsilon| = 1) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in -(1 / 2)..1,
        p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
          ((x : ℂ) + (epsilon * B) * I)) atTop (𝓝 0) := by
  let C : ℝ := 7 + |s.im|
  let P : ℝ := p53CpowEndpointBound U V (-(1 / 2)) 1
  let K : ℝ := 19200 * (2 : ℝ) ^ q.primeFactors.card * C ^ 6 * P
  let E : ℝ → ℝ := fun B => K * ((1 + B) ^ 8 * Real.exp (-B))
  have hE : Tendsto E atTop (𝓝 0) := by
    have hshift : Tendsto (fun B : ℝ => 1 + B) atTop atTop :=
      Filter.tendsto_atTop_add_const_left atTop 1 tendsto_id
    have hcore := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 8).comp hshift
    have hscaled := hcore.const_mul (K * Real.exp 1)
    have hscaled' : Tendsto (fun B : ℝ =>
        (K * Real.exp 1) * ((1 + B) ^ 8 * Real.exp (-(1 + B))))
        atTop (𝓝 0) := by
      simpa only [Function.comp_apply, mul_zero] using hscaled
    convert hscaled' using 1
    funext B
    dsimp [E]
    have hexp : Real.exp 1 * Real.exp (-(1 + B)) = Real.exp (-B) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hexp]
    ring
  have hbound : ∀ᶠ B : ℝ in atTop,
      ‖∫ x : ℝ in -(1 / 2)..1,
        p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
          ((x : ℂ) + (epsilon * B) * I)‖ ≤
        E B * |(1 : ℝ) - (-(1 / 2))| := by
    filter_upwards [eventually_ge_atTop (max 1 (2 * (1 + |s.im|)))] with B hB
    have hBone : 1 ≤ B := (le_max_left _ _).trans hB
    have hBsep : 2 * (1 + |s.im|) ≤ B := (le_max_right _ _).trans hB
    have hB0 : 0 ≤ B := by linarith
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc (-(1 / 2 : ℝ)) 1 := by
      have := Set.uIoc_subset_uIcc hx
      rw [Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1)] at this
      exact this
    have hpoint := norm_p53PrincipalIntegrand_horizontal_le q s hU hV
      hsLo hsHi hx'.1 hx'.2 hBsep hepsilon
    have hC : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg s.im]
    have hCB : C + B ≤ C * (1 + B) := by nlinarith
    have hpow : (C + B) ^ 6 ≤ C ^ 6 * (1 + B) ^ 6 := by
      calc
        _ ≤ (C * (1 + B)) ^ 6 := pow_le_pow_left₀ (by positivity) hCB 6
        _ = _ := by ring
    have hexp : Real.exp (-(Real.pi / 2) * B) ≤ Real.exp (-B) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_gt_three]
    have hP : 0 ≤ P := by
      dsimp [P]
      exact p53CpowEndpointBound_nonneg hU hV _ _
    calc
      _ ≤ 19200 * (2 : ℝ) ^ q.primeFactors.card * (1 + B) ^ 2 *
          (C + B) ^ 6 * Real.exp (-(Real.pi / 2) * B) * P := by
        simpa [C, P] using hpoint
      _ ≤ 19200 * (2 : ℝ) ^ q.primeFactors.card * (1 + B) ^ 2 *
          (C ^ 6 * (1 + B) ^ 6) * Real.exp (-B) * P := by gcongr
      _ = E B := by dsimp [E, K]; ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · exact hbound
  · simpa using hE.mul_const |(1 : ℝ) - (-(1 / 2))|

/-- Full principal left-line envelope with a certified margin from the pole. -/
theorem norm_p53PrincipalIntegrand_leftHalf_le
    (q : ℕ) [NeZero q] (s : ℂ) {U V t : ℝ}
    (hU : 0 < U) (hV : 0 < V)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 4) :
    ‖p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
      (((-(1 / 2 : ℝ)) : ℂ) + t * I)‖ ≤
      153600 * (2 : ℝ) ^ q.primeFactors.card *
        (1 + |t|) * (5 + |s.im| + |t|) ^ 6 *
        Real.exp (-(Real.pi / 2) * |t|) *
        p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2)) := by
  let w : ℂ := (((-(1 / 2 : ℝ)) : ℂ) + t * I)
  have hGammaPoint : w + 1 =
      GammaCompactStripScratch.stripPoint (1 / 2) t := by
    apply Complex.ext <;> simp [w, GammaCompactStripScratch.stripPoint] <;>
      norm_num
  have hGamma := norm_Gamma_positive_strip_le_exp_pi_half
    (show (1 / 2 : ℝ) ≤ 1 / 2 by rfl)
    (show (1 / 2 : ℝ) ≤ 3 / 2 by norm_num) (t := t)
  rw [← hGammaPoint] at hGamma
  have hQ := norm_p53ScaleRemovableQuotient_leftHalf_le hU hV (t := t)
  have hL := norm_principal_LFunction_leftHalf_le q hsLo hsHi t
  have hP := p53CpowEndpointBound_nonneg hU hV (-(1 / 2)) (-(1 / 2))
  unfold p53TwoScaleContourIntegrand
  simp only [norm_mul]
  calc
    _ ≤ (12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) *
        (2 * p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2))) *
        (6400 * (2 : ℝ) ^ q.primeFactors.card *
          (5 + |s.im| + |t|) ^ 6) := by gcongr
    _ = _ := by ring

def p53PrincipalUniversalVerticalMass : ℝ :=
  ∫ t : ℝ, (1 + |t|) ^ 7 * Real.exp (-|t|)

theorem integrable_p53PrincipalIntegrand_leftHalf
    (q : ℕ) [NeZero q] (s : ℂ) {U V : ℝ}
    (hU : 0 < U) (hV : 0 < V)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 4) :
    Integrable (fun t : ℝ =>
      p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
        (((-(1 / 2 : ℝ)) : ℂ) + t * I)) := by
  let F : ℝ → ℂ := fun t =>
    p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
      (((-(1 / 2 : ℝ)) : ℂ) + t * I)
  let C : ℝ := 5 + |s.im|
  let K : ℝ := 153600 * (2 : ℝ) ^ q.primeFactors.card * C ^ 6 *
    p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2))
  let E : ℝ → ℝ := fun t => K * ((1 + |t|) ^ 7 * Real.exp (-|t|))
  have hEbase : Integrable (fun t : ℝ =>
      (1 + |t|) ^ 7 * Real.exp (-|t|)) := by
    have h := JutilaPolynomialExponentialIntegral.integrable_shiftedAbsPowExp
      (A := 1) (k := 7) (c := 1) (by norm_num) (by norm_num)
    convert h using 1
    ext t
    simp [JutilaPolynomialExponentialIntegral.shiftedAbsPowExp]
  have hE : Integrable E := hEbase.const_mul K
  apply hE.mono'
  · have hcontGamma : Continuous (fun t : ℝ =>
        Complex.Gamma (((-(1 / 2 : ℝ)) : ℂ) + t * I + 1)) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hnp : ∀ n : ℕ,
          (((-(1 / 2 : ℝ)) : ℂ) + (t : ℂ) * I + 1) ≠ -(n : ℂ) := by
        intro n hn
        have hre := congrArg Complex.re hn
        norm_num [Complex.neg_re] at hre
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hinner : ContinuousAt (fun u : ℝ =>
          (((-(1 / 2 : ℝ)) : ℂ) + u * I + 1)) t := by fun_prop
      exact ContinuousAt.comp
        (f := fun u : ℝ => (((-(1 / 2 : ℝ)) : ℂ) + u * I + 1))
        (g := Complex.Gamma) (x := t)
        (Complex.continuousAt_Gamma _ hnp) hinner
  
    have hcontQ : Continuous (fun t : ℝ =>
        p53ScaleRemovableQuotient U V
          (((-(1 / 2 : ℝ)) : ℂ) + t * I)) := by
      exact continuous_iff_continuousAt.mpr fun t =>
        (differentiableAt_p53ScaleRemovableQuotient hU hV _).continuousAt.comp
          (by fun_prop)
    have hcontL : Continuous (fun t : ℝ =>
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
          (1 + s + (((-(1 / 2 : ℝ)) : ℂ) + t * I))) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hz1 : 1 + s + (((-(1 / 2 : ℝ)) : ℂ) + (t : ℂ) * I) ≠ 1 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      have hinner : ContinuousAt (fun u : ℝ =>
          1 + s + (((-(1 / 2 : ℝ)) : ℂ) + u * I)) t := by fun_prop
      exact ContinuousAt.comp
        (f := fun u : ℝ => 1 + s + (((-(1 / 2 : ℝ)) : ℂ) + u * I))
        (g := DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
        (x := t)
        (DirichletCharacter.differentiableAt_LFunction
          (1 : DirichletCharacter ℂ q) _ (Or.inl hz1)).continuousAt hinner
    simpa [F, p53TwoScaleContourIntegrand] using!
      ((hcontGamma.mul hcontQ).mul hcontL).aestronglyMeasurable
  · filter_upwards [] with t
    have hraw := norm_p53PrincipalIntegrand_leftHalf_le q s hU hV hsLo hsHi
      (t := t)
    have hC : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg s.im]
    have hCu : C + |t| ≤ C * (1 + |t|) := by
      nlinarith [abs_nonneg t]
    have hpow : (C + |t|) ^ 6 ≤ C ^ 6 * (1 + |t|) ^ 6 := by
      calc
        _ ≤ (C * (1 + |t|)) ^ 6 := pow_le_pow_left₀ (by positivity) hCu 6
        _ = _ := by ring
    have hexp : Real.exp (-(Real.pi / 2) * |t|) ≤ Real.exp (-|t|) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_gt_three, abs_nonneg t]
    have hP := p53CpowEndpointBound_nonneg hU hV (-(1 / 2)) (-(1 / 2))
    calc
      ‖F t‖ ≤ 153600 * (2 : ℝ) ^ q.primeFactors.card *
          (1 + |t|) * (C + |t|) ^ 6 *
          Real.exp (-(Real.pi / 2) * |t|) *
          p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2)) := by
        simpa [F, C] using hraw
      _ ≤ 153600 * (2 : ℝ) ^ q.primeFactors.card *
          (1 + |t|) * (C ^ 6 * (1 + |t|) ^ 6) *
          Real.exp (-|t|) *
          p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2)) := by gcongr
      _ = E t := by dsimp [E, K]; ring

theorem norm_integral_p53PrincipalIntegrand_leftHalf_le
    (q : ℕ) [NeZero q] (s : ℂ) {U V : ℝ}
    (hU : 0 < U) (hV : 0 < V)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 4) :
    ‖∫ t : ℝ,
      p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
        (((-(1 / 2 : ℝ)) : ℂ) + t * I)‖ ≤
      (153600 * (2 : ℝ) ^ q.primeFactors.card * (5 + |s.im|) ^ 6 *
        p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2))) *
        p53PrincipalUniversalVerticalMass := by
  let K : ℝ := 153600 * (2 : ℝ) ^ q.primeFactors.card * (5 + |s.im|) ^ 6 *
    p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2))
  let E : ℝ → ℝ := fun t => K * ((1 + |t|) ^ 7 * Real.exp (-|t|))
  have hEbase : Integrable (fun t : ℝ =>
      (1 + |t|) ^ 7 * Real.exp (-|t|)) := by
    have h := JutilaPolynomialExponentialIntegral.integrable_shiftedAbsPowExp
      (A := 1) (k := 7) (c := 1) (by norm_num) (by norm_num)
    convert h using 1
    ext t
    simp [JutilaPolynomialExponentialIntegral.shiftedAbsPowExp]
  have hE : Integrable E := hEbase.const_mul K
  calc
    _ ≤ ∫ t : ℝ, E t := by
      apply MeasureTheory.norm_integral_le_of_norm_le hE
      filter_upwards [] with t
      have hraw := norm_p53PrincipalIntegrand_leftHalf_le q s hU hV hsLo hsHi
        (t := t)
      have hC : 1 ≤ 5 + |s.im| := by linarith [abs_nonneg s.im]
      have hCu : 5 + |s.im| + |t| ≤
          (5 + |s.im|) * (1 + |t|) := by
        nlinarith [abs_nonneg t]
      have hpow : (5 + |s.im| + |t|) ^ 6 ≤
          (5 + |s.im|) ^ 6 * (1 + |t|) ^ 6 := by
        calc
          _ ≤ ((5 + |s.im|) * (1 + |t|)) ^ 6 :=
            pow_le_pow_left₀ (by positivity) hCu 6
          _ = _ := by ring
      have hexp : Real.exp (-(Real.pi / 2) * |t|) ≤ Real.exp (-|t|) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_gt_three, abs_nonneg t]
      have hP := p53CpowEndpointBound_nonneg hU hV (-(1 / 2)) (-(1 / 2))
      calc
        _ ≤ 153600 * (2 : ℝ) ^ q.primeFactors.card *
            (1 + |t|) * (5 + |s.im| + |t|) ^ 6 *
            Real.exp (-(Real.pi / 2) * |t|) *
            p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2)) := hraw
        _ ≤ 153600 * (2 : ℝ) ^ q.primeFactors.card *
            (1 + |t|) * ((5 + |s.im|) ^ 6 * (1 + |t|) ^ 6) *
            Real.exp (-|t|) *
            p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2)) := by gcongr
        _ = E t := by dsimp [E, K]; ring
    _ = _ := by
      rw [MeasureTheory.integral_const_mul]
      rfl

end
end MAPJutilaP53PrincipalLeftLineEstimate

#print axioms MAPJutilaP53PrincipalLeftLineEstimate.norm_trivialEulerCorrection_le_twoPow
#print axioms MAPJutilaP53PrincipalLeftLineEstimate.regularizedLFunction_principal_eq_zeta_mul_euler
#print axioms MAPJutilaP53PrincipalLeftLineEstimate.norm_principal_LFunction_leftHalf_le
#print axioms MAPJutilaP53PrincipalLeftLineEstimate.norm_p53PrincipalIntegrand_leftHalf_le
#print axioms MAPJutilaP53PrincipalLeftLineEstimate.integrable_p53PrincipalIntegrand_leftHalf
#print axioms MAPJutilaP53PrincipalLeftLineEstimate.norm_integral_p53PrincipalIntegrand_leftHalf_le
#print axioms MAPJutilaP53PrincipalLeftLineEstimate.norm_regularized_principal_fixedStrip_le_twoPow
#print axioms MAPJutilaP53PrincipalLeftLineEstimate.norm_principal_LFunction_horizontal_le
#print axioms MAPJutilaP53PrincipalLeftLineEstimate.norm_p53PrincipalIntegrand_horizontal_le
#print axioms MAPJutilaP53PrincipalLeftLineEstimate.tendsto_p53PrincipalFullHorizontalIntegral_zero
