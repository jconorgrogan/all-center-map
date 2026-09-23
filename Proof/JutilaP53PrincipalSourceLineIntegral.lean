import JutilaP53SourceLineEstimate
import JutilaPrincipalSourceConvexity
import JutilaP53PrincipalLeftLineEstimate
import PrimeFactorSquareRootBound

/-! # Actual integrability and uniform norm bound on Jutila's source line -/
namespace MAPJutilaP53PrincipalSourceLineIntegral
open Complex Real MeasureTheory
open MAPJutilaP53TwoScaleContour MAPJutilaP53SourceLineEstimate
open MAPJutilaPrincipalSourceConvexity MAPJutilaP53PrincipalLeftLineEstimate
open MAPPrimeFactorSquareRootBound MAPBHPPrincipalNegativeEulerBound
open RamachandraShiftedGammaPoleContour
noncomputable section

/-- Actual principal ambient source-strip estimate. -/
theorem exists_principal_source_convexity
    {epsilon : ℝ} (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1/8) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (sigma t : ℝ),
      epsilon ≤ sigma → sigma ≤ 3*epsilon →
      ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
        ((sigma : ℂ) + (t : ℂ)*I)‖ ≤
        C * Real.rpow ((q : ℝ)*(1+|t|)) (1/2) := by
  obtain ⟨C,hC,hz⟩ := exists_riemannZeta_sqrt_bound heps hepsHi
  refine ⟨4*C, by positivity, ?_⟩
  intro q _inst sigma t hsLo hsHi
  have hz1 : (sigma : ℂ)+(t : ℂ)*I ≠ 1 := by
    intro h
    have h := congrArg Complex.re h
    simp at h
    linarith
  have hE := (norm_trivialEulerCorrection_le_twoPow
    (q := q) (z := (sigma : ℂ)+(t : ℂ)*I) (by simp; linarith)).trans
      (two_pow_card_primeFactors_le_four_sqrt q (NeZero.ne q))
  change ‖DirichletCharacter.LFunctionTrivChar q _‖ ≤ _
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hz1, norm_mul]
  calc
    _ ≤ (4 * Real.sqrt (q : ℝ)) * (C * Real.sqrt (1+|t|)) :=
      mul_le_mul hE (hz sigma t hsLo hsHi) (norm_nonneg _) (by positivity)
    _ = (4*C) * Real.rpow ((q : ℝ)*(1+|t|)) (1/2) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (Nat.cast_nonneg q)]
      ring

/-- An actual ambient nonprincipal source-line integral theorem: neither
integrability nor a pointwise L-bound is assumed. -/
theorem exists_principal_sourceLine_integrable_and_norm_integral_le
    {epsilon : ℝ} (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1 / 8) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (q : ℕ) [NeZero q],
      ∀ (s : ℂ) (U V : ℝ), 0 < U → 0 < V →
      0 ≤ s.re → s.re ≤ 2 * epsilon →
      Integrable (fun t : ℝ => p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
        (((-1 + epsilon : ℝ) : ℂ) + (t : ℂ) * I)) ∧
      ‖∫ t : ℝ, p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
        (((-1 + epsilon : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        K * Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2) *
          (Real.rpow U (-1 + epsilon) + Real.rpow V (-1 + epsilon)) := by
  obtain ⟨C, hC, hL⟩ := exists_principal_source_convexity heps hepsHi
  let f : ℝ → ℝ := fun t => (1 + |t|)^6 * Real.exp (-|t|)
  let J : ℝ := ∫ t : ℝ, f t
  have hf : Integrable f := integrable_one_add_abs_pow_six_mul_exp_neg_abs
  have hJ : 0 ≤ J := integral_nonneg fun t => by dsimp [f]; positivity
  let A : ℝ := (24 / epsilon) * C
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A * (1 + J), mul_pos hA (by linarith), ?_⟩
  intro q _inst s U V hU hV hsLo hsHi
  let B : ℝ := Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2)
  let D : ℝ := Real.rpow U (-1 + epsilon) + Real.rpow V (-1 + epsilon)
  let F : ℝ → ℂ := fun t => p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
    (((-1 + epsilon : ℝ) : ℂ) + (t : ℂ) * I)
  have hB : 0 ≤ B := Real.rpow_nonneg (by positivity) _
  have hD : 0 ≤ D := add_nonneg (Real.rpow_nonneg hU.le _) (Real.rpow_nonneg hV.le _)
  have hbound (t : ℝ) : ‖F t‖ ≤ (A * B * D) * f t := by
    have hraw := norm_integrand_sourceLine_le_of_pointwiseL (1 : DirichletCharacter ℂ q) hC.le hU hV
      heps hepsHi hsLo hsHi
      (hL q (epsilon + s.re) (s.im + t) (by linarith) (by linarith))
    have hpow : (1 + |t|)^2 ≤ (1 + |t|)^6 :=
      pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by norm_num)
    have hexp : Real.exp (-(Real.pi / 2) * |t|) ≤ Real.exp (-|t|) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_gt_three, abs_nonneg t]
    calc
      ‖F t‖ ≤ A * B * (1 + |t|)^2 * Real.exp (-(Real.pi / 2) * |t|) * D := hraw
      _ ≤ A * B * (1 + |t|)^6 * Real.exp (-|t|) * D := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_left hpow (mul_nonneg hA.le hB)) hexp
            (Real.exp_pos _).le (by positivity)) hD
      _ = (A * B * D) * f t := by dsimp [f]; ring
  have hcontGamma : Continuous (fun t : ℝ =>
      Complex.Gamma (((-1 + epsilon : ℝ) : ℂ) + t * I + 1)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hnp : ∀ n : ℕ,
        (((-1 + epsilon : ℝ) : ℂ) + (t : ℂ) * I + 1) ≠ -(n : ℂ) := by
      intro n hn
      have hre := congrArg Complex.re hn
      simp [Complex.neg_re] at hre
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hinner : ContinuousAt (fun u : ℝ =>
        (((-1 + epsilon : ℝ) : ℂ) + u * I + 1)) t := by fun_prop
    exact ContinuousAt.comp
      (f := fun u : ℝ => (((-1 + epsilon : ℝ) : ℂ) + u * I + 1))
      (g := Complex.Gamma) (x := t)
      (Complex.continuousAt_Gamma _ hnp) hinner

  have hcontQ : Continuous (fun t : ℝ =>
      p53ScaleRemovableQuotient U V
        (((-1 + epsilon : ℝ) : ℂ) + t * I)) := by
    exact continuous_iff_continuousAt.mpr fun t =>
      (differentiableAt_p53ScaleRemovableQuotient hU hV _).continuousAt.comp
        (by fun_prop)
  have hcontL : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
        (1 + s + (((-1 + epsilon : ℝ) : ℂ) + t * I))) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hz1 : 1 + s + (((-1 + epsilon : ℝ) : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    have hinner : ContinuousAt (fun u : ℝ =>
        1 + s + (((-1 + epsilon : ℝ) : ℂ) + u * I)) t := by fun_prop
    exact ContinuousAt.comp
      (f := fun u : ℝ => 1 + s + (((-1 + epsilon : ℝ) : ℂ) + u * I))
      (g := DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
      (x := t)
      (DirichletCharacter.differentiableAt_LFunction
        (1 : DirichletCharacter ℂ q) _ (Or.inl hz1)).continuousAt hinner
  have hcont : Continuous F := by
    simpa [F, p53TwoScaleContourIntegrand] using! (hcontGamma.mul hcontQ).mul hcontL
  have hmajor : Integrable (fun t : ℝ => (A * B * D) * f t) := hf.const_mul _
  have hInt : Integrable F := hmajor.mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  refine ⟨hInt, ?_⟩
  calc
    ‖∫ t : ℝ, F t‖ ≤ ∫ t : ℝ, (A * B * D) * f t :=
      MeasureTheory.norm_integral_le_of_norm_le hmajor (Filter.Eventually.of_forall hbound)
    _ = (A * B * D) * J := by rw [integral_const_mul]
    _ ≤ (A * B * D) * (1 + J) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg hA.le hB) hD)
    _ = _ := by dsimp [B, D]; ring
end
end MAPJutilaP53PrincipalSourceLineIntegral
#print axioms MAPJutilaP53PrincipalSourceLineIntegral.exists_principal_sourceLine_integrable_and_norm_integral_le
