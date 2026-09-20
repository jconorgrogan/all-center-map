import KoukTheorem113HalfStripFormula
import PrimitiveContourComponentBounds
import PrincipalZetaTransport

/-!
# Deterministic bounds for the endpoint-regularized horizontal contour

These estimates differ from the ordinary Perron contour only by the endpoint
kernel `(x^s-1)/s`.  On a horizontal line it costs at most twice the ordinary
kernel.  All logarithmic-derivative input remains explicit.
-/

namespace KoukEndpointContourBounds

open Set MeasureTheory Complex
open KoukTheorem113EndpointKernel KoukTheorem113Residues
open KoukTheorem113ExactFormula

noncomputable section

/-- At a nonreal point, nonvanishing of the regularized function implies
nonvanishing of the literal Dirichlet L-function, including for an ambient
principal character. -/
theorem LFunction_ne_zero_of_regularized_ne_zero_of_im_ne_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) {s : ℂ}
    (him : s.im ≠ 0) (hreg : DirichletZeros.regularizedLFunction chi s ≠ 0) :
    DirichletCharacter.LFunction chi s ≠ 0 := by
  classical
  by_cases hchi : chi = 1
  · subst chi
    have hs1 : s ≠ 1 := by
      intro hs
      rw [hs] at him
      norm_num at him
    intro hL
    apply hreg
    simp [DirichletZeros.regularizedLFunction,
      DirichletCharacter.LFunctionTrivChar₁, hs1, hL]
  · simpa [DirichletZeros.regularizedLFunction, hchi] using hreg

/-- On a nonreal horizontal line, the endpoint kernel is bounded by twice
the largest power on the real interval. -/
theorem norm_endpointPerronKernel_horizontal_le
    {x r c tau : ℝ} (hx : 1 ≤ x) (hc0 : 0 ≤ c) (hrc : r ≤ c)
    (htau : 0 < |tau|) :
    ‖endpointPerronKernel x ((r : ℂ) + Complex.I * tau)‖ ≤
      2 * x ^ c / |tau| := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  let s : ℂ := (r : ℂ) + Complex.I * tau
  have hs0 : s ≠ 0 := by
    intro hs
    have hi := congrArg Complex.im hs
    dsimp [s] at hi
    simp at hi
    exact (ne_of_gt htau) (by simpa [hi])
  have hden : |tau| ≤ ‖s‖ := by
    calc
      |tau| = |s.im| := by simp [s]
      _ ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hcPowOne : 1 ≤ x ^ c := Real.one_le_rpow hx hc0
  rw [endpointPerronKernel_of_ne hs0, norm_div]
  have hnum : ‖(x : ℂ) ^ s - 1‖ ≤ 2 * x ^ c := by
    calc
      ‖(x : ℂ) ^ s - 1‖ ≤ ‖(x : ℂ) ^ s‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ = x ^ r + 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        simp [s]
      _ ≤ x ^ c + 1 := by
        have hp := Real.rpow_le_rpow_of_exponent_le hx hrc
        linarith
      _ ≤ 2 * x ^ c := by linarith
  calc
    ‖(x : ℂ) ^ s - 1‖ / ‖s‖ ≤ (2 * x ^ c) / ‖s‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg s)
    _ ≤ (2 * x ^ c) / |tau| :=
      div_le_div_of_nonneg_left (by positivity) htau hden

/-- Pointwise endpoint source-integrand bound. -/
theorem norm_endpointPerronContourIntegrand_horizontal_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x r c tau M : ℝ} (hx : 1 ≤ x) (hc0 : 0 ≤ c) (hrc : r ≤ c)
    (htau : 0 < |tau|)
    (hlog : ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * tau)‖ ≤ M) :
    ‖endpointPerronContourIntegrand chi x
        ((r : ℂ) + Complex.I * tau)‖ ≤
      2 * M * x ^ c / |tau| := by
  unfold endpointPerronContourIntegrand
  rw [norm_mul, norm_neg]
  have hker := norm_endpointPerronKernel_horizontal_le hx hc0 hrc htau
  calc
    ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * tau)‖ *
        ‖endpointPerronKernel x ((r : ℂ) + Complex.I * tau)‖ ≤
      M * (2 * x ^ c / |tau|) :=
        mul_le_mul hlog hker (norm_nonneg _) (le_trans (norm_nonneg _) hlog)
    _ = 2 * M * x ^ c / |tau| := by ring

/-- Away from a literal L-zero, the decomposed integrand equals the endpoint
source integrand at a nonreal horizontal point. -/
theorem endpointDecomposed_eq_source_horizontal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x r tau : ℝ} (htau : tau ≠ 0)
    (hL : DirichletCharacter.LFunction chi
      ((r : ℂ) + Complex.I * tau) ≠ 0) :
    endpointDecomposedContourIntegrand chi x
        ((r : ℂ) + Complex.I * tau) =
      endpointPerronContourIntegrand chi x
        ((r : ℂ) + Complex.I * tau) := by
  let s : ℂ := (r : ℂ) + Complex.I * tau
  have hs0 : s ≠ 0 := by
    intro hs
    have hi := congrArg Complex.im hs
    dsimp [s] at hi
    simp at hi
    exact htau hi
  have hs1 : s ≠ 1 := by
    intro hs
    have hi := congrArg Complex.im hs
    dsimp [s] at hi
    simp at hi
    exact htau hi
  exact (endpointPerronContourIntegrand_eq_regularized_add_principal
    chi hs0 hs1 hL).symm

/-- Horizontal endpoint contour bound with all source hypotheses explicit. -/
theorem norm_endpointHorizontalBoundaryIntegral_le_of_logDeriv
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x sigma c T M : ℝ} (hx : 1 ≤ x) (hc0 : 0 ≤ c)
    (hsigma : sigma ≤ c) (hT : 0 < T) (hM : 0 ≤ M)
    (hLtop : ∀ r ∈ Set.Icc sigma c,
      DirichletCharacter.LFunction chi
        ((r : ℂ) + Complex.I * T) ≠ 0)
    (hLbottom : ∀ r ∈ Set.Icc sigma c,
      DirichletCharacter.LFunction chi
        ((r : ℂ) - Complex.I * T) ≠ 0)
    (htop : ∀ r ∈ Set.Icc sigma c,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * T)‖ ≤ M)
    (hbottom : ∀ r ∈ Set.Icc sigma c,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) - Complex.I * T)‖ ≤ M) :
    ‖endpointHorizontalBoundaryIntegral chi x sigma c T‖ ≤
      2 * (c - sigma) / Real.pi * (M * x ^ c / T) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have habsT : |T| = T := abs_of_pos hT
  have habsNegT : |-T| = T := by simp [abs_of_pos hT]
  have htopint :
      ‖∫ r in sigma..c,
          endpointDecomposedContourIntegrand chi x
            ((r : ℂ) + (T : ℂ) * Complex.I)‖ ≤
        (2 * M * x ^ c / T) * |c - sigma| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun r hr => by
      have hr' : r ∈ Set.Icc sigma c := by
        have hru : r ∈ Set.uIcc sigma c := Set.uIoc_subset_uIcc hr
        simpa [Set.uIcc_of_le hsigma] using hru
      rw [show (T : ℂ) * Complex.I = Complex.I * (T : ℂ) by ring]
      rw [endpointDecomposed_eq_source_horizontal chi hT.ne'
        (hLtop r hr')]
      simpa only [habsT] using
        norm_endpointPerronContourIntegrand_horizontal_le chi hx hc0 hr'.2
          (by simpa [habsT] using hT) (htop r hr'))
  have hbottomint :
      ‖∫ r in sigma..c,
          endpointDecomposedContourIntegrand chi x
            ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤
        (2 * M * x ^ c / T) * |c - sigma| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun r hr => by
      have hr' : r ∈ Set.Icc sigma c := by
        have hru : r ∈ Set.uIcc sigma c := Set.uIoc_subset_uIcc hr
        simpa [Set.uIcc_of_le hsigma] using hru
      rw [show ((-T : ℝ) : ℂ) * Complex.I =
        Complex.I * ((-T : ℝ) : ℂ) by ring]
      rw [endpointDecomposed_eq_source_horizontal chi (neg_ne_zero.mpr hT.ne')
        (by simpa [sub_eq_add_neg] using hLbottom r hr')]
      have hp := norm_endpointPerronContourIntegrand_horizontal_le chi hx hc0
        hr'.2 (tau := -T) (M := M)
        (by simpa [habsNegT] using hT)
        (by simpa [sub_eq_add_neg, mul_comm] using hbottom r hr')
      simpa only [habsNegT] using hp)
  let A : ℂ := (2 * Real.pi * Complex.I : ℂ)⁻¹
  let Ibottom : ℂ := ∫ r in sigma..c,
    endpointDecomposedContourIntegrand chi x
      ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
  let Itop : ℂ := ∫ r in sigma..c,
    endpointDecomposedContourIntegrand chi x
      ((r : ℂ) + (T : ℂ) * Complex.I)
  have hA : ‖A‖ = (2 * Real.pi)⁻¹ := by
    dsimp [A]
    rw [norm_inv, norm_mul, Complex.norm_I, mul_one]
    congr 1
    rw [norm_mul]
    norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  change ‖A * (Ibottom - Itop)‖ ≤ _
  rw [norm_mul, hA]
  have hdiff : ‖Ibottom - Itop‖ ≤
      2 * ((2 * M * x ^ c / T) * |c - sigma|) := by
    calc
      ‖Ibottom - Itop‖ ≤ ‖Ibottom‖ + ‖Itop‖ := norm_sub_le _ _
      _ ≤ (2 * M * x ^ c / T) * |c - sigma| +
          (2 * M * x ^ c / T) * |c - sigma| :=
        add_le_add (by simpa [Ibottom] using hbottomint)
          (by simpa [Itop] using htopint)
      _ = 2 * ((2 * M * x ^ c / T) * |c - sigma|) := by ring
  calc
    (2 * Real.pi)⁻¹ * ‖Ibottom - Itop‖ ≤
        (2 * Real.pi)⁻¹ *
          (2 * ((2 * M * x ^ c / T) * |c - sigma|)) :=
      mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = 2 * (c - sigma) / Real.pi * (M * x ^ c / T) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hsigma)]
      field_simp [ne_of_gt hpi]

/-- Consumer form using the regularized-function edge legality already
carried by the full-support contour. -/
theorem norm_endpointHorizontalBoundaryIntegral_le_of_regularized_logDeriv
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x sigma c T M : ℝ} (hx : 1 ≤ x) (hc0 : 0 ≤ c)
    (hsigma : sigma ≤ c) (hT : 0 < T) (hM : 0 ≤ M)
    (hregTop : ∀ r ∈ Set.Icc sigma c,
      DirichletZeros.regularizedLFunction chi
        ((r : ℂ) + Complex.I * T) ≠ 0)
    (hregBottom : ∀ r ∈ Set.Icc sigma c,
      DirichletZeros.regularizedLFunction chi
        ((r : ℂ) - Complex.I * T) ≠ 0)
    (htop : ∀ r ∈ Set.Icc sigma c,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * T)‖ ≤ M)
    (hbottom : ∀ r ∈ Set.Icc sigma c,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) - Complex.I * T)‖ ≤ M) :
    ‖endpointHorizontalBoundaryIntegral chi x sigma c T‖ ≤
      2 * (c - sigma) / Real.pi * (M * x ^ c / T) := by
  apply norm_endpointHorizontalBoundaryIntegral_le_of_logDeriv
    chi hx hc0 hsigma hT hM
  · intro r hr
    apply LFunction_ne_zero_of_regularized_ne_zero_of_im_ne_zero chi
    · simp
      exact hT.ne'
    · exact hregTop r hr
  · intro r hr
    apply LFunction_ne_zero_of_regularized_ne_zero_of_im_ne_zero chi
    · simp
      exact hT.ne'
    · simpa [sub_eq_add_neg] using hregBottom r hr
  · exact htop
  · exact hbottom

end
end KoukEndpointContourBounds

#print axioms KoukEndpointContourBounds.norm_endpointHorizontalBoundaryIntegral_le_of_logDeriv
