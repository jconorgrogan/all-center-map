import GuthMaynardLemma295DeepLeftTailPolynomial
import GuthMaynardLemma295PolynomialKernel
import GuthMaynardLemma295DeepLeftCompactIntegral

/-! An explicit integrable envelope for the exterior deep-left tail. -/

namespace GuthMaynardLemma295DeepLeftExteriorEnvelope

open Complex Real MeasureTheory
open GuthMaynardLemma295DualTail
open GuthMaynardLemma295MellinPolynomialDecay
open GuthMaynardLemma295DeepLeftTailPolynomial
open GuthMaynardLemma295PolynomialKernel
open GuthMaynardLemma295DeepLeftCompactIntegral

noncomputable section

def deepLeftDegree (n : ℕ) : ℕ := 2 * n + 5

def deepLeftGeometryConstant (n : ℕ) : ℝ :=
  1152 * (1 + |deepLeftSigma n| + 2 * n) ^ (2 * n) *
    (1 + |(0 : ℝ)|) -- harmless normalization, definitionally one

theorem thetaPolynomialEnvelope_le
    (n : ℕ) (g t : ℝ) :
    (((1 + ‖((deepLeftSigma n : ℂ) + (t - g) * I)‖ + 2 * n) ^ 2) ^ n *
        (1152 * (1 + |t - g|) ^ 5)) ≤
      1152 * (1 + |deepLeftSigma n| + 2 * n) ^ (2 * n) *
        (1 + |g|) ^ (deepLeftDegree n) *
        (1 + |t|) ^ (deepLeftDegree n) := by
  let a : ℝ := 1 + |deepLeftSigma n| + 2 * n
  let x : ℝ := |t - g|
  have ha1 : 1 ≤ a := by
    dsimp [a]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [abs_nonneg (deepLeftSigma n)]
  have hx0 : 0 ≤ x := abs_nonneg _
  have hnorm : ‖((deepLeftSigma n : ℂ) + (t - g) * I)‖ ≤
      |deepLeftSigma n| + |t - g| := by
    calc
      ‖((deepLeftSigma n : ℂ) + ((t : ℂ) - (g : ℂ)) * I)‖ ≤
          ‖(deepLeftSigma n : ℂ)‖ + ‖((t : ℂ) - (g : ℂ)) * I‖ :=
        norm_add_le _ _
      _ = |deepLeftSigma n| + |t - g| := by
        have heq : (t : ℂ) - (g : ℂ) = ((t - g : ℝ) : ℂ) := by
          push_cast
          rfl
        have hnormsub : ‖(t : ℂ) - (g : ℂ)‖ = |t - g| := by
          rw [heq]
          exact norm_real _
        rw [norm_mul, norm_I, mul_one, hnormsub]
        exact congrArg (fun y : ℝ => y + |t - g|) (norm_real _)
  have hlinear : 1 + ‖((deepLeftSigma n : ℂ) + (t - g) * I)‖ + 2 * n ≤
      a * (1 + x) := by
    dsimp [a, x]
    calc
      1 + ‖((deepLeftSigma n : ℂ) + (t - g) * I)‖ + 2 * n ≤
          1 + (|deepLeftSigma n| + |t - g|) + 2 * n := by linarith
      _ ≤ (1 + |deepLeftSigma n| + 2 * n) * (1 + |t - g|) := by
        nlinarith [abs_nonneg (deepLeftSigma n), abs_nonneg (t-g)]
  have hshift : 1 + |t - g| ≤ (1 + |g|) * (1 + |t|) := by
    have htri : |t - g| ≤ |t| + |g| := abs_sub t g
    nlinarith [abs_nonneg t, abs_nonneg g]
  have hpow :
      ((1 + ‖((deepLeftSigma n : ℂ) + (t - g) * I)‖ + 2 * n) ^ 2) ^ n ≤
        a ^ (2*n) * (1+x) ^ (2*n) := by
    rw [← pow_mul]
    calc
      (1 + ‖((deepLeftSigma n : ℂ) + (t - g) * I)‖ + 2 * n) ^ (2*n) ≤
          (a * (1+x)) ^ (2*n) := by gcongr
      _ = a ^ (2*n) * (1+x) ^ (2*n) := mul_pow _ _ _
  have hcombine : (1+x) ^ (2*n) * (1+x)^5 =
      (1+x) ^ deepLeftDegree n := by
    rw [← pow_add]
    rfl
  have hshiftpow : (1+x) ^ deepLeftDegree n ≤
      ((1+|g|) * (1+|t|)) ^ deepLeftDegree n := by gcongr
  dsimp [deepLeftDegree]
  calc
    (((1 + ‖((deepLeftSigma n : ℂ) + (t - g) * I)‖ + 2 * n) ^ 2) ^ n *
        (1152 * (1 + |t - g|) ^ 5)) ≤
      (a ^ (2*n) * (1+x)^(2*n)) * (1152 * (1+x)^5) := by gcongr
    _ = 1152 * a^(2*n) * (1+x)^(2*n+5) := by ring
    _ ≤ 1152 * a^(2*n) * (((1+|g|)*(1+|t|))^(2*n+5)) := by gcongr
    _ = 1152 * (1 + |deepLeftSigma n| + 2 * n) ^ (2 * n) *
        (1 + |g|) ^ (2*n+5) * (1+|t|)^(2*n+5) := by
      dsimp [a]
      rw [mul_pow]
      ring

/-- Literal tail integrand dominated by an explicit integrable kernel on the
exterior range.  The Mellin order is four larger than the theta degree. -/
theorem norm_deepLeftTailIntegrand_le_exteriorKernel
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K n : ℕ) {t : ℝ}
    (htg : t ≠ g) (him : 2 ≤ |t - g|) :
    ‖lemma295DeepLeftTailIntegrand N g K n t‖ ≤
      (1152 * (1 + |deepLeftSigma n| + 2 * n) ^ (2*n) *
        (1+|g|) ^ deepLeftDegree n) *
      ((K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
        (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n)) *
      (Real.rpow N (deepLeftSigma n) *
        sourceMellinDecayConstantAt (deepLeftSigma n) (deepLeftDegree n + 4)) *
      ((1+|t|)^deepLeftDegree n /
        (1+|t|^(deepLeftDegree n + 4))) := by
  have hraw := norm_lemma295DeepLeftTailIntegrand_le_polynomial
    hN g K n (deepLeftDegree n + 4) htg him
  have htheta := thetaPolynomialEnvelope_le n g t
  have htail0 : 0 ≤
      (K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
        (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n) := by
    have hs : deepLeftSigma n < 0 := by
      unfold deepLeftSigma
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hz : (((deepLeftSigma n : ℂ) + (t-g)*I)).re < 0 := by simpa using hs
    exact (norm_nonneg _).trans (by
      simpa using (norm_sourceDualTailNat_le hz K))
  have hNpow : 0 ≤ Real.rpow N (deepLeftSigma n) := Real.rpow_nonneg hN.le _
  have hC : 0 ≤ sourceMellinDecayConstantAt
      (deepLeftSigma n) (deepLeftDegree n + 4) :=
    sourceMellinDecayConstantAt_nonneg _ _
  calc
    ‖lemma295DeepLeftTailIntegrand N g K n t‖ ≤
      (((1 + ‖((deepLeftSigma n : ℂ) + (t - g) * I)‖ + 2 * n) ^ 2) ^ n *
        (1152 * (1 + |t - g|) ^ 5)) *
      ((K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
        (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n)) *
      (Real.rpow N (deepLeftSigma n) *
        (sourceMellinDecayConstantAt (deepLeftSigma n) (deepLeftDegree n + 4) /
          (1 + |t| ^ (deepLeftDegree n + 4)))) := hraw
    _ ≤ (1152 * (1 + |deepLeftSigma n| + 2 * n) ^ (2*n) *
        (1+|g|) ^ deepLeftDegree n * (1+|t|)^deepLeftDegree n) *
      ((K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
        (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n)) *
      (Real.rpow N (deepLeftSigma n) *
        (sourceMellinDecayConstantAt (deepLeftSigma n) (deepLeftDegree n + 4) /
          (1 + |t| ^ (deepLeftDegree n + 4)))) := by gcongr
    _ = (1152 * (1 + |deepLeftSigma n| + 2 * n) ^ (2*n) *
        (1+|g|) ^ deepLeftDegree n) *
      ((K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
        (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n)) *
      (Real.rpow N (deepLeftSigma n) *
        sourceMellinDecayConstantAt (deepLeftSigma n) (deepLeftDegree n + 4)) *
      ((1+|t|)^deepLeftDegree n /
        (1+|t|^(deepLeftDegree n + 4))) := by ring

/-- The literal discarded reflected tail is Bochner integrable on the whole
deep-left vertical line. -/
theorem integrable_lemma295DeepLeftTailIntegrand
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K n : ℕ) :
    Integrable (lemma295DeepLeftTailIntegrand N g K n) := by
  let E : ℝ :=
    (1152 * (1 + |deepLeftSigma n| + 2 * n) ^ (2*n) *
      (1+|g|) ^ deepLeftDegree n) *
    ((K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
      (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n)) *
    (Real.rpow N (deepLeftSigma n) *
      sourceMellinDecayConstantAt (deepLeftSigma n) (deepLeftDegree n + 4))
  let ker : ℝ → ℝ := fun t =>
    (1+|t|)^deepLeftDegree n / (1+|t|^(deepLeftDegree n + 4))
  have hmajor : Integrable (fun t : ℝ => E * ker t) :=
    (integrable_polynomial_kernel (deepLeftDegree n)).const_mul E
  have hcont := continuous_lemma295DeepLeftTailIntegrand hN g K n
  have hpiece : ∀ S : Set ℝ, MeasurableSet S →
      (∀ t ∈ S, 2 ≤ |t-g|) →
      Integrable (lemma295DeepLeftTailIntegrand N g K n)
        (volume.restrict S) := by
    intro S hSm hS
    apply Integrable.mono' hmajor.integrableOn
    · exact hcont.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem hSm] with t ht
      have him := hS t ht
      have htg : t ≠ g := by intro h; subst t; norm_num at him
      simpa [E, ker] using
        (norm_deepLeftTailIntegrand_le_exteriorKernel hN g K n htg him)
  have hleft := hpiece (Set.Iic (g-2)) measurableSet_Iic (by
    intro t ht
    change t ≤ g - 2 at ht
    rw [abs_of_nonpos (by linarith)]
    linarith)
  have hright := hpiece (Set.Ici (g+2)) measurableSet_Ici (by
    intro t ht
    change g + 2 ≤ t at ht
    rw [abs_of_nonneg (by linarith)]
    linarith)
  have hmid : Integrable (lemma295DeepLeftTailIntegrand N g K n)
      (volume.restrict (Set.Icc (g-2) (g+2))) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hall := (IntegrableOn.union hleft hmid).union hright
  have hunion : (Set.Iic (g-2) ∪ Set.Icc (g-2) (g+2)) ∪
      Set.Ici (g+2) = Set.univ := by
    ext t
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc, Set.mem_Ici,
      Set.mem_univ, iff_true]
    by_cases h : t ≤ g-2
    · exact Or.inl (Or.inl h)
    by_cases h' : t ≤ g+2
    · exact Or.inl (Or.inr ⟨le_of_not_ge h, h'⟩)
    · exact Or.inr (le_of_not_ge h')
  rw [hunion] at hall
  exact integrableOn_univ.mp hall

/-- Quantitative full-line estimate before substituting the source scale. -/
theorem exists_norm_integral_deepLeftTail_le
    (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℝ} (hN : 0 < N) (g : ℝ) (K : ℕ),
    ‖∫ t : ℝ, lemma295DeepLeftTailIntegrand N g K n t‖ ≤
      (4*C*sourceMellinDecayConstantAt (deepLeftSigma n) 0 +
        (1152 * (1 + |deepLeftSigma n| + 2*n)^(2*n) *
          (1+|g|)^deepLeftDegree n *
          sourceMellinDecayConstantAt (deepLeftSigma n) (deepLeftDegree n+4) *
          ((2:ℝ)^(deepLeftDegree n+1)*Real.pi))) *
      ((K+1:ℝ)^(deepLeftSigma n-1) +
        (K+1:ℝ)^(deepLeftSigma n)/(-deepLeftSigma n)) *
      Real.rpow N (deepLeftSigma n) := by
  obtain ⟨C,hC,hmidAll⟩ := exists_norm_integral_deepLeft_compact_le n
  refine ⟨C,hC,?_⟩
  intro N hN g K
  have hmid := hmidAll hN g K
  let d := deepLeftDegree n
  let tail : ℝ := (K+1:ℝ)^(deepLeftSigma n-1) +
    (K+1:ℝ)^(deepLeftSigma n)/(-deepLeftSigma n)
  let E : ℝ := (1152 * (1+|deepLeftSigma n|+2*n)^(2*n) *
      (1+|g|)^d) * tail *
    (Real.rpow N (deepLeftSigma n) *
      sourceMellinDecayConstantAt (deepLeftSigma n) (d+4))
  let ker : ℝ → ℝ := fun t => (1+|t|)^d/(1+|t|^(d+4))
  let S : Set ℝ := Set.Icc (g-2) (g+2)
  have hInt := integrable_lemma295DeepLeftTailIntegrand hN g K n
  have hker := integrable_polynomial_kernel d
  have hE0 : 0 ≤ E := by
    have hs : deepLeftSigma n < 0 := by
      unfold deepLeftSigma
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have htail0 : 0 ≤ tail := by
      dsimp [tail]
      have hz : (((deepLeftSigma n:ℂ) + (0:ℝ)*I)).re < 0 := by simpa using hs
      exact (norm_nonneg _).trans (by simpa using norm_sourceDualTailNat_le hz K)
    dsimp [E]
    apply mul_nonneg
    · exact mul_nonneg (by positivity) htail0
    · exact mul_nonneg (Real.rpow_nonneg hN.le _)
        (sourceMellinDecayConstantAt_nonneg _ _)
  have hcomp :
      ‖∫ t : ℝ in Sᶜ, lemma295DeepLeftTailIntegrand N g K n t‖ ≤
        E * ((2:ℝ)^(d+1)*Real.pi) := by
    have hmajor : Integrable (fun t : ℝ => E*ker t) := hker.const_mul E
    calc
      ‖∫ t : ℝ in Sᶜ, lemma295DeepLeftTailIntegrand N g K n t‖ ≤
          ∫ t : ℝ in Sᶜ, E*ker t := by
        apply norm_integral_le_of_norm_le hmajor.integrableOn
        filter_upwards [ae_restrict_mem (measurableSet_Icc.compl)] with t ht
        have hout : 2 ≤ |t-g| := by
          change t ∉ Set.Icc (g-2) (g+2) at ht
          simp only [Set.mem_Icc, not_and_or, not_le] at ht
          rcases ht with ht | ht
          · rw [abs_of_nonpos (by linarith)]
            linarith
          · rw [abs_of_nonneg (by linarith)]
            linarith
        have htg : t ≠ g := by intro h; subst t; norm_num at hout
        simpa [E,ker,d,tail] using
          norm_deepLeftTailIntegrand_le_exteriorKernel hN g K n htg hout
      _ ≤ ∫ t : ℝ, E*ker t :=
        setIntegral_le_integral hmajor
          (Filter.Eventually.of_forall fun t => by dsimp [ker]; positivity)
      _ = E * (∫ t : ℝ, ker t) := by rw [integral_const_mul]
      _ ≤ E * ((2:ℝ)^(d+1)*Real.pi) := by
        gcongr
        simpa [ker,d] using integral_polynomial_kernel_le d
  have hsplit := integral_add_compl (f := lemma295DeepLeftTailIntegrand N g K n)
    (s := S) (by exact measurableSet_Icc) hInt
  calc
    ‖∫ t : ℝ, lemma295DeepLeftTailIntegrand N g K n t‖ =
        ‖(∫ t : ℝ in S, lemma295DeepLeftTailIntegrand N g K n t) +
          ∫ t : ℝ in Sᶜ, lemma295DeepLeftTailIntegrand N g K n t‖ := by
      rw [hsplit]
    _ ≤ ‖∫ t : ℝ in S, lemma295DeepLeftTailIntegrand N g K n t‖ +
        ‖∫ t : ℝ in Sᶜ, lemma295DeepLeftTailIntegrand N g K n t‖ := norm_add_le _ _
    _ ≤ 4*C*tail*(Real.rpow N (deepLeftSigma n)*
          sourceMellinDecayConstantAt (deepLeftSigma n) 0) +
        E*((2:ℝ)^(d+1)*Real.pi) := by
      exact add_le_add (by simpa [S,tail] using hmid) hcomp
    _ = (4*C*sourceMellinDecayConstantAt (deepLeftSigma n) 0 +
        (1152 * (1 + |deepLeftSigma n| + 2*n)^(2*n) *
          (1+|g|)^deepLeftDegree n *
          sourceMellinDecayConstantAt (deepLeftSigma n) (deepLeftDegree n+4) *
          ((2:ℝ)^(deepLeftDegree n+1)*Real.pi))) *
      ((K+1:ℝ)^(deepLeftSigma n-1) +
        (K+1:ℝ)^(deepLeftSigma n)/(-deepLeftSigma n)) *
      Real.rpow N (deepLeftSigma n) := by
        dsimp [E,tail,d]
        ring

end
end GuthMaynardLemma295DeepLeftExteriorEnvelope

#print axioms GuthMaynardLemma295DeepLeftExteriorEnvelope.thetaPolynomialEnvelope_le
#print axioms GuthMaynardLemma295DeepLeftExteriorEnvelope.norm_deepLeftTailIntegrand_le_exteriorKernel
#print axioms GuthMaynardLemma295DeepLeftExteriorEnvelope.integrable_lemma295DeepLeftTailIntegrand
#print axioms GuthMaynardLemma295DeepLeftExteriorEnvelope.exists_norm_integral_deepLeftTail_le
