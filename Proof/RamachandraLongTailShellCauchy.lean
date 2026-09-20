import RamachandraWeightedCauchyAE
import RamachandraShiftedFunctionalFactorMomentEnvelope
import RamachandraGammaWeightUniformMass
import RamachandraShiftedReflectedTailInfiniteAssembly

/-!
# Weighted Cauchy for one exact long-tail shell

This is the deterministic contour inequality before summing shells or using
the character mean square.  The sharp functional-factor bound is used only
almost everywhere, correctly discarding the null point `v=-t`.
-/

namespace RamachandraLongTailShellCauchy

open Complex MeasureTheory
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedContourSharpEnvelopes
open RamachandraShiftedFunctionalFactorMomentEnvelope
open RamachandraGammaWeightIntegrability
open RamachandraShiftedReflectedTailInfiniteAssembly
open BHPRamachandraMeanValueFromDyadicAFE
open BHPAllCharacterDyadicBudget
open MAPMRTLemma210OrthogonalityReduction
open MontgomeryVaughanFiniteReduction
open RamachandraShiftedReflectedSeries
open RamachandraPrimitiveShiftedMellinReduction
open RamachandraShiftedHeadFiniteContour

noncomputable section

set_option maxHeartbeats 800000

variable {d : ℕ} [NeZero d]

/-- The literal contribution of one standard dyadic shell to the long
reflected contour integrand. -/
def longTailShellIntegrand
    (psi : DirichletCharacter ℂ d) (X sigma t : ℝ) (j : ℕ)
    (v : ℝ) : ℂ :=
  ramachandraFunctionalFactor psi (longFunctionalPoint sigma t v) ^ 2 *
    ramachandraReflectedTailDyadicShell psi X
      (longFunctionalPoint sigma t v) j *
    Complex.Gamma (((-(sigma + 1 / 4) : ℝ) : ℂ) + (v : ℂ) * I) *
    (X : ℂ) ^ (((-(sigma + 1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)

/-- A finite, ordinate-independent bound for one literal shell. -/
def longTailShellUniformNormBound
    (psi : DirichletCharacter ℂ d) (X sigma : ℝ) (j : ℕ) : ℝ :=
  ∑ n ∈ dyadicSupport (2 ^ j),
    ‖reflectedTailInfiniteShellCoeff X sigma (-(sigma + 1 / 4)) 0 n *
      star psi n‖

private theorem norm_reflectedTailInfiniteShellCoeff_eq_zero
    (X sigma u v : ℝ) (n : ℕ) :
    ‖reflectedTailInfiniteShellCoeff X sigma u v n‖ =
      ‖reflectedTailInfiniteShellCoeff X sigma u 0 n‖ := by
  unfold reflectedTailInfiniteShellCoeff
  by_cases h : X < n
  · simp only [h, if_true]
    unfold shiftedReflectedBlockCoeff
    rw [norm_mul, norm_mul, norm_twistedPhase, norm_twistedPhase]
  · simp [h]

theorem norm_longTailShell_le_uniform
    (psi : DirichletCharacter ℂ d) (X sigma t v : ℝ) (j : ℕ) :
    ‖ramachandraReflectedTailDyadicShell psi X
      (longFunctionalPoint sigma t v) j‖ ≤
        longTailShellUniformNormBound psi X sigma j := by
  rw [show longFunctionalPoint sigma t v =
      ramachandraShiftedPoint sigma t +
        (((-(sigma + 1 / 4) : ℝ) : ℂ) + (v : ℂ) * I) by
    apply Complex.ext <;> simp [longFunctionalPoint, ramachandraShiftedPoint] <;> ring]
  rw [ramachandraReflectedTailDyadicShell_eq_ramachandraDyadicBlock]
  unfold ramachandraDyadicBlock twistedFinitePolynomial
  simp only [if_true]
  apply (norm_sum_le _ _).trans
  unfold longTailShellUniformNormBound
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul, norm_mul, norm_twistedPhase, mul_one,
    norm_reflectedTailInfiniteShellCoeff_eq_zero]
  rw [norm_mul]

theorem continuous_longTailShell
    (psi : DirichletCharacter ℂ d) (X sigma t : ℝ) (j : ℕ) :
    Continuous (fun v => ramachandraReflectedTailDyadicShell psi X
      (longFunctionalPoint sigma t v) j) := by
  have heq : (fun v => ramachandraReflectedTailDyadicShell psi X
      (longFunctionalPoint sigma t v) j) =
      (fun v => ramachandraDyadicBlock d (2 ^ j)
        (reflectedTailInfiniteShellCoeff X sigma
          (-(sigma + 1 / 4)) v) true psi t) := by
    funext v
    rw [show longFunctionalPoint sigma t v =
        ramachandraShiftedPoint sigma t +
          (((-(sigma + 1 / 4) : ℝ) : ℂ) + (v : ℂ) * I) by
      apply Complex.ext <;> simp [longFunctionalPoint, ramachandraShiftedPoint] <;> ring]
    exact ramachandraReflectedTailDyadicShell_eq_ramachandraDyadicBlock
      psi X sigma (-(sigma + 1 / 4)) v t j
  rw [heq]
  have hjoint := continuous_uncurry_ramachandraDyadicBlock d (2 ^ j) true
    (fun v => reflectedTailInfiniteShellCoeff X sigma
      (-(sigma + 1 / 4)) v)
    (fun n => continuous_reflectedTailInfiniteShellCoeff
      X sigma (-(sigma + 1 / 4)) n) psi
  simpa only [Function.uncurry_apply_pair] using
    hjoint.comp (continuous_const.prodMk continuous_id)

/-- Joint continuity in the source ordinate `t` and Mellin ordinate `v`.
This is the measurability input for the later full-line Fubini assembly. -/
theorem continuous_uncurry_longTailShell
    (psi : DirichletCharacter ℂ d) (X sigma : ℝ) (j : ℕ) :
    Continuous (Function.uncurry (fun t v =>
      ramachandraReflectedTailDyadicShell psi X
        (longFunctionalPoint sigma t v) j)) := by
  have heq : Function.uncurry (fun t v =>
      ramachandraReflectedTailDyadicShell psi X
        (longFunctionalPoint sigma t v) j) =
      Function.uncurry (fun t v =>
        ramachandraDyadicBlock d (2 ^ j)
          (reflectedTailInfiniteShellCoeff X sigma
            (-(sigma + 1 / 4)) v) true psi t) := by
    funext p
    change ramachandraReflectedTailDyadicShell psi X
        (longFunctionalPoint sigma p.1 p.2) j =
      ramachandraDyadicBlock d (2 ^ j)
        (reflectedTailInfiniteShellCoeff X sigma
          (-(sigma + 1 / 4)) p.2) true psi p.1
    rw [show longFunctionalPoint sigma p.1 p.2 =
        ramachandraShiftedPoint sigma p.1 +
          (((-(sigma + 1 / 4) : ℝ) : ℂ) + (p.2 : ℂ) * I) by
      apply Complex.ext <;>
        simp [longFunctionalPoint, ramachandraShiftedPoint] <;> ring]
    exact ramachandraReflectedTailDyadicShell_eq_ramachandraDyadicBlock
      psi X sigma (-(sigma + 1 / 4)) p.2 p.1 j
  rw [heq]
  exact continuous_uncurry_ramachandraDyadicBlock d (2 ^ j) true
    (fun v => reflectedTailInfiniteShellCoeff X sigma
      (-(sigma + 1 / 4)) v)
    (fun n => continuous_reflectedTailInfiniteShellCoeff
      X sigma (-(sigma + 1 / 4)) n) psi

/-- Joint continuity of the literal long-shell contour integrand. -/
theorem continuous_uncurry_longTailShellIntegrand
    (psi : DirichletCharacter ℂ d) {X sigma : ℝ} (hX : 0 < X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) (j : ℕ) :
    Continuous (Function.uncurry
      (longTailShellIntegrand psi X sigma · j)) := by
  rw [continuous_iff_continuousAt]
  intro p
  let z : ℂ := longFunctionalPoint sigma p.1 p.2
  let w : ℂ := ((-(sigma + 1 / 4) : ℝ) : ℂ) + (p.2 : ℂ) * I
  have hzinner : ContinuousAt (fun y : ℝ × ℝ =>
      longFunctionalPoint sigma y.1 y.2) p := by
    unfold longFunctionalPoint ramachandraShiftedPoint
    fun_prop
  have hzre : z.re = -(1 / 4 : ℝ) :=
    longFunctionalPoint_re sigma p.1 p.2
  have hfacDiff :=
    differentiableAt_ramachandraFunctionalFactor psi (z := z) (by
      rw [sub_re, one_re, hzre]
      norm_num)
  have hfac : ContinuousAt (fun y : ℝ × ℝ =>
      ramachandraFunctionalFactor psi
        (longFunctionalPoint sigma y.1 y.2)) p := by
    change ContinuousAt
      (ramachandraFunctionalFactor psi ∘
        (fun y : ℝ × ℝ => longFunctionalPoint sigma y.1 y.2)) p
    exact ContinuousAt.comp
      (f := fun y : ℝ × ℝ => longFunctionalPoint sigma y.1 y.2)
      (g := ramachandraFunctionalFactor psi)
      (by simpa [z] using hfacDiff.continuousAt) hzinner
  have hshell : ContinuousAt (fun y : ℝ × ℝ =>
      ramachandraReflectedTailDyadicShell psi X
        (longFunctionalPoint sigma y.1 y.2) j) p :=
    (continuous_uncurry_longTailShell psi X sigma j).continuousAt
  have hwinner : ContinuousAt (fun y : ℝ × ℝ =>
      (((-(sigma + 1 / 4) : ℝ) : ℂ) + (y.2 : ℂ) * I)) p := by fun_prop
  have hGammaDiff : DifferentiableAt ℂ Complex.Gamma w := by
    apply Complex.differentiableAt_Gamma
    intro n hn
    have hre := congrArg Complex.re hn
    simp [w] at hre
    by_cases hn0 : n = 0
    · subst n
      norm_num at hre
      linarith
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
      linarith
  have hGamma : ContinuousAt (fun y : ℝ × ℝ =>
      Complex.Gamma
        (((-(sigma + 1 / 4) : ℝ) : ℂ) + (y.2 : ℂ) * I)) p := by
    change ContinuousAt (Complex.Gamma ∘ (fun y : ℝ × ℝ =>
      (((-(sigma + 1 / 4) : ℝ) : ℂ) + (y.2 : ℂ) * I))) p
    exact ContinuousAt.comp
      (f := fun y : ℝ × ℝ =>
        (((-(sigma + 1 / 4) : ℝ) : ℂ) + (y.2 : ℂ) * I))
      (g := Complex.Gamma)
      (by simpa [w] using hGammaDiff.continuousAt) hwinner
  have hcpowDiff : DifferentiableAt ℂ (fun a : ℂ => (X : ℂ) ^ a) w :=
    differentiableAt_id.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  have hcpow : ContinuousAt (fun y : ℝ × ℝ =>
      (X : ℂ) ^ (((-(sigma + 1 / 4) : ℝ) : ℂ) + (y.2 : ℂ) * I)) p := by
    change ContinuousAt ((fun a : ℂ => (X : ℂ) ^ a) ∘
      (fun y : ℝ × ℝ =>
        (((-(sigma + 1 / 4) : ℝ) : ℂ) + (y.2 : ℂ) * I))) p
    exact ContinuousAt.comp
      (f := fun y : ℝ × ℝ =>
        (((-(sigma + 1 / 4) : ℝ) : ℂ) + (y.2 : ℂ) * I))
      (g := fun a : ℂ => (X : ℂ) ^ a)
      (by simpa [w] using hcpowDiff.continuousAt) hwinner
  unfold Function.uncurry longTailShellIntegrand
  exact (((hfac.pow 2).mul hshell).mul hGamma).mul hcpow

/-- The weighted square of one finite shell is genuinely integrable on the
whole Mellin line. -/
theorem integrable_gammaWeight_mul_longTailShell_sq
    (psi : DirichletCharacter ℂ d) {X sigma t : ℝ}
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) (j : ℕ) :
    Integrable (fun v : ℝ =>
      gammaPolynomialWeight (-(sigma + 1 / 4)) v *
        ‖ramachandraReflectedTailDyadicShell psi X
          (longFunctionalPoint sigma t v) j‖ ^ 2) := by
  let C : ℝ := longTailShellUniformNormBound psi X sigma j
  have hC : 0 ≤ C := by dsimp [C, longTailShellUniformNormBound]; positivity
  have hmajor : Integrable (fun v => C ^ 2 *
      gammaPolynomialWeight (-(sigma + 1 / 4)) v) :=
    (integrable_gammaPolynomialWeight hcLo hcHi).const_mul (C ^ 2)
  apply hmajor.mono'
  · exact ((continuous_gammaPolynomialWeight hcLo hcHi).mul
      ((continuous_longTailShell psi X sigma t j).norm.pow 2)).aestronglyMeasurable
  · filter_upwards with v
    have hs := norm_longTailShell_le_uniform psi X sigma t v j
    have hs2 : ‖ramachandraReflectedTailDyadicShell psi X
        (longFunctionalPoint sigma t v) j‖ ^ 2 ≤ C ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hs 2
    rw [Real.norm_of_nonneg (mul_nonneg
      (gammaPolynomialWeight_nonneg _ _) (sq_nonneg _))]
    calc
      gammaPolynomialWeight (-(sigma + 1 / 4)) v *
          ‖ramachandraReflectedTailDyadicShell psi X
            (longFunctionalPoint sigma t v) j‖ ^ 2 ≤
        gammaPolynomialWeight (-(sigma + 1 / 4)) v * C ^ 2 :=
          mul_le_mul_of_nonneg_left hs2 (gammaPolynomialWeight_nonneg _ _)
      _ = C ^ 2 * gammaPolynomialWeight (-(sigma + 1 / 4)) v := by ring

theorem continuous_longTailShellIntegrand
    (psi : DirichletCharacter ℂ d) {X sigma t : ℝ} (hX : 0 < X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) (j : ℕ) :
    Continuous (longTailShellIntegrand psi X sigma t j) := by
  rw [continuous_iff_continuousAt]
  intro v
  let z : ℂ := longFunctionalPoint sigma t v
  let w : ℂ := ((-(sigma + 1 / 4) : ℝ) : ℂ) + (v : ℂ) * I
  have hzinner : ContinuousAt (fun y : ℝ =>
      longFunctionalPoint sigma t y) v := by
    unfold longFunctionalPoint
    fun_prop
  have hzre : z.re = -(1 / 4 : ℝ) := longFunctionalPoint_re sigma t v
  have hfacDiff :=
    differentiableAt_ramachandraFunctionalFactor psi (z := z) (by
      rw [sub_re, one_re, hzre]
      norm_num)
  have hfac : ContinuousAt (fun y : ℝ =>
      ramachandraFunctionalFactor psi (longFunctionalPoint sigma t y)) v := by
    change ContinuousAt
      (ramachandraFunctionalFactor psi ∘
        (fun y : ℝ => longFunctionalPoint sigma t y)) v
    exact ContinuousAt.comp
      (f := fun y : ℝ => longFunctionalPoint sigma t y)
      (g := ramachandraFunctionalFactor psi)
      (by simpa [z] using hfacDiff.continuousAt) hzinner
  have hshell : ContinuousAt (fun y =>
      ramachandraReflectedTailDyadicShell psi X
        (longFunctionalPoint sigma t y) j) v :=
    (continuous_longTailShell psi X sigma t j).continuousAt
  have hwinner : ContinuousAt (fun y : ℝ =>
      (((-(sigma + 1 / 4) : ℝ) : ℂ) + (y : ℂ) * I)) v := by fun_prop
  have hGammaDiff : DifferentiableAt ℂ Complex.Gamma w := by
    apply Complex.differentiableAt_Gamma
    intro n hn
    have hre := congrArg Complex.re hn
    simp [w] at hre
    by_cases hn0 : n = 0
    · subst n
      norm_num at hre
      linarith
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
      linarith
  have hGamma : ContinuousAt (fun y : ℝ =>
      Complex.Gamma (((-(sigma + 1 / 4) : ℝ) : ℂ) + (y : ℂ) * I)) v :=
    by
      change ContinuousAt (Complex.Gamma ∘ (fun y : ℝ =>
        (((-(sigma + 1 / 4) : ℝ) : ℂ) + (y : ℂ) * I))) v
      exact ContinuousAt.comp
        (f := fun y : ℝ => (((-(sigma + 1 / 4) : ℝ) : ℂ) + (y : ℂ) * I))
        (g := Complex.Gamma)
        (by simpa [w] using hGammaDiff.continuousAt) hwinner
  have hcpowDiff : DifferentiableAt ℂ (fun p : ℂ => (X : ℂ) ^ p) w :=
    differentiableAt_id.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  have hcpow : ContinuousAt (fun y : ℝ =>
      (X : ℂ) ^ (((-(sigma + 1 / 4) : ℝ) : ℂ) + (y : ℂ) * I)) v :=
    by
      change ContinuousAt ((fun p : ℂ => (X : ℂ) ^ p) ∘ (fun y : ℝ =>
        (((-(sigma + 1 / 4) : ℝ) : ℂ) + (y : ℂ) * I))) v
      exact ContinuousAt.comp
        (f := fun y : ℝ => (((-(sigma + 1 / 4) : ℝ) : ℂ) + (y : ℂ) * I))
        (g := fun p : ℂ => (X : ℂ) ^ p)
        (by simpa [w] using hcpowDiff.continuousAt) hwinner
  unfold longTailShellIntegrand
  exact (((hfac.pow 2).mul hshell).mul hGamma).mul hcpow

private theorem sqrt_factorization_of_sq
    {a w g : ℝ} (ha : 0 ≤ a) (hw : 0 ≤ w) (hg : 0 ≤ g)
    (h : a ^ 2 ≤ w * g) :
    a ≤ Real.sqrt w * Real.sqrt g := by
  have hsq : a ≤ Real.sqrt (w * g) := by
    rw [← Real.sqrt_sq ha]
    exact Real.sqrt_le_sqrt h
  rwa [Real.sqrt_mul hw] at hsq

private theorem integrable_of_ae_sqrt_mul_sqrt
    (f : ℝ → ℂ) (w g : ℝ → ℝ)
    (hfmeas : AEStronglyMeasurable f)
    (hw : Integrable w) (hg : Integrable g)
    (hw0 : ∀ x, 0 ≤ w x) (hg0 : ∀ x, 0 ≤ g x)
    (hfg : ∀ᵐ x, ‖f x‖ ≤ Real.sqrt (w x) * Real.sqrt (g x)) :
    Integrable f := by
  let sw : ℝ → ℝ := fun x => Real.sqrt (w x)
  let sg : ℝ → ℝ := fun x => Real.sqrt (g x)
  have hswMeas : AEStronglyMeasurable sw :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hw.1
  have hsgMeas : AEStronglyMeasurable sg :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hg.1
  have hsw2 : MemLp sw 2 := by
    rw [memLp_two_iff_integrable_sq hswMeas]
    have heq : (fun x => sw x ^ 2) = w := by
      funext x
      exact Real.sq_sqrt (hw0 x)
    rwa [heq]
  have hsg2 : MemLp sg 2 := by
    rw [memLp_two_iff_integrable_sq hsgMeas]
    have heq : (fun x => sg x ^ 2) = g := by
      funext x
      exact Real.sq_sqrt (hg0 x)
    rwa [heq]
  have hprod : Integrable (sw * sg) := hsw2.integrable_mul hsg2
  apply hprod.mono' hfmeas
  simpa [sw, sg] using hfg

/-- Almost-everywhere pointwise square majorant. -/
theorem norm_longTailShellIntegrand_sq_le_ae
    (psi : DirichletCharacter ℂ d) (hprim : psi.IsPrimitive)
    {X sigma t : ℝ} (hX : 0 < X) (j : ℕ) :
    ∀ᵐ v : ℝ,
      ‖longTailShellIntegrand psi X sigma t j v‖ ^ 2 ≤
        (gammaPolynomialWeight (-(sigma + 1 / 4)) v) *
          ((longFunctionalMomentConstant * (d : ℝ) ^ 3 *
              Real.rpow X (-2 * (sigma + 1 / 4)) *
              (1 + |t|) ^ 3) *
            gammaPolynomialWeight (-(sigma + 1 / 4)) v *
            ‖ramachandraReflectedTailDyadicShell psi X
              (longFunctionalPoint sigma t v) j‖ ^ 2) := by
  have hneae : ∀ᵐ v : ℝ, v ≠ -t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hneae] with v hv
  have hne : t + v ≠ 0 := by
    intro h
    apply hv
    linarith
  have hfac := norm_functionalFactor_long_pow_four_le
    psi hprim (sigma := sigma) (t := t) (v := v) hne
  have hsep := one_add_abs_add_pow_three_le t v
  have hscale :
      ‖(X : ℂ) ^ (((-(sigma + 1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖ ^ 2 =
        Real.rpow X (-2 * (sigma + 1 / 4)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, zero_mul,
      mul_zero, sub_zero, add_zero]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]
    congr 1
    ring
  have hvbase : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
  have hvpow : (1 + |v|) ^ 3 ≤ (1 + |v|) ^ 12 := by
    gcongr <;> norm_num
  unfold longTailShellIntegrand gammaPolynomialWeight
  simp only [norm_mul, norm_pow]
  let R : ℝ :=
    ‖ramachandraReflectedTailDyadicShell psi X
      (longFunctionalPoint sigma t v) j‖ ^ 2
  let G : ℝ :=
    ‖Complex.Gamma
      (((-(sigma + 1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hG : 0 ≤ G := norm_nonneg _
  have hXpow : 0 ≤ Real.rpow X (-2 * (sigma + 1 / 4)) :=
    Real.rpow_nonneg hX.le _
  have hleftEq :
      (‖ramachandraFunctionalFactor psi (longFunctionalPoint sigma t v)‖ ^ 2 *
            ‖ramachandraReflectedTailDyadicShell psi X
              (longFunctionalPoint sigma t v) j‖ *
          ‖Complex.Gamma
            (((-(sigma + 1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖ *
        ‖(X : ℂ) ^ (((-(sigma + 1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖) ^ 2 =
        ‖ramachandraFunctionalFactor psi (longFunctionalPoint sigma t v)‖ ^ 4 *
          R * G ^ 2 * Real.rpow X (-2 * (sigma + 1 / 4)) := by
    calc
      _ = ‖ramachandraFunctionalFactor psi (longFunctionalPoint sigma t v)‖ ^ 4 *
          ‖ramachandraReflectedTailDyadicShell psi X
            (longFunctionalPoint sigma t v) j‖ ^ 2 *
          ‖Complex.Gamma
            (((-(sigma + 1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖ ^ 2 *
          ‖(X : ℂ) ^ (((-(sigma + 1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖ ^ 2 := by
            ring
      _ = _ := by rw [hscale]
  rw [hleftEq]
  calc
    ‖ramachandraFunctionalFactor psi (longFunctionalPoint sigma t v)‖ ^ 4 *
          R * G ^ 2 * Real.rpow X (-2 * (sigma + 1 / 4)) ≤
        (longFunctionalMomentConstant * (d : ℝ) ^ 3 *
            (1 + |t + v|) ^ 3) * R * G ^ 2 *
              Real.rpow X (-2 * (sigma + 1 / 4)) := by
      gcongr
    _ ≤ (longFunctionalMomentConstant * (d : ℝ) ^ 3 *
            ((1 + |t|) ^ 3 * (1 + |v|) ^ 3)) * R * G ^ 2 *
              Real.rpow X (-2 * (sigma + 1 / 4)) := by
      have hQ : 0 ≤ longFunctionalMomentConstant * (d : ℝ) ^ 3 :=
        mul_nonneg longFunctionalMomentConstant_nonneg (by positivity)
      gcongr
    _ ≤ (G * (1 + |v|) ^ 6) *
          ((longFunctionalMomentConstant * (d : ℝ) ^ 3 *
              Real.rpow X (-2 * (sigma + 1 / 4)) *
              (1 + |t|) ^ 3) *
            (G * (1 + |v|) ^ 6) * R) := by
      have hC : 0 ≤ longFunctionalMomentConstant * (d : ℝ) ^ 3 *
          Real.rpow X (-2 * (sigma + 1 / 4)) * (1 + |t|) ^ 3 := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg longFunctionalMomentConstant_nonneg (by positivity))
            hXpow) (by positivity)
      let P : ℝ := longFunctionalMomentConstant * (d : ℝ) ^ 3 *
        Real.rpow X (-2 * (sigma + 1 / 4)) * (1 + |t|) ^ 3 *
          R * G ^ 2
      have hP : 0 ≤ P := by dsimp [P]; positivity
      calc
        (longFunctionalMomentConstant * (d : ℝ) ^ 3 *
              ((1 + |t|) ^ 3 * (1 + |v|) ^ 3)) * R * G ^ 2 *
                Real.rpow X (-2 * (sigma + 1 / 4)) =
            P * (1 + |v|) ^ 3 := by dsimp [P]; ring
        _ ≤ P * (1 + |v|) ^ 12 :=
          mul_le_mul_of_nonneg_left hvpow hP
        _ = (G * (1 + |v|) ^ 6) *
          ((longFunctionalMomentConstant * (d : ℝ) ^ 3 *
              Real.rpow X (-2 * (sigma + 1 / 4)) *
              (1 + |t|) ^ 3) *
            (G * (1 + |v|) ^ 6) * R) := by dsimp [P]; ring

/-- Weighted Cauchy for one shell.  The two integrability assumptions are
literal scalar integrability statements, not moment estimates. -/
theorem norm_integral_longTailShell_sq_le
    (psi : DirichletCharacter ℂ d) (hprim : psi.IsPrimitive)
    {X sigma t : ℝ} (hX : 0 < X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) (j : ℕ)
    (hf : Integrable (longTailShellIntegrand psi X sigma t j))
    (hblock : Integrable (fun v : ℝ =>
      gammaPolynomialWeight (-(sigma + 1 / 4)) v *
        ‖ramachandraReflectedTailDyadicShell psi X
          (longFunctionalPoint sigma t v) j‖ ^ 2)) :
    ‖∫ v : ℝ, longTailShellIntegrand psi X sigma t j v‖ ^ 2 ≤
      (∫ v : ℝ, gammaPolynomialWeight (-(sigma + 1 / 4)) v) *
        ∫ v : ℝ,
          (longFunctionalMomentConstant * (d : ℝ) ^ 3 *
              Real.rpow X (-2 * (sigma + 1 / 4)) *
              (1 + |t|) ^ 3) *
            gammaPolynomialWeight (-(sigma + 1 / 4)) v *
            ‖ramachandraReflectedTailDyadicShell psi X
              (longFunctionalPoint sigma t v) j‖ ^ 2 := by
  let A : ℝ := longFunctionalMomentConstant * (d : ℝ) ^ 3 *
    Real.rpow X (-2 * (sigma + 1 / 4)) * (1 + |t|) ^ 3
  let w := gammaPolynomialWeight (-(sigma + 1 / 4))
  let g : ℝ → ℝ := fun v => A * w v *
    ‖ramachandraReflectedTailDyadicShell psi X
      (longFunctionalPoint sigma t v) j‖ ^ 2
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg longFunctionalMomentConstant_nonneg (by positivity))
        (Real.rpow_nonneg hX.le _)) (by positivity)
  apply RamachandraWeightedCauchyAE.norm_integral_sq_le_integral_mul_integral_ae
    (f := longTailShellIntegrand psi X sigma t j) (w := w) (g := g)
      hf (integrable_gammaPolynomialWeight hcLo hcHi)
      (by
        simpa only [g, w, mul_assoc] using hblock.const_mul A)
      (fun v => gammaPolynomialWeight_nonneg _ _)
      (fun v => by
        dsimp [g]
        exact mul_nonneg
          (mul_nonneg hA (gammaPolynomialWeight_nonneg _ _)) (sq_nonneg _))
  filter_upwards [norm_longTailShellIntegrand_sq_le_ae
    psi hprim hX j] with v hv
  apply sqrt_factorization_of_sq (norm_nonneg _)
    (gammaPolynomialWeight_nonneg _ _) (by
      dsimp [g]
      exact mul_nonneg
        (mul_nonneg hA (gammaPolynomialWeight_nonneg _ _)) (sq_nonneg _))
  simpa [g, A, w, mul_assoc] using hv

/-- Premise-free shell Cauchy bound: continuity plus the certified Gamma
mass and finite-shell norm bound discharge both integrability hypotheses. -/
theorem norm_integral_longTailShell_sq_le_certified
    (psi : DirichletCharacter ℂ d) (hprim : psi.IsPrimitive)
    {X sigma t : ℝ} (hX : 0 < X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) (j : ℕ) :
    ‖∫ v : ℝ, longTailShellIntegrand psi X sigma t j v‖ ^ 2 ≤
      (∫ v : ℝ, gammaPolynomialWeight (-(sigma + 1 / 4)) v) *
        ∫ v : ℝ,
          (longFunctionalMomentConstant * (d : ℝ) ^ 3 *
              Real.rpow X (-2 * (sigma + 1 / 4)) *
              (1 + |t|) ^ 3) *
            gammaPolynomialWeight (-(sigma + 1 / 4)) v *
            ‖ramachandraReflectedTailDyadicShell psi X
              (longFunctionalPoint sigma t v) j‖ ^ 2 := by
  let A : ℝ := longFunctionalMomentConstant * (d : ℝ) ^ 3 *
    Real.rpow X (-2 * (sigma + 1 / 4)) * (1 + |t|) ^ 3
  let w := gammaPolynomialWeight (-(sigma + 1 / 4))
  let g : ℝ → ℝ := fun v => A * w v *
    ‖ramachandraReflectedTailDyadicShell psi X
      (longFunctionalPoint sigma t v) j‖ ^ 2
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg longFunctionalMomentConstant_nonneg (by positivity))
        (Real.rpow_nonneg hX.le _)) (by positivity)
  have hw : Integrable w := integrable_gammaPolynomialWeight hcLo hcHi
  have hblock := integrable_gammaWeight_mul_longTailShell_sq
    psi (X := X) (sigma := sigma) (t := t) hcLo hcHi j
  have hg : Integrable g := by
    simpa only [g, w, mul_assoc] using hblock.const_mul A
  have hw0 (v : ℝ) : 0 ≤ w v := gammaPolynomialWeight_nonneg _ _
  have hg0 (v : ℝ) : 0 ≤ g v := by
    dsimp [g]
    exact mul_nonneg (mul_nonneg hA (hw0 v)) (sq_nonneg _)
  have hsq := norm_longTailShellIntegrand_sq_le_ae
    psi hprim (X := X) (sigma := sigma) (t := t) hX j
  have hfg : ∀ᵐ v : ℝ,
      ‖longTailShellIntegrand psi X sigma t j v‖ ≤
        Real.sqrt (w v) * Real.sqrt (g v) := by
    filter_upwards [hsq] with v hv
    apply sqrt_factorization_of_sq (norm_nonneg _) (hw0 v) (hg0 v)
    simpa [w, g, A, mul_assoc] using hv
  have hf : Integrable (longTailShellIntegrand psi X sigma t j) :=
    integrable_of_ae_sqrt_mul_sqrt _ w g
      (continuous_longTailShellIntegrand psi hX hcLo hcHi j).aestronglyMeasurable
      hw hg hw0 hg0 hfg
  exact norm_integral_longTailShell_sq_le psi hprim hX hcLo hcHi j hf hblock

end
end RamachandraLongTailShellCauchy

#print axioms RamachandraLongTailShellCauchy.norm_longTailShellIntegrand_sq_le_ae
#print axioms RamachandraLongTailShellCauchy.norm_integral_longTailShell_sq_le
#print axioms RamachandraLongTailShellCauchy.norm_integral_longTailShell_sq_le_certified
