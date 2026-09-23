import RamachandraLongTailShellSecondMoment
import RamachandraLpSeriesMinkowski
import RamachandraFunctionalFactorEnvelope

/-!
# Literal infinite-shell assembly for the shifted long contour

This module proves that the exact long reflected contour is the sum of its
standard dyadic shell integrals.  The proof is absolute: the dyadic uniform
shell norms are summable, and the fixed long-line Gamma/functional-factor
weight is integrable.  No moment estimate is assumed here.
-/

namespace RamachandraLongContourInfiniteAssembly

open scoped BigOperators Interval LSeries.notation
open Complex MeasureTheory
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedFunctionalEquationBridge
open RamachandraShiftedReflectedTailInfiniteAssembly
open RamachandraShiftedContourSharpEnvelopes
open RamachandraLongTailShellCauchy
open BHPRamachandraMeanValueFromDyadicAFE
open RamachandraShiftedReflectedSeries
open RamachandraGammaWeightIntegrability
open RamachandraFunctionalFactorEnvelope
open RamachandraShiftedFunctionalFactorMomentEnvelope
open MAPMRTLemma210OrthogonalityReduction
open MontgomeryVaughanFiniteReduction

noncomputable section

set_option maxHeartbeats 2000000

variable {d : ℕ} [NeZero d]

private theorem uniformNormBound_eq_shell_norm_sum
    (psi : DirichletCharacter ℂ d) (X sigma : ℝ) (j : ℕ) :
    longTailShellUniformNormBound psi X sigma j =
      ∑ n ∈ dyadicSupport (2 ^ j),
        ‖if X < n then
            ramachandraReflectedTerm psi (longFunctionalPoint sigma 0 0) n
          else 0‖ := by
  unfold longTailShellUniformNormBound
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
  by_cases hXn : X < n
  · rw [if_pos hXn]
    have hp : longFunctionalPoint sigma 0 0 =
        ramachandraShiftedPoint sigma 0 +
          (((-(sigma + 1 / 4) : ℝ) : ℂ) + (0 : ℂ) * I) := by
      apply Complex.ext <;>
        simp [longFunctionalPoint, ramachandraShiftedPoint] <;> ring
    rw [hp]
    simp only [ofReal_zero, zero_mul, add_zero]
    have href := reflectedTerm_eq_blockTerm psi hnpos sigma
      (-(sigma + 1 / 4)) 0 0
    simp only [ofReal_zero, zero_mul, add_zero] at href
    rw [href]
    simp [reflectedTailInfiniteShellCoeff, hXn, norm_mul, norm_twistedPhase]
  · simp [reflectedTailInfiniteShellCoeff, hXn]


/-- A global pointwise envelope for one long shell.  Unlike the sharp moment
bound, this qualitative envelope is valid also at `t+v=0`; it is used only
to justify exchanging the absolutely convergent shell series and integral. -/
theorem norm_longTailShellIntegrand_le_global_of_envelope
    (psi : DirichletCharacter ℂ d)
    {X sigma t : ℝ} (hX : 0 < X) {Cgamma : ℝ}
    (hCgamma : 0 ≤ Cgamma)
    (hglobal : ∀ z : ℂ, -(1 / 4 : ℝ) ≤ z.re → z.re ≤ 1 / 2 →
      ‖ramachandraFunctionalFactor psi z‖ ≤
        Real.rpow (d : ℝ) (1 / 2 - z.re) *
          (Cgamma * (1 + |z.im|) ^ 3))
    (j : ℕ) (v : ℝ) :
    ‖longTailShellIntegrand psi X sigma t j v‖ ≤
      (Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
          Real.rpow X (-(sigma + 1 / 4)) * (1 + |t|) ^ 6) *
        gammaPolynomialWeight (-(sigma + 1 / 4)) v *
        longTailShellUniformNormBound psi X sigma j := by
  let z := longFunctionalPoint sigma t v
  have hzre : z.re = -(1 / 4 : ℝ) := longFunctionalPoint_re sigma t v
  have hzim : z.im = t + v := longFunctionalPoint_im sigma t v
  have hfac := hglobal z (by rw [hzre]) (by rw [hzre]; norm_num)
  rw [hzre, hzim] at hfac
  norm_num at hfac
  have hfac2 := pow_le_pow_left₀ (norm_nonneg _) hfac 2
  have hsep3 := one_add_abs_add_pow_three_le t v
  have hsep6 : (1 + |t + v|) ^ 6 ≤
      (1 + |t|) ^ 6 * (1 + |v|) ^ 6 := by
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (1 + |t + v|) ^ 3)
      hsep3 2
    nlinarith
  have hshell := norm_longTailShell_le_uniform psi X sigma t v j
  have hscale :
      ‖(X : ℂ) ^ (((-(sigma + 1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖ =
        Real.rpow X (-(sigma + 1 / 4)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
    simp
  have hdcalc :
      (Real.rpow (d : ℝ) (3 / 4)) ^ 2 =
        Real.rpow (d : ℝ) (3 / 2) := by
    calc
      (Real.rpow (d : ℝ) (3 / 4)) ^ 2 =
          Real.rpow (Real.rpow (d : ℝ) (3 / 4)) (2 : ℝ) := by
        exact (Real.rpow_natCast _ 2).symm
      _ = Real.rpow (d : ℝ) ((3 / 4 : ℝ) * 2) := by
        exact (Real.rpow_mul (Nat.cast_nonneg d) (3 / 4 : ℝ) 2).symm
      _ = Real.rpow (d : ℝ) (3 / 2) := by norm_num
  unfold longTailShellIntegrand gammaPolynomialWeight
  simp only [norm_mul, norm_pow]
  rw [hscale]
  have hfacFinal :
      ‖ramachandraFunctionalFactor psi z‖ ^ 2 ≤
        Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
          ((1 + |t|) ^ 6 * (1 + |v|) ^ 6) := by
    calc
      ‖ramachandraFunctionalFactor psi z‖ ^ 2 ≤
          (Real.rpow (d : ℝ) (3 / 4) *
            (Cgamma * (1 + |t + v|) ^ 3)) ^ 2 := hfac2
      _ = Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
            (1 + |t + v|) ^ 6 := by rw [mul_pow, mul_pow, hdcalc]; ring
      _ ≤ Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
            ((1 + |t|) ^ 6 * (1 + |v|) ^ 6) := by
        exact mul_le_mul_of_nonneg_left hsep6
          (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (sq_nonneg _))
  have hnonneg : 0 ≤ Real.rpow X (-(sigma + 1 / 4)) :=
    Real.rpow_nonneg hX.le _
  calc
    ‖ramachandraFunctionalFactor psi z‖ ^ 2 *
          ‖ramachandraReflectedTailDyadicShell psi X z j‖ *
          ‖Complex.Gamma
            (((-(sigma + 1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖ *
          Real.rpow X (-(sigma + 1 / 4)) ≤
        (Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
          ((1 + |t|) ^ 6 * (1 + |v|) ^ 6)) *
          longTailShellUniformNormBound psi X sigma j *
          ‖Complex.Gamma
            (((-(sigma + 1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖ *
          Real.rpow X (-(sigma + 1 / 4)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul hfacFinal hshell (norm_nonneg _)
            (mul_nonneg
              (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (sq_nonneg _))
              (mul_nonneg (by positivity) (by positivity))))
          (norm_nonneg _)) hnonneg
    _ = (Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
          Real.rpow X (-(sigma + 1 / 4)) * (1 + |t|) ^ 6) *
        (‖Complex.Gamma
            (((-(sigma + 1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖ *
          (1 + |v|) ^ 6) *
        longTailShellUniformNormBound psi X sigma j := by ring

/-- Primitive-character wrapper around the envelope-parametrized pointwise
bound.  The proof itself only needs the displayed functional-factor envelope. -/
theorem norm_longTailShellIntegrand_le_global
    (psi : DirichletCharacter ℂ d) (_hprim : psi.IsPrimitive)
    {X sigma t : ℝ} (hX : 0 < X) {Cgamma : ℝ}
    (hCgamma : 0 ≤ Cgamma)
    (hglobal : ∀ z : ℂ, -(1 / 4 : ℝ) ≤ z.re → z.re ≤ 1 / 2 →
      ‖ramachandraFunctionalFactor psi z‖ ≤
        Real.rpow (d : ℝ) (1 / 2 - z.re) *
          (Cgamma * (1 + |z.im|) ^ 3))
    (j : ℕ) (v : ℝ) :
    ‖longTailShellIntegrand psi X sigma t j v‖ ≤
      (Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
          Real.rpow X (-(sigma + 1 / 4)) * (1 + |t|) ^ 6) *
        gammaPolynomialWeight (-(sigma + 1 / 4)) v *
        longTailShellUniformNormBound psi X sigma j :=
  norm_longTailShellIntegrand_le_global_of_envelope psi hX hCgamma hglobal j v

/-- The scalar absolute norm of every exact dyadic tail shell is summable.
This is the absolute-convergence input for exchanging the shell series with
the Mellin integral. -/
theorem summable_longTailShellUniformNormBound
    (psi : DirichletCharacter ℂ d) {X sigma : ℝ} (hX : 1 ≤ X) :
    Summable (fun j : ℕ => longTailShellUniformNormBound psi X sigma j) := by
  let z : ℂ := longFunctionalPoint sigma 0 0
  let f : ℕ → ℝ := fun n =>
    ‖if X < n then ramachandraReflectedTerm psi z n else 0‖
  have hz : 1 < (1 - z).re := by
    simp [z, longFunctionalPoint, ramachandraShiftedPoint]
  have hfull : Summable (fun n : ℕ => ramachandraReflectedTerm psi z n) :=
    summable_ramachandraReflectedTerm psi hz
  have hf : Summable f := by
    have hi : Summable (fun n : ℕ =>
        if X < n then ramachandraReflectedTerm psi z n else 0) := by
      simpa [Set.indicator] using!
        hfull.indicator ({n : ℕ | X < (n : ℝ)} : Set ℕ)
    simpa [f] using hi.norm
  have hcompl : Summable
      (fun n : {n : ℕ // n ∉ ({0, 1} : Finset ℕ)} => f n) :=
    hf.comp_injective Subtype.val_injective
  have hsigma : Summable
      (fun a : ReflectedDyadicIndex => f a.2.1) := by
    exact (reflectedDyadicIndexEquivNatCompl.summable_iff).2 hcompl
  have hgroup : Summable (fun j : ℕ =>
      ∑' n : {n : ℕ // n ∈ dyadicSupport (2 ^ j)}, f n) :=
    hsigma.sigma
  convert hgroup using 1
  funext j
  rw [uniformNormBound_eq_shell_norm_sum psi X sigma j]
  rw [← Finset.sum_attach, tsum_fintype]
  rfl


/-- Every exact long shell is Bochner integrable on the full Mellin line. -/
theorem integrable_longTailShellIntegrand_global
    (psi : DirichletCharacter ℂ d) (hprim : psi.IsPrimitive)
    {X sigma t : ℝ} (hX : 0 < X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) (j : ℕ) :
    Integrable (longTailShellIntegrand psi X sigma t j) := by
  rcases exists_norm_ramachandraFunctionalFactor_le_global (q := d) with
    ⟨Cgamma, hCgamma, hglobal⟩
  let B : ℝ := Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
    Real.rpow X (-(sigma + 1 / 4)) * (1 + |t|) ^ 6
  let Cj : ℝ := longTailShellUniformNormBound psi X sigma j
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hCj0 : 0 ≤ Cj := by
    dsimp [Cj, longTailShellUniformNormBound]
    positivity
  have hmajor : Integrable (fun v : ℝ =>
      (B * Cj) * gammaPolynomialWeight (-(sigma + 1 / 4)) v) :=
    (integrable_gammaPolynomialWeight hcLo hcHi).const_mul (B * Cj)
  apply hmajor.mono'
  · exact (continuous_longTailShellIntegrand psi hX hcLo hcHi j).aestronglyMeasurable
  · filter_upwards with v
    have h := norm_longTailShellIntegrand_le_global psi hprim (sigma := sigma) (t := t) hX
      (le_trans (by norm_num) hCgamma) (hglobal psi hprim) j v
    simpa [B, Cj, mul_assoc, mul_comm, mul_left_comm] using h

/-- Quantitative full-line norm bound for one integrated shell, with the
qualitative global functional-factor constant exposed. -/
theorem norm_integral_longTailShell_le_global
    (psi : DirichletCharacter ℂ d) (hprim : psi.IsPrimitive)
    {X sigma t : ℝ} (hX : 0 < X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) {Cgamma : ℝ}
    (hCgamma : 0 ≤ Cgamma)
    (hglobal : ∀ z : ℂ, -(1 / 4 : ℝ) ≤ z.re → z.re ≤ 1 / 2 →
      ‖ramachandraFunctionalFactor psi z‖ ≤
        Real.rpow (d : ℝ) (1 / 2 - z.re) *
          (Cgamma * (1 + |z.im|) ^ 3))
    (j : ℕ) :
    ‖∫ v : ℝ, longTailShellIntegrand psi X sigma t j v‖ ≤
      (Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
        Real.rpow X (-(sigma + 1 / 4)) * (1 + |t|) ^ 6) *
      (∫ v : ℝ, gammaPolynomialWeight (-(sigma + 1 / 4)) v) *
      longTailShellUniformNormBound psi X sigma j := by
  let B : ℝ := Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
    Real.rpow X (-(sigma + 1 / 4)) * (1 + |t|) ^ 6
  have hInt := integrable_longTailShellIntegrand_global psi hprim (t := t) hX hcLo hcHi j
  have hmajor := (integrable_gammaPolynomialWeight hcLo hcHi).const_mul
    (B * longTailShellUniformNormBound psi X sigma j)
  calc
    ‖∫ v : ℝ, longTailShellIntegrand psi X sigma t j v‖ ≤
        ∫ v : ℝ, ‖longTailShellIntegrand psi X sigma t j v‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ v : ℝ, B * longTailShellUniformNormBound psi X sigma j *
        gammaPolynomialWeight (-(sigma + 1 / 4)) v := by
      apply integral_mono hInt.norm hmajor
      intro v
      have h := norm_longTailShellIntegrand_le_global psi hprim
        (sigma := sigma) (t := t) hX hCgamma hglobal j v
      simpa [B, mul_assoc, mul_comm, mul_left_comm] using h
    _ = B * (∫ v : ℝ, gammaPolynomialWeight (-(sigma + 1 / 4)) v) *
        longTailShellUniformNormBound psi X sigma j := by
      rw [MeasureTheory.integral_const_mul]
      ring

/-- The integral norms of the exact shells form a summable scalar series. -/
theorem summable_integral_norm_longTailShellIntegrand
    (psi : DirichletCharacter ℂ d) (hprim : psi.IsPrimitive)
    {X sigma t : ℝ} (hX : 1 ≤ X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) :
    Summable (fun j : ℕ =>
      ∫ v : ℝ, ‖longTailShellIntegrand psi X sigma t j v‖) := by
  rcases exists_norm_ramachandraFunctionalFactor_le_global (q := d) with
    ⟨Cgamma, hCgamma, hglobal⟩
  let B : ℝ := Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
    Real.rpow X (-(sigma + 1 / 4)) * (1 + |t|) ^ 6
  let W : ℝ := ∫ v : ℝ, gammaPolynomialWeight (-(sigma + 1 / 4)) v
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hW0 : 0 ≤ W := integral_nonneg (fun v => gammaPolynomialWeight_nonneg _ _)
  have hbase := (summable_longTailShellUniformNormBound psi (sigma := sigma) hX).mul_left (B * W)
  apply Summable.of_nonneg_of_le
    (fun j => integral_nonneg (fun v => norm_nonneg _))
    (fun j => ?_) hbase
  have hInt := integrable_longTailShellIntegrand_global psi hprim (t := t) (lt_of_lt_of_le zero_lt_one hX) hcLo hcHi j
  have hmajor := (integrable_gammaPolynomialWeight hcLo hcHi).const_mul
    (B * longTailShellUniformNormBound psi X sigma j)
  calc
    (∫ v : ℝ, ‖longTailShellIntegrand psi X sigma t j v‖) ≤
        ∫ v : ℝ, B * longTailShellUniformNormBound psi X sigma j *
          gammaPolynomialWeight (-(sigma + 1 / 4)) v := by
      apply integral_mono hInt.norm hmajor
      intro v
      have h := norm_longTailShellIntegrand_le_global psi hprim (sigma := sigma) (t := t)
        (lt_of_lt_of_le zero_lt_one hX)
        (le_trans (by norm_num) hCgamma) (hglobal psi hprim) j v
      simpa [B, mul_assoc, mul_comm, mul_left_comm] using h
    _ = (B * W) * longTailShellUniformNormBound psi X sigma j := by
      rw [MeasureTheory.integral_const_mul]
      dsimp [W]
      ring

/-- The pointwise shell integrands sum to the literal reflected-tail contour
integrand. -/
theorem tsum_longTailShellIntegrand_eq
    (psi : DirichletCharacter ℂ d) {X sigma t : ℝ}
    (hX : 1 ≤ X) (v : ℝ) :
    (∑' j : ℕ, longTailShellIntegrand psi X sigma t j v) =
      ramachandraShiftedContourIntegrand psi X sigma
        (-(sigma + 1 / 4)) t v true := by
  let z := longFunctionalPoint sigma t v
  have hz : 1 < (1 - z).re := by
    norm_num [z, longFunctionalPoint, ramachandraShiftedPoint]
  have hshell := tsum_ramachandraReflectedTailDyadicShell_eq psi hX hz
  unfold longTailShellIntegrand ramachandraShiftedContourIntegrand
  dsimp only
  have heq : ramachandraShiftedPoint sigma t +
        (↑(-(sigma + 1 / 4)) + ↑v * I) = z := by
    apply Complex.ext <;>
      simp [z, longFunctionalPoint, ramachandraShiftedPoint] <;> ring
  rw [heq]
  simp only [ite_true]
  let A : ℂ := ramachandraFunctionalFactor psi z ^ 2
  let B : ℂ := Complex.Gamma (↑(-(sigma + 1 / 4)) + ↑v * I) *
    ↑X ^ (↑(-(sigma + 1 / 4)) + ↑v * I)
  calc
    (∑' j : ℕ,
      ramachandraFunctionalFactor psi z ^ 2 *
          ramachandraReflectedTailDyadicShell psi X z j *
          Complex.Gamma (↑(-(sigma + 1 / 4)) + ↑v * I) *
          ↑X ^ (↑(-(sigma + 1 / 4)) + ↑v * I)) =
        ∑' j : ℕ, A * (ramachandraReflectedTailDyadicShell psi X z j * B) := by
      apply tsum_congr
      intro j
      dsimp [A, B]
      ring
    _ = A * (∑' j : ℕ,
        ramachandraReflectedTailDyadicShell psi X z j * B) := by
      rw [tsum_mul_left]
    _ = A * ((∑' j : ℕ,
        ramachandraReflectedTailDyadicShell psi X z j) * B) := by
      rw [tsum_mul_right]
    _ = A * (ramachandraReflectedTail psi X z * B) := by rw [hshell]
    _ = ramachandraFunctionalFactor psi z ^ 2 *
          ramachandraReflectedTail psi X z *
          Complex.Gamma (↑(-(sigma + 1 / 4)) + ↑v * I) *
          ↑X ^ (↑(-(sigma + 1 / 4)) + ↑v * I) := by
      dsimp [A, B]
      ring

/-- Absolute integral exchange: the integrals of the exact long shells sum
to the integral of the literal reflected-tail contour. -/
theorem hasSum_integral_longTailShellIntegrand
    (psi : DirichletCharacter ℂ d) (hprim : psi.IsPrimitive)
    {X sigma t : ℝ} (hX : 1 ≤ X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) :
    HasSum (fun j : ℕ =>
      ∫ v : ℝ, longTailShellIntegrand psi X sigma t j v)
      (∫ v : ℝ, ramachandraShiftedContourIntegrand psi X sigma
        (-(sigma + 1 / 4)) t v true) := by
  have hInt : ∀ j : ℕ, Integrable
      (longTailShellIntegrand psi X sigma t j) := fun j =>
    integrable_longTailShellIntegrand_global psi hprim (t := t) (lt_of_lt_of_le zero_lt_one hX) hcLo hcHi j
  have hSum := summable_integral_norm_longTailShellIntegrand
    psi hprim (t := t) hX hcLo hcHi
  have h := MeasureTheory.hasSum_integral_of_summable_integral_norm hInt hSum
  simpa only [tsum_longTailShellIntegrand_eq psi hX] using h

end
end RamachandraLongContourInfiniteAssembly

#print axioms RamachandraLongContourInfiniteAssembly.summable_longTailShellUniformNormBound
#print axioms RamachandraLongContourInfiniteAssembly.hasSum_integral_longTailShellIntegrand
#print axioms RamachandraLongContourInfiniteAssembly.norm_integral_longTailShell_le_global
