import GuthMaynardLemma295ExactSourceSurface
import GuthMaynardJutilaHighRangeMeanSquare
import GuthMaynardJutilaOneSpacingWeld
import GuthMaynardLowAnchorTransfer

/-!
# Finite collars and the high-length branch of Jutila Lemma 29.10

The exact-M AFE is intentionally restricted to the reflected range where the
source uses it.  Above the aperture, the unconditional Hilbert mean-square
bound supplies the first regime.  This file also records the finite prefix
collar needed below the recurrence threshold.
-/

namespace GuthMaynardLemma2910HighRangeFromAFE

open scoped BigOperators
open CGLProofDAG
open GuthMaynardJutilaReflection2941
open GuthMaynardLemma295OffDiagonalAssembly
open GuthMaynardLemma295ReflectedPairConstruction
open GuthMaynardLemma296SmoothingReduction
open GuthMaynardTPowerCardinality
open GuthMaynardLengthComparison
open GuthMaynardJutilaTransference
open GuthMaynardHeathBrownMajorant
open GuthMaynardJutilaHighRangeMeanSquare
open GuthMaynardJutilaOneSpacingWeld
open GuthMaynardLowAnchorTransfer

noncomputable section

theorem natRealIoc_zero_eq_empty_of_lt_one
    {M : ℝ} (hM0 : 0 ≤ M) (hM : M < 1) : natRealIoc 0 M = ∅ := by
  ext n
  constructor
  · intro hn
    rw [mem_natRealIoc_iff hM0] at hn
    have hnOne : 1 ≤ n := by exact_mod_cast hn.1
    have hnOneR : (1 : ℝ) ≤ n := by exact_mod_cast hnOne
    linarith
  · simp

theorem jutilaReflectedPrefixMoment_eq_zero_of_lt_one
    {M : ℝ} (hM0 : 0 ≤ M) (hM : M < 1) (G : Finset ℝ) :
    jutilaReflectedPrefixMoment M G = 0 := by
  unfold jutilaReflectedPrefixMoment sourceQuadratic realGramQuadratic
  rw [natRealIoc_zero_eq_empty_of_lt_one hM0 hM]
  simp [gramPolynomial]

/-- A fully finite bound for the reflected prefix.  This is the source-faithful
bounded-reflected-length collar needed before the recurrence threshold `M₀`:
every coefficient has norm at most one, so the ordered-pair Gram moment costs
only the square of the support cardinality. -/
theorem jutilaReflectedPrefixMoment_le_card_sq
    {M : ℝ} (hM0 : 0 ≤ M) (G : Finset ℝ) :
    jutilaReflectedPrefixMoment M G ≤
      (G.card : ℝ)^2 * ((natRealIoc 0 M).card : ℝ)^2 := by
  have hphase (n : ℕ) (g : ℝ) : ‖negativeDirichletPhase n g‖ = 1 := by
    unfold negativeDirichletPhase dirichletPhase
    rw [Complex.norm_exp]
    have hre : (((((-g * Real.log n : ℝ) : ℂ) * Complex.I))).re = 0 := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero]
    rw [hre, Real.exp_zero]
  have hpoly (g₁ g₂ : ℝ) :
      ‖gramPolynomial (natRealIoc 0 M)
          (fun n => (Real.rpow (n : ℝ) (-(1/2 : ℝ)) : ℂ))
          negativeDirichletPhase g₁ g₂‖ ≤
        ((natRealIoc 0 M).card : ℝ) := by
    unfold gramPolynomial
    calc
      ‖∑ n ∈ natRealIoc 0 M,
          (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ) *
            negativeDirichletPhase n g₁ * star (negativeDirichletPhase n g₂)‖ ≤
          ∑ n ∈ natRealIoc 0 M,
            ‖(Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ) *
              negativeDirichletPhase n g₁ * star (negativeDirichletPhase n g₂)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _n ∈ natRealIoc 0 M, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' := (mem_natRealIoc_iff hM0).mp hn
        have hnNat : 1 ≤ n := by exact_mod_cast hn'.1
        have hw : inverseSqrtWeight n ≤ 1 :=
          GuthMaynardJutilaLemma29NineKTwo.inverseSqrtWeight_le_one_of_one_le
            (by exact_mod_cast hnNat)
        rw [norm_mul, norm_mul, norm_star]
        rw [show ‖(Real.rpow (n : ℝ) (-(1/2 : ℝ)) : ℂ)‖ =
            inverseSqrtWeight n by
          have hr0 : 0 ≤ Real.rpow (n : ℝ) (-(1/2 : ℝ)) :=
            Real.rpow_nonneg (by positivity) _
          calc
            ‖(Real.rpow (n : ℝ) (-(1/2 : ℝ)) : ℂ)‖ =
                |Real.rpow (n : ℝ) (-(1/2 : ℝ))| := by
                  rw [Complex.norm_real, Real.norm_eq_abs]
            _ = Real.rpow (n : ℝ) (-(1/2 : ℝ)) := abs_of_nonneg hr0
            _ = inverseSqrtWeight n :=
              GuthMaynardJutilaLemma29NineKTwo.inverseSqrtWeight_eq_rpow_neg_half n |>.symm]
        rw [hphase, hphase]
        simpa using hw
      _ = ((natRealIoc 0 M).card : ℝ) := by simp
  unfold jutilaReflectedPrefixMoment sourceQuadratic sigmaCoefficient
    realGramQuadratic
  simp only [one_mul]
  calc
    (∑ g₁ ∈ G, ∑ g₂ ∈ G,
        ‖gramPolynomial (natRealIoc 0 M)
          (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
          negativeDirichletPhase g₁ g₂‖ ^ 2) ≤
      ∑ _g₁ ∈ G, ∑ _g₂ ∈ G,
        ((natRealIoc 0 M).card : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro g₁ hg₁
      apply Finset.sum_le_sum
      intro g₂ hg₂
      exact pow_le_pow_left₀ (norm_nonneg _) (hpoly g₁ g₂) 2
    _ = (G.card : ℝ)^2 * ((natRealIoc 0 M).card : ℝ)^2 := by simp; ring

theorem card_natRealIoc_zero_le_ceil_add_one
    {M L : ℝ} (hML : M ≤ L) :
    (natRealIoc 0 M).card ≤ Nat.ceil L + 1 := by
  unfold natRealIoc
  exact (Finset.card_filter_le _ _).trans
    (by simpa using Nat.add_le_add_right (Nat.ceil_mono hML) 1)

/-- The exact bounded-reflected-length base inequality inside the legal AFE
range.  Unlike the recurrence, it needs no lower threshold on the reflected
length: the prefix is bounded directly as a finite Gram sum. -/
theorem jutilaSecondMoment_le_finitePrefixCollar_of_exactM
    (hAFE : Lemma295ApproximateFunctionalEquationExactM)
    {delta epsilon A : ℝ}
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) (hA : 0 < A) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T N : ℝ) (G : Finset ℝ),
        T₀ ≤ T → 1 ≤ N →
        N ≤ sourceReflectionNumerator29_40 T epsilon →
        TPowerSeparated G T delta → InOpenClosedZeroT G T →
        jutilaSecondMoment N G ≤
          C * (G.card : ℝ) * N +
          C * (G.card : ℝ)^2 *
            ((natRealIoc 0 (reflectedLength29_40 T epsilon N)).card : ℝ)^2 +
          C * Real.rpow T (-A) := by
  obtain ⟨C, T₀, hC, hT₀, hpair⟩ :=
    GuthMaynardLemma295ExactSourceSurface.lemma295ReflectedPairMoment_of_exactAFE
      hAFE delta epsilon A hdelta hepsilon hA
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T N G hT hN hNupper hsep hheight
  have hraw := hpair T N G hT hN hNupper hsep hheight
  have hM0 : 0 ≤ reflectedLength29_40 T epsilon N := by
    unfold reflectedLength29_40 sourceReflectionNumerator29_40
    exact div_nonneg (Real.rpow_nonneg (by linarith) _)
      (by linarith : 0 ≤ N)
  have hpref := jutilaReflectedPrefixMoment_le_card_sq hM0 G
  have hscaled := mul_le_mul_of_nonneg_left hpref hC.le
  calc
    jutilaSecondMoment N G ≤
        C * ((G.card : ℝ) * N +
          jutilaReflectedPrefixMoment
            (reflectedLength29_40 T epsilon N) G) +
          C * Real.rpow T (-A) := hraw
    _ ≤ C * ((G.card : ℝ) * N +
          (G.card : ℝ)^2 *
            ((natRealIoc 0 (reflectedLength29_40 T epsilon N)).card : ℝ)^2) +
          C * Real.rpow T (-A) := by gcongr
    _ = _ := by ring

/-- A `T^delta`-separated subset of `(0,T]` is one-separated once `T≥1`.
This is the exact bridge from the source spacing to the unconditional Hilbert
mean-square theorem. -/
theorem oneSeparated_of_TPowerSeparated
    {T delta : ℝ} {G : Finset ℝ} (hT : 1 ≤ T) (hdelta : 0 ≤ delta)
    (hsep : TPowerSeparated G T delta) : OneSeparated G := by
  intro g₁ hg₁ g₂ hg₂ hne
  exact (Real.one_le_rpow hT hdelta).trans (hsep g₁ hg₁ g₂ hg₂ hne)

/-- The genuine high-length branch consumed by the final three-regime weld.
It uses no AFE and already has the first term of the Jutila three-term shape. -/
theorem jutilaSecondMoment_natCast_highRange_le_threeTerm
    {T delta : ℝ} {M : ℕ} {G : Finset ℝ}
    (hT : 1 ≤ T) (hdelta : 0 ≤ delta) (hM : 1 ≤ M)
    (hTM : T ≤ M) (hsep : TPowerSeparated G T delta)
    (hheight : InOpenClosedZeroT G T) :
    jutilaSecondMoment (M : ℝ) G ≤
      (6 + 6 * Classical.choose
        MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert) *
        jutilaThreeTermShape T M G := by
  have hbase := jutilaSecondMoment_natCast_le_highRange T M G
    (by linarith) hM hTM
    (oneSeparated_of_TPowerSeparated hT hdelta hsep)
    (fun g hg => ⟨(hheight g hg).1.le, (hheight g hg).2⟩)
  have hC : 0 < Classical.choose
      MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert :=
    (Classical.choose_spec
      MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert).1
  have hshape : 0 ≤
      Real.rpow (G.card : ℝ) (5/4 : ℝ) * Real.rpow T (1/2 : ℝ) +
        (G.card : ℝ)^2 := by
    exact add_nonneg
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg (by linarith) _))
      (sq_nonneg _)
  unfold jutilaThreeTermShape
  nlinarith

/-- Real-length form of the unconditional high-range branch.  The source
recurrence evaluates `S(P)` at the real scale `P = 4 M^2`; rounding that scale
up and using the certified bounded-ratio comparison avoids any use of the AFE
outside its legal `N ≤ T^(1+epsilon)` range. -/
theorem jutilaSecondMoment_real_highRange_le
    {T delta X : ℝ} {G : Finset ℝ}
    (hT : 1 ≤ T) (hdelta : 0 ≤ delta) (hX : 1 ≤ X)
    (hTX : T ≤ X) (hsep : TPowerSeparated G T delta)
    (hheight : InOpenClosedZeroT G T) :
    jutilaSecondMoment X G ≤
      (252 + 252 * Classical.choose
        MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert) *
        (G.card : ℝ) * X := by
  let P : ℕ := Nat.ceil X
  have hXP : X ≤ (P : ℝ) := by
    simpa only [P] using Nat.le_ceil X
  have hP_lt : (P : ℝ) < X + 1 := by
    simpa only [P] using Nat.ceil_lt_add_one (by linarith : 0 ≤ X)
  have hP_le_twoX : (P : ℝ) ≤ 2 * X := by linarith
  have hquarter : (P : ℝ) / 4 ≤ X := by linarith
  have hPnat : 1 ≤ P := by
    have hP_real : (1 : ℝ) ≤ P := hX.trans hXP
    exact_mod_cast hP_real
  have hTP : T ≤ (P : ℝ) := hTX.trans hXP
  have hnear := jutilaSecondMoment_le_twentyOne_of_quarter_le
    hquarter hXP G
  have hhigh := jutilaSecondMoment_natCast_le_highRange T P G
    (by linarith) hPnat hTP
    (oneSeparated_of_TPowerSeparated hT hdelta hsep)
    (fun g hg => ⟨(hheight g hg).1.le, (hheight g hg).2⟩)
  have hC : 0 < Classical.choose
      MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert :=
    (Classical.choose_spec
      MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert).1
  calc
    jutilaSecondMoment X G ≤ 21 * jutilaSecondMoment (P : ℝ) G := hnear
    _ ≤ 21 * ((6 + 6 * Classical.choose
        MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert) *
          (G.card : ℝ) * P) := by gcongr
    _ ≤ (252 + 252 * Classical.choose
        MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert) *
          (G.card : ℝ) * X := by
      have hcard : 0 ≤ (G.card : ℝ) := Nat.cast_nonneg _
      have hcoef : 0 ≤ 21 *
          (6 + 6 * Classical.choose
            MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert) *
          (G.card : ℝ) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hP_le_twoX hcoef
      calc
        21 * ((6 + 6 * Classical.choose
            MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert) *
              (G.card : ℝ) * P) =
            (21 * (6 + 6 * Classical.choose
              MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert) *
              (G.card : ℝ)) * (P : ℝ) := by ring
        _ ≤ (21 * (6 + 6 * Classical.choose
              MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert) *
              (G.card : ℝ)) * (2 * X) := hmul
        _ = (252 + 252 * Classical.choose
              MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert) *
              (G.card : ℝ) * X := by ring

end
end GuthMaynardLemma2910HighRangeFromAFE

#print axioms GuthMaynardLemma2910HighRangeFromAFE.jutilaReflectedPrefixMoment_eq_zero_of_lt_one
#print axioms GuthMaynardLemma2910HighRangeFromAFE.jutilaReflectedPrefixMoment_le_card_sq
#print axioms GuthMaynardLemma2910HighRangeFromAFE.card_natRealIoc_zero_le_ceil_add_one
#print axioms GuthMaynardLemma2910HighRangeFromAFE.jutilaSecondMoment_le_finitePrefixCollar_of_exactM
#print axioms GuthMaynardLemma2910HighRangeFromAFE.oneSeparated_of_TPowerSeparated
#print axioms GuthMaynardLemma2910HighRangeFromAFE.jutilaSecondMoment_natCast_highRange_le_threeTerm
#print axioms GuthMaynardLemma2910HighRangeFromAFE.jutilaSecondMoment_real_highRange_le
