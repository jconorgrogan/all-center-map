import GuthMaynardJutilaOneSpacingWeld
import GuthMaynardJutilaIntervalRecentering
import GuthMaynardHeathBrownFromJutila
import GuthMaynardLemma2910HighRangeFromAFE
import GuthMaynardLemma2910OptimizedAnchor

/-!
# Corrected exact-M AFE to the coefficient-one Heath--Brown core

This file derives Jutila's Lemma 29.10 from the corrected exact-M AFE and
then proves the public coefficient-one Heath--Brown core. The bridge includes
the Hilbert high-length branch, long-spacing coloring, arbitrary-interval
recentering, the `T+1` aperture loss, and the closed-left dyadic endpoint.
The exact-M AFE is the sole remaining analytic premise.
-/

namespace GuthMaynardHeathBrownCoreFromPowerSeparatedJutila

open CGLProofDAG
open GuthMaynardHeathBrownInterface
open GuthMaynardHeathBrownMajorant
open GuthMaynardLengthComparison
open GuthMaynardJutilaReflection2941
open GuthMaynardJutilaSpacingPartition
open GuthMaynardJutilaOneSpacingWeld
open GuthMaynardJutilaIntervalRecentering
open GuthMaynardHeathBrownFromJutila
open GuthMaynardLemma2910HighRangeFromAFE

noncomputable section

/-- The exact three-term conclusion
of Jutila Lemma 29.10 on a `T^delta`-separated set in `(0,T]`.  Unlike the
Heath--Brown target, this is weighted by `n^{-1/2}` and has no closed-endpoint
or arbitrary-interval convention left in it. -/
def PowerSeparatedJutilaThreeTermCore : Prop :=
  ∀ eta delta : ℝ, 0 < eta → 0 < delta →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (M : ℕ) (G : Finset ℝ),
        T₀ ≤ T → 1 ≤ M →
        TPowerSeparated G T delta → InOpenClosedZeroT G T →
        jutilaSecondMoment (M : ℝ) G ≤
          C * Real.rpow T eta *
            GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape T M G

/-- The below-aperture part of Lemma 29.10 after the unconditional
Hilbert mean-square branch is removed.  This restriction is strict: it asks
only for polynomial lengths below the aperture. -/
def BelowAperturePowerSeparatedJutilaCore : Prop :=
  ∀ eta delta : ℝ, 0 < eta → 0 < delta →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (M : ℕ) (G : Finset ℝ),
        T₀ ≤ T → 1 ≤ M → (M : ℝ) < T →
        TPowerSeparated G T delta → InOpenClosedZeroT G T →
        jutilaSecondMoment (M : ℝ) G ≤
          C * Real.rpow T eta *
            GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape T M G

/-- The full power-separated theorem is equivalent to its below-aperture
branch: the complementary range is discharged by the certified Hilbert
mean-square theorem. -/
theorem powerSeparatedJutilaThreeTermCore_of_belowAperture
    (hlow : BelowAperturePowerSeparatedJutilaCore) :
    PowerSeparatedJutilaThreeTermCore := by
  intro eta delta heta hdelta
  obtain ⟨C, T₀, hC, hT₀, hbound⟩ := hlow eta delta heta hdelta
  let H : ℝ := 6 + 6 * Classical.choose
    MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert
  let C' : ℝ := max C H
  refine ⟨C', max T₀ 2, ?_, ?_, ?_⟩
  · exact hC.trans_le (le_max_left _ _)
  · exact le_max_right _ _
  · intro T M G hT hM hsep hheight
    have hT₀' : T₀ ≤ T := (le_max_left _ _).trans hT
    have hTtwo : 2 ≤ T := (le_max_right _ _).trans hT
    have hTone : 1 ≤ T := by linarith
    have hshape0 := jutilaThreeTermShape_nonneg
      (by linarith : 0 ≤ T) (Nat.cast_nonneg M) G
    have hpowOne : 1 ≤ Real.rpow T eta := Real.one_le_rpow hTone heta.le
    by_cases hMT : (M : ℝ) < T
    · exact hbound T M G hT₀' hM hMT hsep hheight |>.trans (by
        have hCC : C ≤ C' := le_max_left _ _
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg (by linarith) _))
          hshape0)
    · have hhigh := jutilaSecondMoment_natCast_highRange_le_threeTerm
        hTone hdelta.le hM (le_of_not_gt hMT) hsep hheight
      have hHC : H ≤ C' := le_max_right _ _
      calc
        jutilaSecondMoment (M : ℝ) G ≤
            H * GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape T M G := by
          simpa only [H] using hhigh
        _ ≤ C' * GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape T M G :=
          mul_le_mul_of_nonneg_right hHC hshape0
        _ ≤ C' * Real.rpow T eta *
            GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape T M G := by
          have hC'0 : 0 ≤ C' := (lt_of_lt_of_le hC (le_max_left _ _)).le
          have hs : GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape T M G ≤
              Real.rpow T eta *
                GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape T M G := by
            simpa only [one_mul] using
              (mul_le_mul_of_nonneg_right hpowOne hshape0)
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hC'0

theorem jutilaThreeTermShape_add_one_le_two
    {T : ℝ} (hT : 1 ≤ T) (M : ℕ) (W : Finset ℝ) :
    GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape (T+1) M W ≤
      2 * GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape T M W := by
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hsqrt : Real.rpow (T+1) (1/2 : ℝ) ≤
      2 * Real.rpow T (1/2 : ℝ) := by
    rw [show Real.rpow (T+1) (1/2 : ℝ) = Real.sqrt (T+1) by
      symm; exact Real.sqrt_eq_rpow (T+1)]
    rw [show Real.rpow T (1/2 : ℝ) = Real.sqrt T by
      symm; exact Real.sqrt_eq_rpow T]
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hs : (Real.sqrt T)^2 = T := Real.sq_sqrt hT0
      nlinarith
  unfold GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape
  have hcard : 0 ≤ (W.card : ℝ) := Nat.cast_nonneg _
  have hM : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
  have hpow : 0 ≤ Real.rpow (W.card : ℝ) (5/4 : ℝ) :=
    Real.rpow_nonneg hcard _
  nlinarith [mul_le_mul_of_nonneg_left hsqrt hpow]

theorem rpow_add_one_half_le_rpow
    {T eta : ℝ} (hT : 2 ≤ T) (heta : 0 ≤ eta) :
    Real.rpow (T+1) (eta/2) ≤ Real.rpow T eta := by
  have hT0 : 0 ≤ T := by linarith
  have hadd : 0 ≤ T+1 := by linarith
  have hbase : T+1 ≤ T^2 := by nlinarith [sq_nonneg (T-1)]
  calc
    Real.rpow (T+1) (eta/2) ≤ Real.rpow (T^2) (eta/2) :=
      Real.rpow_le_rpow hadd hbase (by positivity)
    _ = Real.rpow T eta := by
      calc
        Real.rpow (T^2) (eta/2) =
            Real.rpow (Real.rpow T 2) (eta/2) := by
          congr 1
          exact (Real.rpow_natCast T 2).symm
        _ = Real.rpow T ((2:ℝ)*(eta/2)) :=
          (Real.rpow_mul hT0 2 (eta/2)).symm
        _ = Real.rpow T eta := by
          congr 1
          ring

/-- All deterministic and finite source steps from Lemma 29.10 to the
coefficient-one Heath--Brown theorem.  Thus the low/intermediate
`|W|^(5/4) T^(1/2) M` branch is reduced to exactly
`PowerSeparatedJutilaThreeTermCore`. -/
theorem heathBrownOneCoefficientCore_of_powerSeparatedJutila
    (hJutila : PowerSeparatedJutilaThreeTermCore) :
    HeathBrownOneCoefficientCore := by
  intro eta heta
  let delta : ℝ := eta / 16
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hetaQuarter : 0 < eta/4 := by positivity
  obtain ⟨C, T₀, hC, hT₀, hbound⟩ :=
    hJutila (eta/4) delta hetaQuarter hdelta
  refine ⟨36*C+3, max 2 T₀, by positivity, le_max_left _ _, ?_⟩
  intro T M W hT hM hsep hinterval
  have hTtwo : 2 ≤ T := (le_max_left _ _).trans hT
  have hTsource : T₀ ≤ T := (le_max_right _ _).trans hT
  obtain ⟨x, hx⟩ := hinterval
  let Wr := intervalRecenter x W
  have hsepR : OneSeparated Wr := intervalRecenter_oneSeparated hsep x
  have hheightR : InOpenClosedZeroT Wr (T+1) :=
    intervalRecenter_inOpenClosedZero hx
  have hfiber (i : Fin (powerSpacingColorCount (T+1) delta)) :
      jutilaSecondMoment (M : ℝ)
          (colorFiber (powerSpacingColor (T+1) delta) Wr i) ≤
        C * Real.rpow (T+1) (eta/4) *
          GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape (T+1) M
            (colorFiber (powerSpacingColor (T+1) delta) Wr i) := by
    apply hbound (T+1) M
    · linarith
    · exact hM
    · exact powerSpacingColorFiber_TPowerSeparated hsepR i
    · intro g hg
      exact hheightR g (Finset.mem_filter.mp hg).1
  have hlong := oneSeparated_jutila_of_powerSeparated_fibers
    (T := T+1) (M := (M:ℝ)) (delta := delta) (eta := eta/2)
    (C := C) (W := Wr)
    (by linarith) (Nat.cast_nonneg M) hdelta.le (by positivity)
    (by dsimp [delta]; linarith) hC.le hsepR (by
      intro i
      have he : eta / 4 = eta / 2 / 2 := by ring
      rw [← he]
      exact hfiber i)
  have hmoment : jutilaSecondMoment (M : ℝ) W ≤
      (18*C) * Real.rpow T eta *
        GuthMaynardHeathBrownFromJutila.jutilaThreeTermShape T M W := by
    have hrpow := rpow_add_one_half_le_rpow hTtwo heta.le
    have hshape := jutilaThreeTermShape_add_one_le_two
      (T := T) (by linarith) M Wr
    have hshape0 := GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape_nonneg
      (by linarith : 0 ≤ T+1) (Nat.cast_nonneg M) Wr
    have hpow0 : 0 ≤ Real.rpow (T+1) (eta/2) :=
      Real.rpow_nonneg (by linarith) _
    rw [jutilaSecondMoment_intervalRecenter] at hlong
    have hcard : Wr.card = W.card := card_intervalRecenter x W
    have hshapeEq :
        GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape T M Wr =
          GuthMaynardHeathBrownFromJutila.jutilaThreeTermShape T M W := by
      simp [GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape,
        GuthMaynardHeathBrownFromJutila.jutilaThreeTermShape, hcard]
    calc
      jutilaSecondMoment (M : ℝ) W ≤
          9*C*Real.rpow (T+1) (eta/2) *
            GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape (T+1) M Wr :=
        hlong
      _ ≤ 9*C*Real.rpow T eta *
            (2 * GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape T M Wr) := by
        calc
          9*C*Real.rpow (T+1) (eta/2) *
                GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape (T+1) M Wr ≤
              9*C*Real.rpow T eta *
                GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape (T+1) M Wr := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hrpow (by positivity)) hshape0
          _ ≤ 9*C*Real.rpow T eta *
                (2 * GuthMaynardJutilaOneSpacingWeld.jutilaThreeTermShape T M Wr) := by
            exact mul_le_mul_of_nonneg_left hshape
              (mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
      _ = (18*C) * Real.rpow T eta *
            GuthMaynardHeathBrownFromJutila.jutilaThreeTermShape T M W := by
        rw [hshapeEq]
        ring
  simpa [show 2*(18*C)+3 = 36*C+3 by ring] using
    (differenceQuadraticForm_one_le_of_jutila heta.le
      (by linarith : 1 ≤ T) hM hmoment)


/-- The below-aperture leaf follows from the corrected exact-reflected-length
AFE alone; no arbitrary-M AFE, bootstrap or cardinality bound is assumed. -/
theorem belowAperturePowerSeparatedJutilaCore_of_exactAFE
    (hAFE : Lemma295ApproximateFunctionalEquationExactM) :
    BelowAperturePowerSeparatedJutilaCore := by
  intro eta delta heta hdelta
  obtain ⟨T₀,hT₀,hbound⟩ :=
    GuthMaynardLemma2910OptimizedAnchor.real_below_aperture_of_exactAFE hAFE heta hdelta
  refine ⟨1,T₀,by norm_num,hT₀,?_⟩
  intro T M G hT hM hMT hsep hheight
  simpa only [one_mul] using hbound T (M : ℝ) G hT (by exact_mod_cast hM) hMT hsep hheight

/-- Corrected exact-M AFE to the full three-term Jutila core. The complementary
long-length range is supplied by the unconditional Hilbert theorem. -/
theorem powerSeparatedJutilaThreeTermCore_of_exactAFE
    (hAFE : Lemma295ApproximateFunctionalEquationExactM) :
    PowerSeparatedJutilaThreeTermCore :=
  powerSeparatedJutilaThreeTermCore_of_belowAperture
    (belowAperturePowerSeparatedJutilaCore_of_exactAFE hAFE)

/-- The complete deterministic exact-M AFE to Heath--Brown bridge. -/
theorem heathBrownOneCoefficientCore_of_exactAFE
    (hAFE : Lemma295ApproximateFunctionalEquationExactM) :
    HeathBrownOneCoefficientCore :=
  heathBrownOneCoefficientCore_of_powerSeparatedJutila
    (powerSeparatedJutilaThreeTermCore_of_exactAFE hAFE)

end
end GuthMaynardHeathBrownCoreFromPowerSeparatedJutila

#print axioms GuthMaynardHeathBrownCoreFromPowerSeparatedJutila.jutilaThreeTermShape_add_one_le_two
#print axioms GuthMaynardHeathBrownCoreFromPowerSeparatedJutila.rpow_add_one_half_le_rpow
#print axioms GuthMaynardHeathBrownCoreFromPowerSeparatedJutila.powerSeparatedJutilaThreeTermCore_of_belowAperture
#print axioms GuthMaynardHeathBrownCoreFromPowerSeparatedJutila.heathBrownOneCoefficientCore_of_powerSeparatedJutila

#print axioms GuthMaynardHeathBrownCoreFromPowerSeparatedJutila.heathBrownOneCoefficientCore_of_exactAFE
