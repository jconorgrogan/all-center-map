import GuthMaynardLemma295OffDiagonalAssembly

/-!
# Construction of the reflected pair estimate from its two source leaves

The bundled `Lemma295ReflectedPairMoment` can be built from exactly two
analytic inputs:

1. the pointwise contour/functional-equation estimate of Lemma 29.5;
2. the initial smooth-cutoff/Lemma-29.6 reduction of `S(N)` to the
   off-diagonal `h_g^+` moment.

All later pair summation, weighted Cauchy, cardinality, power-saving
remainder absorption, and constant bookkeeping are proved here or in the
imported modules.
-/

namespace GuthMaynardLemma295ReflectedPairConstruction

open scoped BigOperators
open GuthMaynardJutilaReflection2941
open GuthMaynardLemma295OffDiagonalAssembly
open GuthMaynardTPowerCardinality
open GuthMaynardLengthComparison

noncomputable section

/-- The exact initial smoothing inequality in the first display of the proof
of Lemma 29.10 (Vol. 3, p. 267).  This is the remaining cutoff-calculus leaf;
it contains no reflected AFE. -/
def Lemma296SmoothedSecondMomentReduction : Prop :=
  ∃ B : ℝ, 0 < B ∧
    ∀ (N : ℝ) (G : Finset ℝ), 1 ≤ N →
      jutilaSecondMoment N G ≤
        B * ((G.card : ℝ) * N + N⁻¹ * offDiagonalHPlusPairMoment N G)

/-- The explicit exponent absorption used after summing the pointwise AFE
remainder over at most `4T^2` pairs. -/
theorem square_times_deep_remainder_le
    {T A : ℝ} (hT : 1 ≤ T) (hA : 0 < A) :
    T ^ 2 * Real.rpow T (-2 * (A + 2)) ≤ Real.rpow T (-A) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hnat : T ^ 2 = Real.rpow T (2 : ℝ) := by
    exact (Real.rpow_natCast T 2).symm
  have hadd : Real.rpow T ((2 : ℝ) + (-2 * (A + 2))) =
      Real.rpow T 2 * Real.rpow T (-2 * (A + 2)) :=
    Real.rpow_add hTpos _ _
  have hexp : (2 : ℝ) + (-2 * (A + 2)) ≤ -A := by linarith
  calc
    T ^ 2 * Real.rpow T (-2 * (A + 2)) =
        Real.rpow T 2 * Real.rpow T (-2 * (A + 2)) := by rw [hnat]
    _ = Real.rpow T ((2 : ℝ) + (-2 * (A + 2))) := hadd.symm
    _ ≤ Real.rpow T (-A) := Real.rpow_le_rpow_of_exponent_le hT hexp

/-- The published reflected-pair estimate follows from the pointwise AFE and
the initial smooth reduction.  No prime-reciprocal, dyadic transference, or
Heath--Brown theorem is assumed here. -/
theorem lemma295ReflectedPairMoment_of_AFE_and_smoothing
    (hAFE : Lemma295ApproximateFunctionalEquationExactM)
    (hsmooth : Lemma296SmoothedSecondMomentReduction) :
    Lemma295ReflectedPairMoment := by
  intro delta epsilon A hdelta hepsilon hA
  obtain ⟨B, hB, hsmoothBound⟩ := hsmooth
  have hAdeep : 0 < A + 2 := by linarith
  obtain ⟨C, T₀, hC, hT₀, hoff⟩ :=
    offDiagonalHPlusPairMoment_le_of_lemma295AFE
      hAFE hdelta hepsilon hAdeep
  let Cfinal : ℝ := B * (1 + 2 * C ^ 2 * Real.pi ^ 2 + 8 * C ^ 2)
  have hCfinal : 0 < Cfinal := by
    dsimp [Cfinal]
    have hpi : 0 < Real.pi := Real.pi_pos
    positivity
  refine ⟨Cfinal, T₀, hCfinal, hT₀, ?_⟩
  intro T N G hT hN hNupper hsep hheight
  have hTone : 1 ≤ T := by linarith
  have hTtwo : 2 ≤ T := hT₀.trans hT
  have hTnonneg : 0 ≤ T := le_trans zero_le_one hTone
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNinv0 : 0 ≤ N⁻¹ := inv_nonneg.mpr hNpos.le
  have hNinvLe : N⁻¹ ≤ 1 := (inv_le_one₀ hNpos).2 hN
  have hcard := card_cast_le_two_mul_T hTtwo hdelta.le hsep hheight
  have hcard0 : 0 ≤ (G.card : ℝ) := by positivity
  have hcardsq : (G.card : ℝ) ^ 2 ≤ (2 * T) ^ 2 :=
    pow_le_pow_left₀ hcard0 hcard 2
  have hprefix0 :
      0 ≤ jutilaReflectedPrefixMoment
        (reflectedLength29_40 T epsilon N) G :=
    jutilaReflectedPrefixMoment_nonneg _ _
  have herr0 : 0 ≤ Real.rpow T (-2 * (A + 2)) :=
    Real.rpow_nonneg hTnonneg _
  have htargetErr0 : 0 ≤ Real.rpow T (-A) :=
    Real.rpow_nonneg hTnonneg _
  have hoffBound := hoff T N G hT hN hNupper hsep hheight
  have herrAbsorb :
      N⁻¹ *
          (2 * C ^ 2 * (G.card : ℝ) ^ 2 *
            Real.rpow T (-2 * (A + 2))) ≤
        8 * C ^ 2 * Real.rpow T (-A) := by
    calc
      N⁻¹ * (2 * C ^ 2 * (G.card : ℝ) ^ 2 *
          Real.rpow T (-2 * (A + 2))) ≤
        1 * (2 * C ^ 2 * (2 * T) ^ 2 *
          Real.rpow T (-2 * (A + 2))) := by
            gcongr
      _ = 8 * C ^ 2 *
          (T ^ 2 * Real.rpow T (-2 * (A + 2))) := by ring
      _ ≤ 8 * C ^ 2 * Real.rpow T (-A) := by
        exact mul_le_mul_of_nonneg_left
          (square_times_deep_remainder_le hTone hA)
          (by positivity)
  have hoffScaled :
      N⁻¹ * offDiagonalHPlusPairMoment N G ≤
        2 * C ^ 2 * Real.pi ^ 2 *
          jutilaReflectedPrefixMoment
            (reflectedLength29_40 T epsilon N) G +
        8 * C ^ 2 * Real.rpow T (-A) := by
    calc
      N⁻¹ * offDiagonalHPlusPairMoment N G ≤
        N⁻¹ *
          (2 * C ^ 2 *
              (N * Real.pi ^ 2 *
                jutilaReflectedPrefixMoment
                  (reflectedLength29_40 T epsilon N) G) +
            2 * C ^ 2 * (G.card : ℝ) ^ 2 *
              Real.rpow T (-2 * (A + 2))) :=
        mul_le_mul_of_nonneg_left hoffBound hNinv0
      _ = 2 * C ^ 2 * Real.pi ^ 2 *
            jutilaReflectedPrefixMoment
              (reflectedLength29_40 T epsilon N) G +
          N⁻¹ * (2 * C ^ 2 * (G.card : ℝ) ^ 2 *
            Real.rpow T (-2 * (A + 2))) := by
        field_simp [hNpos.ne']
      _ ≤ 2 * C ^ 2 * Real.pi ^ 2 *
            jutilaReflectedPrefixMoment
              (reflectedLength29_40 T epsilon N) G +
          8 * C ^ 2 * Real.rpow T (-A) :=
        add_le_add le_rfl herrAbsorb
  have hs := hsmoothBound N G hN
  have hRN0 : 0 ≤ (G.card : ℝ) * N :=
    mul_nonneg hcard0 hNpos.le
  have hmainCoeff : B ≤ Cfinal := by
    dsimp [Cfinal]
    calc
      B = B * 1 := by ring
      _ ≤ B * (1 + 2 * C ^ 2 * Real.pi ^ 2 + 8 * C ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hB.le
        nlinarith [sq_nonneg C, sq_nonneg Real.pi,
          mul_nonneg (sq_nonneg C) (sq_nonneg Real.pi)]
  have hprefCoeff : B * (2 * C ^ 2 * Real.pi ^ 2) ≤ Cfinal := by
    dsimp [Cfinal]
    apply mul_le_mul_of_nonneg_left _ hB.le
    nlinarith [sq_nonneg C, sq_nonneg Real.pi,
      mul_nonneg (sq_nonneg C) (sq_nonneg Real.pi)]
  have herrCoeff : B * (8 * C ^ 2) ≤ Cfinal := by
    dsimp [Cfinal]
    apply mul_le_mul_of_nonneg_left _ hB.le
    nlinarith [sq_nonneg C, sq_nonneg Real.pi,
      mul_nonneg (sq_nonneg C) (sq_nonneg Real.pi)]
  calc
    jutilaSecondMoment N G ≤
        B * ((G.card : ℝ) * N +
          N⁻¹ * offDiagonalHPlusPairMoment N G) := hs
    _ ≤ B * ((G.card : ℝ) * N +
        (2 * C ^ 2 * Real.pi ^ 2 *
          jutilaReflectedPrefixMoment
            (reflectedLength29_40 T epsilon N) G +
          8 * C ^ 2 * Real.rpow T (-A))) := by
      gcongr
    _ = B * ((G.card : ℝ) * N) +
        (B * (2 * C ^ 2 * Real.pi ^ 2)) *
          jutilaReflectedPrefixMoment
            (reflectedLength29_40 T epsilon N) G +
        (B * (8 * C ^ 2)) * Real.rpow T (-A) := by ring
    _ ≤ Cfinal * ((G.card : ℝ) * N) +
        Cfinal *
          jutilaReflectedPrefixMoment
            (reflectedLength29_40 T epsilon N) G +
        Cfinal * Real.rpow T (-A) := by
      gcongr
    _ = Cfinal * ((G.card : ℝ) * N +
          jutilaReflectedPrefixMoment
            (reflectedLength29_40 T epsilon N) G) +
        Cfinal * Real.rpow T (-A) := by ring

end

end GuthMaynardLemma295ReflectedPairConstruction

#print axioms GuthMaynardLemma295ReflectedPairConstruction.square_times_deep_remainder_le
#print axioms GuthMaynardLemma295ReflectedPairConstruction.lemma295ReflectedPairMoment_of_AFE_and_smoothing
