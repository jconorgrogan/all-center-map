import GuthMaynardJutilaLemma29NineKTwo
import GuthMaynardJutilaTransferenceOneScale
import GuthMaynardKTwoMultiplicitySubpower

/-!
# The missing `1 ≤ J < 2` collar in Jutila--Heath--Brown Lemma 29.10

The published transference argument is finite and only needs a positive lower
prime scale.  The former Lean interface imposed `2 ≤ J`, although none of its
Parseval or collection steps uses that stronger bound.  The companion finite reconstruction in this module family states the exact
usable hypothesis `1 ≤ J`; the shared source-facing interface is left unchanged.

For the collar `1 ≤ J < 2`, the prime interval `[J,2J]` is nonempty for the
literal reason that it contains `2`.  This module splices that witness into the
`k=2` powering argument and retains the same three dyadic blocks
`(P/4,P/2]`, `(P/2,P]`, `(P,2P]`.  Thus there is no exceptional endpoint and
no new analytic input.
-/

namespace GuthMaynardJutilaSmallScaleTransference

open scoped BigOperators ComplexConjugate
open GuthMaynardHeathBrownMajorant
open GuthMaynardJutilaTransference
open GuthMaynardLengthComparison
open GuthMaynardPoweringKTwo
open GuthMaynardJutilaLemma29NineKTwo
open GuthMaynardKTwoMultiplicitySubpower

noncomputable section

/-- In the entire collar `1 ≤ J < 2`, the literal prime interval `[J,2J]`
contains the prime `2`. -/
theorem two_mem_primeRealIcc_of_smallScale
    {J : ℝ} (hJ : 1 ≤ J) (hJlt : J < 2) :
    2 ∈ primeRealIcc J (2 * J) := by
  rw [mem_primeRealIcc_iff (by positivity : 0 ≤ 2 * J)]
  constructor
  · exact hJlt.le
  · constructor
    · norm_num at *
      linarith
    · norm_num

/-- Bertrand's postulate supplies the same nonemptiness for every real
`J ≥ 2`; using `floor J` preserves the required upper endpoint `2J`. -/
theorem primeRealIcc_nonempty_of_two_le
    {J : ℝ} (hJ : 2 ≤ J) :
    (primeRealIcc J (2 * J)).Nonempty := by
  let n : ℕ := Nat.floor J
  have hJ0 : 0 ≤ J := by linarith
  have hnpos : 0 < n := by
    dsimp [n]
    rw [Nat.floor_pos]
    linarith
  obtain ⟨p, hpPrime, hnp, hpUpper⟩ := Nat.bertrand n hnpos.ne'
  refine ⟨p, ?_⟩
  rw [mem_primeRealIcc_iff (by positivity : 0 ≤ 2 * J)]
  refine ⟨?_, ?_, hpPrime⟩
  · have hJfloor : J < (n : ℝ) + 1 := by
      simpa [n] using (Nat.lt_floor_add_one J)
    have hfloorSucc : n + 1 ≤ p := by omega
    have hfloorSuccR : (n : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hfloorSucc
    exact hJfloor.le.trans hfloorSuccR
  · have hfloor : (n : ℝ) ≤ J := by
      simpa [n] using Nat.floor_le hJ0
    have hpUpperR : (p : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hpUpper
    exact hpUpperR.trans (mul_le_mul_of_nonneg_left hfloor (by norm_num))

/-- Consequently the prime range used by the `k=2` specialization is
nonempty throughout the missing collar. -/
theorem kTwoPrimeRange_nonempty_of_smallScale
    {N P : ℝ}
    (hJ : 1 ≤ kTwoPrimeLower N P)
    (hJlt : kTwoPrimeLower N P < 2) :
    (kTwoPrimeRange N P).Nonempty := by
  refine ⟨2, ?_⟩
  exact two_mem_primeRealIcc_of_smallScale hJ hJlt


/-- Every transference fiber in the small collar injects into the two-element
set `{2,3}` by its prime coordinate. -/
theorem kTwoTransferenceFiberCard_le_two_of_smallScale
    {N P : ℝ}
    (hJ : 1 ≤ kTwoPrimeLower N P)
    (hJlt : kTwoPrimeLower N P < 2)
    (l : ℕ) :
    kTwoTransferenceFiberCard N P l ≤ 2 := by
  let F := (((kTwoPrimeRange N P).product (productIoc N)).filter
    (fun q => q.1 * q.2 = l))
  have hcard : F.card ≤ ({2, 3} : Finset ℕ).card := by
    apply Finset.card_le_card_of_injOn (fun q : ℕ × ℕ => q.1)
    · intro q hq
      have hqf := (Finset.mem_filter.mp hq).1
      have hpRange : q.1 ∈ kTwoPrimeRange N P :=
        (Finset.mem_product.mp hqf).1
      rw [kTwoPrimeRange, mem_primeRealIcc_iff (by positivity :
        0 ≤ 2 * kTwoPrimeLower N P)] at hpRange
      have hpLtFour : q.1 < 4 := by
        have : (q.1 : ℝ) < 4 := lt_of_le_of_lt hpRange.2.1 (by linarith)
        exact_mod_cast this
      have hpPrime := hpRange.2.2
      have hpTwo : 2 ≤ q.1 := hpPrime.two_le
      by_cases heqTwo : q.1 = 2
      · simp [heqTwo]
      · have heqThree : q.1 = 3 := by omega
        simp [heqThree]
    · intro q hq r hr heq
      change q.1 = r.1 at heq
      have hqprod := (Finset.mem_filter.mp hq).2
      have hrprod := (Finset.mem_filter.mp hr).2
      have hqbase := (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
      have hpPrime : Nat.Prime q.1 := by
        rw [kTwoPrimeRange, mem_primeRealIcc_iff (by positivity :
          0 ≤ 2 * kTwoPrimeLower N P)] at hqbase
        exact hqbase.2.2
      apply Prod.ext heq
      apply Nat.mul_left_cancel hpPrime.pos
      calc
        q.1 * q.2 = l := hqprod
        _ = r.1 * r.2 := hrprod.symm
        _ = q.1 * r.2 := by rw [heq]
  simpa [F] using hcard

/-- Hence the exact supremum fiber loss is at most two. -/
theorem kTwoTransferenceFiberCap_le_two_of_smallScale
    {N P : ℝ}
    (hJ : 1 ≤ kTwoPrimeLower N P)
    (hJlt : kTwoPrimeLower N P < 2) :
    kTwoTransferenceFiberCap N P ≤ 2 := by
  unfold kTwoTransferenceFiberCap
  apply Finset.sup_le
  intro l hl
  exact kTwoTransferenceFiberCard_le_two_of_smallScale hJ hJlt l

/-- The `p=2` term gives reciprocal prime mass at least `1/2`, so the
normalizing inverse costs at most the absolute constant two. -/
theorem kTwoPrimeReciprocal_inv_le_two_of_smallScale
    {N P : ℝ}
    (hJ : 1 ≤ kTwoPrimeLower N P)
    (hJlt : kTwoPrimeLower N P < 2) :
    (kTwoPrimeReciprocal N P)⁻¹ ≤ 2 := by
  have htwo := two_mem_primeRealIcc_of_smallScale hJ hJlt
  have hterm : Real.rpow (2 : ℝ) (-2 * (1 / 2 : ℝ)) ≤
      kTwoPrimeReciprocal N P := by
    unfold kTwoPrimeReciprocal primeReciprocalSum
    exact Finset.single_le_sum
      (fun p hp => Real.rpow_nonneg (Nat.cast_nonneg p) _) htwo
  have htermEq : Real.rpow (2 : ℝ) (-2 * (1 / 2 : ℝ)) = (2 : ℝ)⁻¹ := by
    norm_num [Real.rpow_neg_one]
  rw [htermEq] at hterm
  have hsumPos : 0 < kTwoPrimeReciprocal N P :=
    (inv_pos.mpr (by norm_num : (0 : ℝ) < 2)).trans_le hterm
  have hinv :=
    (inv_le_inv₀ hsumPos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)).2 hterm
  norm_num at hinv ⊢
  exact hinv

/-- The product range identity needs only `J ≥ 1`, not `J ≥ 2`.
This is the exact arithmetic identity behind the three-block split. -/
theorem kTwoProductRange_eq_dyadicUnion_of_one_le
    {N P : ℝ} (hN : 0 < N)
    (hJ : 1 ≤ kTwoPrimeLower N P) :
    kTwoProductRange N P = kTwoDyadicUnion P := by
  have hden : 0 < 4 * N ^ 2 := by positivity
  have hP : 0 < P := by
    have hmul : 1 * (4 * N ^ 2) ≤ P := by
      calc
        1 * (4 * N ^ 2) ≤ kTwoPrimeLower N P * (4 * N ^ 2) :=
          mul_le_mul_of_nonneg_right hJ hden.le
        _ = P := by
          unfold kTwoPrimeLower
          field_simp
    nlinarith
  have hlower : kTwoPrimeLower N P * N ^ 2 = P / 4 := by
    unfold kTwoPrimeLower
    field_simp [hN.ne']
  have hupper :
      (2 * kTwoPrimeLower N P) * (4 * N ^ 2) = 2 * P := by
    unfold kTwoPrimeLower
    field_simp [hN.ne']
  ext l
  simp only [kTwoProductRange, productRealIoc,
    mem_natRealIoc_iff (by positivity :
      0 ≤ (2 * kTwoPrimeLower N P) * (4 * N ^ 2)),
    kTwoDyadicUnion, Finset.mem_union,
    mem_realDyadicIoc_iff]
  rw [hlower, hupper]
  constructor
  · intro hl
    by_cases h₁ : (l : ℝ) ≤ P / 2
    · exact Or.inl (Or.inl ⟨hl.1, by linarith⟩)
    · by_cases h₂ : (l : ℝ) ≤ P
      · exact Or.inl (Or.inr ⟨lt_of_not_ge h₁, by linarith⟩)
      · exact Or.inr ⟨lt_of_not_ge h₂, hl.2⟩
  · rintro ((hl | hl) | hl)
    · constructor <;> linarith
    · constructor <;> linarith
    · constructor <;> linarith

/-- The three-block Cauchy estimate is valid throughout `J ≥ 1`. -/
theorem kTwoFullCoefficientOneMoment_le_three_dyadic_of_one_le
    {N P : ℝ} (hN : 0 < N)
    (hJ : 1 ≤ kTwoPrimeLower N P) (G : Finset ℝ) :
    kTwoFullCoefficientOneMoment N P G ≤
      3 * (jutilaSecondMoment (P / 4) G +
        jutilaSecondMoment (P / 2) G + jutilaSecondMoment P G) := by
  have hdis := kTwoDyadicBlocks_pairwise_disjoint P
  unfold kTwoFullCoefficientOneMoment
  rw [kTwoProductRange_eq_dyadicUnion_of_one_le hN hJ]
  have hsplit := realGramQuadratic_union_three_le
    (realDyadicIoc (P / 4)) (realDyadicIoc (P / 2))
    (realDyadicIoc P) hdis.1 hdis.2.1 hdis.2.2 G
    (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
    negativeDirichletPhase
  unfold kTwoDyadicUnion
  have hA : realGramQuadratic (realDyadicIoc (P / 4)) G
      (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
      negativeDirichletPhase = jutilaSecondMoment (P / 4) G :=
    negativeJutilaSecondMoment_eq_jutilaSecondMoment (P / 4) G
  have hB : realGramQuadratic (realDyadicIoc (P / 2)) G
      (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
      negativeDirichletPhase = jutilaSecondMoment (P / 2) G :=
    negativeJutilaSecondMoment_eq_jutilaSecondMoment (P / 2) G
  have hC : realGramQuadratic (realDyadicIoc P) G
      (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
      negativeDirichletPhase = jutilaSecondMoment P G :=
    negativeJutilaSecondMoment_eq_jutilaSecondMoment P G
  rw [hA, hB, hC] at hsplit
  exact hsplit

/-- After Lemma 29.8, the collar has the same absolute factor `21` as the
printed `J ≥ 2` range. -/
theorem kTwoFullCoefficientOneMoment_le_twentyOne_of_one_le
    {N P : ℝ} (hN : 0 < N)
    (hJ : 1 ≤ kTwoPrimeLower N P) (G : Finset ℝ) :
    kTwoFullCoefficientOneMoment N P G ≤
      21 * jutilaSecondMoment P G := by
  have hsplit := kTwoFullCoefficientOneMoment_le_three_dyadic_of_one_le
    hN hJ G
  have hlength := three_dyadic_jutilaSecondMoments_le_seven P G
  nlinarith

/-- Exact normalized `k=2` powering/transference inequality in the missing
small-prime collar.  All coefficients, fibers, and prime weights remain literal
finite objects. -/
theorem jutila_lemma29Nine_kTwo_normalized_smallScale
    {N P : ℝ} (hN : 0 < N)
    (hJ : 1 ≤ kTwoPrimeLower N P)
    (hJlt : kTwoPrimeLower N P < 2)
    (G : Finset ℝ) :
    jutilaSecondMoment N G ^ 2 ≤
      21 * (G.card : ℝ) ^ 2 *
        ((kTwoTransferenceFiberCap N P : ℝ) *
          (maxProductMultiplicity N : ℝ)) ^ 2 *
        (kTwoPrimeReciprocal N P)⁻¹ * jutilaSecondMoment P G := by
  have hprime := kTwoPrimeRange_nonempty_of_smallScale hJ hJlt
  have hJupper : kTwoPrimeLower N P ≤ 2 * kTwoPrimeLower N P := by
    have : 0 ≤ kTwoPrimeLower N P := le_trans (by norm_num) hJ
    linarith
  have hM : 0 ≤ N ^ 2 := sq_nonneg N
  have hM' : N ^ 2 < 4 * N ^ 2 := by nlinarith [sq_pos_of_pos hN]
  have hpow := jutilaSecondMoment_sq_le_multiplicityQuadraticForm N hN.le G
  have htrans := GuthMaynardJutilaTransferenceOneScale.jutila_transference hJ hJupper hM hM'
    (fun n => (productMultiplicity N n : ℂ)) (1 / 2) G hprime
  change sourceQuadratic (fun n => (productMultiplicity N n : ℂ))
      (N ^ 2) (4 * N ^ 2) (1 / 2) G ≤
    (primeReciprocalSum (kTwoPrimeLower N P)
      (2 * kTwoPrimeLower N P) (1 / 2))⁻¹ *
      targetQuadratic (fun n => (productMultiplicity N n : ℂ))
        (kTwoPrimeLower N P) (2 * kTwoPrimeLower N P)
        (N ^ 2) (4 * N ^ 2) (1 / 2) G at htrans
  rw [← multiplicityQuadraticForm_eq_sourceQuadratic] at htrans
  have hcap := targetQuadratic_productMultiplicity_le_fiberCap
    (P := P) hN.le G
  have hdyadic := kTwoFullCoefficientOneMoment_le_twentyOne_of_one_le
    hN hJ G
  have hqnonneg : 0 ≤ (kTwoPrimeReciprocal N P)⁻¹ := by
    unfold kTwoPrimeReciprocal
    exact inv_nonneg.mpr (Finset.sum_nonneg
      (fun p hp => Real.rpow_nonneg (Nat.cast_nonneg p) _))
  have hRnonneg : 0 ≤ (G.card : ℝ) ^ 2 := sq_nonneg _
  calc
    jutilaSecondMoment N G ^ 2 ≤
        (G.card : ℝ) ^ 2 * multiplicityQuadraticForm N G := hpow
    _ ≤ (G.card : ℝ) ^ 2 *
        ((kTwoPrimeReciprocal N P)⁻¹ *
          targetQuadratic (fun n => (productMultiplicity N n : ℂ))
            (kTwoPrimeLower N P) (2 * kTwoPrimeLower N P)
            (N ^ 2) (4 * N ^ 2) (1 / 2) G) :=
      mul_le_mul_of_nonneg_left htrans hRnonneg
    _ ≤ (G.card : ℝ) ^ 2 *
        ((kTwoPrimeReciprocal N P)⁻¹ *
          (((kTwoTransferenceFiberCap N P : ℝ) *
              (maxProductMultiplicity N : ℝ)) ^ 2 *
            kTwoFullCoefficientOneMoment N P G)) := by
      gcongr
    _ ≤ (G.card : ℝ) ^ 2 *
        ((kTwoPrimeReciprocal N P)⁻¹ *
          (((kTwoTransferenceFiberCap N P : ℝ) *
              (maxProductMultiplicity N : ℝ)) ^ 2 *
            (21 * jutilaSecondMoment P G))) := by
      gcongr
    _ = _ := by ring


/-- The corrected finite `k=2` transference theorem for the full range
`J ≥ 1`.  The small branch uses the explicit prime `2`; the large branch uses
Bertrand.  No nonemptiness premise remains. -/
theorem jutila_lemma29Nine_kTwo_normalized_of_one_le
    {N P : ℝ} (hN : 0 < N)
    (hJ : 1 ≤ kTwoPrimeLower N P)
    (G : Finset ℝ) :
    jutilaSecondMoment N G ^ 2 ≤
      21 * (G.card : ℝ) ^ 2 *
        ((kTwoTransferenceFiberCap N P : ℝ) *
          (maxProductMultiplicity N : ℝ)) ^ 2 *
        (kTwoPrimeReciprocal N P)⁻¹ * jutilaSecondMoment P G := by
  by_cases hsmall : kTwoPrimeLower N P < 2
  · exact jutila_lemma29Nine_kTwo_normalized_smallScale hN hJ hsmall G
  · have hlarge : 2 ≤ kTwoPrimeLower N P := le_of_not_gt hsmall
    have hprime : (kTwoPrimeRange N P).Nonempty := by
      unfold kTwoPrimeRange
      exact primeRealIcc_nonempty_of_two_le hlarge
    exact jutila_lemma29Nine_kTwo_normalized hN hlarge G hprime

/-- Uniform absolute-constant form of the missing collar.  The constant is
`21 × 2² × 2 = 168`: three-block Cauchy/length comparison, at most two prime
fibers, and reciprocal prime mass at least `1/2`. -/
theorem jutila_lemma29Nine_kTwo_smallScale_uniform
    {N P : ℝ} (hN : 0 < N)
    (hJ : 1 ≤ kTwoPrimeLower N P)
    (hJlt : kTwoPrimeLower N P < 2)
    (G : Finset ℝ) :
    jutilaSecondMoment N G ^ 2 ≤
      168 * (G.card : ℝ) ^ 2 *
        (maxProductMultiplicity N : ℝ) ^ 2 *
        jutilaSecondMoment P G := by
  have hmain := jutila_lemma29Nine_kTwo_normalized_smallScale
    hN hJ hJlt G
  have hFNat := kTwoTransferenceFiberCap_le_two_of_smallScale hJ hJlt
  have hF : (kTwoTransferenceFiberCap N P : ℝ) ≤ 2 := by
    exact_mod_cast hFNat
  have hQ := kTwoPrimeReciprocal_inv_le_two_of_smallScale hJ hJlt
  have hR : 0 ≤ (G.card : ℝ) ^ 2 := sq_nonneg _
  have hA : 0 ≤ (maxProductMultiplicity N : ℝ) := Nat.cast_nonneg _
  have hS : 0 ≤ jutilaSecondMoment P G := by
    unfold jutilaSecondMoment realGramQuadratic
    positivity
  have hF0 : 0 ≤ (kTwoTransferenceFiberCap N P : ℝ) := Nat.cast_nonneg _
  have hQ0 : 0 ≤ (kTwoPrimeReciprocal N P)⁻¹ := by
    unfold kTwoPrimeReciprocal primeReciprocalSum
    exact inv_nonneg.mpr (Finset.sum_nonneg
      (fun p hp => Real.rpow_nonneg (Nat.cast_nonneg p) _))
  calc
    jutilaSecondMoment N G ^ 2 ≤
      21 * (G.card : ℝ) ^ 2 *
        ((kTwoTransferenceFiberCap N P : ℝ) *
          (maxProductMultiplicity N : ℝ)) ^ 2 *
        (kTwoPrimeReciprocal N P)⁻¹ * jutilaSecondMoment P G := hmain
    _ ≤ 21 * (G.card : ℝ) ^ 2 *
        ((2 : ℝ) * (maxProductMultiplicity N : ℝ)) ^ 2 *
        (2 : ℝ) * jutilaSecondMoment P G := by
      gcongr
    _ = 168 * (G.card : ℝ) ^ 2 *
        (maxProductMultiplicity N : ℝ) ^ 2 *
        jutilaSecondMoment P G := by ring


/-- Premise-free subpower form of the collar: the only remaining hypotheses
are the literal numerical range conditions. -/
theorem jutila_lemma29Nine_kTwo_smallScale_subpower
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N P : ℝ) (G : Finset ℝ), 1 ≤ N →
        1 ≤ kTwoPrimeLower N P → kTwoPrimeLower N P < 2 →
        jutilaSecondMoment N G ^ 2 ≤
          C * (G.card : ℝ) ^ 2 * Real.rpow (4 * N ^ 2) epsilon *
            jutilaSecondMoment P G := by
  obtain ⟨C₀, hC₀, hmult⟩ :=
    maxProductMultiplicity_square_subpolynomial epsilon hepsilon
  refine ⟨168 * C₀, by positivity, ?_⟩
  intro N P G hN hJ hJlt
  have hmain := jutila_lemma29Nine_kTwo_smallScale_uniform
    (lt_of_lt_of_le zero_lt_one hN) hJ hJlt G
  have hm := hmult N hN
  have hR : 0 ≤ (G.card : ℝ) ^ 2 := sq_nonneg _
  have hS : 0 ≤ jutilaSecondMoment P G := by
    unfold jutilaSecondMoment realGramQuadratic
    positivity
  calc
    jutilaSecondMoment N G ^ 2 ≤
      168 * (G.card : ℝ) ^ 2 *
        (maxProductMultiplicity N : ℝ) ^ 2 *
        jutilaSecondMoment P G := hmain
    _ ≤ 168 * (G.card : ℝ) ^ 2 *
        (C₀ * Real.rpow (4 * N ^ 2) epsilon) *
        jutilaSecondMoment P G := by
      gcongr
    _ = (168 * C₀) * (G.card : ℝ) ^ 2 *
        Real.rpow (4 * N ^ 2) epsilon *
        jutilaSecondMoment P G := by ring

end

end GuthMaynardJutilaSmallScaleTransference

#print axioms GuthMaynardJutilaSmallScaleTransference.two_mem_primeRealIcc_of_smallScale
#print axioms GuthMaynardJutilaSmallScaleTransference.primeRealIcc_nonempty_of_two_le
#print axioms GuthMaynardJutilaSmallScaleTransference.kTwoProductRange_eq_dyadicUnion_of_one_le
#print axioms GuthMaynardJutilaSmallScaleTransference.jutila_lemma29Nine_kTwo_normalized_smallScale
#print axioms GuthMaynardJutilaSmallScaleTransference.jutila_lemma29Nine_kTwo_normalized_of_one_le
#print axioms GuthMaynardJutilaSmallScaleTransference.kTwoTransferenceFiberCap_le_two_of_smallScale
#print axioms GuthMaynardJutilaSmallScaleTransference.kTwoPrimeReciprocal_inv_le_two_of_smallScale
#print axioms GuthMaynardJutilaSmallScaleTransference.jutila_lemma29Nine_kTwo_smallScale_uniform
#print axioms GuthMaynardJutilaSmallScaleTransference.jutila_lemma29Nine_kTwo_smallScale_subpower
