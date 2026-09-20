import KTwoPrimeFiberBound

/-!
# Corrected large-scale arithmetic budget for Jutila's `k = 2` step

The earlier unrestricted budget is false for `P < 1`.  This module restores
the application-faithful premise `2 ≤ P`, proves the complete elementary
fiber contribution, and exposes the one genuine prime-distribution input:
the reciprocal-prime mass in every dyadic interval.
-/

namespace GuthMaynardJutilaLemma29NineKTwo

open GuthMaynardJutilaTransference
open GuthMaynardPoweringKTwo
open GuthMaynardHeathBrownMajorant
open GuthMaynardLengthComparison

noncomputable section

/-- Source-exact content of the note following Vol. 3, Lemma 29.7,
equation (29.32), printed pp. 264--265: on a dyadic prime interval the
reciprocal-prime mass is bounded below by a constant times `1 / log J`, for
all sufficiently large `J`. -/
def DyadicPrimeReciprocalLower29_32 : Prop :=
  ∃ c J₀ : ℝ, 0 < c ∧ 2 ≤ J₀ ∧
    ∀ J : ℝ, J₀ ≤ J →
      c / Real.log J ≤ primeReciprocalSum J (2 * J) (1 / 2)

/-- Exact analytic prime input.  This is the reciprocal-prime lower bound
used in the printed proof, written as the inverse upper bound needed by the
transference normalization. -/
def DyadicPrimeReciprocalInverseLogBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ J : ℝ, 2 ≤ J → (primeRealIcc J (2 * J)).Nonempty →
      (primeReciprocalSum J (2 * J) (1 / 2))⁻¹ ≤
        C * Real.log (4 * J)

/-- The source's eventual lower bound globalizes over `J ≥ 2` whenever the
dyadic interval is nonempty.  The bounded range uses one displayed prime;
no further prime-distribution theorem is hidden in the adapter. -/
theorem dyadicPrimeReciprocalInverseLogBound_of_29_32
    (hsource : DyadicPrimeReciprocalLower29_32) :
    DyadicPrimeReciprocalInverseLogBound := by
  obtain ⟨c, J₀, hc, hJ₀, hlarge⟩ := hsource
  let C : ℝ := max c⁻¹ ((2 * J₀) / Real.log 8)
  have hlogEight : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hJ₀pos : 0 < J₀ := lt_of_lt_of_le (by norm_num) hJ₀
  have hC : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le (inv_pos.mpr hc) (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro J hJ hprime
  have hJpos : 0 < J := lt_of_lt_of_le (by norm_num) hJ
  have hlogJ : 0 < Real.log J := Real.log_pos (lt_of_lt_of_le (by norm_num) hJ)
  have hfourJpos : 0 < 4 * J := by positivity
  have hlogMono : Real.log J ≤ Real.log (4 * J) := by
    apply Real.log_le_log hJpos
    nlinarith
  by_cases hJJ₀ : J₀ ≤ J
  · have hlower := hlarge J hJJ₀
    have hbase : 0 < c / Real.log J := div_pos hc hlogJ
    have hsum : 0 < primeReciprocalSum J (2 * J) (1 / 2) :=
      hbase.trans_le hlower
    have hinv :
        (primeReciprocalSum J (2 * J) (1 / 2))⁻¹ ≤
          (c / Real.log J)⁻¹ :=
      (inv_le_inv₀ hsum hbase).2 hlower
    calc
      (primeReciprocalSum J (2 * J) (1 / 2))⁻¹ ≤
          (c / Real.log J)⁻¹ := hinv
      _ = c⁻¹ * Real.log J := by field_simp [hc.ne']
      _ ≤ c⁻¹ * Real.log (4 * J) :=
        mul_le_mul_of_nonneg_left hlogMono (inv_nonneg.mpr hc.le)
      _ ≤ C * Real.log (4 * J) := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.log_nonneg (by nlinarith : 1 ≤ 4 * J))
  · have hJlt : J < J₀ := lt_of_not_ge hJJ₀
    obtain ⟨p, hp⟩ := hprime
    have hpData := (mem_primeRealIcc_iff (by positivity : 0 ≤ 2 * J)).mp hp
    have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpData.2.2.pos
    have hpUpper : (p : ℝ) ≤ 2 * J := hpData.2.1
    have hterm :
        Real.rpow (p : ℝ) (-2 * (1 / 2 : ℝ)) ≤
          primeReciprocalSum J (2 * J) (1 / 2) := by
      unfold primeReciprocalSum
      exact Finset.single_le_sum
        (fun q hq => Real.rpow_nonneg (Nat.cast_nonneg q) _) hp
    have hterm' : (p : ℝ)⁻¹ ≤
        primeReciprocalSum J (2 * J) (1 / 2) := by
      simpa [Real.rpow_neg_one] using hterm
    have hbaseLower : (2 * J)⁻¹ ≤
        primeReciprocalSum J (2 * J) (1 / 2) := by
      have hbaseToP : (2 * J)⁻¹ ≤ (p : ℝ)⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hpPos hpUpper
      exact hbaseToP.trans hterm'
    have hbasePos : 0 < (2 * J)⁻¹ := inv_pos.mpr (by positivity)
    have hsum : 0 < primeReciprocalSum J (2 * J) (1 / 2) :=
      hbasePos.trans_le hbaseLower
    have hinv :
        (primeReciprocalSum J (2 * J) (1 / 2))⁻¹ ≤ 2 * J := by
      have := (inv_le_inv₀ hsum hbasePos).2 hbaseLower
      simpa using this
    have htwoJ : 2 * J ≤ 2 * J₀ := by linarith
    have hratio : 2 * J₀ ≤
        ((2 * J₀) / Real.log 8) * Real.log (4 * J) := by
      have hlogLower : Real.log 8 ≤ Real.log (4 * J) := by
        apply Real.log_le_log (by norm_num)
        nlinarith
      have hfactor : 0 ≤ (2 * J₀) / Real.log 8 := by positivity
      calc
        2 * J₀ = ((2 * J₀) / Real.log 8) * Real.log 8 := by
          field_simp [hlogEight.ne']
        _ ≤ ((2 * J₀) / Real.log 8) * Real.log (4 * J) :=
          mul_le_mul_of_nonneg_left hlogLower hfactor
    calc
      (primeReciprocalSum J (2 * J) (1 / 2))⁻¹ ≤ 2 * J := hinv
      _ ≤ 2 * J₀ := htwoJ
      _ ≤ ((2 * J₀) / Real.log 8) * Real.log (4 * J) := hratio
      _ ≤ C * Real.log (4 * J) := by
        exact mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.log_nonneg (by nlinarith : 1 ≤ 4 * J))

/-- Corrected source-facing log budget.  The sole change from the false
unrestricted interface is the eventual-application premise `2 ≤ P`. -/
def KTwoPrimeArithmeticLogBudgetLargeScale : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (N P : ℝ), 0 < N → 2 ≤ kTwoPrimeLower N P → 2 ≤ P →
      (kTwoPrimeRange N P).Nonempty →
      21 * (kTwoTransferenceFiberCap N P : ℝ) ^ 2 *
          (kTwoPrimeReciprocal N P)⁻¹ ≤
        C * (Real.log P) ^ 3

/-- If the divisor-fiber cap is nonzero, the product interval contains a
positive integer.  Hence `4N² ≥ 1`, and the auxiliary prime scale
`J=P/(4N²)` is no larger than `P`. -/
theorem kTwoPrimeLower_le_P_of_fiberCap_pos
    {N P : ℝ} (hN : 0 < N) (hJ : 2 ≤ kTwoPrimeLower N P)
    (hP : 0 ≤ P) (hcap : 0 < kTwoTransferenceFiberCap N P) :
    kTwoPrimeLower N P ≤ P := by
  have hex : ∃ l ∈ kTwoProductRange N P,
      0 < kTwoTransferenceFiberCard N P l := by
    by_contra hnone
    have hcapzero : kTwoTransferenceFiberCap N P ≤ 0 := by
      unfold kTwoTransferenceFiberCap
      apply Finset.sup_le
      intro l hl
      exact Nat.le_of_not_gt (fun hpos => hnone ⟨l, hl, hpos⟩)
    omega
  obtain ⟨l, hl, hfiber⟩ := hex
  have hfiberNonempty :
      (((kTwoPrimeRange N P).product (productIoc N)).filter
        (fun q => q.1 * q.2 = l)).Nonempty := by
    exact Finset.card_pos.mp (by simpa [kTwoTransferenceFiberCard] using hfiber)
  obtain ⟨q, hq⟩ := hfiberNonempty
  have hq' := Finset.mem_filter.mp hq
  have hqmem : q.1 ∈ kTwoPrimeRange N P ∧ q.2 ∈ productIoc N := by
    simpa using hq'.1
  have hlpos : 0 < l := by
    exact_mod_cast (kTwoProductRange_cast_pos_and_le hN hJ hl).1
  have hnpos : 0 < q.2 := by
    by_contra hn
    have hnzero : q.2 = 0 := Nat.eq_zero_of_not_pos hn
    rw [hnzero, Nat.mul_zero] at hq'
    omega
  have hnrange := (mem_productIoc_iff.mp hqmem.2).2
  have hden : (1 : ℝ) ≤ 4 * N ^ 2 := by
    have hone : (1 : ℝ) ≤ (q.2 : ℝ) := by exact_mod_cast hnpos
    exact hone.trans hnrange
  unfold kTwoPrimeLower
  exact div_le_self hP hden

/-- The dyadic reciprocal-prime theorem plus the certified elementary fiber
count gives the corrected cubic-log budget. -/
theorem kTwoPrimeArithmeticLogBudgetLargeScale_of_dyadicPrimeReciprocal
    (hprimeReciprocal : DyadicPrimeReciprocalInverseLogBound) :
    KTwoPrimeArithmeticLogBudgetLargeScale := by
  obtain ⟨Cr, hCr, hrecip⟩ := hprimeReciprocal
  let Cf : ℝ := 3 / Real.log 2
  let C : ℝ := 63 * Cf ^ 2 * Cr
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCf : 0 < Cf := by dsimp [Cf]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N P hN hJ hP hprime
  have hlogP : 0 < Real.log P :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hP)
  have hfiber := kTwoTransferenceFiberCap_cast_le_log hN hJ hP
  by_cases hcapZero : kTwoTransferenceFiberCap N P = 0
  · simp [hcapZero]
    dsimp [C]
    positivity
  · have hcapPos : 0 < kTwoTransferenceFiberCap N P :=
      Nat.pos_of_ne_zero hcapZero
    have hJleP := kTwoPrimeLower_le_P_of_fiberCap_pos hN hJ
      (le_trans (by norm_num) hP) hcapPos
    have hfourJ : 4 * kTwoPrimeLower N P ≤ P ^ 3 := by
      have hP2 : 4 ≤ P ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hJleP (by norm_num : (0 : ℝ) ≤ 4)]
    have hfourJpos : 0 < 4 * kTwoPrimeLower N P := by
      positivity
    have hlogFourJ :
        Real.log (4 * kTwoPrimeLower N P) ≤ 3 * Real.log P := by
      calc
        Real.log (4 * kTwoPrimeLower N P) ≤ Real.log (P ^ 3) :=
          Real.log_le_log hfourJpos hfourJ
        _ = 3 * Real.log P := by rw [Real.log_pow]; norm_num
    have hrecipAt := hrecip (kTwoPrimeLower N P) hJ hprime
    have hrecipNonneg : 0 ≤ Cr * Real.log (4 * kTwoPrimeLower N P) :=
      (inv_nonneg.mpr (Finset.sum_nonneg
        (fun p hp => Real.rpow_nonneg (Nat.cast_nonneg p) _))).trans hrecipAt
    have hrecipP :
        (kTwoPrimeReciprocal N P)⁻¹ ≤ 3 * Cr * Real.log P := by
      unfold kTwoPrimeReciprocal
      calc
        (primeReciprocalSum (kTwoPrimeLower N P)
            (2 * kTwoPrimeLower N P) (1 / 2))⁻¹ ≤
            Cr * Real.log (4 * kTwoPrimeLower N P) := hrecipAt
        _ ≤ Cr * (3 * Real.log P) :=
          mul_le_mul_of_nonneg_left hlogFourJ hCr.le
        _ = 3 * Cr * Real.log P := by ring
    have hcapP :
        (kTwoTransferenceFiberCap N P : ℝ) ≤ Cf * Real.log P := by
      calc
        (kTwoTransferenceFiberCap N P : ℝ) ≤
            3 * Real.log P / Real.log 2 := hfiber
        _ = Cf * Real.log P := by dsimp [Cf]; ring
    have hcapNonneg : 0 ≤ (kTwoTransferenceFiberCap N P : ℝ) := by positivity
    have hrecipInvNonneg : 0 ≤ (kTwoPrimeReciprocal N P)⁻¹ := by
      unfold kTwoPrimeReciprocal primeReciprocalSum
      exact inv_nonneg.mpr (Finset.sum_nonneg
        (fun p hp => Real.rpow_nonneg (Nat.cast_nonneg p) _))
    calc
      21 * (kTwoTransferenceFiberCap N P : ℝ) ^ 2 *
          (kTwoPrimeReciprocal N P)⁻¹ ≤
          21 * (Cf * Real.log P) ^ 2 *
            (3 * Cr * Real.log P) := by
        gcongr
      _ = C * (Real.log P) ^ 3 := by
        dsimp [C]
        ring

/-- Corrected printed `k=2` conclusion, with the large-scale premise kept
visible instead of trying to inhabit the false unrestricted proposition. -/
theorem jutila_lemma29Nine_kTwo_of_primeArithmeticLogBudgetLargeScale
    (hbudget : KTwoPrimeArithmeticLogBudgetLargeScale) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N P : ℝ) (G : Finset ℝ), 0 < N →
        2 ≤ kTwoPrimeLower N P → 2 ≤ P →
        (kTwoPrimeRange N P).Nonempty →
        jutilaSecondMoment N G ^ 2 ≤
          C * (G.card : ℝ) ^ 2 * (Real.log P) ^ 3 *
            (maxProductMultiplicity N : ℝ) ^ 2 *
              jutilaSecondMoment P G := by
  obtain ⟨C, hC, hbudget⟩ := hbudget
  refine ⟨C, hC, ?_⟩
  intro N P G hN hJ hP hprime
  have hdet := jutila_lemma29Nine_kTwo_normalized hN hJ G hprime
  have hprimeBudget := hbudget N P hN hJ hP hprime
  have hR : 0 ≤ (G.card : ℝ) ^ 2 := sq_nonneg _
  have hA : 0 ≤ (maxProductMultiplicity N : ℝ) ^ 2 := sq_nonneg _
  have hS : 0 ≤ jutilaSecondMoment P G := by
    unfold jutilaSecondMoment realGramQuadratic
    positivity
  calc
    jutilaSecondMoment N G ^ 2 ≤
        21 * (G.card : ℝ) ^ 2 *
          ((kTwoTransferenceFiberCap N P : ℝ) *
            (maxProductMultiplicity N : ℝ)) ^ 2 *
          (kTwoPrimeReciprocal N P)⁻¹ * jutilaSecondMoment P G := hdet
    _ = ((G.card : ℝ) ^ 2 * (maxProductMultiplicity N : ℝ) ^ 2 *
          jutilaSecondMoment P G) *
        (21 * (kTwoTransferenceFiberCap N P : ℝ) ^ 2 *
          (kTwoPrimeReciprocal N P)⁻¹) := by ring
    _ ≤ ((G.card : ℝ) ^ 2 * (maxProductMultiplicity N : ℝ) ^ 2 *
          jutilaSecondMoment P G) * (C * (Real.log P) ^ 3) := by
      exact mul_le_mul_of_nonneg_left hprimeBudget
        (mul_nonneg (mul_nonneg hR hA) hS)
    _ = C * (G.card : ℝ) ^ 2 * (Real.log P) ^ 3 *
          (maxProductMultiplicity N : ℝ) ^ 2 *
            jutilaSecondMoment P G := by ring

#print axioms kTwoPrimeLower_le_P_of_fiberCap_pos
#print axioms dyadicPrimeReciprocalInverseLogBound_of_29_32
#print axioms kTwoPrimeArithmeticLogBudgetLargeScale_of_dyadicPrimeReciprocal
#print axioms jutila_lemma29Nine_kTwo_of_primeArithmeticLogBudgetLargeScale

end

end GuthMaynardJutilaLemma29NineKTwo
