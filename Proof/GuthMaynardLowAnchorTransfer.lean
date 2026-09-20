import GuthMaynardJutilaReflection2941Corrected
import GuthMaynardJutilaSmallScaleTransference

/-!
# Arbitrary-endpoint low-anchor transfer in Lemma 29.10

The last paragraph of Lemma 29.10 compares `S(N)` with `S(P)` for arbitrary
real `1 <= N <= P`.  Integer-ratio length comparison alone does not prove
that claim.  This module supplies the missing mechanism: bounded ratios are
put on one common three-dyadic support and treated by zero extension plus
Lemma 29.6; far ratios use the certified one-block prime transference at the
real scale `J=P/(2N)`.
-/

namespace GuthMaynardLowAnchorTransfer

open scoped BigOperators
open GuthMaynardHeathBrownMajorant
open GuthMaynardLengthComparison
open GuthMaynardJutilaTransference
open GuthMaynardJutilaLemma29NineKTwo
open GuthMaynardJutilaReflection2941Corrected
open GuthMaynardJutilaSmallScaleTransference

noncomputable section

def zeroExtendCoeff {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (a : ι → ℂ) (n : ι) : ℂ :=
  if n ∈ A then a n else 0

theorem gramPolynomial_zeroExtend_eq
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {A S : Finset ι} (hAS : A ⊆ S) (a : ι → ℂ)
    (z : ι → κ → ℂ) (t u : κ) :
    gramPolynomial S (zeroExtendCoeff A a) z t u =
      gramPolynomial A a z t u := by
  unfold gramPolynomial
  symm
  apply Finset.sum_subset_zero_on_sdiff hAS
  · intro n hn
    simp only [Finset.mem_sdiff] at hn
    simp [zeroExtendCoeff, hn.2]
  · intro n hn
    simp [zeroExtendCoeff, hn]

theorem realGramQuadratic_zeroExtend_eq
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {A S : Finset ι} (hAS : A ⊆ S) (W : Finset κ)
    (a : ι → ℂ) (z : ι → κ → ℂ) :
    realGramQuadratic S W (zeroExtendCoeff A a) z =
      realGramQuadratic A W a z := by
  unfold realGramQuadratic
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro u hu
  rw [gramPolynomial_zeroExtend_eq hAS]

/-- Lemma 29.6 on a literal common support.  This is the legal replacement
for the false assertion that the Gram quadratic is monotone in its support. -/
theorem realGramQuadratic_subset_le_of_nonnegative
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {A S : Finset ι} (hAS : A ⊆ S) (W : Finset κ)
    (b : ι → ℝ) (z : ι → κ → ℂ)
    (hb : ∀ n ∈ S, 0 ≤ b n) :
    realGramQuadratic A W (fun n => (b n : ℂ)) z ≤
      realGramQuadratic S W (fun n => (b n : ℂ)) z := by
  rw [← realGramQuadratic_zeroExtend_eq hAS W (fun n => (b n : ℂ)) z]
  exact gram_majorant_principle S W
    (zeroExtendCoeff A (fun n => (b n : ℂ))) b z (fun n hn => by
      by_cases hnA : n ∈ A
      · simp [zeroExtendCoeff, hnA, abs_of_nonneg (hb n hn)]
      · simp [zeroExtendCoeff, hnA, hb n hn])

theorem realDyadicIoc_subset_kTwoDyadicUnion
    {N P : ℝ} (hPN : P / 4 ≤ N) (hNP : N ≤ P) :
    realDyadicIoc N ⊆ kTwoDyadicUnion P := by
  intro n hn
  rw [mem_realDyadicIoc_iff] at hn
  unfold kTwoDyadicUnion
  simp only [Finset.mem_union, mem_realDyadicIoc_iff]
  by_cases hhalf : (n : ℝ) ≤ P / 2
  · exact Or.inl (Or.inl ⟨by linarith, by nlinarith⟩)
  · by_cases hone : (n : ℝ) ≤ P
    · exact Or.inl (Or.inr ⟨lt_of_not_ge hhalf, by nlinarith⟩)
    · exact Or.inr ⟨lt_of_not_ge hone, by linarith⟩

theorem negativeJutilaSecondMoment_le_kTwoUnion
    {N P : ℝ} (hPN : P / 4 ≤ N) (hNP : N ≤ P)
    (G : Finset ℝ) :
    negativeJutilaSecondMoment N G ≤
      realGramQuadratic (kTwoDyadicUnion P) G
        (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
        negativeDirichletPhase := by
  unfold negativeJutilaSecondMoment
  exact realGramQuadratic_subset_le_of_nonnegative
    (realDyadicIoc_subset_kTwoDyadicUnion hPN hNP) G
    (fun n => Real.rpow (n : ℝ) (-(1 / 2 : ℝ))) negativeDirichletPhase
    (fun n hn => Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- Uniform bounded-ratio comparison.  The factor `21` is the exact coarse
cost: three-piece Cauchy (`3`) followed by Lemma 29.8 (`1+2+4=7`). -/
theorem jutilaSecondMoment_le_twentyOne_of_quarter_le
    {N P : ℝ} (hPN : P / 4 ≤ N) (hNP : N ≤ P)
    (G : Finset ℝ) :
    jutilaSecondMoment N G ≤ 21 * jutilaSecondMoment P G := by
  have hcommon := negativeJutilaSecondMoment_le_kTwoUnion hPN hNP G
  have hsplit := realGramQuadratic_union_three_le
    (realDyadicIoc (P / 4)) (realDyadicIoc (P / 2)) (realDyadicIoc P)
    (kTwoDyadicBlocks_pairwise_disjoint P).1
    (kTwoDyadicBlocks_pairwise_disjoint P).2.1
    (kTwoDyadicBlocks_pairwise_disjoint P).2.2 G
    (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
    negativeDirichletPhase
  unfold kTwoDyadicUnion at hcommon hsplit
  have hA := negativeJutilaSecondMoment_eq_jutilaSecondMoment (P / 4) G
  have hB := negativeJutilaSecondMoment_eq_jutilaSecondMoment (P / 2) G
  have hC := negativeJutilaSecondMoment_eq_jutilaSecondMoment P G
  unfold negativeJutilaSecondMoment at hA hB hC
  rw [hA, hB, hC] at hsplit
  have hlength := three_dyadic_jutilaSecondMoments_le_seven P G
  rw [negativeJutilaSecondMoment_eq_jutilaSecondMoment] at hcommon
  nlinarith

private noncomputable def certifiedLaterBlock : LaterBlockTransference29_41LogK :=
  laterBlockTransference29_41LogThree
    (by
      simpa only [GuthMaynardJutilaReflection2941Corrected.DyadicPrimeReciprocalInverseLogBound,
        GuthMaynardJutilaLemma29NineKTwo.DyadicPrimeReciprocalInverseLogBound]
        using KTwoDyadicPrimeReciprocalFromCertifiedPsi.dyadicPrimeReciprocalInverseLogBound_certified)

theorem jutilaSecondMoment_far_anchor
    {N P : ℝ} (hN : 1 ≤ N) (hfar : 4 * N ≤ P) (G : Finset ℝ) :
    jutilaSecondMoment N G ≤
      certifiedLaterBlock.C * (Real.log P) ^ 3 * jutilaSecondMoment P G := by
  let J : ℝ := P / (2 * N)
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hJ : 2 ≤ J := by
    dsimp [J]
    apply (le_div_iff₀ (by positivity)).2
    nlinarith
  have hbound := certifiedLaterBlock.bound J N G hJ (by linarith)
    (primeRealIcc_nonempty_of_two_le hJ)
  have href : 2 * J * N = P := by
    dsimp [J]
    field_simp [hNpos.ne']
  simpa only [certifiedLaterBlock, laterBlockTransference29_41LogThree_K,
    href] using hbound

/-- Arbitrary-real comparison sufficient for the low-anchor call. -/
theorem jutilaSecondMoment_low_anchor_certified :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N P : ℝ) (G : Finset ℝ), 1 ≤ N → N ≤ P → 2 ≤ P →
        jutilaSecondMoment N G ≤
          C * (Real.log P) ^ 3 * jutilaSecondMoment P G := by
  let C : ℝ := max certifiedLaterBlock.C (21 / (Real.log 2) ^ 3)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C :=
    lt_of_lt_of_le certifiedLaterBlock.C_pos (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro N P G hN hNP hP
  by_cases hfar : 4 * N ≤ P
  · have hf := jutilaSecondMoment_far_anchor hN hfar G
    have hHC : certifiedLaterBlock.C ≤ C := le_max_left _ _
    have hfactor : 0 ≤ (Real.log P) ^ 3 * jutilaSecondMoment P G := by
      exact mul_nonneg (pow_nonneg (Real.log_nonneg (by linarith)) _)
        (jutilaSecondMoment_nonneg P G)
    exact hf.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hHC hfactor)
  · have hnear := jutilaSecondMoment_le_twentyOne_of_quarter_le
      (N := N) (P := P) (by linarith) hNP G
    have hlog : Real.log 2 ≤ Real.log P :=
      Real.log_le_log (by norm_num) hP
    have hlogpow : (Real.log 2) ^ 3 ≤ (Real.log P) ^ 3 :=
      pow_le_pow_left₀ hlogTwo.le hlog 3
    have hbase : 21 ≤ C * (Real.log P) ^ 3 := by
      have hc0 : 21 / (Real.log 2) ^ 3 ≤ C := le_max_right _ _
      calc
        21 = (21 / (Real.log 2) ^ 3) * (Real.log 2) ^ 3 := by
          field_simp [ne_of_gt (pow_pos hlogTwo 3)]
        _ ≤ C * (Real.log P) ^ 3 :=
          mul_le_mul hc0 hlogpow (by positivity) hC.le
    exact hnear.trans (mul_le_mul_of_nonneg_right hbase
      (jutilaSecondMoment_nonneg P G))

/-- Source-facing `log T` form.  The only scale fact it needs from the
definition of the anchor is the very coarse `P ≤ T²`; the analytic comparison
itself is premise-free. -/
theorem jutilaSecondMoment_low_anchor_time_squared_certified :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T N P : ℝ) (G : Finset ℝ), 2 ≤ T → 1 ≤ N → N ≤ P → 2 ≤ P →
        P ≤ T ^ 2 →
        jutilaSecondMoment N G ≤
          C * (Real.log T) ^ 3 * jutilaSecondMoment P G := by
  obtain ⟨C₀, hC₀, hbase⟩ := jutilaSecondMoment_low_anchor_certified
  refine ⟨8 * C₀, by positivity, ?_⟩
  intro T N P G hT hN hNP hP hPT
  have hraw := hbase N P G hN hNP hP
  have hTpos : 0 < T := by linarith
  have hPpos : 0 < P := by linarith
  have hlogPTwo : Real.log P ≤ Real.log (T ^ 2) :=
    Real.log_le_log hPpos hPT
  rw [Real.log_pow] at hlogPTwo
  have hlogP0 : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hpow : (Real.log P) ^ 3 ≤ (2 * Real.log T) ^ 3 :=
    pow_le_pow_left₀ hlogP0 hlogPTwo 3
  have hmoment : 0 ≤ jutilaSecondMoment P G :=
    jutilaSecondMoment_nonneg P G
  calc
    jutilaSecondMoment N G ≤
        C₀ * (Real.log P) ^ 3 * jutilaSecondMoment P G := hraw
    _ ≤ C₀ * (2 * Real.log T) ^ 3 * jutilaSecondMoment P G := by
      gcongr
    _ = (8 * C₀) * (Real.log T) ^ 3 * jutilaSecondMoment P G := by ring

end

end GuthMaynardLowAnchorTransfer

#print axioms GuthMaynardLowAnchorTransfer.realGramQuadratic_zeroExtend_eq
#print axioms GuthMaynardLowAnchorTransfer.realGramQuadratic_subset_le_of_nonnegative
#print axioms GuthMaynardLowAnchorTransfer.jutilaSecondMoment_le_twentyOne_of_quarter_le
#print axioms GuthMaynardLowAnchorTransfer.jutilaSecondMoment_far_anchor
#print axioms GuthMaynardLowAnchorTransfer.jutilaSecondMoment_low_anchor_certified
#print axioms GuthMaynardLowAnchorTransfer.jutilaSecondMoment_low_anchor_time_squared_certified
