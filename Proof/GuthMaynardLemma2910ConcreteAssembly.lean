import GuthMaynardLemma295ExactSourceSurface
import GuthMaynardLemma2910ScalarClosure
import GuthMaynardLemma2910SourceScale
import GuthMaynardKTwoMultiplicitySubpower
import KTwoDyadicPrimeReciprocalFromCertifiedPsi
import GuthMaynardJutilaSmallScaleTransference

/-!
# Concrete low/intermediate assembly for Jutila Lemma 29.10

This file begins the source-facing assembly after the exact Lemma-29.5 AFE.
It does two things which were previously separated across abstract interfaces:

* it combines the certified `k = 2` powering theorem with the premise-free
  subpower estimate for the product multiplicity;
* it inserts that estimate into the corrected fixed-fifth-power reflection
  recurrence and closes the direct-feedback middle regime.

The direct product-convolution proof below repairs the exact prime-scale-one
endpoint (and hence the powering call in the bootstrap step).  The bounded
prime-scale collar is now handled separately and welded to the Bertrand range,
giving one premise-free source-range powering theorem and one unified direct
AFE constructor.  The final section retains the old endpoint calculation only
as documentation of the interface defect that this assembly repairs.
-/

namespace GuthMaynardLemma2910ConcreteAssembly

open GuthMaynardJutilaReflection2941
open GuthMaynardLemma295ExactSourceSurface
open GuthMaynardLemma2910ScalarClosure
open GuthMaynardLemma2910SourceScale
open GuthMaynardJutilaLemma29NineKTwo
open GuthMaynardKTwoMultiplicitySubpower
open GuthMaynardLengthComparison
open GuthMaynardPoweringKTwo
open GuthMaynardHeathBrownMajorant
open GuthMaynardJutilaTransference
open KTwoDyadicPrimeReciprocalFromCertifiedPsi
open GuthMaynardJutilaSmallScaleTransference

noncomputable section

/-- The corrected `k = 2` powering theorem with both finite arithmetic losses
discharged.  The only loss left is the explicit subpower factor
`(4 N^2)^eta`; in particular, no multiplicity proposition remains among the
hypotheses. -/
theorem kTwo_powering_with_subpower_multiplicity
    {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N P : ℝ) (G : Finset ℝ), 1 ≤ N →
        2 ≤ kTwoPrimeLower N P → 2 ≤ P →
        (kTwoPrimeRange N P).Nonempty →
        jutilaSecondMoment N G ^ 2 ≤
          C * (G.card : ℝ) ^ 2 * (Real.log P) ^ 3 *
            Real.rpow (4 * N ^ 2) eta * jutilaSecondMoment P G := by
  obtain ⟨Cp, hCp, hpower⟩ :=
    jutila_lemma29Nine_kTwo_of_primeArithmeticLogBudgetLargeScale
      (kTwoPrimeArithmeticLogBudgetLargeScale_of_dyadicPrimeReciprocal
        dyadicPrimeReciprocalInverseLogBound_certified)
  obtain ⟨Cm, hCm, hmult⟩ :=
    maxProductMultiplicity_square_subpolynomial eta heta
  refine ⟨Cp * Cm, mul_pos hCp hCm, ?_⟩
  intro N P G hN hJ hP hprime
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hp := hpower N P G hNpos hJ hP hprime
  have hm := hmult N hN
  have hbase : 0 ≤ Real.rpow (4 * N ^ 2) eta :=
    Real.rpow_nonneg (by positivity) _
  have hS : 0 ≤ jutilaSecondMoment P G := by
    unfold jutilaSecondMoment realGramQuadratic
    positivity
  have hfront :
      0 ≤ Cp * (G.card : ℝ) ^ 2 * (Real.log P) ^ 3 := by
    have hlog : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
    positivity
  calc
    jutilaSecondMoment N G ^ 2 ≤
        Cp * (G.card : ℝ) ^ 2 * (Real.log P) ^ 3 *
          (maxProductMultiplicity N : ℝ) ^ 2 *
            jutilaSecondMoment P G := hp
    _ ≤ Cp * (G.card : ℝ) ^ 2 * (Real.log P) ^ 3 *
          (Cm * Real.rpow (4 * N ^ 2) eta) *
            jutilaSecondMoment P G := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hm hfront) hS
    _ = (Cp * Cm) * (G.card : ℝ) ^ 2 * (Real.log P) ^ 3 *
          Real.rpow (4 * N ^ 2) eta * jutilaSecondMoment P G := by ring

/-- In the collar `1 ≤ J < 2`, the prime reciprocal mass is at least the
literal contribution of `p=2`; hence its inverse is at most two. -/
theorem smallScale_kTwoPrimeReciprocal_inv_le_two
    {N P : ℝ} (hJ : 1 ≤ kTwoPrimeLower N P)
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
  have hinv := (inv_le_inv₀ hsumPos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)).2 hterm
  norm_num at hinv ⊢
  exact hinv

/-- Fully explicit small-collar powering bound. -/
theorem kTwo_powering_smallScale_explicit
    {N P : ℝ} (hN : 0 < N)
    (hJ : 1 ≤ kTwoPrimeLower N P)
    (hJlt : kTwoPrimeLower N P < 2) (G : Finset ℝ) :
    jutilaSecondMoment N G ^ 2 ≤
      168 * (G.card : ℝ) ^ 2 *
        (maxProductMultiplicity N : ℝ) ^ 2 *
          jutilaSecondMoment P G := by
  exact jutila_lemma29Nine_kTwo_smallScale_uniform hN hJ hJlt G

/-- Small-collar powering with the multiplicity already absorbed into an
explicit subpower factor. -/
theorem kTwo_powering_smallScale_subpower
    {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N P : ℝ) (G : Finset ℝ), 1 ≤ N →
        1 ≤ kTwoPrimeLower N P → kTwoPrimeLower N P < 2 →
        jutilaSecondMoment N G ^ 2 ≤
          C * (G.card : ℝ) ^ 2 * Real.rpow (4 * N ^ 2) eta *
            jutilaSecondMoment P G := by
  obtain ⟨Cm, hCm, hm⟩ :=
    maxProductMultiplicity_square_subpolynomial eta heta
  refine ⟨168 * Cm, by positivity, ?_⟩
  intro N P G hN hJ hJlt
  have hraw := kTwo_powering_smallScale_explicit
    (lt_of_lt_of_le zero_lt_one hN) hJ hJlt G
  have hmult := hm N hN
  have hR : 0 ≤ (G.card : ℝ) ^ 2 := sq_nonneg _
  have hS : 0 ≤ jutilaSecondMoment P G := by
    unfold jutilaSecondMoment realGramQuadratic
    positivity
  calc
    jutilaSecondMoment N G ^ 2 ≤
        168 * (G.card : ℝ) ^ 2 *
          (maxProductMultiplicity N : ℝ) ^ 2 *
            jutilaSecondMoment P G := hraw
    _ ≤ 168 * (G.card : ℝ) ^ 2 *
          (Cm * Real.rpow (4 * N ^ 2) eta) *
            jutilaSecondMoment P G := by gcongr
    _ = (168 * Cm) * (G.card : ℝ) ^ 2 *
          Real.rpow (4 * N ^ 2) eta * jutilaSecondMoment P G := by ring

/-- Bertrand's theorem supplies the prime interval required by the large
prime-scale branch for every real lower endpoint `J ≥ 2`. -/
theorem primeRealIcc_self_double_nonempty_of_two_le
    {J : ℝ} (hJ : 2 ≤ J) :
    (primeRealIcc J (2 * J)).Nonempty := by
  let n : ℕ := Nat.floor J
  have hnTwo : 2 ≤ n := by
    dsimp [n]
    exact Nat.le_floor (by exact_mod_cast hJ)
  have hn0 : n ≠ 0 := by omega
  obtain ⟨p, hpPrime, hnp, hpUpper⟩ := Nat.bertrand n hn0
  refine ⟨p, ?_⟩
  rw [mem_primeRealIcc_iff (by positivity : 0 ≤ 2 * J)]
  have hJlt : J < (n : ℝ) + 1 := by
    simpa [n] using Nat.lt_floor_add_one J
  have hnpCast : (n : ℝ) + 1 ≤ p := by exact_mod_cast hnp
  have hnleJ : (n : ℝ) ≤ J := by
    dsimp [n]
    exact Nat.floor_le (by linarith)
  constructor
  · exact (hJlt.trans_le hnpCast).le
  · constructor
    · have hpUpperR : (p : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hpUpper
      exact hpUpperR.trans (mul_le_mul_of_nonneg_left hnleJ (by norm_num))
    · exact hpPrime

theorem kTwoPrimeRange_nonempty_of_two_le
    {N P : ℝ} (hJ : 2 ≤ kTwoPrimeLower N P) :
    (kTwoPrimeRange N P).Nonempty := by
  exact primeRealIcc_self_double_nonempty_of_two_le hJ

/-- Unified corrected `k=2` powering theorem on the full legal source range
`J ≥ 1`.  The bounded collar and the large dyadic-prime range are combined
under one harmless `(1+log P)^3` envelope. -/
theorem kTwo_powering_oneScale_subpower
    {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N P : ℝ) (G : Finset ℝ), 1 ≤ N → 2 ≤ P →
        1 ≤ kTwoPrimeLower N P →
        jutilaSecondMoment N G ^ 2 ≤
          C * (1 + Real.log P) ^ 3 * (G.card : ℝ) ^ 2 *
            Real.rpow (4 * N ^ 2) eta * jutilaSecondMoment P G := by
  obtain ⟨Cl, hCl, hlarge⟩ := kTwo_powering_with_subpower_multiplicity heta
  obtain ⟨Cs, hCs, hsmall⟩ := kTwo_powering_smallScale_subpower heta
  let C := max Cl Cs
  have hC : 0 < C := hCl.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro N P G hN hP hJ
  have hlog : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
  have hbase : 1 ≤ 1 + Real.log P := by linarith
  have hF : 1 ≤ (1 + Real.log P) ^ (3 : ℕ) := by
    calc
      1 = (1 : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ (1 + Real.log P) ^ (3 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) hbase 3
  have hS : 0 ≤ jutilaSecondMoment P G := by
    unfold jutilaSecondMoment realGramQuadratic
    positivity
  have hB : 0 ≤ (G.card : ℝ) ^ 2 *
      Real.rpow (4 * N ^ 2) eta * jutilaSecondMoment P G := by
    exact mul_nonneg
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)) hS
  by_cases hcollar : kTwoPrimeLower N P < 2
  · have hs := hsmall N P G hN hJ hcollar
    calc
      jutilaSecondMoment N G ^ 2 ≤
          Cs * ((G.card : ℝ) ^ 2 * Real.rpow (4 * N ^ 2) eta *
            jutilaSecondMoment P G) := by simpa [mul_assoc] using hs
      _ ≤ C * ((G.card : ℝ) ^ 2 * Real.rpow (4 * N ^ 2) eta *
            jutilaSecondMoment P G) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hB
      _ ≤ C * (1 + Real.log P) ^ 3 * (G.card : ℝ) ^ 2 *
            Real.rpow (4 * N ^ 2) eta * jutilaSecondMoment P G := by
        have hcoeff : C ≤ C * (1 + Real.log P) ^ 3 := by
          simpa using mul_le_mul_of_nonneg_left hF hC.le
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff hB
  · have hJtwo : 2 ≤ kTwoPrimeLower N P := le_of_not_gt hcollar
    have hp := kTwoPrimeRange_nonempty_of_two_le hJtwo
    have hl := hlarge N P G hN hJtwo hP hp
    have hlogPow : (Real.log P) ^ (3 : ℕ) ≤
        (1 + Real.log P) ^ (3 : ℕ) := by
      exact pow_le_pow_left₀ hlog (by linarith) 3
    have htail : 0 ≤ (G.card : ℝ) ^ 2 *
        Real.rpow (4 * N ^ 2) eta * jutilaSecondMoment P G := hB
    calc
      jutilaSecondMoment N G ^ 2 ≤
          Cl * (Real.log P) ^ 3 * ((G.card : ℝ) ^ 2 *
            Real.rpow (4 * N ^ 2) eta * jutilaSecondMoment P G) := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hl
      _ ≤ C * (1 + Real.log P) ^ 3 * ((G.card : ℝ) ^ 2 *
            Real.rpow (4 * N ^ 2) eta * jutilaSecondMoment P G) := by
        have hcoeff : Cl * (Real.log P) ^ 3 ≤
            C * (1 + Real.log P) ^ 3 :=
          mul_le_mul (le_max_left _ _) hlogPow
            (pow_nonneg hlog _) hC.le
        exact mul_le_mul_of_nonneg_right hcoeff htail
      _ = C * (1 + Real.log P) ^ 3 * (G.card : ℝ) ^ 2 *
            Real.rpow (4 * N ^ 2) eta * jutilaSecondMoment P G := by ring

/-! ## Prime-free powering at the boundary scale -/

def productCoefficientOneMoment (N : ℝ) (G : Finset ℝ) : ℝ :=
  realGramQuadratic (productIoc N) G
    (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
    negativeDirichletPhase

/-- Coefficient majorization for the literal product convolution, before any
prime transference. -/
theorem multiplicityQuadraticForm_le_maxProductMultiplicity
    {N : ℝ} (hN : 0 ≤ N) (G : Finset ℝ) :
    multiplicityQuadraticForm N G ≤
      (maxProductMultiplicity N : ℝ) ^ 2 *
        productCoefficientOneMoment N G := by
  have hmajor := gram_majorant_principle
    (productIoc N) G
    (fun n => ((productMultiplicity N n : ℝ) *
      Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
    (fun n => (maxProductMultiplicity N : ℝ) *
      Real.rpow (n : ℝ) (-(1 / 2 : ℝ)))
    negativeDirichletPhase
    (fun n hn => by
      have hm : (productMultiplicity N n : ℝ) ≤
          (maxProductMultiplicity N : ℝ) := by
        exact_mod_cast productMultiplicity_le_maxProductMultiplicity hN n
      have hp := Real.rpow_nonneg (Nat.cast_nonneg n) (-(1 / 2 : ℝ))
      rw [norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg _)]
      have habs : |Real.rpow (n : ℝ) (-(1 / 2 : ℝ))| =
          Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) := abs_of_nonneg hp
      change (productMultiplicity N n : ℝ) *
          |Real.rpow (n : ℝ) (-(1 / 2 : ℝ))| ≤
        (maxProductMultiplicity N : ℝ) *
          Real.rpow (n : ℝ) (-(1 / 2 : ℝ))
      rw [habs]
      exact mul_le_mul_of_nonneg_right hm hp)
  rw [multiplicityQuadraticForm_eq_sourceQuadratic]
  unfold sourceQuadratic sigmaCoefficient productCoefficientOneMoment
  calc
    realGramQuadratic (productIoc N) G
        (fun n => (productMultiplicity N n : ℂ) *
          (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
        negativeDirichletPhase ≤
      realGramQuadratic (productIoc N) G
        (fun n => (((maxProductMultiplicity N : ℝ) *
          Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℝ) : ℂ))
        negativeDirichletPhase := by
      convert hmajor using 1 <;> norm_cast
    _ = ‖((maxProductMultiplicity N : ℝ) : ℂ)‖ ^ 2 *
        realGramQuadratic (productIoc N) G
          (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
          negativeDirichletPhase := by
      convert realGramQuadratic_const_mul
        (productIoc N) G ((maxProductMultiplicity N : ℝ) : ℂ)
        (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
        negativeDirichletPhase using 1
      all_goals norm_cast
    _ = (maxProductMultiplicity N : ℝ) ^ 2 *
        realGramQuadratic (productIoc N) G
          (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
          negativeDirichletPhase := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem productIoc_eq_twoDyadic (N : ℝ) :
    productIoc N = realDyadicIoc (N ^ 2) ∪ realDyadicIoc (2 * N ^ 2) := by
  ext n
  rw [mem_productIoc_iff, Finset.mem_union,
    mem_realDyadicIoc_iff, mem_realDyadicIoc_iff]
  constructor
  · intro hn
    by_cases hmid : (n : ℝ) ≤ 2 * N ^ 2
    · exact Or.inl ⟨hn.1, hmid⟩
    · exact Or.inr ⟨lt_of_not_ge hmid, by nlinarith [hn.2]⟩
  · rintro (hn | hn)
    · constructor <;> nlinarith
    · constructor <;> nlinarith

theorem productDyadic_disjoint (N : ℝ) :
    Disjoint (realDyadicIoc (N ^ 2)) (realDyadicIoc (2 * N ^ 2)) := by
  apply Finset.disjoint_left.mpr
  intro n hn₁ hn₂
  rw [mem_realDyadicIoc_iff] at hn₁ hn₂
  linarith

/-- The coefficient-one product interval is bounded directly by the moment
at `4N²`.  This is the missing `J=1` endpoint treatment: it uses no prime
interval and therefore has no illegal `J ≥ 2` premise. -/
theorem productCoefficientOneMoment_le_twelve
    (N : ℝ) (G : Finset ℝ) :
    productCoefficientOneMoment N G ≤
      12 * jutilaSecondMoment (4 * N ^ 2) G := by
  unfold productCoefficientOneMoment
  rw [productIoc_eq_twoDyadic]
  have hsplit :=
    GuthMaynardJutilaReflection2941Corrected.realGramQuadratic_union_two_le
      (realDyadicIoc (N ^ 2)) (realDyadicIoc (2 * N ^ 2))
      (productDyadic_disjoint N) G
      (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
      negativeDirichletPhase
  have hfirstEq := negativeJutilaSecondMoment_eq_jutilaSecondMoment
    (N ^ 2) G
  have hsecondEq := negativeJutilaSecondMoment_eq_jutilaSecondMoment
    (2 * N ^ 2) G
  change realGramQuadratic (realDyadicIoc (N ^ 2)) G
      (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
      negativeDirichletPhase = jutilaSecondMoment (N ^ 2) G at hfirstEq
  change realGramQuadratic (realDyadicIoc (2 * N ^ 2)) G
      (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
      negativeDirichletPhase = jutilaSecondMoment (2 * N ^ 2) G at hsecondEq
  rw [hfirstEq, hsecondEq] at hsplit
  have hfirst := jutilaSecondMoment_div_le (4 * N ^ 2) 4 G (by norm_num)
  have hsecond := jutilaSecondMoment_div_le (4 * N ^ 2) 2 G (by norm_num)
  norm_num only [Nat.cast_ofNat] at hfirst hsecond
  have hfour : (4 * N ^ 2) / (4 : ℝ) = N ^ 2 := by ring
  have htwo : (4 * N ^ 2) / (2 : ℝ) = 2 * N ^ 2 := by ring
  rw [hfour] at hfirst
  rw [htwo] at hsecond
  linarith

/-- Exact prime-free `k=2` powering inequality at the comparison length
`P=4N²`.  This repairs the prime-scale-one endpoint which the transference
version cannot legally reach. -/
theorem jutila_kTwo_powering_at_four_square
    {N : ℝ} (hN : 0 ≤ N) (G : Finset ℝ) :
    jutilaSecondMoment N G ^ 2 ≤
      12 * (G.card : ℝ) ^ 2 *
        (maxProductMultiplicity N : ℝ) ^ 2 *
          jutilaSecondMoment (4 * N ^ 2) G := by
  have hholder := jutilaSecondMoment_sq_le_multiplicityQuadraticForm N hN G
  have hmajor := multiplicityQuadraticForm_le_maxProductMultiplicity hN G
  have hsplit := productCoefficientOneMoment_le_twelve N G
  have hR : 0 ≤ (G.card : ℝ) ^ 2 := sq_nonneg _
  have hA : 0 ≤ (maxProductMultiplicity N : ℝ) ^ 2 := sq_nonneg _
  calc
    jutilaSecondMoment N G ^ 2 ≤
        (G.card : ℝ) ^ 2 * multiplicityQuadraticForm N G := hholder
    _ ≤ (G.card : ℝ) ^ 2 *
        ((maxProductMultiplicity N : ℝ) ^ 2 *
          productCoefficientOneMoment N G) :=
      mul_le_mul_of_nonneg_left hmajor hR
    _ ≤ (G.card : ℝ) ^ 2 *
        ((maxProductMultiplicity N : ℝ) ^ 2 *
          (12 * jutilaSecondMoment (4 * N ^ 2) G)) := by
      gcongr
    _ = 12 * (G.card : ℝ) ^ 2 *
        (maxProductMultiplicity N : ℝ) ^ 2 *
          jutilaSecondMoment (4 * N ^ 2) G := by ring

/-- Premise-free subpower form of the prime-free boundary powering theorem. -/
theorem jutila_kTwo_powering_at_four_square_subpower
    {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℝ) (G : Finset ℝ), 1 ≤ N →
      jutilaSecondMoment N G ^ 2 ≤
        C * (G.card : ℝ) ^ 2 * Real.rpow (4 * N ^ 2) eta *
          jutilaSecondMoment (4 * N ^ 2) G := by
  obtain ⟨Cm, hCm, hm⟩ :=
    maxProductMultiplicity_square_subpolynomial eta heta
  refine ⟨12 * Cm, by positivity, ?_⟩
  intro N G hN
  have hraw := jutila_kTwo_powering_at_four_square
    (N := N) (le_trans (by norm_num) hN) G
  have hmult := hm N hN
  have hR : 0 ≤ (G.card : ℝ) ^ 2 := sq_nonneg _
  have hS : 0 ≤ jutilaSecondMoment (4 * N ^ 2) G := by
    unfold jutilaSecondMoment realGramQuadratic
    positivity
  calc
    jutilaSecondMoment N G ^ 2 ≤
        12 * (G.card : ℝ) ^ 2 *
          (maxProductMultiplicity N : ℝ) ^ 2 *
            jutilaSecondMoment (4 * N ^ 2) G := hraw
    _ ≤ 12 * (G.card : ℝ) ^ 2 *
          (Cm * Real.rpow (4 * N ^ 2) eta) *
            jutilaSecondMoment (4 * N ^ 2) G := by
      gcongr
    _ = (12 * Cm) * (G.card : ℝ) ^ 2 *
          Real.rpow (4 * N ^ 2) eta *
            jutilaSecondMoment (4 * N ^ 2) G := by ring

/-- The bootstrap scalar step with the exact prime-free comparison length
`4M²`.  The only extra input is the already-controlled bound at that explicit
length; the powering inequality itself has no prime-scale side condition. -/
theorem lemma2910_bootstrap_at_four_square_of_exactAFE
    (hAFE : Lemma295ApproximateFunctionalEquationExactM)
    {delta epsilon A eta : ℝ}
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hA : 0 < A) (heta : 0 < eta) :
    ∃ C₁ C₂ Cp T₀ M₀ : ℝ,
      0 < C₁ ∧ 0 < C₂ ∧ 0 < Cp ∧ 2 ≤ T₀ ∧ 2 ≤ M₀ ∧
      ∀ (T N D : ℝ) (G : Finset ℝ),
        T₀ ≤ T → 1 ≤ N →
        N ≤ sourceReflectionNumerator29_40 T epsilon →
        TPowerSeparated G T delta → InOpenClosedZeroT G T →
        let M := reflectedLength29_40 T epsilon N
        M₀ ≤ M →
        jutilaSecondMoment (4 * M ^ 2) G ≤ D →
        jutilaSecondMoment N G ≤
          C₁ * (G.card : ℝ) * N + C₁ * Real.rpow T (-A) +
          (C₁ * C₂ * (Real.log M) ^ (5 : ℕ)) *
            Real.sqrt
              ((Cp * (G.card : ℝ) ^ 2 *
                Real.rpow (4 * M ^ 2) eta) * D) := by
  obtain ⟨C₁, C₂, T₀, M₀, hC₁, hC₂, hT₀, hM₀, hreflect⟩ :=
    jutila_reflection_recurrence_fixedFive_of_exactAFE hAFE
      hdelta hepsilon hA
  obtain ⟨Cp, hCp, hpower⟩ :=
    jutila_kTwo_powering_at_four_square_subpower heta
  refine ⟨C₁, C₂, Cp, T₀, M₀, hC₁, hC₂, hCp, hT₀, hM₀, ?_⟩
  intro T N D G hT hN hNupper hsep hheight
  dsimp only
  intro hM htarget
  let M := reflectedLength29_40 T epsilon N
  have hMone : 1 ≤ M := (by linarith : 1 ≤ M₀).trans hM
  have hr := hreflect T N G hT hN hNupper hsep hheight hM
  have hp := hpower M G hMone
  have hlog : 0 ≤ Real.log M := Real.log_nonneg hMone
  have hB : 0 ≤ C₁ * C₂ * (Real.log M) ^ (5 : ℕ) := by positivity
  have hC : 0 ≤ Cp * (G.card : ℝ) ^ 2 *
      Real.rpow (4 * M ^ 2) eta := by
    exact mul_nonneg (mul_nonneg hCp.le (sq_nonneg _))
      (Real.rpow_nonneg (by positivity) _)
  have hSP : 0 ≤ jutilaSecondMoment (4 * M ^ 2) G := by
    unfold jutilaSecondMoment realGramQuadratic
    positivity
  apply reflection_powering_controlled_target hB hC hSP
    (x := jutilaSecondMoment N G)
    (y := jutilaSecondMoment M G)
    (z := jutilaSecondMoment (4 * M ^ 2) G)
    (a := C₁ * (G.card : ℝ) * N + C₁ * Real.rpow T (-A))
    (b := C₁ * C₂ * (Real.log M) ^ (5 : ℕ))
    (c := Cp * (G.card : ℝ) ^ 2 * Real.rpow (4 * M ^ 2) eta)
    (d := D)
  · simpa [M] using (show jutilaSecondMoment N G ≤
        C₁ * (G.card : ℝ) * N + C₁ * Real.rpow T (-A) +
          C₁ * C₂ * (Real.log (reflectedLength29_40 T epsilon N)) ^ 5 *
            jutilaSecondMoment (reflectedLength29_40 T epsilon N) G from by
        calc
          jutilaSecondMoment N G ≤
              C₁ * (G.card : ℝ) * N +
                C₁ * C₂ * (Real.log (reflectedLength29_40 T epsilon N)) ^ 5 *
                  jutilaSecondMoment (reflectedLength29_40 T epsilon N) G +
                C₁ * Real.rpow T (-A) := hr
          _ = _ := by ring)
  · simpa using hp
  · exact htarget

/-- Concrete direct-feedback middle regime.  This theorem starts only from
the pointwise Lemma-29.5 AFE and then uses the actual corrected recurrence,
the actual `k=2` powering theorem, and the certified multiplicity bound.

The hypothesis `hprimeScale` is the exact legality condition of the corrected
large-scale transference step.  Nonemptiness of its real dyadic prime interval
is discharged here from Bertrand's theorem. -/
theorem lemma2910_direct_middle_of_exactAFE
    (hAFE : Lemma295ApproximateFunctionalEquationExactM)
    {delta epsilon A eta : ℝ}
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hA : 0 < A) (heta : 0 < eta) :
    ∃ C₁ C₂ Cp T₀ M₀ : ℝ,
      0 < C₁ ∧ 0 < C₂ ∧ 0 < Cp ∧ 2 ≤ T₀ ∧ 2 ≤ M₀ ∧
      ∀ (T N : ℝ) (G : Finset ℝ),
        T₀ ≤ T → 1 ≤ N →
        N ≤ sourceReflectionNumerator29_40 T epsilon →
        TPowerSeparated G T delta → InOpenClosedZeroT G T →
        let M := reflectedLength29_40 T epsilon N
        M₀ ≤ M → 2 ≤ kTwoPrimeLower M N →
        jutilaSecondMoment N G ≤
          2 * (C₁ * (G.card : ℝ) * N + C₁ * Real.rpow T (-A)) +
          (C₁ * C₂ * (Real.log M) ^ (5 : ℕ)) ^ 2 *
            (Cp * (G.card : ℝ) ^ 2 * (Real.log N) ^ 3 *
              Real.rpow (4 * M ^ 2) eta) := by
  obtain ⟨C₁, C₂, T₀, M₀, hC₁, hC₂, hT₀, hM₀, hreflect⟩ :=
    jutila_reflection_recurrence_fixedFive_of_exactAFE hAFE
      hdelta hepsilon hA
  obtain ⟨Cp, hCp, hpower⟩ :=
    kTwo_powering_with_subpower_multiplicity heta
  refine ⟨C₁, C₂, Cp, T₀, M₀, hC₁, hC₂, hCp, hT₀, hM₀, ?_⟩
  intro T N G hT hN hNupper hsep hheight
  dsimp only
  intro hM hprimeScale
  let M := reflectedLength29_40 T epsilon N
  have hMdef : M = reflectedLength29_40 T epsilon N := rfl
  have hMone : 1 ≤ M := (by linarith : 1 ≤ M₀).trans hM
  have hNtwo : 2 ≤ N := by
    unfold kTwoPrimeLower at hprimeScale
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hMone
    have hden : 0 < 4 * M ^ 2 := by positivity
    have hmul := (le_div_iff₀ hden).mp hprimeScale
    nlinarith [sq_nonneg (M - 1)]
  have hr := hreflect T N G hT hN hNupper hsep hheight hM
  have hprimeNonempty := kTwoPrimeRange_nonempty_of_two_le hprimeScale
  have hp := hpower M N G hMone hprimeScale hNtwo hprimeNonempty
  have hTnonneg : 0 ≤ T := by linarith
  have hAnonneg :
      0 ≤ C₁ * (G.card : ℝ) * N + C₁ * Real.rpow T (-A) := by
    exact add_nonneg
      (mul_nonneg (mul_nonneg hC₁.le (by positivity))
        (le_trans (by norm_num) hN))
      (mul_nonneg hC₁.le (Real.rpow_nonneg hTnonneg _))
  have hcnonneg :
      0 ≤ Cp * (G.card : ℝ) ^ 2 * (Real.log N) ^ 3 *
          Real.rpow (4 * M ^ 2) eta := by
    have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hCp.le (sq_nonneg _)) (pow_nonneg hlog _))
      (Real.rpow_nonneg (by positivity) _)
  apply quadratic_feedback_le hAnonneg hcnonneg
    (x := jutilaSecondMoment N G)
    (y := jutilaSecondMoment M G)
    (a := C₁ * (G.card : ℝ) * N + C₁ * Real.rpow T (-A))
    (b := C₁ * C₂ * (Real.log M) ^ (5 : ℕ))
    (c := Cp * (G.card : ℝ) ^ 2 * (Real.log N) ^ 3 *
      Real.rpow (4 * M ^ 2) eta)
  · simpa [M] using (show jutilaSecondMoment N G ≤
        C₁ * (G.card : ℝ) * N + C₁ * Real.rpow T (-A) +
          C₁ * C₂ * (Real.log (reflectedLength29_40 T epsilon N)) ^ 5 *
            jutilaSecondMoment (reflectedLength29_40 T epsilon N) G from by
        calc
          jutilaSecondMoment N G ≤
              C₁ * (G.card : ℝ) * N +
                C₁ * C₂ * (Real.log (reflectedLength29_40 T epsilon N)) ^ 5 *
                  jutilaSecondMoment (reflectedLength29_40 T epsilon N) G +
                C₁ * Real.rpow T (-A) := hr
          _ = _ := by ring)
  · simpa using hp

/-- The formerly missing direct collar `1 ≤ N/(4M²) < 2`.  Unlike the
large-prime branch, its powering coefficient has no logarithmic factor:
the primes and product fibers are bounded finite objects. -/
theorem lemma2910_direct_smallScale_collar_of_exactAFE
    (hAFE : Lemma295ApproximateFunctionalEquationExactM)
    {delta epsilon A eta : ℝ}
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hA : 0 < A) (heta : 0 < eta) :
    ∃ C₁ C₂ Cp T₀ M₀ : ℝ,
      0 < C₁ ∧ 0 < C₂ ∧ 0 < Cp ∧ 2 ≤ T₀ ∧ 2 ≤ M₀ ∧
      ∀ (T N : ℝ) (G : Finset ℝ),
        T₀ ≤ T → 1 ≤ N →
        N ≤ sourceReflectionNumerator29_40 T epsilon →
        TPowerSeparated G T delta → InOpenClosedZeroT G T →
        let M := reflectedLength29_40 T epsilon N
        M₀ ≤ M → 1 ≤ kTwoPrimeLower M N →
        kTwoPrimeLower M N < 2 →
        jutilaSecondMoment N G ≤
          2 * (C₁ * (G.card : ℝ) * N + C₁ * Real.rpow T (-A)) +
          (C₁ * C₂ * (Real.log M) ^ (5 : ℕ)) ^ 2 *
            (Cp * (G.card : ℝ) ^ 2 *
              Real.rpow (4 * M ^ 2) eta) := by
  obtain ⟨C₁, C₂, T₀, M₀, hC₁, hC₂, hT₀, hM₀, hreflect⟩ :=
    jutila_reflection_recurrence_fixedFive_of_exactAFE hAFE
      hdelta hepsilon hA
  obtain ⟨Cp, hCp, hpower⟩ := kTwo_powering_smallScale_subpower heta
  refine ⟨C₁, C₂, Cp, T₀, M₀, hC₁, hC₂, hCp, hT₀, hM₀, ?_⟩
  intro T N G hT hN hNupper hsep hheight
  dsimp only
  intro hM hprimeScale hprimeScaleLt
  let M := reflectedLength29_40 T epsilon N
  have hMone : 1 ≤ M := (by linarith : 1 ≤ M₀).trans hM
  have hr := hreflect T N G hT hN hNupper hsep hheight hM
  have hp := hpower M N G hMone hprimeScale hprimeScaleLt
  have hTnonneg : 0 ≤ T := by linarith
  have hAnonneg :
      0 ≤ C₁ * (G.card : ℝ) * N + C₁ * Real.rpow T (-A) := by
    exact add_nonneg
      (mul_nonneg (mul_nonneg hC₁.le (by positivity))
        (le_trans (by norm_num) hN))
      (mul_nonneg hC₁.le (Real.rpow_nonneg hTnonneg _))
  have hcnonneg :
      0 ≤ Cp * (G.card : ℝ) ^ 2 * Real.rpow (4 * M ^ 2) eta := by
    exact mul_nonneg (mul_nonneg hCp.le (sq_nonneg _))
      (Real.rpow_nonneg (by positivity) _)
  apply quadratic_feedback_le hAnonneg hcnonneg
    (x := jutilaSecondMoment N G)
    (y := jutilaSecondMoment M G)
    (a := C₁ * (G.card : ℝ) * N + C₁ * Real.rpow T (-A))
    (b := C₁ * C₂ * (Real.log M) ^ (5 : ℕ))
    (c := Cp * (G.card : ℝ) ^ 2 * Real.rpow (4 * M ^ 2) eta)
  · simpa [M] using (show jutilaSecondMoment N G ≤
        C₁ * (G.card : ℝ) * N + C₁ * Real.rpow T (-A) +
          C₁ * C₂ * (Real.log (reflectedLength29_40 T epsilon N)) ^ 5 *
            jutilaSecondMoment (reflectedLength29_40 T epsilon N) G from by
        calc
          jutilaSecondMoment N G ≤
              C₁ * (G.card : ℝ) * N +
                C₁ * C₂ * (Real.log (reflectedLength29_40 T epsilon N)) ^ 5 *
                  jutilaSecondMoment (reflectedLength29_40 T epsilon N) G +
                C₁ * Real.rpow T (-A) := hr
          _ = _ := by ring)
  · simpa using hp

/-- Unified direct-feedback regime on the full corrected source range
`N/(4M²) ≥ 1`.  The small prime-scale collar and the Bertrand-supported
large range are hidden inside `kTwo_powering_oneScale_subpower`, so this
constructor has no prime-nonemptiness or case-split premise. -/
theorem lemma2910_direct_oneScale_of_exactAFE
    (hAFE : Lemma295ApproximateFunctionalEquationExactM)
    {delta epsilon A eta : ℝ}
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hA : 0 < A) (heta : 0 < eta) :
    ∃ C₁ C₂ Cp T₀ M₀ : ℝ,
      0 < C₁ ∧ 0 < C₂ ∧ 0 < Cp ∧ 2 ≤ T₀ ∧ 2 ≤ M₀ ∧
      ∀ (T N : ℝ) (G : Finset ℝ),
        T₀ ≤ T → 1 ≤ N →
        N ≤ sourceReflectionNumerator29_40 T epsilon →
        TPowerSeparated G T delta → InOpenClosedZeroT G T →
        let M := reflectedLength29_40 T epsilon N
        M₀ ≤ M → 1 ≤ kTwoPrimeLower M N →
        jutilaSecondMoment N G ≤
          2 * (C₁ * (G.card : ℝ) * N + C₁ * Real.rpow T (-A)) +
          (C₁ * C₂ * (Real.log M) ^ (5 : ℕ)) ^ 2 *
            (Cp * (1 + Real.log N) ^ 3 * (G.card : ℝ) ^ 2 *
              Real.rpow (4 * M ^ 2) eta) := by
  obtain ⟨C₁, C₂, T₀, M₀, hC₁, hC₂, hT₀, hM₀, hreflect⟩ :=
    jutila_reflection_recurrence_fixedFive_of_exactAFE hAFE
      hdelta hepsilon hA
  obtain ⟨Cp, hCp, hpower⟩ := kTwo_powering_oneScale_subpower heta
  refine ⟨C₁, C₂, Cp, T₀, M₀, hC₁, hC₂, hCp, hT₀, hM₀, ?_⟩
  intro T N G hT hN hNupper hsep hheight
  dsimp only
  intro hM hprimeScale
  let M := reflectedLength29_40 T epsilon N
  have hMone : 1 ≤ M := (by linarith : 1 ≤ M₀).trans hM
  have hNtwo : 2 ≤ N := by
    unfold kTwoPrimeLower at hprimeScale
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hMone
    have hden : 0 < 4 * M ^ 2 := by positivity
    have hmul := (le_div_iff₀ hden).mp hprimeScale
    nlinarith [sq_nonneg (M - 1)]
  have hr := hreflect T N G hT hN hNupper hsep hheight hM
  have hp := hpower M N G hMone hNtwo hprimeScale
  have hTnonneg : 0 ≤ T := by linarith
  have hAnonneg :
      0 ≤ C₁ * (G.card : ℝ) * N + C₁ * Real.rpow T (-A) := by
    exact add_nonneg
      (mul_nonneg (mul_nonneg hC₁.le (by positivity))
        (le_trans (by norm_num) hN))
      (mul_nonneg hC₁.le (Real.rpow_nonneg hTnonneg _))
  have hcnonneg :
      0 ≤ Cp * (1 + Real.log N) ^ 3 * (G.card : ℝ) ^ 2 *
          Real.rpow (4 * M ^ 2) eta := by
    have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hCp.le (pow_nonneg (by linarith : 0 ≤ 1 + Real.log N) _))
        (sq_nonneg _))
      (Real.rpow_nonneg (by positivity) _)
  apply quadratic_feedback_le hAnonneg hcnonneg
    (x := jutilaSecondMoment N G)
    (y := jutilaSecondMoment M G)
    (a := C₁ * (G.card : ℝ) * N + C₁ * Real.rpow T (-A))
    (b := C₁ * C₂ * (Real.log M) ^ (5 : ℕ))
    (c := Cp * (1 + Real.log N) ^ 3 * (G.card : ℝ) ^ 2 *
      Real.rpow (4 * M ^ 2) eta)
  · simpa [M] using (show jutilaSecondMoment N G ≤
        C₁ * (G.card : ℝ) * N + C₁ * Real.rpow T (-A) +
          C₁ * C₂ * (Real.log (reflectedLength29_40 T epsilon N)) ^ 5 *
            jutilaSecondMoment (reflectedLength29_40 T epsilon N) G from by
        calc
          jutilaSecondMoment N G ≤
              C₁ * (G.card : ℝ) * N +
                C₁ * C₂ * (Real.log (reflectedLength29_40 T epsilon N)) ^ 5 *
                  jutilaSecondMoment (reflectedLength29_40 T epsilon N) G +
                C₁ * Real.rpow T (-A) := hr
          _ = _ := by ring)
  · simpa only [mul_assoc, mul_left_comm, mul_comm] using hp

/-! ## The exact endpoint obstruction in the existing corrected interfaces -/

/-- At equality in the printed cubic threshold `K^3 = 4 A^2`, the prime
scale required by the current corrected `k=2` transference theorem is exactly
one.  Its legality condition is two. -/
theorem printed_cubic_endpoint_has_primeScale_one
    {A K : ℝ} (hK : 0 < K) (hcube : K ^ 3 = 4 * A ^ 2) :
    kTwoPrimeLower (A / K) K = 1 := by
  unfold kTwoPrimeLower
  have hKne : K ≠ 0 := hK.ne'
  have hAsq : 0 < A ^ 2 := by nlinarith [pow_pos hK 3]
  have hAne : A ≠ 0 := by nlinarith
  apply (div_eq_iff (mul_ne_zero (by norm_num)
    (pow_ne_zero 2 (div_ne_zero hAne hKne)))).2
  field_simp [hKne]
  nlinarith

theorem printed_cubic_endpoint_not_legal_for_corrected_kTwo
    {A K : ℝ} (hK : 0 < K) (hcube : K ^ 3 = 4 * A ^ 2) :
    ¬ 2 ≤ kTwoPrimeLower (A / K) K := by
  rw [printed_cubic_endpoint_has_primeScale_one hK hcube]
  norm_num

end

end GuthMaynardLemma2910ConcreteAssembly

#print axioms GuthMaynardLemma2910ConcreteAssembly.kTwo_powering_with_subpower_multiplicity
#print axioms GuthMaynardLemma2910ConcreteAssembly.smallScale_kTwoPrimeReciprocal_inv_le_two
#print axioms GuthMaynardLemma2910ConcreteAssembly.kTwo_powering_smallScale_explicit
#print axioms GuthMaynardLemma2910ConcreteAssembly.kTwo_powering_smallScale_subpower
#print axioms GuthMaynardLemma2910ConcreteAssembly.kTwo_powering_oneScale_subpower
#print axioms GuthMaynardLemma2910ConcreteAssembly.primeRealIcc_self_double_nonempty_of_two_le
#print axioms GuthMaynardLemma2910ConcreteAssembly.multiplicityQuadraticForm_le_maxProductMultiplicity
#print axioms GuthMaynardLemma2910ConcreteAssembly.productCoefficientOneMoment_le_twelve
#print axioms GuthMaynardLemma2910ConcreteAssembly.jutila_kTwo_powering_at_four_square
#print axioms GuthMaynardLemma2910ConcreteAssembly.jutila_kTwo_powering_at_four_square_subpower
#print axioms GuthMaynardLemma2910ConcreteAssembly.lemma2910_bootstrap_at_four_square_of_exactAFE
#print axioms GuthMaynardLemma2910ConcreteAssembly.lemma2910_direct_middle_of_exactAFE
#print axioms GuthMaynardLemma2910ConcreteAssembly.lemma2910_direct_smallScale_collar_of_exactAFE
#print axioms GuthMaynardLemma2910ConcreteAssembly.lemma2910_direct_oneScale_of_exactAFE
#print axioms GuthMaynardLemma2910ConcreteAssembly.printed_cubic_endpoint_has_primeScale_one
