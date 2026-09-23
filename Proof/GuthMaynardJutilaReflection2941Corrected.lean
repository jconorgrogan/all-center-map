import KTwoPrimeFiberBound
import KTwoDyadicPrimeReciprocalFromCertifiedPsi
import GuthMaynardJutilaReflection2941Robust
import Mathlib.NumberTheory.Bertrand

/-!
# Corrected deterministic block behind (29.41)

The printed proof of Vol. 3, Lemma 29.10 cannot apply Lemma 29.7 to its
first block: there `J = 1`, while Lemma 29.7 requires `J >= 2`.  This file
therefore isolates that first block for direct treatment by Lemma 29.8 and
proves the exact transference/majorant theorem for every later block.

For a later block the source length is `X`, the prime interval is `[J,2J]`,
and the collected products lie in the literal interval `(JX,4JX]`.  We keep
the product fibers themselves, split this interval into the two disjoint
open-left blocks `(JX,2JX]` and `(2JX,4JX]`, and only then apply Lemma 29.8.
The resulting one-block logarithmic loss is cubic.  Combining it with the
two coarse outer logarithmic losses displayed on pp. 267--268 gives a
source-faithful fixed exponent five, not the printed exponent three.
-/

namespace GuthMaynardJutilaReflection2941Corrected

open scoped BigOperators ComplexConjugate
open GuthMaynardHeathBrownMajorant
open GuthMaynardJutilaTransference
open GuthMaynardLengthComparison
open GuthMaynardJutilaLemma29NineKTwo

noncomputable section

/-- The exact inverse form of the reciprocal-prime input (29.32).  It is
definitionally the same contract used by the certified prime-arithmetic
module, but is kept local so this deterministic correction has the narrowest
possible import surface. -/
def DyadicPrimeReciprocalInverseLogBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ J : ℝ, 2 ≤ J → (primeRealIcc J (2 * J)).Nonempty →
      (primeReciprocalSum J (2 * J) (1 / 2))⁻¹ ≤
        C * Real.log (4 * J)

/-! ## Literal later-block fibers -/

/-- The exact number of representations `l = p*n` with
`J <= p <= 2J` prime and `X < n <= 2X`. -/
def prefixBlockFiberCard (J X : ℝ) (l : ℕ) : ℕ :=
  (((primeRealIcc J (2 * J)).product (natRealIoc X (2 * X))).filter
    (fun q => q.1 * q.2 = l)).card

/-- The largest literal coefficient fiber on the exact product interval
`JX < l <= 4JX`. -/
def prefixBlockFiberCap (J X : ℝ) : ℕ :=
  (productRealIoc J (2 * J) X (2 * X)).sup
    (prefixBlockFiberCard J X)

/-- The coefficient-one quadratic form on the complete transference product
interval.  It retains the sign convention of Lemma 29.7. -/
def prefixBlockFullMoment (J X : ℝ) (G : Finset ℝ) : ℝ :=
  realGramQuadratic (productRealIoc J (2 * J) X (2 * X)) G
    (fun l => (Real.rpow (l : ℝ) (-(1 / 2 : ℝ)) : ℂ))
    negativeDirichletPhase

theorem sourceQuadratic_one_dyadic_eq_jutilaSecondMoment
    (X : ℝ) (G : Finset ℝ) :
    sourceQuadratic (fun _ => (1 : ℂ)) X (2 * X) (1 / 2) G =
      jutilaSecondMoment X G := by
  unfold sourceQuadratic sigmaCoefficient
  simp only [one_mul]
  change negativeJutilaSecondMoment X G = jutilaSecondMoment X G
  exact negativeJutilaSecondMoment_eq_jutilaSecondMoment X G

theorem collectedAbsoluteCoefficient_one_eq_prefixBlockFiberCard
    (J X : ℝ) (l : ℕ) :
    collectedAbsoluteCoefficient (fun _ => (1 : ℂ))
        J (2 * J) X (2 * X) l =
      (prefixBlockFiberCard J X l : ℝ) := by
  unfold collectedAbsoluteCoefficient prefixBlockFiberCard
  simp

theorem prefixBlockFiberCard_le_cap
    {J X : ℝ} {l : ℕ}
    (hl : l ∈ productRealIoc J (2 * J) X (2 * X)) :
    prefixBlockFiberCard J X l ≤ prefixBlockFiberCap J X := by
  unfold prefixBlockFiberCap
  exact Finset.le_sup (f := prefixBlockFiberCard J X) hl

/-- Exact coefficient-fiber majorization of the Lemma-29.7 target. -/
theorem targetQuadratic_one_le_prefixBlockFiberCap
    (J X : ℝ) (G : Finset ℝ) :
    targetQuadratic (fun _ => (1 : ℂ)) J (2 * J) X (2 * X)
        (1 / 2) G ≤
      (prefixBlockFiberCap J X : ℝ) ^ 2 *
        prefixBlockFullMoment J X G := by
  let B : ℝ := (prefixBlockFiberCap J X : ℝ)
  have hB : 0 ≤ B := by positivity
  have hmajor := gram_majorant_principle
    (productRealIoc J (2 * J) X (2 * X)) G
    (fun l => ((collectedAbsoluteCoefficient (fun _ => (1 : ℂ))
        J (2 * J) X (2 * X) l *
          Real.rpow (l : ℝ) (-(1 / 2 : ℝ)) : ℝ) : ℂ))
    (fun l => B * Real.rpow (l : ℝ) (-(1 / 2 : ℝ)))
    negativeDirichletPhase
    (fun l hl => by
      simp only [Complex.norm_real, Real.norm_eq_abs]
      have hfiber : collectedAbsoluteCoefficient (fun _ => (1 : ℂ))
          J (2 * J) X (2 * X) l ≤ B := by
        rw [collectedAbsoluteCoefficient_one_eq_prefixBlockFiberCard]
        change (prefixBlockFiberCard J X l : ℝ) ≤
          (prefixBlockFiberCap J X : ℝ)
        exact_mod_cast prefixBlockFiberCard_le_cap hl
      have hpow := Real.rpow_nonneg (Nat.cast_nonneg l) (-(1 / 2 : ℝ))
      have hAnonneg : 0 ≤ collectedAbsoluteCoefficient (fun _ => (1 : ℂ))
          J (2 * J) X (2 * X) l := by
        unfold collectedAbsoluteCoefficient
        positivity
      have habs :
          |collectedAbsoluteCoefficient (fun _ => (1 : ℂ))
              J (2 * J) X (2 * X) l *
            Real.rpow (l : ℝ) (-(1 / 2 : ℝ))| =
          collectedAbsoluteCoefficient (fun _ => (1 : ℂ))
              J (2 * J) X (2 * X) l *
            Real.rpow (l : ℝ) (-(1 / 2 : ℝ)) :=
        abs_of_nonneg (mul_nonneg hAnonneg hpow)
      have hmul := mul_le_mul_of_nonneg_right hfiber hpow
      rw [habs]
      exact hmul)
  unfold targetQuadratic prefixBlockFullMoment
  calc
    realGramQuadratic (productRealIoc J (2 * J) X (2 * X)) G
        (fun l => ((collectedAbsoluteCoefficient (fun _ => (1 : ℂ))
          J (2 * J) X (2 * X) l *
            Real.rpow (l : ℝ) (-(1 / 2 : ℝ)) : ℝ) : ℂ))
        negativeDirichletPhase ≤
      realGramQuadratic (productRealIoc J (2 * J) X (2 * X)) G
        (fun l => ((B * Real.rpow (l : ℝ) (-(1 / 2 : ℝ)) : ℝ) : ℂ))
        negativeDirichletPhase := hmajor
    _ = ‖(B : ℂ)‖ ^ 2 *
        realGramQuadratic (productRealIoc J (2 * J) X (2 * X)) G
          (fun l => (Real.rpow (l : ℝ) (-(1 / 2 : ℝ)) : ℂ))
          negativeDirichletPhase := by
      convert realGramQuadratic_const_mul
        (productRealIoc J (2 * J) X (2 * X)) G (B : ℂ)
        (fun l => (Real.rpow (l : ℝ) (-(1 / 2 : ℝ)) : ℂ))
        negativeDirichletPhase using 1
      all_goals norm_cast
    _ = B ^ 2 *
        realGramQuadratic (productRealIoc J (2 * J) X (2 * X)) G
          (fun l => (Real.rpow (l : ℝ) (-(1 / 2 : ℝ)) : ℂ))
          negativeDirichletPhase := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB]
    _ = _ := by rfl

/-! ## Exact two-block product interval -/

theorem prefixBlockProductRange_eq_twoDyadic
    {J X : ℝ} (hJ : 0 ≤ J) (hX : 0 ≤ X) :
    productRealIoc J (2 * J) X (2 * X) =
      realDyadicIoc (J * X) ∪ realDyadicIoc (2 * J * X) := by
  ext l
  simp only [productRealIoc,
    mem_natRealIoc_iff (by positivity : 0 ≤ (2 * J) * (2 * X)),
    Finset.mem_union, mem_realDyadicIoc_iff]
  constructor
  · intro hl
    by_cases hm : (l : ℝ) ≤ 2 * J * X
    · exact Or.inl ⟨hl.1, by nlinarith⟩
    · exact Or.inr ⟨lt_of_not_ge hm, by nlinarith [hl.2]⟩
  · rintro (hl | hl)
    · constructor <;> nlinarith
    · constructor <;> nlinarith

theorem prefixBlockDyadic_disjoint (J X : ℝ) :
    Disjoint (realDyadicIoc (J * X))
      (realDyadicIoc (2 * J * X)) := by
  apply Finset.disjoint_left.mpr
  intro l hl₁ hl₂
  rw [mem_realDyadicIoc_iff] at hl₁ hl₂
  linarith

theorem norm_sq_add_le_two (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hnorm := norm_add_le x y
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have hxy : 0 ≤ ‖x‖ + ‖y‖ := add_nonneg hx hy
  have hsquare : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hxy).2 hnorm
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

theorem realGramQuadratic_union_two_le
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (A B : Finset ι) (hAB : Disjoint A B)
    (W : Finset κ) (a : ι → ℂ) (z : ι → κ → ℂ) :
    realGramQuadratic (A ∪ B) W a z ≤
      2 * (realGramQuadratic A W a z +
        realGramQuadratic B W a z) := by
  unfold realGramQuadratic
  calc
    (∑ t ∈ W, ∑ u ∈ W,
        ‖gramPolynomial (A ∪ B) a z t u‖ ^ 2) ≤
      ∑ t ∈ W, ∑ u ∈ W,
        2 * (‖gramPolynomial A a z t u‖ ^ 2 +
          ‖gramPolynomial B a z t u‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro u hu
      rw [gramPolynomial_union A B hAB]
      exact norm_sq_add_le_two _ _
    _ = _ := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The exact product-fiber majorant is supported on two open-left dyadic
blocks.  No endpoint atom is introduced. -/
theorem prefixBlockFullMoment_le_twoDyadic
    {J X : ℝ} (hJ : 0 ≤ J) (hX : 0 ≤ X) (G : Finset ℝ) :
    prefixBlockFullMoment J X G ≤
      2 * (jutilaSecondMoment (J * X) G +
        jutilaSecondMoment (2 * J * X) G) := by
  unfold prefixBlockFullMoment
  rw [prefixBlockProductRange_eq_twoDyadic hJ hX]
  have hsplit := realGramQuadratic_union_two_le
    (realDyadicIoc (J * X)) (realDyadicIoc (2 * J * X))
    (prefixBlockDyadic_disjoint J X) G
    (fun l => (Real.rpow (l : ℝ) (-(1 / 2 : ℝ)) : ℂ))
    negativeDirichletPhase
  have hA : realGramQuadratic (realDyadicIoc (J * X)) G
      (fun l => (Real.rpow (l : ℝ) (-(1 / 2 : ℝ)) : ℂ))
      negativeDirichletPhase = jutilaSecondMoment (J * X) G :=
    negativeJutilaSecondMoment_eq_jutilaSecondMoment (J * X) G
  have hB : realGramQuadratic (realDyadicIoc (2 * J * X)) G
      (fun l => (Real.rpow (l : ℝ) (-(1 / 2 : ℝ)) : ℂ))
      negativeDirichletPhase = jutilaSecondMoment (2 * J * X) G :=
    negativeJutilaSecondMoment_eq_jutilaSecondMoment (2 * J * X) G
  rw [hA, hB] at hsplit
  exact hsplit

theorem prefixBlockFullMoment_le_six
    {J X : ℝ} (hJ : 0 ≤ J) (hX : 0 ≤ X) (G : Finset ℝ) :
    prefixBlockFullMoment J X G ≤
      6 * jutilaSecondMoment (2 * J * X) G := by
  have hsplit := prefixBlockFullMoment_le_twoDyadic hJ hX G
  have hlength := jutilaSecondMoment_div_le
    (2 * J * X) 2 G (by norm_num)
  norm_num only [Nat.cast_ofNat] at hlength
  have hrewrite : (2 * J * X) / (2 : ℝ) = J * X := by ring
  rw [hrewrite] at hlength
  nlinarith

/-! ## Exact and logarithmic one-block transference -/

/-- The source-exact normalized theorem for every legal later block.  Its
left support is `(X,2X]`, its prime range is `[J,2J]`, and its two target
blocks are `(JX,2JX]` and `(2JX,4JX]`. -/
theorem jutila_later_block_transference_normalized
    {J X : ℝ} (hJ : 2 ≤ J) (hX : 0 < X) (G : Finset ℝ)
    (hprime : (primeRealIcc J (2 * J)).Nonempty) :
    jutilaSecondMoment X G ≤
      6 * (prefixBlockFiberCap J X : ℝ) ^ 2 *
        (primeReciprocalSum J (2 * J) (1 / 2))⁻¹ *
          jutilaSecondMoment (2 * J * X) G := by
  have htrans := jutila_transference hJ (by linarith : J ≤ 2 * J)
    hX.le (by linarith : X < 2 * X)
    (fun _ => (1 : ℂ)) (1 / 2) G hprime
  rw [sourceQuadratic_one_dyadic_eq_jutilaSecondMoment] at htrans
  have hcap := targetQuadratic_one_le_prefixBlockFiberCap J X G
  have hblocks := prefixBlockFullMoment_le_six
    (le_trans (by norm_num) hJ) hX.le G
  have hinv : 0 ≤ (primeReciprocalSum J (2 * J) (1 / 2))⁻¹ :=
    inv_nonneg.mpr (Finset.sum_nonneg
      (fun p hp => Real.rpow_nonneg (Nat.cast_nonneg p) _))
  have hcapSq : 0 ≤ (prefixBlockFiberCap J X : ℝ) ^ 2 := sq_nonneg _
  calc
    jutilaSecondMoment X G ≤
        (primeReciprocalSum J (2 * J) (1 / 2))⁻¹ *
          targetQuadratic (fun _ => (1 : ℂ)) J (2 * J) X (2 * X)
            (1 / 2) G := htrans
    _ ≤ (primeReciprocalSum J (2 * J) (1 / 2))⁻¹ *
        ((prefixBlockFiberCap J X : ℝ) ^ 2 *
          prefixBlockFullMoment J X G) := by gcongr
    _ ≤ (primeReciprocalSum J (2 * J) (1 / 2))⁻¹ *
        ((prefixBlockFiberCap J X : ℝ) ^ 2 *
          (6 * jutilaSecondMoment (2 * J * X) G)) := by gcongr
    _ = _ := by ring

/-! ## Elementary logarithmic conversion for the literal fibers -/

theorem prefixBlockFiberCard_le_primeFactors_card
    {J X : ℝ} {l : ℕ} (hl : 0 < l) :
    prefixBlockFiberCard J X l ≤ l.primeFactors.card := by
  unfold prefixBlockFiberCard
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqmem :
        q.1 ∈ primeRealIcc J (2 * J) ∧
          q.2 ∈ natRealIoc X (2 * X) := by
      simpa using hq'.1
    have hp : Nat.Prime q.1 := by
      unfold primeRealIcc at hqmem
      exact (Finset.mem_filter.mp hqmem.1).2.2.2
    exact hp.mem_primeFactors ⟨q.2, hq'.2.symm⟩ hl.ne'
  · intro a ha b hb hab
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    apply Prod.ext hab
    have hmul : a.1 * a.2 = a.1 * b.2 := by
      calc
        a.1 * a.2 = l := ha'.2
        _ = b.1 * b.2 := hb'.2.symm
        _ = a.1 * b.2 := by rw [hab]
    have haMem : a.1 ∈ primeRealIcc J (2 * J) := by
      exact (Finset.mem_product.mp ha'.1).1
    have haPrime : Nat.Prime a.1 := by
      unfold primeRealIcc at haMem
      exact (Finset.mem_filter.mp haMem).2.2.2
    exact Nat.mul_left_cancel haPrime.pos hmul

theorem prefixBlockFiberCard_cast_le_log
    {J X : ℝ} {l : ℕ} (hl : 0 < l) :
    (prefixBlockFiberCard J X l : ℝ) ≤
      Real.log (l : ℝ) / Real.log 2 := by
  have hcard := prefixBlockFiberCard_le_primeFactors_card
    (J := J) (X := X) hl
  have hpow : 2 ^ prefixBlockFiberCard J X l ≤ l :=
    (Nat.pow_le_pow_right (by norm_num) hcard).trans
      (two_pow_primeFactors_card_le hl)
  have hpowReal :
      (2 : ℝ) ^ prefixBlockFiberCard J X l ≤ (l : ℝ) := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) <
    (2 : ℝ) ^ prefixBlockFiberCard J X l) hpowReal
  rw [Real.log_pow] at hlog
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (le_div_iff₀ hlogTwo).2 (by simpa [mul_comm] using hlog)

theorem prefixBlockProductRange_cast_pos_and_le
    {J X : ℝ} (hJ : 0 < J) (hX : 0 < X)
    {l : ℕ} (hl : l ∈ productRealIoc J (2 * J) X (2 * X)) :
    0 < (l : ℝ) ∧ (l : ℝ) ≤ 2 * (2 * J * X) := by
  have hl' : J * X < (l : ℝ) ∧
      (l : ℝ) ≤ (2 * J) * (2 * X) := by
    unfold productRealIoc at hl
    exact (mem_natRealIoc_iff (by positivity)).mp hl
  constructor
  · exact (mul_pos hJ hX).trans hl'.1
  · nlinarith [hl'.2]

/-- The exact fiber cap costs one logarithm at the reference length
`P = 2JX`.  The deliberately coarse constant is source-safe and uniform in
the block index. -/
theorem prefixBlockFiberCap_cast_le_log
    {J X : ℝ} (hJ : 0 < J) (hX : 0 < X)
    (hP : 2 ≤ 2 * J * X) :
    (prefixBlockFiberCap J X : ℝ) ≤
      3 * Real.log (2 * J * X) / Real.log 2 := by
  let P : ℝ := 2 * J * X
  let x : ℝ := Real.log (2 * P) / Real.log 2
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwoP : 1 < 2 * P := by dsimp [P]; linarith
  have hx : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (Real.log_nonneg htwoP.le) hlogTwo.le
  have hsupNat : prefixBlockFiberCap J X ≤ Nat.ceil x := by
    unfold prefixBlockFiberCap
    apply Finset.sup_le
    intro l hl
    have hlbounds := prefixBlockProductRange_cast_pos_and_le hJ hX hl
    have hlpos : 0 < l := by exact_mod_cast hlbounds.1
    have hcard := prefixBlockFiberCard_cast_le_log
      (J := J) (X := X) hlpos
    have hlogmono : Real.log (l : ℝ) ≤ Real.log (2 * P) :=
      Real.log_le_log hlbounds.1 (by simpa [P] using hlbounds.2)
    have hcardx : (prefixBlockFiberCard J X l : ℝ) ≤ x := by
      dsimp [x]
      exact hcard.trans (div_le_div_of_nonneg_right hlogmono hlogTwo.le)
    exact (Nat.cast_le (α := ℝ)).mp (hcardx.trans (Nat.le_ceil x))
  have hcapx : (prefixBlockFiberCap J X : ℝ) < x + 1 := by
    exact (Nat.cast_le.mpr hsupNat).trans_lt (Nat.ceil_lt_add_one hx)
  have hPpos : 0 < P := by dsimp [P]; positivity
  have hlogP : Real.log 2 ≤ Real.log P := by
    apply Real.log_le_log (by norm_num)
    simpa [P] using hP
  have hlogMul : Real.log (2 * P) = Real.log 2 + Real.log P := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hPpos.ne']
  have htarget : x + 1 ≤ 3 * Real.log P / Real.log 2 := by
    dsimp [x]
    rw [hlogMul]
    have hlogTwoNe : Real.log 2 ≠ 0 := hlogTwo.ne'
    field_simp [hlogTwoNe]
    nlinarith
  simpa only [P] using hcapx.le.trans htarget

theorem jutilaSecondMoment_nonneg (X : ℝ) (G : Finset ℝ) :
    0 ≤ jutilaSecondMoment X G := by
  unfold jutilaSecondMoment realGramQuadratic
  positivity

/-- A data-bearing corrected replacement for an opaque proposition at the
one-block level.  The field `K` records the certified logarithmic exponent. -/
structure LaterBlockTransference29_41LogK where
  K : ℕ
  C : ℝ
  C_pos : 0 < C
  bound : ∀ (J X : ℝ) (G : Finset ℝ),
    2 ≤ J → 1 / 2 ≤ X →
      (primeRealIcc J (2 * J)).Nonempty →
      jutilaSecondMoment X G ≤
        C * (Real.log (2 * J * X)) ^ K *
          jutilaSecondMoment (2 * J * X) G

/-- The complete source-faithful later-block result.  Lemma 29.7, the
literal coefficient fibers, (29.32), the exact two-block split, and Lemma
29.8 certify `K = 3`. -/
noncomputable def laterBlockTransference29_41LogThree
    (hprimeReciprocal : DyadicPrimeReciprocalInverseLogBound) :
    LaterBlockTransference29_41LogK := by
  let C₀ : ℝ := Classical.choose hprimeReciprocal
  have hC₀ : 0 < C₀ := (Classical.choose_spec hprimeReciprocal).1
  have hreciprocal : ∀ J : ℝ, 2 ≤ J →
      (primeRealIcc J (2 * J)).Nonempty →
      (primeReciprocalSum J (2 * J) (1 / 2))⁻¹ ≤
        C₀ * Real.log (4 * J) :=
    (Classical.choose_spec hprimeReciprocal).2
  let D : ℝ := 3 / Real.log 2
  let C : ℝ := 18 * C₀ * D ^ 2
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨3, C, hC, ?_⟩
  intro J X G hJ hX hprime
  have hJpos : 0 < J := lt_of_lt_of_le (by norm_num) hJ
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  let P : ℝ := 2 * J * X
  have hP : 2 ≤ P := by dsimp [P]; nlinarith
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hJleP : J ≤ P := by dsimp [P]; nlinarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlogJleP : Real.log J ≤ Real.log P :=
    Real.log_le_log hJpos hJleP
  have hlogTwoLeP : Real.log 2 ≤ Real.log P :=
    Real.log_le_log (by norm_num) hP
  have hlogFour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hlogFourJ : Real.log (4 * J) = Real.log 4 + Real.log J := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hJpos.ne']
  have hlogFourJLe : Real.log (4 * J) ≤ 3 * Real.log P := by
    rw [hlogFourJ, hlogFour]
    nlinarith
  have hcap0 := prefixBlockFiberCap_cast_le_log hJpos hXpos
    (by simpa only [P] using hP)
  have hcap : (prefixBlockFiberCap J X : ℝ) ≤ D * Real.log P := by
    dsimp [D, P] at hcap0 ⊢
    convert hcap0 using 1
    all_goals ring
  have hcapSq : (prefixBlockFiberCap J X : ℝ) ^ 2 ≤
      (D * Real.log P) ^ 2 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcap 2
  have hinv0 := hreciprocal J hJ hprime
  have hinv : (primeReciprocalSum J (2 * J) (1 / 2))⁻¹ ≤
      3 * C₀ * Real.log P := by
    calc
      (primeReciprocalSum J (2 * J) (1 / 2))⁻¹ ≤
          C₀ * Real.log (4 * J) := hinv0
      _ ≤ C₀ * (3 * Real.log P) :=
        mul_le_mul_of_nonneg_left hlogFourJLe hC₀.le
      _ = 3 * C₀ * Real.log P := by ring
  have hnormalized := jutila_later_block_transference_normalized
    hJ hXpos G hprime
  have hinvNonneg : 0 ≤
      (primeReciprocalSum J (2 * J) (1 / 2))⁻¹ :=
    inv_nonneg.mpr (Finset.sum_nonneg
      (fun p hp => Real.rpow_nonneg (Nat.cast_nonneg p) _))
  have hmoment := jutilaSecondMoment_nonneg P G
  calc
    jutilaSecondMoment X G ≤
        6 * (prefixBlockFiberCap J X : ℝ) ^ 2 *
          (primeReciprocalSum J (2 * J) (1 / 2))⁻¹ *
            jutilaSecondMoment P G := by simpa only [P] using hnormalized
    _ ≤ 6 * (D * Real.log P) ^ 2 *
          (3 * C₀ * Real.log P) * jutilaSecondMoment P G := by
      gcongr
    _ = C * (Real.log P) ^ (3 : ℕ) *
          jutilaSecondMoment P G := by
      dsimp [C]
      ring
    _ = C * (Real.log (2 * J * X)) ^ (3 : ℕ) *
          jutilaSecondMoment (2 * J * X) G := by rfl

@[simp]
theorem laterBlockTransference29_41LogThree_K
    (hprimeReciprocal : DyadicPrimeReciprocalInverseLogBound) :
    (laterBlockTransference29_41LogThree hprimeReciprocal).K = 3 := by
  rfl

/-! ## Literal source powers for `j >= 2` -/

def prefixPrimeScale29_41 (j : ℕ) : ℝ :=
  ((2 ^ (j - 1) : ℕ) : ℝ)

def prefixBlockLength29_41 (M : ℝ) (j : ℕ) : ℝ :=
  M / (2 : ℝ) ^ j

theorem prefixPrimeRange29_41_nonempty
    (j : ℕ) :
    (primeRealIcc (prefixPrimeScale29_41 j)
      (2 * prefixPrimeScale29_41 j)).Nonempty := by
  let n : ℕ := 2 ^ (j - 1)
  have hn : n ≠ 0 := by dsimp [n]; positivity
  obtain ⟨p, hp, hnp, hpupper⟩ := Nat.bertrand n hn
  refine ⟨p, ?_⟩
  rw [mem_primeRealIcc_iff (by
    unfold prefixPrimeScale29_41
    positivity : 0 ≤ 2 * prefixPrimeScale29_41 j)]
  constructor
  · unfold prefixPrimeScale29_41
    exact_mod_cast hnp.le
  · constructor
    · unfold prefixPrimeScale29_41
      exact_mod_cast hpupper
    · exact hp

theorem prefixPrimeScale29_41_ge_two
    {j : ℕ} (hj : 2 ≤ j) :
    2 ≤ prefixPrimeScale29_41 j := by
  unfold prefixPrimeScale29_41
  have hpow : 2 ^ (1 : ℕ) ≤ 2 ^ (j - 1) := by
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact_mod_cast hpow

theorem prefixBlock_reference_length
    {M : ℝ} {j : ℕ} (hj : 1 ≤ j) :
    2 * prefixPrimeScale29_41 j * prefixBlockLength29_41 M j = M := by
  have hjEq : j - 1 + 1 = j := Nat.sub_add_cancel hj
  have hpow : (2 : ℝ) ^ j = 2 * (2 : ℝ) ^ (j - 1) := by
    calc
      (2 : ℝ) ^ j = (2 : ℝ) ^ (j - 1 + 1) := by rw [hjEq]
      _ = 2 * (2 : ℝ) ^ (j - 1) := by rw [pow_succ]; ring
  unfold prefixPrimeScale29_41 prefixBlockLength29_41
  norm_cast at hpow ⊢
  rw [hpow]
  field_simp

/-- The exact printed specialization of the certified later-block theorem:
`J = 2^(j-1)`, `J' = 2^j`,
`X = M/2^j`, `X' = M/2^(j-1)`, and reference length `M`.
The premise `1/2 <= X` is exactly the range in which this dyadic block can
contain a positive integer. -/
theorem jutila_dyadic_power_later_block_log_three
    (hprimeReciprocal : DyadicPrimeReciprocalInverseLogBound)
    {M : ℝ} {j : ℕ} (hj : 2 ≤ j)
    (hX : 1 / 2 ≤ prefixBlockLength29_41 M j)
    (G : Finset ℝ) :
    jutilaSecondMoment (prefixBlockLength29_41 M j) G ≤
      (laterBlockTransference29_41LogThree hprimeReciprocal).C *
        (Real.log M) ^ 3 * jutilaSecondMoment M G := by
  have hbound :=
    (laterBlockTransference29_41LogThree hprimeReciprocal).bound
      (prefixPrimeScale29_41 j) (prefixBlockLength29_41 M j) G
      (prefixPrimeScale29_41_ge_two hj) hX
      (prefixPrimeRange29_41_nonempty j)
  have href := prefixBlock_reference_length (M := M) (j := j)
    (by omega : 1 ≤ j)
  simpa only [laterBlockTransference29_41LogThree_K, href] using hbound

/-- The illegal first printed block is handled directly by Lemma 29.8. -/
theorem jutila_first_block_direct (M : ℝ) (G : Finset ℝ) :
    jutilaSecondMoment (M / 2) G ≤ 2 * jutilaSecondMoment M G := by
  exact jutilaSecondMoment_div_le M 2 G (by norm_num)

/-! ## The one remaining finite partition inequality -/

/-- The exact reflected prefix, repeated here so this correction module does
not depend on the old exponent-three proposition. -/
def jutilaReflectedPrefixMoment (M : ℝ) (G : Finset ℝ) : ℝ :=
  sourceQuadratic (fun _ => (1 : ℂ)) 0 M (1 / 2) G

def prefixPolynomial29_41 (M g₁ g₂ : ℝ) : ℂ :=
  gramPolynomial (natRealIoc 0 M)
    (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
    negativeDirichletPhase g₁ g₂

def prefixDyadicBlockPolynomial29_41
    (M : ℝ) (i : ℕ) (g₁ g₂ : ℝ) : ℂ :=
  gramPolynomial
    (natRealIoc (M / (2 : ℝ) ^ (i + 1)) (M / (2 : ℝ) ^ i))
    (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
    negativeDirichletPhase g₁ g₂

def prefixDyadicCount29_41 (M : ℝ) : ℕ :=
  Nat.ceil (Real.log M / Real.log 2) + 1

theorem natRealIoc_zero_split_half
    {Y : ℝ} (hY : 0 ≤ Y) :
    natRealIoc 0 Y =
      natRealIoc 0 (Y / 2) ∪ natRealIoc (Y / 2) Y := by
  ext n
  simp only [mem_natRealIoc_iff hY,
    mem_natRealIoc_iff (by positivity : 0 ≤ Y / 2),
    Finset.mem_union]
  constructor
  · intro hn
    by_cases hhalf : (n : ℝ) ≤ Y / 2
    · exact Or.inl ⟨hn.1, hhalf⟩
    · exact Or.inr ⟨lt_of_not_ge hhalf, hn.2⟩
  · rintro (hn | hn)
    · exact ⟨hn.1, hn.2.trans (by linarith)⟩
    · exact ⟨(by linarith [hn.1]), hn.2⟩

theorem natRealIoc_zero_half_disjoint (Y : ℝ) :
    Disjoint (natRealIoc 0 (Y / 2)) (natRealIoc (Y / 2) Y) := by
  apply Finset.disjoint_left.mpr
  intro n hn₁ hn₂
  have hn₁' := (Finset.mem_filter.mp hn₁).2
  have hn₂' := (Finset.mem_filter.mp hn₂).2
  linarith

theorem prefixPolynomial29_41_split_half
    {Y : ℝ} (hY : 0 ≤ Y) (g₁ g₂ : ℝ) :
    prefixPolynomial29_41 Y g₁ g₂ =
      prefixPolynomial29_41 (Y / 2) g₁ g₂ +
        gramPolynomial (natRealIoc (Y / 2) Y)
          (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
          negativeDirichletPhase g₁ g₂ := by
  unfold prefixPolynomial29_41
  rw [natRealIoc_zero_split_half hY,
    gramPolynomial_union _ _ (natRealIoc_zero_half_disjoint Y)]

theorem prefixPolynomial29_41_split_at
    {M : ℝ} (hM : 0 ≤ M) (i : ℕ) (g₁ g₂ : ℝ) :
    prefixPolynomial29_41 (M / (2 : ℝ) ^ i) g₁ g₂ =
      prefixPolynomial29_41 (M / (2 : ℝ) ^ (i + 1)) g₁ g₂ +
        prefixDyadicBlockPolynomial29_41 M i g₁ g₂ := by
  have hY : 0 ≤ M / (2 : ℝ) ^ i := by positivity
  have hsplit := prefixPolynomial29_41_split_half hY g₁ g₂
  have hscale : M / (2 : ℝ) ^ i / 2 =
      M / (2 : ℝ) ^ (i + 1) := by
    rw [pow_succ]
    ring
  rw [hscale] at hsplit
  simpa only [prefixDyadicBlockPolynomial29_41] using hsplit

theorem prefixPolynomial29_41_eq_terminal_add_sum
    {M : ℝ} (hM : 0 ≤ M) (Q : ℕ) (g₁ g₂ : ℝ) :
    prefixPolynomial29_41 M g₁ g₂ =
      prefixPolynomial29_41 (M / (2 : ℝ) ^ Q) g₁ g₂ +
        ∑ i ∈ Finset.range Q,
          prefixDyadicBlockPolynomial29_41 M i g₁ g₂ := by
  induction Q with
  | zero => simp
  | succ Q ih =>
      rw [ih, prefixPolynomial29_41_split_at hM Q,
        Finset.sum_range_succ]
      ring

theorem prefixDyadicCount29_41_terminal_lt_one
    {M : ℝ} (hM : 2 ≤ M) :
    M / (2 : ℝ) ^ prefixDyadicCount29_41 M < 1 := by
  let x : ℝ := Real.log M / Real.log 2
  let Q : ℕ := prefixDyadicCount29_41 M
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxceil : x < (Q : ℝ) := by
    have hxle : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
    have hxlt : x < (Nat.ceil x : ℝ) + 1 := by linarith
    simpa only [Q, prefixDyadicCount29_41, x, Nat.cast_add,
      Nat.cast_one] using hxlt
  have hloglt : Real.log M < (Q : ℝ) * Real.log 2 := by
    have hmul := mul_lt_mul_of_pos_right hxceil hlogTwo
    dsimp [x] at hmul
    field_simp [hlogTwo.ne'] at hmul
    simpa [mul_comm] using hmul
  have hpow : M < (2 : ℝ) ^ Q := by
    have hexp := (Real.exp_lt_exp).2 hloglt
    rw [Real.exp_log (by linarith : 0 < M), Real.exp_nat_mul] at hexp
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
    simpa using hexp
  have hpowPos : 0 < (2 : ℝ) ^ Q := by positivity
  exact (div_lt_one hpowPos).2 hpow

theorem natRealIoc_zero_eq_empty_of_lt_one
    {Y : ℝ} (hY : Y < 1) : natRealIoc 0 Y = ∅ := by
  ext n
  simp only [Finset.notMem_empty, iff_false]
  intro hn
  have hn' := (Finset.mem_filter.mp hn).2
  have hnpos : 0 < n := by exact_mod_cast hn'.1
  have hone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
  linarith

theorem prefixPolynomial29_41_terminal_eq_zero
    {M : ℝ} (hM : 2 ≤ M) (g₁ g₂ : ℝ) :
    prefixPolynomial29_41
      (M / (2 : ℝ) ^ prefixDyadicCount29_41 M) g₁ g₂ = 0 := by
  unfold prefixPolynomial29_41
  rw [natRealIoc_zero_eq_empty_of_lt_one
    (prefixDyadicCount29_41_terminal_lt_one hM)]
  unfold gramPolynomial
  simp

theorem prefixPolynomial29_41_eq_sum
    {M : ℝ} (hM : 2 ≤ M) (g₁ g₂ : ℝ) :
    prefixPolynomial29_41 M g₁ g₂ =
      ∑ i ∈ Finset.range (prefixDyadicCount29_41 M),
        prefixDyadicBlockPolynomial29_41 M i g₁ g₂ := by
  have hiter := prefixPolynomial29_41_eq_terminal_add_sum
    (le_trans (by norm_num) hM)
    (prefixDyadicCount29_41 M) g₁ g₂
  rw [prefixPolynomial29_41_terminal_eq_zero hM] at hiter
  simpa using hiter

theorem norm_prefixPolynomial29_41_sq_le
    {M : ℝ} (hM : 2 ≤ M) (g₁ g₂ : ℝ) :
    ‖prefixPolynomial29_41 M g₁ g₂‖ ^ 2 ≤
      (prefixDyadicCount29_41 M : ℝ) *
        ∑ i ∈ Finset.range (prefixDyadicCount29_41 M),
          ‖prefixDyadicBlockPolynomial29_41 M i g₁ g₂‖ ^ 2 := by
  rw [prefixPolynomial29_41_eq_sum hM]
  have hnorm := norm_sum_le
    (Finset.range (prefixDyadicCount29_41 M))
    (prefixDyadicBlockPolynomial29_41 M · g₁ g₂)
  have hsumNonneg : 0 ≤
      ∑ i ∈ Finset.range (prefixDyadicCount29_41 M),
        ‖prefixDyadicBlockPolynomial29_41 M i g₁ g₂‖ := by positivity
  have hsquare :
      ‖∑ i ∈ Finset.range (prefixDyadicCount29_41 M),
          prefixDyadicBlockPolynomial29_41 M i g₁ g₂‖ ^ 2 ≤
        (∑ i ∈ Finset.range (prefixDyadicCount29_41 M),
          ‖prefixDyadicBlockPolynomial29_41 M i g₁ g₂‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hsumNonneg).2 hnorm
  exact hsquare.trans (by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := Finset.range (prefixDyadicCount29_41 M))
      (f := fun i => ‖prefixDyadicBlockPolynomial29_41 M i g₁ g₂‖)))

theorem prefixDyadicBlockMoment_eq
    (M : ℝ) (i : ℕ) (G : Finset ℝ) :
    (∑ g₁ ∈ G, ∑ g₂ ∈ G,
      ‖prefixDyadicBlockPolynomial29_41 M i g₁ g₂‖ ^ 2) =
      jutilaSecondMoment (M / (2 : ℝ) ^ (i + 1)) G := by
  have hscale : M / (2 : ℝ) ^ i =
      2 * (M / (2 : ℝ) ^ (i + 1)) := by
    rw [pow_succ]
    ring
  unfold prefixDyadicBlockPolynomial29_41
  rw [hscale]
  rw [← sourceQuadratic_one_dyadic_eq_jutilaSecondMoment]
  unfold sourceQuadratic sigmaCoefficient
  simp only [one_mul]
  rfl

/-- The precise finite partition/Cauchy inequality left implicit in the
printed proof.  This is the first of the two outer logarithmic losses. -/
theorem jutilaReflectedPrefixMoment_le_dyadic_sum
    {M : ℝ} (hM : 2 ≤ M) (G : Finset ℝ) :
    jutilaReflectedPrefixMoment M G ≤
      (prefixDyadicCount29_41 M : ℝ) *
        ∑ i ∈ Finset.range (prefixDyadicCount29_41 M),
          jutilaSecondMoment (M / (2 : ℝ) ^ (i + 1)) G := by
  unfold jutilaReflectedPrefixMoment sourceQuadratic realGramQuadratic
    sigmaCoefficient
  simp only [one_mul]
  change (∑ g₁ ∈ G, ∑ g₂ ∈ G,
      ‖prefixPolynomial29_41 M g₁ g₂‖ ^ 2) ≤ _
  calc
    (∑ g₁ ∈ G, ∑ g₂ ∈ G,
        ‖prefixPolynomial29_41 M g₁ g₂‖ ^ 2) ≤
      ∑ g₁ ∈ G, ∑ g₂ ∈ G,
        (prefixDyadicCount29_41 M : ℝ) *
          ∑ i ∈ Finset.range (prefixDyadicCount29_41 M),
            ‖prefixDyadicBlockPolynomial29_41 M i g₁ g₂‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro g₁ hg₁
      apply Finset.sum_le_sum
      intro g₂ hg₂
      exact norm_prefixPolynomial29_41_sq_le hM g₁ g₂
    _ = (prefixDyadicCount29_41 M : ℝ) *
        ∑ i ∈ Finset.range (prefixDyadicCount29_41 M),
          (∑ g₁ ∈ G, ∑ g₂ ∈ G,
            ‖prefixDyadicBlockPolynomial29_41 M i g₁ g₂‖ ^ 2) := by
      simp_rw [Finset.mul_sum]
      calc
        (∑ g₁ ∈ G, ∑ g₂ ∈ G,
            ∑ i ∈ Finset.range (prefixDyadicCount29_41 M),
              (prefixDyadicCount29_41 M : ℝ) *
                ‖prefixDyadicBlockPolynomial29_41 M i g₁ g₂‖ ^ 2) =
          ∑ g₁ ∈ G, ∑ i ∈ Finset.range (prefixDyadicCount29_41 M),
            ∑ g₂ ∈ G, (prefixDyadicCount29_41 M : ℝ) *
              ‖prefixDyadicBlockPolynomial29_41 M i g₁ g₂‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro g₁ hg₁
            rw [Finset.sum_comm]
        _ = ∑ i ∈ Finset.range (prefixDyadicCount29_41 M),
            ∑ g₁ ∈ G, ∑ g₂ ∈ G,
              (prefixDyadicCount29_41 M : ℝ) *
                ‖prefixDyadicBlockPolynomial29_41 M i g₁ g₂‖ ^ 2 := by
            rw [Finset.sum_comm]
    _ = _ := by
      apply congrArg ((prefixDyadicCount29_41 M : ℝ) * ·)
      apply Finset.sum_congr rfl
      intro i hi
      exact prefixDyadicBlockMoment_eq M i G

theorem prefixDyadicCount29_41_cast_le_log
    {M : ℝ} (hM : 2 ≤ M) :
    (prefixDyadicCount29_41 M : ℝ) ≤
      (3 / Real.log 2) * Real.log M := by
  let x : ℝ := Real.log M / Real.log 2
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogMono : Real.log 2 ≤ Real.log M :=
    Real.log_le_log (by norm_num) hM
  have hx : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (Real.log_nonneg (by linarith)) hlogTwo.le
  have hxOne : 1 ≤ x := by
    dsimp [x]
    exact (le_div_iff₀ hlogTwo).2 (by simpa using hlogMono)
  have hceil : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  have hQ : (prefixDyadicCount29_41 M : ℝ) < x + 2 := by
    dsimp [prefixDyadicCount29_41]
    push_cast
    dsimp [x] at hceil ⊢
    linarith
  have hthree : x + 2 ≤ 3 * x := by linarith
  calc
    (prefixDyadicCount29_41 M : ℝ) ≤ 3 * x :=
      (hQ.trans_le hthree).le
    _ = (3 / Real.log 2) * Real.log M := by
      dsimp [x]
      field_simp [hlogTwo.ne']

theorem realDyadicIoc_eq_empty_of_lt_half
    {X : ℝ} (hX : X < 1 / 2) : realDyadicIoc X = ∅ := by
  ext n
  simp only [Finset.notMem_empty, iff_false]
  intro hn
  have hn' := (Finset.mem_filter.mp hn).2
  have hnpos : 0 < n := pos_of_mem_realDyadicIoc hn
  have hone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
  linarith

theorem jutilaSecondMoment_eq_zero_of_lt_half
    {X : ℝ} (hX : X < 1 / 2) (G : Finset ℝ) :
    jutilaSecondMoment X G = 0 := by
  unfold jutilaSecondMoment
  rw [realDyadicIoc_eq_empty_of_lt_half hX]
  unfold realGramQuadratic gramPolynomial
  simp

theorem prefix_dyadic_block_uniform_log_three
    (hprimeReciprocal : DyadicPrimeReciprocalInverseLogBound) :
    ∃ E : ℝ, 0 < E ∧
      ∀ (M : ℝ) (i : ℕ) (G : Finset ℝ), 2 ≤ M →
        jutilaSecondMoment (M / (2 : ℝ) ^ (i + 1)) G ≤
          E * (Real.log M) ^ 3 * jutilaSecondMoment M G := by
  let B := laterBlockTransference29_41LogThree hprimeReciprocal
  let E : ℝ := max B.C (2 / (Real.log 2) ^ 3)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 < B.C := B.C_pos
  have hE : 0 < E := lt_of_lt_of_le hB (le_max_left _ _)
  refine ⟨E, hE, ?_⟩
  intro M i G hM
  let X : ℝ := M / (2 : ℝ) ^ (i + 1)
  by_cases hhalf : 1 / 2 ≤ X
  · by_cases hi : i = 0
    · subst i
      have hfirst := jutila_first_block_direct M G
      norm_num only [pow_one] at hfirst
      have hlogMono : Real.log 2 ≤ Real.log M :=
        Real.log_le_log (by norm_num) hM
      have hpowMono : (Real.log 2) ^ 3 ≤ (Real.log M) ^ 3 :=
        pow_le_pow_left₀ hlogTwo.le hlogMono 3
      have hconst : 2 ≤ E * (Real.log M) ^ 3 := by
        have hEbase : 2 / (Real.log 2) ^ 3 ≤ E := le_max_right _ _
        have hlogPowPos : 0 < (Real.log 2) ^ 3 := by positivity
        calc
          2 = (2 / (Real.log 2) ^ 3) * (Real.log 2) ^ 3 := by
            field_simp [hlogPowPos.ne']
          _ ≤ E * (Real.log M) ^ 3 :=
            mul_le_mul hEbase hpowMono (by positivity) hE.le
      have hmom := jutilaSecondMoment_nonneg M G
      simpa only [Nat.zero_add, pow_one] using
        hfirst.trans (mul_le_mul_of_nonneg_right hconst hmom)
    · have hiPos : 0 < i := Nat.pos_of_ne_zero hi
      have hlater := jutila_dyadic_power_later_block_log_three
        hprimeReciprocal (M := M) (j := i + 1) (by omega)
        (by simpa only [prefixBlockLength29_41, X] using hhalf) G
      have hBC :
          (laterBlockTransference29_41LogThree hprimeReciprocal).C ≤ E := by
        simpa only [B, E] using
          (le_max_left B.C (2 / (Real.log 2) ^ 3))
      have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
      have hfactor : 0 ≤ (Real.log M) ^ 3 * jutilaSecondMoment M G :=
        mul_nonneg (pow_nonneg hlogM _) (jutilaSecondMoment_nonneg M G)
      exact hlater.trans (by
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_right hBC hfactor))
  · have hzero := jutilaSecondMoment_eq_zero_of_lt_half
      (lt_of_not_ge hhalf) G
    rw [show M / (2 : ℝ) ^ (i + 1) = X by rfl, hzero]
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
    exact mul_nonneg
      (mul_nonneg hE.le (pow_nonneg hlogM _))
      (jutilaSecondMoment_nonneg M G)

/-- A data-bearing corrected version of the old opaque prefix proposition.
The certified exponent is a field, so downstream users cannot silently read
the printed but unsupported exponent three into the theorem. -/
structure PrefixDyadicTransference29_41LogK where
  K : ℕ
  C : ℝ
  M₀ : ℝ
  C_pos : 0 < C
  M₀_ge_two : 2 ≤ M₀
  bound : ∀ (M : ℝ) (G : Finset ℝ), M₀ ≤ M →
    jutilaReflectedPrefixMoment M G ≤
      C * (Real.log M) ^ K * jutilaSecondMoment M G

/-- Corrected deterministic prefix transference.  The exact dyadic Cauchy
factor, the number of blocks, and the cubic one-block theorem give the
source-faithful coarse exponent `K = 5`. -/
noncomputable def prefixDyadicTransference29_41LogFive
    (hprimeReciprocal : DyadicPrimeReciprocalInverseLogBound) :
    PrefixDyadicTransference29_41LogK := by
  let E : ℝ := Classical.choose
    (prefix_dyadic_block_uniform_log_three hprimeReciprocal)
  have hEspec := Classical.choose_spec
    (prefix_dyadic_block_uniform_log_three hprimeReciprocal)
  have hE : 0 < E := hEspec.1
  have hblock := hEspec.2
  let D : ℝ := 3 / Real.log 2
  let C : ℝ := E * D ^ 2
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨5, C, 2, hC, le_rfl, ?_⟩
  intro M G hM
  have hpartition := jutilaReflectedPrefixMoment_le_dyadic_sum hM G
  have hsum :
      (∑ i ∈ Finset.range (prefixDyadicCount29_41 M),
        jutilaSecondMoment (M / (2 : ℝ) ^ (i + 1)) G) ≤
      (prefixDyadicCount29_41 M : ℝ) *
        (E * (Real.log M) ^ 3 * jutilaSecondMoment M G) := by
    calc
      (∑ i ∈ Finset.range (prefixDyadicCount29_41 M),
          jutilaSecondMoment (M / (2 : ℝ) ^ (i + 1)) G) ≤
        ∑ _i ∈ Finset.range (prefixDyadicCount29_41 M),
          E * (Real.log M) ^ 3 * jutilaSecondMoment M G := by
            apply Finset.sum_le_sum
            intro i hi
            exact hblock M i G hM
      _ = (prefixDyadicCount29_41 M : ℝ) *
          (E * (Real.log M) ^ 3 * jutilaSecondMoment M G) := by simp
  have hQ := prefixDyadicCount29_41_cast_le_log hM
  have hQnonneg : 0 ≤ (prefixDyadicCount29_41 M : ℝ) := Nat.cast_nonneg _
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  have hDlog : 0 ≤ D * Real.log M := by positivity
  have hQsq : (prefixDyadicCount29_41 M : ℝ) ^ 2 ≤
      (D * Real.log M) ^ 2 := by
    have hQ' : (prefixDyadicCount29_41 M : ℝ) ≤ D * Real.log M := by
      simpa only [D] using hQ
    exact pow_le_pow_left₀ hQnonneg hQ' 2
  calc
    jutilaReflectedPrefixMoment M G ≤
        (prefixDyadicCount29_41 M : ℝ) *
          ∑ i ∈ Finset.range (prefixDyadicCount29_41 M),
            jutilaSecondMoment (M / (2 : ℝ) ^ (i + 1)) G := hpartition
    _ ≤ (prefixDyadicCount29_41 M : ℝ) *
        ((prefixDyadicCount29_41 M : ℝ) *
          (E * (Real.log M) ^ 3 * jutilaSecondMoment M G)) :=
      mul_le_mul_of_nonneg_left hsum hQnonneg
    _ = (prefixDyadicCount29_41 M : ℝ) ^ 2 *
        (E * (Real.log M) ^ 3 * jutilaSecondMoment M G) := by ring
    _ ≤ (D * Real.log M) ^ 2 *
        (E * (Real.log M) ^ 3 * jutilaSecondMoment M G) := by
      exact mul_le_mul_of_nonneg_right hQsq
        (mul_nonneg
          (mul_nonneg hE.le (by positivity))
          (jutilaSecondMoment_nonneg M G))
    _ = C * (Real.log M) ^ (5 : ℕ) *
        jutilaSecondMoment M G := by
      dsimp [C]
      ring

@[simp]
theorem prefixDyadicTransference29_41LogFive_K
    (hprimeReciprocal : DyadicPrimeReciprocalInverseLogBound) :
    (prefixDyadicTransference29_41LogFive hprimeReciprocal).K = 5 := by
  rfl

/-- Exact adapter to the robust downstream recurrence interface. -/
theorem prefixDyadicTransferenceFixedLogPower_five
    (hprimeReciprocal : DyadicPrimeReciprocalInverseLogBound) :
    GuthMaynardJutilaReflection2941Robust.PrefixDyadicTransferenceFixedLogPower 5 := by
  let h := prefixDyadicTransference29_41LogFive hprimeReciprocal
  refine ⟨h.C, h.M₀, h.C_pos, h.M₀_ge_two, ?_⟩
  intro M G hM
  have hbound := h.bound M G hM
  have hK : h.K = 5 := rfl
  rw [hK] at hbound
  simpa only [jutilaReflectedPrefixMoment,
    GuthMaynardJutilaReflection2941.jutilaReflectedPrefixMoment] using hbound

/-- Certified source-facing adapter: equation (29.32) supplies the inverse
reciprocal-prime contract, hence the corrected robust exponent five. -/
theorem prefixDyadicTransferenceFixedLogPower_five_of_29_32
    (h29_32 :
      GuthMaynardJutilaLemma29NineKTwo.DyadicPrimeReciprocalLower29_32) :
    GuthMaynardJutilaReflection2941Robust.PrefixDyadicTransferenceFixedLogPower 5 := by
  apply prefixDyadicTransferenceFixedLogPower_five
  have hinv :=
    GuthMaynardJutilaLemma29NineKTwo.dyadicPrimeReciprocalInverseLogBound_of_29_32
      h29_32
  simpa only [DyadicPrimeReciprocalInverseLogBound,
    GuthMaynardJutilaLemma29NineKTwo.DyadicPrimeReciprocalInverseLogBound] using hinv

/-- Assumption-free certified endpoint, using the conductor-one psi theorem
to discharge (29.32). -/
theorem prefixDyadicTransferenceFixedLogPower_five_certified :
    GuthMaynardJutilaReflection2941Robust.PrefixDyadicTransferenceFixedLogPower 5 :=
  prefixDyadicTransferenceFixedLogPower_five_of_29_32
    KTwoDyadicPrimeReciprocalFromCertifiedPsi.dyadicPrimeReciprocalLower29_32_certified

end

end GuthMaynardJutilaReflection2941Corrected

#print axioms GuthMaynardJutilaReflection2941Corrected.jutila_first_block_direct
#print axioms GuthMaynardJutilaReflection2941Corrected.jutila_later_block_transference_normalized
#print axioms GuthMaynardJutilaReflection2941Corrected.laterBlockTransference29_41LogThree
#print axioms GuthMaynardJutilaReflection2941Corrected.jutila_dyadic_power_later_block_log_three
#print axioms GuthMaynardJutilaReflection2941Corrected.jutilaReflectedPrefixMoment_le_dyadic_sum
#print axioms GuthMaynardJutilaReflection2941Corrected.prefixDyadicTransference29_41LogFive
#print axioms GuthMaynardJutilaReflection2941Corrected.prefixDyadicTransferenceFixedLogPower_five
#print axioms GuthMaynardJutilaReflection2941Corrected.prefixDyadicTransferenceFixedLogPower_five_of_29_32
#print axioms GuthMaynardJutilaReflection2941Corrected.prefixDyadicTransferenceFixedLogPower_five_certified
