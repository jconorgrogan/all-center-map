import GuthMaynardJutilaLemma29NineKTwo
import Mathlib.Data.Nat.PrimeFin

/-!
# The elementary divisor-fiber bound in the `k = 2` transference

For fixed `l`, projection `(p,n) ↦ p` injects the transference fiber into
the distinct prime factors of `l`.  Consequently the fiber has at most
`log l / log 2` elements.  This is the elementary half of the arithmetic
log budget; no prime-distribution input enters here.
-/

namespace GuthMaynardJutilaLemma29NineKTwo

open GuthMaynardJutilaTransference
open GuthMaynardPoweringKTwo

noncomputable section

/-- Projection to the prime coordinate injects a nonzero product fiber into
the prime factors of its product. -/
theorem kTwoTransferenceFiberCard_le_primeFactors_card
    {N P : ℝ} {l : ℕ} (hl : 0 < l) :
    kTwoTransferenceFiberCard N P l ≤ l.primeFactors.card := by
  unfold kTwoTransferenceFiberCard
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqmem :
        q.1 ∈ kTwoPrimeRange N P ∧ q.2 ∈ productIoc N := by
      simpa using hq'.1
    have hp : Nat.Prime q.1 := by
      unfold kTwoPrimeRange primeRealIcc at hqmem
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
    have haMem : a.1 ∈ kTwoPrimeRange N P := by
      have := (Finset.mem_product.mp ha'.1).1
      simpa using this
    have haPrime : Nat.Prime a.1 := by
      unfold kTwoPrimeRange primeRealIcc at haMem
      exact (Finset.mem_filter.mp haMem).2.2.2
    exact Nat.mul_left_cancel haPrime.pos hmul

/-- Distinct prime factors of a positive integer give the elementary
exponential lower bound `2^ω(l) ≤ l`. -/
theorem two_pow_primeFactors_card_le {l : ℕ} (hl : 0 < l) :
    2 ^ l.primeFactors.card ≤ l := by
  calc
    2 ^ l.primeFactors.card ≤ ∏ p ∈ l.primeFactors, p := by
      exact Finset.pow_card_le_prod _ id 2 (fun p hp =>
        (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ l := Nat.le_of_dvd hl (Nat.prod_primeFactors_dvd l)

/-- The literal fiber cardinality is at most `log l / log 2`. -/
theorem kTwoTransferenceFiberCard_cast_le_log
    {N P : ℝ} {l : ℕ} (hl : 0 < l) :
    (kTwoTransferenceFiberCard N P l : ℝ) ≤
      Real.log (l : ℝ) / Real.log 2 := by
  have hcard := kTwoTransferenceFiberCard_le_primeFactors_card
    (N := N) (P := P) hl
  have hpow : 2 ^ kTwoTransferenceFiberCard N P l ≤ l :=
    (Nat.pow_le_pow_right (by norm_num) hcard).trans
      (two_pow_primeFactors_card_le hl)
  have hpowReal :
      (2 : ℝ) ^ kTwoTransferenceFiberCard N P l ≤ (l : ℝ) := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) <
    (2 : ℝ) ^ kTwoTransferenceFiberCard N P l) hpowReal
  rw [Real.log_pow] at hlog
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (le_div_iff₀ hlogTwo).2 (by simpa [mul_comm] using hlog)

/-- Every integer in the exact transference product range is positive and at
most `2P`. -/
theorem kTwoProductRange_cast_pos_and_le
    {N P : ℝ} (hN : 0 < N) (hJ : 2 ≤ kTwoPrimeLower N P)
    {l : ℕ} (hl : l ∈ kTwoProductRange N P) :
    0 < (l : ℝ) ∧ (l : ℝ) ≤ 2 * P := by
  have hJpos : 0 < kTwoPrimeLower N P := lt_of_lt_of_le (by norm_num) hJ
  have hl' :
      kTwoPrimeLower N P * N ^ 2 < (l : ℝ) ∧
        (l : ℝ) ≤ (2 * kTwoPrimeLower N P) * (4 * N ^ 2) := by
    unfold kTwoProductRange productRealIoc natRealIoc at hl
    exact (Finset.mem_filter.mp hl).2
  have hupper :
      (2 * kTwoPrimeLower N P) * (4 * N ^ 2) = 2 * P := by
    unfold kTwoPrimeLower
    field_simp [hN.ne']
  constructor
  · exact (mul_pos hJpos (sq_pos_of_pos hN)).trans hl'.1
  · simpa [hupper] using hl'.2

/-- The exact finite divisor-fiber cap costs only one logarithm.  The
constant `3 / log 2` is explicit and deliberately unoptimized. -/
theorem kTwoTransferenceFiberCap_cast_le_log
    {N P : ℝ} (hN : 0 < N) (hJ : 2 ≤ kTwoPrimeLower N P)
    (hP : 2 ≤ P) :
    (kTwoTransferenceFiberCap N P : ℝ) ≤
      3 * Real.log P / Real.log 2 := by
  let x : ℝ := Real.log (2 * P) / Real.log 2
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwoP : 1 < 2 * P := by linarith
  have hx : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (Real.log_nonneg htwoP.le) hlogTwo.le
  have hsupNat :
      kTwoTransferenceFiberCap N P ≤ Nat.ceil x := by
    unfold kTwoTransferenceFiberCap
    apply Finset.sup_le
    intro l hl
    have hlbounds := kTwoProductRange_cast_pos_and_le hN hJ hl
    have hlpos : 0 < l := by exact_mod_cast hlbounds.1
    have hcard := kTwoTransferenceFiberCard_cast_le_log
      (N := N) (P := P) hlpos
    have hlogmono : Real.log (l : ℝ) ≤ Real.log (2 * P) :=
      Real.log_le_log hlbounds.1 hlbounds.2
    have hcardx : (kTwoTransferenceFiberCard N P l : ℝ) ≤ x := by
      dsimp [x]
      exact hcard.trans (div_le_div_of_nonneg_right hlogmono hlogTwo.le)
    exact (Nat.cast_le (α := ℝ)).mp (hcardx.trans (Nat.le_ceil x))
  have hcapx : (kTwoTransferenceFiberCap N P : ℝ) < x + 1 := by
    exact (Nat.cast_le.mpr hsupNat).trans_lt (Nat.ceil_lt_add_one hx)
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hlogP : Real.log 2 ≤ Real.log P :=
    Real.log_le_log (by norm_num) hP
  have hlogMul : Real.log (2 * P) = Real.log 2 + Real.log P := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hPpos.ne']
  have htarget : x + 1 ≤ 3 * Real.log P / Real.log 2 := by
    dsimp [x]
    rw [hlogMul]
    have hlogTwoNe : Real.log 2 ≠ 0 := hlogTwo.ne'
    field_simp [hlogTwoNe]
    nlinarith
  exact hcapx.le.trans htarget

#print axioms kTwoTransferenceFiberCard_le_primeFactors_card
#print axioms kTwoTransferenceFiberCap_cast_le_log

end

end GuthMaynardJutilaLemma29NineKTwo
