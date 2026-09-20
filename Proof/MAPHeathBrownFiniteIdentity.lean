import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Exact finite Heath--Brown truncation identity

This file certifies the algebraic truncation at the start of MRT Lemma 2.15.
It contains no dyadic decomposition and no analytic estimate.
-/

namespace MAPHeathBrownFiniteIdentity

open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction

noncomputable section

/-- The real-valued Möbius coefficient, cut off at `y`. -/
def truncatedMoebius (y : ℕ) : ArithmeticFunction ℝ where
  toFun n := if n ≤ y then (ArithmeticFunction.moebius n : ℝ) else 0
  map_zero' := by simp

/-- The omitted Möbius tail. -/
def moebiusTail (y : ℕ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ) - truncatedMoebius y

/-- Real-threshold cutoff, matching the literal `d ≤ (2X)^(1/K)` convention
in the published source. -/
def realTruncatedMoebius (Y : ℝ) : ArithmeticFunction ℝ where
  toFun n := if (n : ℝ) ≤ Y then (ArithmeticFunction.moebius n : ℝ) else 0
  map_zero' := by simp

def realMoebiusTail (Y : ℝ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ) - realTruncatedMoebius Y

@[simp] theorem truncatedMoebius_apply_of_le
    {y n : ℕ} (hn : n ≤ y) : truncatedMoebius y n = (ArithmeticFunction.moebius n : ℝ) := by
  simp [truncatedMoebius, hn]

@[simp] theorem moebiusTail_apply_of_le
    {y n : ℕ} (hn : n ≤ y) : moebiusTail y n = 0 := by
  change (ArithmeticFunction.moebius n : ℝ) -
      (if n ≤ y then (ArithmeticFunction.moebius n : ℝ) else 0) = 0
  simp [hn]

@[simp] theorem realMoebiusTail_apply_of_le
    {Y : ℝ} {n : ℕ} (hn : (n : ℝ) ≤ Y) : realMoebiusTail Y n = 0 := by
  change (ArithmeticFunction.moebius n : ℝ) -
      (if (n : ℝ) ≤ Y then (ArithmeticFunction.moebius n : ℝ) else 0) = 0
  simp [hn]

theorem antidiagonal_right_le
    {n : ℕ} {z : ℕ × ℕ} (hz : z ∈ n.divisorsAntidiagonal) : z.2 ≤ n := by
  have hmul : z.1 * z.2 = n := (Nat.mem_divisorsAntidiagonal.mp hz).1
  have hn0 : n ≠ 0 := (Nat.mem_divisorsAntidiagonal.mp hz).2
  have hleft0 : z.1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact hn0 hmul.symm
  have hpos : 0 < z.1 := Nat.pos_of_ne_zero hleft0
  rw [← hmul]
  exact Nat.le_mul_of_pos_left z.2 hpos

/-- A `K`-fold Dirichlet convolution of coefficients supported strictly above
`y` vanishes at every `n ≤ y^K`.  This is the exact support mechanism behind
the finite Heath--Brown identity. -/
theorem pow_eq_zero_below
    (f : ArithmeticFunction ℝ) {y K n : ℕ}
    (hK : 1 ≤ K) (hf : ∀ d, d ≤ y → f d = 0) (hn : n ≤ y ^ K) :
    (f ^ K) n = 0 := by
  induction K generalizing n with
  | zero => omega
  | succ K ih =>
      by_cases hKzero : K = 0
      · subst K
        have hn' : n ≤ y := by simpa using hn
        simpa using hf n hn'
      rw [pow_succ, ArithmeticFunction.mul_apply]
      apply Finset.sum_eq_zero
      intro z hz
      have hmul : z.1 * z.2 = n := (Nat.mem_divisorsAntidiagonal.mp hz).1
      have hn0 : n ≠ 0 := (Nat.mem_divisorsAntidiagonal.mp hz).2
      have hleft0 : z.1 ≠ 0 := by
        intro h
        rw [h, zero_mul] at hmul
        exact hn0 hmul.symm
      have hleftPos : 0 < z.1 := Nat.pos_of_ne_zero hleft0
      have hyPos : 0 < y := by
        by_contra hy
        have hy0 : y = 0 := Nat.eq_zero_of_not_pos hy
        subst y
        simp at hn
        exact hn0 hn
      by_cases hright : z.2 ≤ y
      · simp [hf z.2 hright]
      · have hyRight : y < z.2 := Nat.lt_of_not_ge hright
        have hleft : z.1 ≤ y ^ K := by
          by_contra hnot
          have hyPowLeft : y ^ K < z.1 := Nat.lt_of_not_ge hnot
          have hprod : y ^ K * y < z.1 * z.2 :=
            (Nat.mul_lt_mul_of_pos_right hyPowLeft hyPos).trans
              (Nat.mul_lt_mul_of_pos_left hyRight hleftPos)
          rw [hmul, ← Nat.pow_succ] at hprod
          exact (Nat.not_lt_of_ge hn) hprod
        have hKpos : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hKzero
        simp [ih hKpos hleft]

/-- Real-threshold version of `pow_eq_zero_below`.  This is the exact endpoint
statement needed when the Möbius cutoff is a real `K`-th root. -/
theorem pow_eq_zero_below_real
    (f : ArithmeticFunction ℝ) {Y : ℝ} {K n : ℕ}
    (hK : 1 ≤ K) (hY : 0 ≤ Y)
    (hf : ∀ d : ℕ, (d : ℝ) ≤ Y → f d = 0)
    (hn : (n : ℝ) ≤ Y ^ K) :
    (f ^ K) n = 0 := by
  induction K generalizing n with
  | zero => omega
  | succ K ih =>
      by_cases hKzero : K = 0
      · subst K
        have hn' : (n : ℝ) ≤ Y := by simpa using hn
        simpa using hf n hn'
      rw [pow_succ, ArithmeticFunction.mul_apply]
      apply Finset.sum_eq_zero
      intro z hz
      have hmulNat : z.1 * z.2 = n := (Nat.mem_divisorsAntidiagonal.mp hz).1
      have hmulReal : (z.1 : ℝ) * (z.2 : ℝ) = n := by
        exact_mod_cast hmulNat
      by_cases hright : (z.2 : ℝ) ≤ Y
      · simp [hf z.2 hright]
      · have hyRight : Y < (z.2 : ℝ) := lt_of_not_ge hright
        have hleft : (z.1 : ℝ) ≤ Y ^ K := by
          by_contra hnot
          have hyPowLeft : Y ^ K < (z.1 : ℝ) := lt_of_not_ge hnot
          have hn0 : n ≠ 0 := (Nat.mem_divisorsAntidiagonal.mp hz).2
          have hleft0 : z.1 ≠ 0 := by
            intro h
            rw [h, zero_mul] at hmulNat
            exact hn0 hmulNat.symm
          have hleftPos : (0 : ℝ) < z.1 := by exact_mod_cast Nat.pos_of_ne_zero hleft0
          have hprod : Y ^ K * Y < (z.1 : ℝ) * (z.2 : ℝ) := by
            calc
              Y ^ K * Y ≤ (z.1 : ℝ) * Y :=
                mul_le_mul_of_nonneg_right hyPowLeft.le hY
              _ < (z.1 : ℝ) * (z.2 : ℝ) :=
                mul_lt_mul_of_pos_left hyRight hleftPos
          rw [hmulReal, ← pow_succ] at hprod
          exact (not_lt_of_ge hn) hprod
        have hKpos : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hKzero
        simp [ih hKpos hleft]

theorem realMoebiusTail_pow_eq_zero
    {Y : ℝ} {K n : ℕ} (hK : 1 ≤ K) (hY : 0 ≤ Y)
    (hn : (n : ℝ) ≤ Y ^ K) :
    (realMoebiusTail Y ^ K) n = 0 := by
  exact pow_eq_zero_below_real (realMoebiusTail Y) hK hY
    (fun d hd => realMoebiusTail_apply_of_le hd) hn

theorem zeta_mul_realMoebiusTail_pow_eq_zero
    {Y : ℝ} {K n : ℕ} (hK : 1 ≤ K) (hY : 0 ≤ Y)
    (hn : (n : ℝ) ≤ Y ^ K) :
    (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      realMoebiusTail Y) ^ K) n = 0 := by
  rw [mul_pow, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro z hz
  have hright : z.2 ≤ n := antidiagonal_right_le hz
  have hrightReal : (z.2 : ℝ) ≤ n := by exact_mod_cast hright
  have hzero : (realMoebiusTail Y ^ K) z.2 = 0 :=
    realMoebiusTail_pow_eq_zero hK hY (hrightReal.trans hn)
  simp [hzero]

theorem moebiusTail_pow_eq_zero
    {y K n : ℕ} (hK : 1 ≤ K) (hn : n ≤ y ^ K) :
    (moebiusTail y ^ K) n = 0 := by
  exact pow_eq_zero_below (moebiusTail y) hK
    (fun d hd => moebiusTail_apply_of_le hd) hn

/-- The zeta factor does not spoil the support cutoff. -/
theorem zeta_mul_moebiusTail_pow_eq_zero
    {y K n : ℕ} (hK : 1 ≤ K) (hn : n ≤ y ^ K) :
    (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * moebiusTail y) ^ K) n = 0 := by
  rw [mul_pow, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro z hz
  have hright : z.2 ≤ n := antidiagonal_right_le hz
  have hzero : (moebiusTail y ^ K) z.2 = 0 :=
    moebiusTail_pow_eq_zero hK (hright.trans hn)
  simp [hzero]

/-! ## Exact finite binomial normal form -/

/-- The positive-index part of the binomial expansion of
`1 - (1 - a)^K`, written with the exact Heath--Brown signs. -/
def heathBrownPolynomial (K : ℕ) (a : ArithmeticFunction ℝ) :
    ArithmeticFunction ℝ :=
  ∑ k ∈ Finset.range K,
    ((-1 : ArithmeticFunction ℝ) ^ k *
      (K.choose (k + 1) : ArithmeticFunction ℝ)) * a ^ (k + 1)

theorem heathBrownPolynomial_eq
    (K : ℕ) (a : ArithmeticFunction ℝ) :
    heathBrownPolynomial K a = 1 - (1 - a) ^ K := by
  have hpow := add_pow (-a) 1 K
  have hpow' :
      (1 - a) ^ K =
        ∑ m ∈ Finset.range (K + 1),
          (-a) ^ m * (K.choose m : ArithmeticFunction ℝ) := by
    simpa [sub_eq_add_neg, add_comm, mul_comm] using hpow
  rw [hpow', Finset.sum_range_succ']
  simp only [heathBrownPolynomial, pow_zero, Nat.choose_zero_right,
    Nat.cast_one, mul_one]
  rw [show (∑ x ∈ Finset.range K,
      ((-1 : ArithmeticFunction ℝ) ^ x *
        (K.choose (x + 1) : ArithmeticFunction ℝ)) * a ^ (x + 1)) =
      -∑ x ∈ Finset.range K,
        (-a) ^ (x + 1) * (K.choose (x + 1) : ArithmeticFunction ℝ) by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [show (-a) ^ (x + 1) =
        ((-1 : ArithmeticFunction ℝ) ^ (x + 1)) * a ^ (x + 1) by
      exact neg_pow a (x + 1)]
    ring]
  ring

/-- The exact finite Heath--Brown arithmetic function before expanding `Λζ`
to `log`. -/
def heathBrownTruncation (K y : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.vonMangoldt *
    heathBrownPolynomial K
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * truncatedMoebius y)

/-- The literal `L * 1^{*(j-1)} * μ_{≤y}^{*j}` sum printed in the
Heath--Brown decomposition, indexed by `j = k+1`. -/
def heathBrownPublishedSum (K y : ℕ) : ArithmeticFunction ℝ :=
  ∑ k ∈ Finset.range K,
    ((-1 : ArithmeticFunction ℝ) ^ k *
      (K.choose (k + 1) : ArithmeticFunction ℝ)) *
      (ArithmeticFunction.log *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k *
        truncatedMoebius y ^ (k + 1))

theorem vonMangoldt_mul_truncated_power
    (k y : ℕ) :
    ArithmeticFunction.vonMangoldt *
        (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          truncatedMoebius y) ^ (k + 1)) =
      ArithmeticFunction.log *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k *
        truncatedMoebius y ^ (k + 1) := by
  calc
    ArithmeticFunction.vonMangoldt *
        (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          truncatedMoebius y) ^ (k + 1)) =
        (ArithmeticFunction.vonMangoldt *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) *
          ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k *
            truncatedMoebius y ^ (k + 1)) := by
      rw [mul_pow, pow_succ]
      ring
    _ = ArithmeticFunction.log *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k *
        truncatedMoebius y ^ (k + 1) := by
      rw [ArithmeticFunction.vonMangoldt_mul_zeta]
      ring

/-- The polynomial form and the literal published convolution sum are exactly
the same arithmetic function. -/
theorem heathBrownTruncation_eq_publishedSum (K y : ℕ) :
    heathBrownTruncation K y = heathBrownPublishedSum K y := by
  unfold heathBrownTruncation heathBrownPolynomial heathBrownPublishedSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  let c : ArithmeticFunction ℝ :=
    (-1 : ArithmeticFunction ℝ) ^ k *
      (K.choose (k + 1) : ArithmeticFunction ℝ)
  calc
    ArithmeticFunction.vonMangoldt *
        (c * (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          truncatedMoebius y) ^ (k + 1))) =
        c * (ArithmeticFunction.vonMangoldt *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            truncatedMoebius y) ^ (k + 1))) := by ring
    _ = c * (ArithmeticFunction.log *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k *
        truncatedMoebius y ^ (k + 1)) := by
      rw [vonMangoldt_mul_truncated_power]
    _ = ((-1 : ArithmeticFunction ℝ) ^ k *
          (K.choose (k + 1) : ArithmeticFunction ℝ)) *
        (ArithmeticFunction.log *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k *
          truncatedMoebius y ^ (k + 1)) := by rfl

/-- The exact closed-form truncation identity.  The omitted term is the
`K`-fold large-Möbius tail and therefore vanishes below `y^K`. -/
theorem vonMangoldt_closedForm_truncation
    {y K n : ℕ} (hK : 1 ≤ K) (hn : n ≤ y ^ K) :
    (ArithmeticFunction.vonMangoldt *
      (1 - (1 - (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        truncatedMoebius y) ^ K)) n =
      ArithmeticFunction.vonMangoldt n := by
  have hsplit :
      (1 - (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          truncatedMoebius y) =
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * moebiusTail y := by
    unfold moebiusTail
    rw [mul_sub, ArithmeticFunction.coe_zeta_mul_coe_moebius]
  rw [mul_sub, mul_one]
  change ArithmeticFunction.vonMangoldt n -
      (ArithmeticFunction.vonMangoldt *
        ((1 - (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          truncatedMoebius y) ^ K)) n = ArithmeticFunction.vonMangoldt n
  have hconv :
      (ArithmeticFunction.vonMangoldt *
        ((1 - (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          truncatedMoebius y) ^ K)) n = 0 := by
    rw [ArithmeticFunction.mul_apply]
    apply Finset.sum_eq_zero
    intro z hz
    have hright : z.2 ≤ n := antidiagonal_right_le hz
    have htailRight :
        ((1 - (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            truncatedMoebius y) ^ K) z.2 = 0 := by
      rw [hsplit]
      exact zeta_mul_moebiusTail_pow_eq_zero hK (hright.trans hn)
    simp [htailRight]
  rw [hconv, sub_zero]

/-- Closed-form identity at the literal real cutoff used in MRT Lemma 2.15. -/
theorem vonMangoldt_closedForm_real_truncation
    {Y : ℝ} {K n : ℕ} (hK : 1 ≤ K) (hY : 0 ≤ Y)
    (hn : (n : ℝ) ≤ Y ^ K) :
    (ArithmeticFunction.vonMangoldt *
      (1 - (1 - (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        realTruncatedMoebius Y) ^ K)) n =
      ArithmeticFunction.vonMangoldt n := by
  have hsplit :
      (1 - (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          realTruncatedMoebius Y) =
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * realMoebiusTail Y := by
    unfold realMoebiusTail
    rw [mul_sub, ArithmeticFunction.coe_zeta_mul_coe_moebius]
  rw [mul_sub, mul_one]
  change ArithmeticFunction.vonMangoldt n -
      (ArithmeticFunction.vonMangoldt *
        ((1 - (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          realTruncatedMoebius Y) ^ K)) n = ArithmeticFunction.vonMangoldt n
  have hconv :
      (ArithmeticFunction.vonMangoldt *
        ((1 - (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          realTruncatedMoebius Y) ^ K)) n = 0 := by
    rw [ArithmeticFunction.mul_apply]
    apply Finset.sum_eq_zero
    intro z hz
    have hright : z.2 ≤ n := antidiagonal_right_le hz
    have hrightReal : (z.2 : ℝ) ≤ n := by exact_mod_cast hright
    have htailRight :
        ((1 - (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            realTruncatedMoebius Y) ^ K) z.2 = 0 := by
      rw [hsplit]
      exact zeta_mul_realMoebiusTail_pow_eq_zero hK hY (hrightReal.trans hn)
    simp [htailRight]
  rw [hconv, sub_zero]

/-- Literal published real-cutoff sum. -/
def heathBrownPublishedRealSum (K : ℕ) (Y : ℝ) : ArithmeticFunction ℝ :=
  ∑ k ∈ Finset.range K,
    ((-1 : ArithmeticFunction ℝ) ^ k *
      (K.choose (k + 1) : ArithmeticFunction ℝ)) *
      (ArithmeticFunction.log *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k *
        realTruncatedMoebius Y ^ (k + 1))

theorem heathBrownPublishedRealSum_apply
    {Y : ℝ} {K n : ℕ} (hK : 1 ≤ K) (hY : 0 ≤ Y)
    (hn : (n : ℝ) ≤ Y ^ K) :
    heathBrownPublishedRealSum K Y n = ArithmeticFunction.vonMangoldt n := by
  have hpoly := heathBrownPolynomial_eq K
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * realTruncatedMoebius Y)
  have hsum :
      ArithmeticFunction.vonMangoldt *
          heathBrownPolynomial K
            ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              realTruncatedMoebius Y) =
        heathBrownPublishedRealSum K Y := by
    unfold heathBrownPolynomial heathBrownPublishedRealSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    let c : ArithmeticFunction ℝ :=
      (-1 : ArithmeticFunction ℝ) ^ k *
        (K.choose (k + 1) : ArithmeticFunction ℝ)
    have hterm :
        ArithmeticFunction.vonMangoldt *
            (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              realTruncatedMoebius Y) ^ (k + 1)) =
          ArithmeticFunction.log *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k *
            realTruncatedMoebius Y ^ (k + 1) := by
      calc
        ArithmeticFunction.vonMangoldt *
            (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              realTruncatedMoebius Y) ^ (k + 1)) =
            (ArithmeticFunction.vonMangoldt *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) *
              ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k *
                realTruncatedMoebius Y ^ (k + 1)) := by
          rw [mul_pow, pow_succ]
          ring
        _ = _ := by
          rw [ArithmeticFunction.vonMangoldt_mul_zeta]
          ring
    change ArithmeticFunction.vonMangoldt *
        (c * (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          realTruncatedMoebius Y) ^ (k + 1))) = c *
        (ArithmeticFunction.log *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k *
          realTruncatedMoebius Y ^ (k + 1))
    rw [show ArithmeticFunction.vonMangoldt *
          (c * (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            realTruncatedMoebius Y) ^ (k + 1))) =
        c * (ArithmeticFunction.vonMangoldt *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            realTruncatedMoebius Y) ^ (k + 1))) by ring, hterm]
  rw [← hsum, hpoly]
  exact vonMangoldt_closedForm_real_truncation hK hY hn

/-- Exact finite identity at every coefficient in the legal truncation range. -/
theorem heathBrownTruncation_apply
    {y K n : ℕ} (hK : 1 ≤ K) (hn : n ≤ y ^ K) :
    heathBrownTruncation K y n = ArithmeticFunction.vonMangoldt n := by
  rw [heathBrownTruncation, heathBrownPolynomial_eq]
  exact vonMangoldt_closedForm_truncation hK hn

/-- Published-form finite Heath--Brown identity, with no analytic or
asymptotic premise. -/
theorem heathBrownPublishedSum_apply
    {y K n : ℕ} (hK : 1 ≤ K) (hn : n ≤ y ^ K) :
    heathBrownPublishedSum K y n = ArithmeticFunction.vonMangoldt n := by
  rw [← heathBrownTruncation_eq_publishedSum]
  exact heathBrownTruncation_apply hK hn

end
end MAPHeathBrownFiniteIdentity

#print axioms MAPHeathBrownFiniteIdentity.pow_eq_zero_below
#print axioms MAPHeathBrownFiniteIdentity.zeta_mul_moebiusTail_pow_eq_zero
#print axioms MAPHeathBrownFiniteIdentity.heathBrownPolynomial_eq
#print axioms MAPHeathBrownFiniteIdentity.heathBrownTruncation_apply
#print axioms MAPHeathBrownFiniteIdentity.heathBrownPublishedSum_apply
#print axioms MAPHeathBrownFiniteIdentity.heathBrownPublishedRealSum_apply
#print axioms MAPHeathBrownFiniteIdentity.vonMangoldt_closedForm_truncation
#print axioms MAPHeathBrownFiniteIdentity.vonMangoldt_closedForm_real_truncation
