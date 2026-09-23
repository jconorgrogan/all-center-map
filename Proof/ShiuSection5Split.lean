import SelbergDenominatorLower
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Shiu's canonical Section 5 split and four finite classes

This module formalizes the purely finite part of pages 166--169 of Shiu
(1980).  The prime powers of `n` are ordered by increasing prime.  The factor
`b_n` is the largest initial prime-power block product not exceeding `z`, and
`d_n = n / b_n`.  The four classes use the squared natural-number versions of
Shiu's conditions, avoiding any rounding convention for `sqrt z`.

No Brun--Titchmarsh estimate is postulated here.  The final weld accepts one
bound for each of the three genuinely distinct analytic outputs in the paper:
class I, the combined exceptional classes II--III, and class IV.
-/

namespace ShiuSection5Split

open ArithmeticFunction ShiuFoundation
open scoped BigOperators

noncomputable section

/-- Distinct prime divisors of `n`, in increasing order. -/
def orderedPrimes (n : ℕ) : List ℕ := n.primeFactors.sort (· ≤ ·)

/-- Shiu's ordered complete prime-power blocks `p_i^{s_i}`. -/
def primePowerBlocks (n : ℕ) : List ℕ :=
  (orderedPrimes n).map fun p ↦ p ^ n.factorization p

/-- Product of the first `j` complete prime-power blocks. -/
def prefixProduct (n j : ℕ) : ℕ := (primePowerBlocks n |>.take j).prod

/-- Admissible prefix lengths: exactly those whose block product is at most
`z`.  The extra endpoint is the full list length. -/
def admissiblePrefixLengths (n z : ℕ) : Finset ℕ :=
  (Finset.range (primePowerBlocks n).length.succ).filter fun j ↦
    prefixProduct n j ≤ z

/-- Canonical number of complete prime-power blocks in Shiu's `b_n`.
For `z = 0` the admissible set may be empty, so we use `0`; every application
below assumes `1 ≤ z`, when the set contains `0`. -/
def canonicalIndex (n z : ℕ) : ℕ := by
  classical
  exact if h : (admissiblePrefixLengths n z).Nonempty then
    (admissiblePrefixLengths n z).max' h
  else 0

/-- Shiu's `b_n`: the last full prime-power prefix whose product is `≤ z`. -/
def canonicalB (n z : ℕ) : ℕ := prefixProduct n (canonicalIndex n z)

/-- Shiu's complementary factor `d_n`. -/
def canonicalD (n z : ℕ) : ℕ := n / canonicalB n z

lemma prefixProduct_zero (n : ℕ) : prefixProduct n 0 = 1 := by
  simp [prefixProduct]

lemma orderedPrimes_toFinset (n : ℕ) : (orderedPrimes n).toFinset = n.primeFactors := by
  simp [orderedPrimes]

lemma primePowerBlocks_prod {n : ℕ} (hn : n ≠ 0) : (primePowerBlocks n).prod = n := by
  rw [primePowerBlocks, orderedPrimes]
  rw [show ((n.primeFactors.sort (· ≤ ·)).map fun p ↦ p ^ n.factorization p).prod =
      ∏ p ∈ n.primeFactors, p ^ n.factorization p by
    rw [Finset.prod_eq_multiset_prod]
    exact congrArg Multiset.prod
      (congrArg (Multiset.map fun p ↦ p ^ n.factorization p)
        (Finset.sort_eq n.primeFactors (· ≤ ·)))]
  exact Nat.prod_factorization_pow_eq_self hn

lemma admissiblePrefixLengths_nonempty {n z : ℕ} (hz : 1 ≤ z) :
    (admissiblePrefixLengths n z).Nonempty := by
  refine ⟨0, ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _), by simpa only [prefixProduct_zero] using hz⟩

lemma canonicalIndex_mem {n z : ℕ} (hz : 1 ≤ z) :
    canonicalIndex n z ∈ admissiblePrefixLengths n z := by
  classical
  rw [canonicalIndex]
  have h := admissiblePrefixLengths_nonempty (n := n) hz
  rw [dif_pos h]
  exact Finset.max'_mem _ h

lemma le_canonicalIndex_of_mem {n z i : ℕ} (hz : 1 ≤ z)
    (hi : i ∈ admissiblePrefixLengths n z) : i ≤ canonicalIndex n z := by
  classical
  rw [canonicalIndex]
  have h := admissiblePrefixLengths_nonempty (n := n) hz
  rw [dif_pos h]
  exact Finset.le_max' _ _ hi

lemma canonicalIndex_le_length {n z : ℕ} (hz : 1 ≤ z) :
    canonicalIndex n z ≤ (primePowerBlocks n).length := by
  have hmem := canonicalIndex_mem (n := n) hz
  simp only [admissiblePrefixLengths, Finset.mem_filter, Finset.mem_range] at hmem
  omega

lemma canonicalB_le {n z : ℕ} (hz : 1 ≤ z) : canonicalB n z ≤ z := by
  have hmem := canonicalIndex_mem (n := n) hz
  exact (Finset.mem_filter.mp hmem).2

lemma canonicalB_dvd {n z : ℕ} (hn : n ≠ 0) (_hz : 1 ≤ z) : canonicalB n z ∣ n := by
  have hdvd : canonicalB n z ∣ (primePowerBlocks n).prod :=
    List.Sublist.prod_dvd_prod
      (List.take_sublist (canonicalIndex n z) (primePowerBlocks n))
  simpa [primePowerBlocks_prod hn] using hdvd

lemma canonicalB_pos (n z : ℕ) : 0 < canonicalB n z := by
  unfold canonicalB prefixProduct
  apply List.prod_pos
  intro a ha
  have ha' : a ∈ primePowerBlocks n := List.mem_of_mem_take ha
  rw [primePowerBlocks] at ha'
  rcases List.mem_map.mp ha' with ⟨p, hp, rfl⟩
  have hpfin : p ∈ (orderedPrimes n).toFinset := List.mem_toFinset.mpr hp
  rw [orderedPrimes_toFinset] at hpfin
  exact pow_pos (Nat.prime_of_mem_primeFactors hpfin).pos _

lemma canonicalB_mul_canonicalD {n z : ℕ} (hn : n ≠ 0) (hz : 1 ≤ z) :
    canonicalB n z * canonicalD n z = n := by
  exact Nat.mul_div_cancel' (canonicalB_dvd hn hz)

/-- The complementary factor is exactly the product of the remaining complete
prime-power blocks, not merely an unspecified quotient. -/
theorem canonicalD_eq_suffixProduct {n z : ℕ} (hn : n ≠ 0) (hz : 1 ≤ z) :
    canonicalD n z = (primePowerBlocks n |>.drop (canonicalIndex n z)).prod := by
  apply Nat.eq_of_mul_eq_mul_left (canonicalB_pos n z)
  rw [canonicalB_mul_canonicalD hn hz]
  change n = prefixProduct n (canonicalIndex n z) *
    (primePowerBlocks n |>.drop (canonicalIndex n z)).prod
  rw [prefixProduct, List.prod_take_mul_prod_drop, primePowerBlocks_prod hn]

lemma canonicalIndex_lt_length_of_z_lt_n {n z : ℕ} (hn : n ≠ 0)
    (hz : 1 ≤ z) (hzn : z < n) :
    canonicalIndex n z < (primePowerBlocks n).length := by
  have hle := canonicalIndex_le_length (n := n) hz
  apply lt_of_le_of_ne hle
  intro heq
  have hb : canonicalB n z = n := by
    simp [canonicalB, prefixProduct, heq, primePowerBlocks_prod hn]
  have := canonicalB_le (n := n) hz
  omega

/-- Exact threshold-crossing property (5.2): after the canonical prefix,
the next complete prime-power block pushes the product strictly past `z`. -/
theorem canonical_crossing {n z : ℕ} (hn : n ≠ 0) (hz : 1 ≤ z) (hzn : z < n) :
    ∃ a : ℕ, (primePowerBlocks n)[canonicalIndex n z]? = some a ∧
      z < canonicalB n z * a := by
  classical
  let j := canonicalIndex n z
  have hj : j < (primePowerBlocks n).length :=
    canonicalIndex_lt_length_of_z_lt_n hn hz hzn
  let a := (primePowerBlocks n)[j]
  have ha : (primePowerBlocks n)[j]? = some a := List.getElem?_eq_getElem hj
  have hnot : j + 1 ∉ admissiblePrefixLengths n z := by
    intro hmem
    have hmax := le_canonicalIndex_of_mem hz hmem
    dsimp [j] at hmax
    omega
  have hprod : prefixProduct n (j + 1) = canonicalB n z * a := by
    rw [prefixProduct, List.prod_take_succ _ _ hj]
    rfl
  have hgt : z < prefixProduct n (j + 1) := by
    have hsuccRange : j + 1 < (primePowerBlocks n).length.succ := by omega
    have hnotle : ¬ prefixProduct n (j + 1) ≤ z := by
      intro hle
      apply hnot
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hsuccRange, hle⟩
    omega
  exact ⟨a, ha, by simpa [hprod] using hgt⟩

/-- Least prime divisor, with Shiu's convention `q(1)=1`.
(The value at zero is irrelevant to the positive Section 5 window.) -/
def leastPrimeFactor (n : ℕ) : ℕ := if n = 1 then 1 else n.minFac

inductive FourClass
  | I | II | III | IV
  deriving DecidableEq, Repr

instance : Fintype FourClass where
  elems := {FourClass.I, FourClass.II, FourClass.III, FourClass.IV}
  complete := by
    intro c
    cases c <;> simp

/-- Exact integer classifier corresponding to page 166.  `q(d)>sqrt z` is
encoded as `z < q(d)^2`; `b>sqrt z` as `z < b^2`.
The supplied `smoothCutoff` is Shiu's `log x loglog x`. -/
def classify (n z smoothCutoff : ℕ) : FourClass :=
  let b := canonicalB n z
  let d := canonicalD n z
  let qd := leastPrimeFactor d
  if z < qd ^ 2 then FourClass.I
  else if b ^ 2 ≤ z then FourClass.II
  else if qd ≤ smoothCutoff then FourClass.III
  else FourClass.IV

/-- Literal finite interval/progression to which Section 5 is applied. -/
def progressionWindow (x y modulus residue : ℕ) : Finset ℕ :=
  (Finset.Ioc (x - y) x).filter fun n ↦ n ≡ residue [MOD modulus]

/-- One of Shiu's four disjoint finite classes. -/
def classSet (c : FourClass) (x y modulus residue z smoothCutoff : ℕ) : Finset ℕ :=
  (progressionWindow x y modulus residue).filter fun n ↦
    classify n z smoothCutoff = c

/-- The finite window is definitionally faithful to the progression sum used by
the MAP Shiu interface. -/
theorem sum_progressionWindow_eq_progressionSum
    (f : ArithmeticFunction ℕ) (x y modulus residue : ℕ) :
    ∑ n ∈ progressionWindow x y modulus residue, f n =
      progressionSum f x y modulus residue := by
  classical
  simp only [progressionWindow, progressionSum, Finset.sum_filter]

lemma mem_classSet_iff {c : FourClass} {x y modulus residue z smoothCutoff n : ℕ} :
    n ∈ classSet c x y modulus residue z smoothCutoff ↔
      n ∈ progressionWindow x y modulus residue ∧ classify n z smoothCutoff = c := by
  simp [classSet]

lemma classSet_pairwise_disjoint {x y modulus residue z smoothCutoff : ℕ} :
    Set.PairwiseDisjoint Set.univ fun c : FourClass ↦
      classSet c x y modulus residue z smoothCutoff := by
  intro c _ c' _ hne
  refine Finset.disjoint_left.mpr ?_
  intro n hn hn'
  rw [mem_classSet_iff] at hn hn'
  exact hne (hn.2.symm.trans hn'.2)

lemma mem_class_I_iff {x y modulus residue z smoothCutoff n : ℕ} :
    n ∈ classSet FourClass.I x y modulus residue z smoothCutoff ↔
      n ∈ progressionWindow x y modulus residue ∧
        z < leastPrimeFactor (canonicalD n z) ^ 2 := by
  constructor
  · intro h
    rcases mem_classSet_iff.mp h with ⟨hwin, hc⟩
    by_cases hI : z < leastPrimeFactor (canonicalD n z) ^ 2
    · exact ⟨hwin, hI⟩
    · have hne : classify n z smoothCutoff ≠ FourClass.I := by
        simp only [classify, hI, if_false]
        split
        · simp
        · split <;> simp
      exact (hne hc).elim
  · rintro ⟨hwin, hI⟩
    exact mem_classSet_iff.mpr ⟨hwin, by simp [classify, hI]⟩

lemma mem_class_II_iff {x y modulus residue z smoothCutoff n : ℕ} :
    n ∈ classSet FourClass.II x y modulus residue z smoothCutoff ↔
      n ∈ progressionWindow x y modulus residue ∧
        leastPrimeFactor (canonicalD n z) ^ 2 ≤ z ∧
        canonicalB n z ^ 2 ≤ z := by
  constructor
  · intro h
    rcases mem_classSet_iff.mp h with ⟨hwin, hc⟩
    by_cases hI : z < leastPrimeFactor (canonicalD n z) ^ 2
    · simp [classify, hI] at hc
    · have hq : leastPrimeFactor (canonicalD n z) ^ 2 ≤ z := Nat.le_of_not_gt hI
      by_cases hII : canonicalB n z ^ 2 ≤ z
      · exact ⟨hwin, hq, hII⟩
      · have hne : classify n z smoothCutoff ≠ FourClass.II := by
          simp only [classify, hI, hII, if_false]
          split <;> simp
        exact (hne hc).elim
  · rintro ⟨hwin, hq, hb⟩
    have hI : ¬ z < leastPrimeFactor (canonicalD n z) ^ 2 := Nat.not_lt.mpr hq
    exact mem_classSet_iff.mpr ⟨hwin, by simp [classify, hI, hb]⟩

lemma mem_class_III_iff {x y modulus residue z smoothCutoff n : ℕ} :
    n ∈ classSet FourClass.III x y modulus residue z smoothCutoff ↔
      n ∈ progressionWindow x y modulus residue ∧
        leastPrimeFactor (canonicalD n z) ^ 2 ≤ z ∧
        z < canonicalB n z ^ 2 ∧
        leastPrimeFactor (canonicalD n z) ≤ smoothCutoff := by
  constructor
  · intro h
    rcases mem_classSet_iff.mp h with ⟨hwin, hc⟩
    by_cases hI : z < leastPrimeFactor (canonicalD n z) ^ 2
    · simp [classify, hI] at hc
    · have hq : leastPrimeFactor (canonicalD n z) ^ 2 ≤ z := Nat.le_of_not_gt hI
      by_cases hII : canonicalB n z ^ 2 ≤ z
      · simp [classify, hI, hII] at hc
      · have hb : z < canonicalB n z ^ 2 := Nat.lt_of_not_ge hII
        by_cases hIII : leastPrimeFactor (canonicalD n z) ≤ smoothCutoff
        · exact ⟨hwin, hq, hb, hIII⟩
        · simp [classify, hI, hII, hIII] at hc
  · rintro ⟨hwin, hq, hb, hsmall⟩
    have hI : ¬ z < leastPrimeFactor (canonicalD n z) ^ 2 := Nat.not_lt.mpr hq
    have hII : ¬ canonicalB n z ^ 2 ≤ z := Nat.not_le.mpr hb
    exact mem_classSet_iff.mpr ⟨hwin, by simp [classify, hI, hII, hsmall]⟩

lemma mem_class_IV_iff {x y modulus residue z smoothCutoff n : ℕ} :
    n ∈ classSet FourClass.IV x y modulus residue z smoothCutoff ↔
      n ∈ progressionWindow x y modulus residue ∧
        leastPrimeFactor (canonicalD n z) ^ 2 ≤ z ∧
        z < canonicalB n z ^ 2 ∧
        smoothCutoff < leastPrimeFactor (canonicalD n z) := by
  constructor
  · intro h
    rcases mem_classSet_iff.mp h with ⟨hwin, hc⟩
    by_cases hI : z < leastPrimeFactor (canonicalD n z) ^ 2
    · simp [classify, hI] at hc
    · have hq : leastPrimeFactor (canonicalD n z) ^ 2 ≤ z := Nat.le_of_not_gt hI
      by_cases hII : canonicalB n z ^ 2 ≤ z
      · simp [classify, hI, hII] at hc
      · have hb : z < canonicalB n z ^ 2 := Nat.lt_of_not_ge hII
        by_cases hIII : leastPrimeFactor (canonicalD n z) ≤ smoothCutoff
        · simp [classify, hI, hII, hIII] at hc
        · exact ⟨hwin, hq, hb, Nat.lt_of_not_ge hIII⟩
  · rintro ⟨hwin, hq, hb, hlarge⟩
    have hI : ¬ z < leastPrimeFactor (canonicalD n z) ^ 2 := Nat.not_lt.mpr hq
    have hII : ¬ canonicalB n z ^ 2 ≤ z := Nat.not_le.mpr hb
    have hIII : ¬ leastPrimeFactor (canonicalD n z) ≤ smoothCutoff := Nat.not_le.mpr hlarge
    exact mem_classSet_iff.mpr ⟨hwin, by simp [classify, hI, hII, hIII]⟩

/-- Every admissible integer belongs to exactly one of the four explicit
classes. -/
theorem exists_unique_class {x y modulus residue z smoothCutoff n : ℕ}
    (hn : n ∈ progressionWindow x y modulus residue) :
    ∃! c : FourClass, n ∈ classSet c x y modulus residue z smoothCutoff := by
  refine ⟨classify n z smoothCutoff, ?_, ?_⟩
  · simp [classSet, hn]
  · intro c hc
    exact (mem_classSet_iff.mp hc).2.symm

/-- Exact class partition identity for any commutative additive target. -/
theorem sum_four_classes {R : Type*} [AddCommMonoid R]
    (weight : ℕ → R) (x y modulus residue z smoothCutoff : ℕ) :
    ∑ n ∈ progressionWindow x y modulus residue, weight n =
      (∑ n ∈ classSet FourClass.I x y modulus residue z smoothCutoff, weight n) +
      (∑ n ∈ classSet FourClass.II x y modulus residue z smoothCutoff, weight n) +
      (∑ n ∈ classSet FourClass.III x y modulus residue z smoothCutoff, weight n) +
      (∑ n ∈ classSet FourClass.IV x y modulus residue z smoothCutoff, weight n)  := by
  classical
  rw [← Finset.sum_fiberwise
    (progressionWindow x y modulus residue)
    (fun n ↦ classify n z smoothCutoff) weight]
  rw [show (Finset.univ : Finset FourClass) =
      {FourClass.I, FourClass.II, FourClass.III, FourClass.IV} by decide]
  simp [classSet]
  ac_rfl


/-- Pure Section 5 inequality weld.  Its inputs are exactly the three
analytic outputs produced in Shiu's proof: (5.3), the combined (5.6), and
(5.8).  It does not assume the desired total progression estimate. -/
theorem section5_weld {x y modulus residue z smoothCutoff : ℕ}
    {weight : ℕ → ℝ} {main exceptional target : ℝ}
    (hI : ∑ n ∈ classSet FourClass.I x y modulus residue z smoothCutoff,
        weight n ≤ main)
    (hIIIII :
      (∑ n ∈ classSet FourClass.II x y modulus residue z smoothCutoff, weight n) +
      (∑ n ∈ classSet FourClass.III x y modulus residue z smoothCutoff, weight n) ≤
        exceptional)
    (hIV : ∑ n ∈ classSet FourClass.IV x y modulus residue z smoothCutoff,
        weight n ≤ main)
    (habsorb : 2 * main + exceptional ≤ target) :
    ∑ n ∈ progressionWindow x y modulus residue, weight n ≤ target := by
  rw [sum_four_classes]
  linarith

end

end ShiuSection5Split
