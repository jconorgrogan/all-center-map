import ShiuLemma1ClassIII
import ShiuLemma3TauMean
import ShiuSection5Structure
import ShiuSection5ScaleRounding
import ShiuEndToEndScaffold

/-!
# Shiu Section 5: classes II and III

This file formalizes the combined exceptional-class estimate on page 167 of
Shiu (1980), reusing the promoted prefix/suffix structure and the certified
fourth-power smooth-number bound.
-/

namespace ShiuClassIIIII

open ArithmeticFunction MixedMellinCert ShiuFoundation ShiuAnalyticLayer
  ShiuSection5Split ShiuSection5Structure
open scoped BigOperators ArithmeticFunction.zeta

noncomputable section

/-- Shiu's condition (ii), specialized exactly as on page 167: throughout the
range `n ≤ X < Z^90`, the divisor-square weight costs at most a fixed
multiple of `Z^(1/8)`.  The exponent is literal:
`(1/720) * 90 = 1/8`. -/
theorem exists_tauSquare_le_const_mul_Z_rpow_one_eighth
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧
      ∀ X Z n : ℕ, 0 < n → n ≤ X → X < Z ^ 90 →
        (tauAF k n ^ 2 : ℝ) ≤ C * (Z : ℝ) ^ (1 / 8 : ℝ) := by
  obtain ⟨C, hC, hsubpower⟩ :=
    tauAF_square_subpolynomial k hk (1 / 720 : ℝ) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro X Z n hn hnX hXZ
  have hZ : 0 < Z := by
    by_contra h
    have : Z = 0 := Nat.eq_zero_of_not_pos h
    simp [this] at hXZ
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hXR : (0 : ℝ) ≤ X := by positivity
  have hZX : (n : ℝ) ≤ X := by exact_mod_cast hnX
  have hXZr : (X : ℝ) ≤ (Z : ℝ) ^ (90 : ℕ) := by
    exact_mod_cast hXZ.le
  have hnXpow : (n : ℝ) ^ (1 / 720 : ℝ) ≤
      (X : ℝ) ^ (1 / 720 : ℝ) :=
    Real.rpow_le_rpow hnR hZX (by norm_num)
  have hXZpow : (X : ℝ) ^ (1 / 720 : ℝ) ≤
      ((Z : ℝ) ^ (90 : ℕ)) ^ (1 / 720 : ℝ) :=
    Real.rpow_le_rpow hXR hXZr (by norm_num)
  have hcollapse :
      ((Z : ℝ) ^ (90 : ℕ)) ^ (1 / 720 : ℝ) =
        (Z : ℝ) ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  calc
    (tauAF k n ^ 2 : ℝ) ≤ C * (n : ℝ) ^ (1 / 720 : ℝ) :=
      hsubpower n hn
    _ ≤ C * (X : ℝ) ^ (1 / 720 : ℝ) :=
      mul_le_mul_of_nonneg_left hnXpow hC.le
    _ ≤ C * (((Z : ℝ) ^ (90 : ℕ)) ^ (1 / 720 : ℝ)) :=
      mul_le_mul_of_nonneg_left hXZpow hC.le
    _ = C * (Z : ℝ) ^ (1 / 8 : ℝ) := by rw [hcollapse]

/-- The literal combined class-II/class-III cardinality.  Both summands are
the source-correct classes: their classifiers use `leastPrimeFactor
(canonicalD n Z)` and the squared natural cutoffs for `sqrt Z`. -/
def exceptionalCard
    (X Y modulus residue Z cutoff : ℕ) : ℕ :=
  (classSet FourClass.II X Y modulus residue Z cutoff).card +
    (classSet FourClass.III X Y modulus residue Z cutoff).card

/-- The real-valued exceptional mass, written as the two exact class sums
that appear on the left side of Shiu's equation (5.6). -/
def exceptionalMass
    (k X Y modulus residue Z cutoff : ℕ) : ℝ :=
  (∑ n ∈ classSet FourClass.II X Y modulus residue Z cutoff,
      (tauAF k n ^ 2 : ℝ)) +
    ∑ n ∈ classSet FourClass.III X Y modulus residue Z cutoff,
      (tauAF k n ^ 2 : ℝ)

/-- A prime dividing a product divides one of its factors. -/
lemma Nat.Prime.dvd_list_prod_iff {p : ℕ} (hp : p.Prime) (l : List ℕ) :
    p ∣ l.prod ↔ ∃ a ∈ l, p ∣ a := by
  induction l with
  | nil => simp [hp.not_dvd_one]
  | cons a l ih =>
      simp only [List.prod_cons, hp.dvd_mul, List.mem_cons, exists_eq_or_imp]
      rw [ih]

/-- In a strictly increasing list, the entry at `j` is at most every member
of the suffix beginning at `j`. -/
lemma getElem_le_of_mem_drop {l : List ℕ} (hpair : l.Pairwise (· < ·))
    {j : ℕ} (hj : j < l.length) {q : ℕ} (hq : q ∈ l.drop j) :
    l[j] ≤ q := by
  have hpw : (l.drop j).Pairwise (· < ·) := hpair.drop
  rw [List.drop_eq_getElem_cons hj] at hpw hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact le_rfl
  · exact ((List.pairwise_cons.mp hpw).1 q hq).le

/-- Every prime divisor of the suffix product is at least the boundary prime.
This is the exact ordered-prime fact needed both for `q(d_n)` and for class-III
smoothness. -/
theorem boundaryPrime_le_prime_dvd_suffix
    {n j p r : ℕ} (hj : j < (orderedPrimes n).length)
    (hp : p = (orderedPrimes n)[j]) (hr : r.Prime)
    (hrdvd : r ∣ (primePowerBlocks n |>.drop j).prod) :
    p ≤ r := by
  obtain ⟨a, haSuffix, hra⟩ :=
    (Nat.Prime.dvd_list_prod_iff hr
      (primePowerBlocks n |>.drop j)).mp hrdvd
  have haMap : a ∈
      (orderedPrimes n |>.drop j).map
        (fun q ↦ q ^ n.factorization q) := by
    simpa [primePowerBlocks] using haSuffix
  obtain ⟨q, hqSuffix, rfl⟩ := List.mem_map.mp haMap
  have hrdvdq : r ∣ q := hr.dvd_of_dvd_pow hra
  have hqPrime : q.Prime := by
    have hqAll : q ∈ orderedPrimes n := List.mem_of_mem_drop hqSuffix
    exact Nat.prime_of_mem_primeFactors (by
      rw [← orderedPrimes_toFinset]
      exact List.mem_toFinset.mpr hqAll)
  have hrq : r = q := (Nat.dvd_prime hqPrime).mp hrdvdq |>.resolve_left hr.ne_one
  subst q
  subst p
  exact getElem_le_of_mem_drop (by
    simpa [orderedPrimes] using n.primeFactors.sortedLT_sort.pairwise)
    hj hqSuffix

/-- For `n > Z`, the first prime in the canonical suffix is literally
`q(d_n)`, Shiu's least-prime-factor convention. -/
theorem exists_boundaryPrime_eq_leastPrimeFactor
    {n Z : ℕ} (hn : n ≠ 0) (hZ : 1 ≤ Z) (hZn : Z < n) :
    ∃ p e : ℕ,
      p.Prime ∧ e = n.factorization p ∧
      (orderedPrimes n)[canonicalIndex n Z]? = some p ∧
      (primePowerBlocks n)[canonicalIndex n Z]? = some (p ^ e) ∧
      leastPrimeFactor (canonicalD n Z) = p ∧
      p ^ e ∣ canonicalD n Z ∧
      Z < canonicalB n Z * p ^ e := by
  let j := canonicalIndex n Z
  have hjBlocks : j < (primePowerBlocks n).length :=
    canonicalIndex_lt_length_of_z_lt_n hn hZ hZn
  have hjPrimes : j < (orderedPrimes n).length := by
    simpa [primePowerBlocks] using hjBlocks
  let p := (orderedPrimes n)[j]
  let e := n.factorization p
  have hpMem : p ∈ orderedPrimes n := by
    exact List.get_mem _ ⟨j, hjPrimes⟩
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors (by
    rw [← orderedPrimes_toFinset]
    exact List.mem_toFinset.mpr hpMem)
  have hblock : (primePowerBlocks n)[j]? = some (p ^ e) := by
    rw [List.getElem?_eq_some_iff]
    refine ⟨hjBlocks, ?_⟩
    simp [primePowerBlocks, p, e]
  have hpOption : (orderedPrimes n)[j]? = some p := by
    exact List.getElem?_eq_getElem hjPrimes
  have hdrop : (primePowerBlocks n).drop j =
      p ^ e :: (primePowerBlocks n).drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hjBlocks]
    simp [primePowerBlocks, p, e]
  have hDeq : canonicalD n Z =
      p ^ e * ((primePowerBlocks n).drop (j + 1)).prod := by
    rw [canonicalD_eq_suffixProduct hn hZ, show canonicalIndex n Z = j from rfl,
      hdrop, List.prod_cons]
  have hpPowPos : 0 < p ^ e := pow_pos hpPrime.pos _
  have hDgt : 1 < canonicalD n Z := by
    have hepos : 0 < e := by
      exact hpPrime.factorization_pos_of_dvd hn
        (Nat.dvd_of_mem_primeFactors (by
          rw [← orderedPrimes_toFinset]
          exact List.mem_toFinset.mpr hpMem))
    have hpPowTwo : 2 ≤ p ^ e := by
      exact Nat.one_lt_pow hepos.ne' hpPrime.one_lt
    rw [hDeq]
    have htailPos : 0 < ((primePowerBlocks n).drop (j + 1)).prod := by
      apply List.prod_pos
      intro a ha
      have haAll : a ∈ primePowerBlocks n :=
        List.mem_of_mem_drop ha
      rw [primePowerBlocks] at haAll
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp haAll
      have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors (by
        rw [← orderedPrimes_toFinset]
        exact List.mem_toFinset.mpr hq)
      exact pow_pos hqPrime.pos _
    nlinarith
  have hpPowD : p ^ e ∣ canonicalD n Z := by
    rw [hDeq]
    exact dvd_mul_right _ _
  have hpD : p ∣ canonicalD n Z :=
    dvd_trans (dvd_pow_self p (by
      exact (hpPrime.factorization_pos_of_dvd hn
        (Nat.dvd_of_mem_primeFactors (by
          rw [← orderedPrimes_toFinset]
          exact List.mem_toFinset.mpr hpMem))).ne')) hpPowD
  have hminPrime : (canonicalD n Z).minFac.Prime :=
    Nat.minFac_prime hDgt.ne'
  have hpLeMin : p ≤ (canonicalD n Z).minFac := by
    apply boundaryPrime_le_prime_dvd_suffix hjPrimes rfl hminPrime
    rw [← canonicalD_eq_suffixProduct hn hZ]
    exact Nat.minFac_dvd _
  have hminLeP : (canonicalD n Z).minFac ≤ p :=
    Nat.minFac_le_of_dvd hpPrime.two_le hpD
  have hq : leastPrimeFactor (canonicalD n Z) = p := by
    simp [leastPrimeFactor, hDgt.ne', le_antisymm hminLeP hpLeMin]
  obtain ⟨a, ha, hcross⟩ := canonical_crossing hn hZ hZn
  have hae : a = p ^ e := by
    rw [hblock] at ha
    exact Option.some.inj ha.symm
  subst a
  exact ⟨p, e, hpPrime, rfl, by simpa [j] using hpOption,
    by simpa [j] using hblock, hq, hpPowD,
    by simpa [j] using hcross⟩

/-- Every prime divisor of the canonical prefix is strictly smaller than the
boundary prime beginning the suffix. -/
theorem prime_dvd_canonicalB_lt_boundaryPrime
    {n Z p r : ℕ} (hn : n ≠ 0) (hZ : 1 ≤ Z) (hZn : Z < n)
    (hp : (orderedPrimes n)[canonicalIndex n Z]? = some p)
    (hr : r.Prime) (hrB : r ∣ canonicalB n Z) :
    r < p := by
  let j := canonicalIndex n Z
  have hj : j < (orderedPrimes n).length := by
    simpa [primePowerBlocks] using
      canonicalIndex_lt_length_of_z_lt_n hn hZ hZn
  have hpEq : p = (orderedPrimes n)[j] := by
    have hget := List.getElem?_eq_getElem hj
    rw [show canonicalIndex n Z = j from rfl] at hp
    exact Option.some.inj (hp.symm.trans hget)
  have hrProd : r ∣
      ((orderedPrimes n).take j |>.map
        (fun q ↦ q ^ n.factorization q)).prod := by
    simpa [canonicalB, prefixProduct, primePowerBlocks, j] using hrB
  obtain ⟨a, ha, hra⟩ :=
    (Nat.Prime.dvd_list_prod_iff hr _).mp hrProd
  obtain ⟨qpow, hqTake, haq⟩ := List.mem_map.mp ha
  subst a
  have hrq : r ∣ qpow := hr.dvd_of_dvd_pow hra
  have hqAll : qpow ∈ orderedPrimes n :=
    List.mem_of_mem_take hqTake
  have hqPrime : qpow.Prime := Nat.prime_of_mem_primeFactors (by
    rw [← orderedPrimes_toFinset]
    exact List.mem_toFinset.mpr hqAll)
  have heq : r = qpow :=
    (Nat.dvd_prime hqPrime).mp hrq |>.resolve_left hr.ne_one
  subst qpow
  have hpw : (orderedPrimes n).Pairwise (· < ·) := by
    simpa [orderedPrimes] using n.primeFactors.sortedLT_sort.pairwise
  have happ :
      ((orderedPrimes n).take j ++ (orderedPrimes n).drop j).Pairwise
        (· < ·) := by
    simpa only [List.take_append_drop] using hpw
  have hboundaryMem : (orderedPrimes n)[j] ∈ (orderedPrimes n).drop j := by
    rw [List.drop_eq_getElem_cons hj]
    exact List.mem_cons_self
  have hlt := (List.pairwise_append.mp happ).2.2 r hqTake
    (orderedPrimes n)[j] hboundaryMem
  simpa [hpEq] using hlt

/-- The canonical class-III prefix is counted by Shiu's literal smooth-number
function: all of its prime divisors lie below `q(d_n)`, hence below the
logarithmic cutoff. -/
theorem canonicalB_mem_smoothNumbers_of_leastPrimeFactor_le
    {n Z cutoff : ℕ} (hn : n ≠ 0) (hZ : 1 ≤ Z) (hZn : Z < n)
    (hq : leastPrimeFactor (canonicalD n Z) ≤ cutoff) :
    canonicalB n Z ∈ Nat.smoothNumbers (cutoff + 1) := by
  obtain ⟨p, e, hpPrime, he, hpOption, hblock, hpq, hpPowD, hcross⟩ :=
    exists_boundaryPrime_eq_leastPrimeFactor hn hZ hZn
  rw [Nat.mem_smoothNumbers]
  refine ⟨(canonicalB_pos n Z).ne', ?_⟩
  intro r hr
  have hrPrime := Nat.prime_of_mem_primeFactorsList hr
  have hrB := Nat.dvd_of_mem_primeFactorsList hr
  have hrp : r < p := prime_dvd_canonicalB_lt_boundaryPrime hn hZ hZn
    hpOption hrPrime hrB
  rw [hpq] at hq
  omega

/-- Candidate prefixes in Shiu's class III, with the source inequalities
`sqrt Z < b ≤ Z`, the literal logarithmic smoothness cutoff, and the
coprimality forced by the primitive progression. -/
def classIIIPrefixes (Z cutoff modulus : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Z).filter fun b ↦
    Z < b ^ 2 ∧ b ∈ Nat.smoothNumbers (cutoff + 1) ∧ b.Coprime modulus

/-- One exact progression/divisibility fiber associated with a possible
class-III prefix. -/
def prefixFiber (X Y modulus residue b : ℕ) : Finset ℕ :=
  (Finset.Ioc (X - Y) X).filter fun n ↦
    n ≡ residue [MOD modulus] ∧ b ∣ n

/-- The large members of the literal class III are covered by the smooth
prefix fibers. -/
theorem classIII_large_subset_prefixCover
    {X Y modulus residue Z cutoff : ℕ}
    (hZ : 1 ≤ Z) (hcop : residue.Coprime modulus) :
    (classSet FourClass.III X Y modulus residue Z cutoff).filter
        (fun n ↦ Z < n) ⊆
      (classIIIPrefixes Z cutoff modulus).biUnion
        (prefixFiber X Y modulus residue) := by
  intro n hn
  have hnIII := (Finset.mem_filter.mp hn).1
  have hZn := (Finset.mem_filter.mp hn).2
  have hdata := mem_class_III_iff.mp hnIII
  let b := canonicalB n Z
  have hn0 : n ≠ 0 := by omega
  have hbmem : b ∈ classIIIPrefixes Z cutoff modulus := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨canonicalB_pos n Z, canonicalB_le hZ⟩,
      hdata.2.2.1, ?_, ?_⟩
    · exact canonicalB_mem_smoothNumbers_of_leastPrimeFactor_le hn0 hZ hZn
        hdata.2.2.2
    · have hnmod : n ≡ residue [MOD modulus] := by
        have hwin := hdata.1
        change n ∈ (Finset.Ioc (X - Y) X).filter
          (fun n ↦ n ≡ residue [MOD modulus]) at hwin
        exact (Finset.mem_filter.mp hwin).2
      have hncop : n.Coprime modulus :=
        ShiuSieveSlice.coprime_of_modEq_primitive hnmod hcop
      exact Nat.Coprime.of_dvd (canonicalB_dvd hn0 hZ) (dvd_refl modulus) hncop
  apply Finset.mem_biUnion.mpr
  refine ⟨b, hbmem, ?_⟩
  apply Finset.mem_filter.mpr
  have hwin := hdata.1
  change n ∈ (Finset.Ioc (X - Y) X).filter
    (fun n ↦ n ≡ residue [MOD modulus]) at hwin
  have hnIoc : n ∈ Finset.Ioc (X - Y) X := by
    exact (Finset.mem_filter.mp hwin).1
  have hnmod : n ≡ residue [MOD modulus] := by
    exact (Finset.mem_filter.mp hwin).2
  exact ⟨hnIoc, hnmod, canonicalB_dvd hn0 hZ⟩

/-- The candidate prefix set is a literal subset of the finite smooth-number
set certified by `ShiuLemma1ClassIII`. -/
theorem classIIIPrefixes_card_le_smoothCount
    (Z cutoff modulus : ℕ) :
    (classIIIPrefixes Z cutoff modulus).card ≤
      ShiuLemma1Rankin.smoothCount Z cutoff := by
  apply Finset.card_le_card
  intro b hb
  have hb' := Finset.mem_filter.mp hb
  exact Finset.mem_filter.mpr ⟨hb'.1, hb'.2.2.1⟩

/-- Fourth-power smooth-count control transfers to the actual class-III
prefix candidates, and is expressed as the real fourth-root inequality used
in (5.5). -/
theorem classIIIPrefixes_card_le_fourthRoot
    {Z cutoff modulus : ℕ}
    (hsmooth : ShiuLemma1Rankin.smoothCount Z cutoff ^ 4 ≤ Z) :
    ((classIIIPrefixes Z cutoff modulus).card : ℝ) ≤
      (Z : ℝ) ^ (1 / 4 : ℝ) := by
  have hcardPow : (classIIIPrefixes Z cutoff modulus).card ^ 4 ≤ Z :=
    (Nat.pow_le_pow_left (classIIIPrefixes_card_le_smoothCount Z cutoff modulus) 4).trans
      hsmooth
  rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
  apply (Real.le_rpow_inv_iff_of_pos
    (show (0 : ℝ) ≤ (classIIIPrefixes Z cutoff modulus).card by positivity)
    (show (0 : ℝ) ≤ Z by positivity) (show (0 : ℝ) < 4 by norm_num)).2
  exact_mod_cast hcardPow

/-- Exact CRT fiber count with its unit discrepancy. -/
theorem prefixFiber_card_le_density_add_one
    {X Y modulus residue b : ℕ}
    (hmod : 0 < modulus) (hb : 0 < b)
    (hcop : b.Coprime modulus) (hYX : Y ≤ X) :
    ((prefixFiber X Y modulus residue b).card : ℝ) ≤
      (Y : ℝ) / ((modulus : ℝ) * (b : ℝ)) + 1 := by
  have hdisc := ShiuSieveSlice.combined_filter_card_discrepancy_le_one
    X Y residue modulus b hmod hb hcop.symm hYX
  change
    |((prefixFiber X Y modulus residue b).card : ℝ) -
      (Y : ℝ) / ((modulus : ℝ) * (b : ℝ))| ≤ 1 at hdisc
  linarith [(abs_le.mp hdisc).2]

/-- Equation (5.5) before its final harmless `O(Z)` absorption: the certified
fourth-power smooth count gives the exact `Z^(1/4)` number of candidate
prefixes, while CRT gives `Y/(modulus*b)+1` per prefix. -/
theorem classIII_large_card_le
    {X Y modulus residue Z cutoff : ℕ}
    (hmod : 0 < modulus) (hcop : residue.Coprime modulus)
    (hYX : Y ≤ X) (hZ : 1 ≤ Z)
    (hsmooth : ShiuLemma1Rankin.smoothCount Z cutoff ^ 4 ≤ Z) :
    (((classSet FourClass.III X Y modulus residue Z cutoff).filter
        (fun n ↦ Z < n)).card : ℝ) ≤
      (Z : ℝ) ^ (1 / 4 : ℝ) *
        ((Y : ℝ) /
          ((modulus : ℝ) * (Z : ℝ) ^ (1 / 2 : ℝ)) + 1) := by
  let P := classIIIPrefixes Z cutoff modulus
  let F := prefixFiber X Y modulus residue
  have hsubset := classIII_large_subset_prefixCover
    (X := X) (Y := Y) (modulus := modulus) (residue := residue)
    (Z := Z) (cutoff := cutoff) hZ hcop
  have hcardNat :
      ((classSet FourClass.III X Y modulus residue Z cutoff).filter
          (fun n ↦ Z < n)).card ≤ (P.biUnion F).card :=
    Finset.card_le_card hsubset
  have hcoverNat : (P.biUnion F).card ≤ ∑ b ∈ P, (F b).card :=
    Finset.card_biUnion_le
  have hterm (b : ℕ) (hb : b ∈ P) :
      ((F b).card : ℝ) ≤
        (Y : ℝ) /
            ((modulus : ℝ) * (Z : ℝ) ^ (1 / 2 : ℝ)) + 1 := by
    have hbdata := (Finset.mem_filter.mp hb).2
    have hbpos : 0 < b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
    have hfiber := prefixFiber_card_le_density_add_one
      (X := X) (Y := Y) (modulus := modulus) (residue := residue) (b := b)
      hmod hbpos hbdata.2.2 hYX
    have hsqrtb : (Z : ℝ) ^ (1 / 2 : ℝ) < (b : ℝ) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
      apply (Real.rpow_inv_lt_iff_of_pos
        (show (0 : ℝ) ≤ Z by positivity)
        (show (0 : ℝ) ≤ b by positivity)
        (show (0 : ℝ) < 2 by norm_num)).2
      exact_mod_cast hbdata.1
    have hdenPos : 0 <
        (modulus : ℝ) * (Z : ℝ) ^ (1 / 2 : ℝ) := by
      apply mul_pos
      · exact_mod_cast hmod
      · exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < Z by omega)) _
    have hden :
        (modulus : ℝ) * (Z : ℝ) ^ (1 / 2 : ℝ) ≤
          (modulus : ℝ) * (b : ℝ) := by
      gcongr
    have hdiv := div_le_div_of_nonneg_left
      (by exact_mod_cast (Nat.zero_le Y) : (0 : ℝ) ≤ (Y : ℝ))
      hdenPos hden
    linarith
  have hsum :
      (∑ b ∈ P, ((F b).card : ℝ)) ≤
        ∑ _b ∈ P,
          ((Y : ℝ) /
            ((modulus : ℝ) * (Z : ℝ) ^ (1 / 2 : ℝ)) + 1) := by
    exact Finset.sum_le_sum hterm
  have hP := classIIIPrefixes_card_le_fourthRoot
    (modulus := modulus) hsmooth
  calc
    (((classSet FourClass.III X Y modulus residue Z cutoff).filter
        (fun n ↦ Z < n)).card : ℝ) ≤ ((P.biUnion F).card : ℝ) := by
      exact_mod_cast hcardNat
    _ ≤ (∑ b ∈ P, ((F b).card : ℝ)) := by
      exact_mod_cast hcoverNat
    _ ≤ ∑ _b ∈ P,
        ((Y : ℝ) /
          ((modulus : ℝ) * (Z : ℝ) ^ (1 / 2 : ℝ)) + 1) := hsum
    _ = (P.card : ℝ) *
        ((Y : ℝ) /
          ((modulus : ℝ) * (Z : ℝ) ^ (1 / 2 : ℝ)) + 1) := by
      simp
      ring
    _ ≤ (Z : ℝ) ^ (1 / 4 : ℝ) *
        ((Y : ℝ) /
          ((modulus : ℝ) * (Z : ℝ) ^ (1 / 2 : ℝ)) + 1) := by
      exact mul_le_mul_of_nonneg_right (by simpa [P] using hP) (by positivity)

/-- The members `n ≤ Z`, for which the canonical suffix can be empty, cost at
most the literal `O(Z)` term in (5.5). -/
theorem classIII_small_card_le_Z
    (X Y modulus residue Z cutoff : ℕ) :
    ((classSet FourClass.III X Y modulus residue Z cutoff).filter
        (fun n ↦ n ≤ Z)).card ≤ Z := by
  have hsubset :
      (classSet FourClass.III X Y modulus residue Z cutoff).filter
          (fun n ↦ n ≤ Z) ⊆ Finset.Icc 1 Z := by
    intro n hn
    have hnIII := (Finset.mem_filter.mp hn).1
    have hnZ := (Finset.mem_filter.mp hn).2
    have hwin := (mem_class_III_iff.mp hnIII).1
    change n ∈ (Finset.Ioc (X - Y) X).filter
      (fun n ↦ n ≡ residue [MOD modulus]) at hwin
    have hnIoc := Finset.mem_Ioc.mp (Finset.mem_filter.mp hwin).1
    exact Finset.mem_Icc.mpr ⟨by omega, hnZ⟩
  have hcard := Finset.card_le_card hsubset
  simpa using hcard

/-- Literal class-III cardinal estimate (5.5), including the small-`n`
`O(Z)` term that is normally absorbed asymptotically. -/
theorem classIII_card_le_raw
    {X Y modulus residue Z cutoff : ℕ}
    (hmod : 0 < modulus) (hcop : residue.Coprime modulus)
    (hYX : Y ≤ X) (hZ : 1 ≤ Z)
    (hsmooth : ShiuLemma1Rankin.smoothCount Z cutoff ^ 4 ≤ Z) :
    ((classSet FourClass.III X Y modulus residue Z cutoff).card : ℝ) ≤
      (Z : ℝ) +
        (Z : ℝ) ^ (1 / 4 : ℝ) *
          ((Y : ℝ) /
            ((modulus : ℝ) * (Z : ℝ) ^ (1 / 2 : ℝ)) + 1) := by
  let S := classSet FourClass.III X Y modulus residue Z cutoff
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := S) (fun n ↦ n ≤ Z)
  have hsmall := classIII_small_card_le_Z X Y modulus residue Z cutoff
  have hlarge := classIII_large_card_le hmod hcop hYX hZ hsmooth
  have hsplit' :
      ((S.filter fun n ↦ n ≤ Z).card : ℝ) +
        ((S.filter fun n ↦ Z < n).card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast (by simpa only [Nat.not_le] using hsplit)
  have hsmall' : ((S.filter fun n ↦ n ≤ Z).card : ℝ) ≤ Z := by
    exact_mod_cast hsmall
  simpa [S] using (show
    (S.card : ℝ) ≤
      (Z : ℝ) +
        (Z : ℝ) ^ (1 / 4 : ℝ) *
          ((Y : ℝ) /
            ((modulus : ℝ) * (Z : ℝ) ^ (1 / 2 : ℝ)) + 1) by
      rw [← hsplit']
      exact add_le_add hsmall' hlarge)

/-- The certified fourth-power smooth theorem supplies the exact cutoff and
scale assumptions needed by the raw class-III estimate. -/
theorem exists_classIII_card_le_raw_certified :
    ∃ Z₀ : ℕ, 2 ≤ Z₀ ∧
      ∀ X Y modulus residue Z : ℕ,
        Z₀ ≤ Z → Z ≤ X → X < Z ^ 90 →
        0 < modulus → residue.Coprime modulus → Y ≤ X →
        ((classSet FourClass.III X Y modulus residue Z
            (ShiuLemma1ClassIII.classIIICutoff X)).card : ℝ) ≤
          (Z : ℝ) +
            (Z : ℝ) ^ (1 / 4 : ℝ) *
              ((Y : ℝ) /
                ((modulus : ℝ) * (Z : ℝ) ^ (1 / 2 : ℝ)) + 1) := by
  obtain ⟨Z₀, hZ₀, hsmooth⟩ :=
    ShiuLemma1ClassIII.exists_classIII_smoothCount_pow_four
  refine ⟨Z₀, hZ₀, ?_⟩
  intro X Y modulus residue Z hZ₀Z hZX hXZ hmod hcop hYX
  exact classIII_card_le_raw hmod hcop hYX (by omega)
    (hsmooth X Z hZ₀Z hZX hXZ)

/-- Exact class-II structural witness from the canonical crossing block.  The
base prime is literally `q(d_n)`, hence `p² ≤ Z`; the complete boundary block
divides `n` and lies strictly above `sqrt Z`. -/
theorem classII_member_has_large_boundary_primePower
    {X Y modulus residue Z cutoff n : ℕ}
    (hZ : 1 ≤ Z) (hZn : Z < n)
    (hnII : n ∈ classSet FourClass.II X Y modulus residue Z cutoff) :
    ∃ p e : ℕ,
      p.Prime ∧ p ^ e ∣ n ∧ p ^ 2 ≤ Z ∧ Z < (p ^ e) ^ 2 := by
  have hdata := mem_class_II_iff.mp hnII
  have hn0 : n ≠ 0 := by omega
  obtain ⟨p, e, hp, he, hpOption, hblock, hpq, hpPowD, hcross⟩ :=
    exists_boundaryPrime_eq_leastPrimeFactor hn0 hZ hZn
  have hpPowN : p ^ e ∣ n := by
    rw [← canonicalB_mul_canonicalD hn0 hZ]
    exact dvd_mul_of_dvd_right hpPowD _
  have hpSq : p ^ 2 ≤ Z := by
    rw [hpq] at hdata
    exact hdata.2.1
  have hpowSq : Z < (p ^ e) ^ 2 := by
    by_contra h
    have hpowSqLe : (p ^ e) ^ 2 ≤ Z := Nat.le_of_not_gt h
    have hprodSqLe :
        (canonicalB n Z) ^ 2 * (p ^ e) ^ 2 ≤ Z * Z :=
      Nat.mul_le_mul hdata.2.2 hpowSqLe
    have hprodSqGt : Z * Z <
        (canonicalB n Z * p ^ e) * (canonicalB n Z * p ^ e) :=
      Nat.mul_self_lt_mul_self hcross
    nlinarith [hprodSqLe, hprodSqGt]
  exact ⟨p, e, hp, hpPowN, hpSq, hpowSq⟩

/-- The finite set of prime powers occurring in the class-II overcount (5.4).
The coprimality restriction is forced by the primitive progression. -/
def classIIPrimePowers (Z X modulus : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc 2 X).filter fun a ↦
      a.Coprime modulus ∧
        ∃ p e : ℕ, p.Prime ∧ a = p ^ e ∧ p ^ 2 ≤ Z ∧ Z < a ^ 2 ∧
          ∀ j < e, (p ^ j) ^ 2 ≤ Z

/-- The exact reciprocal least-threshold prime-power inequality isolated by
Shiu immediately before (5.4).  Unlike the desired progression estimate, this
contains no residue class, interval fiber, or divisor weight. -/
def ClassIIReciprocalLeastThresholdTailEstimate : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ Z X modulus : ℕ, 2 ≤ Z → Z ≤ X →
      (∑ a ∈ classIIPrimePowers Z X modulus, (a : ℝ)⁻¹) ≤
        C * (Z : ℝ) ^ (-1 / 4 : ℝ)

/-- The pair of exact elementary tail outputs consumed by (5.4).  The
candidate-count half is certified below; only the preceding reciprocal-sum
statement remains analytic. -/
def ClassIIPrimePowerTailEstimate : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ Z X modulus : ℕ, 2 ≤ Z → Z ≤ X →
      (∑ a ∈ classIIPrimePowers Z X modulus, (a : ℝ)⁻¹) ≤
          C * (Z : ℝ) ^ (-1 / 4 : ℝ) ∧
        ((classIIPrimePowers Z X modulus).card : ℝ) ≤
          C * (Z : ℝ) ^ (1 / 2 : ℝ)

/-- Distinct least-threshold prime powers have distinct base primes, so the
unit-error term has at most `sqrt Z` candidates. -/
theorem classIIPrimePowers_card_le_sqrt
    {Z X modulus : ℕ} (hZ : 2 ≤ Z) :
    (classIIPrimePowers Z X modulus).card ≤ Nat.sqrt Z := by
  classical
  let P := classIIPrimePowers Z X modulus
  have hbase (a : ℕ) (ha : a ∈ P) :
      a.minFac ∈ Finset.Icc 2 (Nat.sqrt Z) := by
    have hdata := (Finset.mem_filter.mp ha).2.2
    obtain ⟨p, e, hp, haeq, hpSq, haLarge, hmin⟩ := hdata
    have he : e ≠ 0 := by
      intro he0
      subst e
      simp at haeq
      subst a
      norm_num at haLarge
      omega
    have hfac : a.minFac = p := by
      rw [haeq, hp.pow_minFac he]
    rw [hfac]
    exact Finset.mem_Icc.mpr ⟨hp.two_le, (Nat.le_sqrt.mpr (by
      simpa [pow_two] using hpSq))⟩
  have hinj : Set.InjOn Nat.minFac (P : Set ℕ) := by
    intro a ha b hb hab
    have haData := (Finset.mem_filter.mp ha).2.2
    have hbData := (Finset.mem_filter.mp hb).2.2
    obtain ⟨p, e, hp, haeq, hpSq, haLarge, haMin⟩ := haData
    obtain ⟨q, f, hq, hbeq, hqSq, hbLarge, hbMin⟩ := hbData
    have he : e ≠ 0 := by
      intro he0
      subst e
      simp at haeq
      subst a
      norm_num at haLarge
      omega
    have hf : f ≠ 0 := by
      intro hf0
      subst f
      simp at hbeq
      subst b
      norm_num at hbLarge
      omega
    have hpq : p = q := by
      have hap : a.minFac = p := by rw [haeq, hp.pow_minFac he]
      have hbq : b.minFac = q := by rw [hbeq, hq.pow_minFac hf]
      omega
    subst q
    have hef : e = f := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hef | hfe
      · have := hbMin e hef
        rw [haeq] at haLarge
        omega
      · have := haMin f hfe
        rw [hbeq] at hbLarge
        omega
    subst f
    simpa [haeq, hbeq]
  have himage : P.image Nat.minFac ⊆ Finset.Icc 2 (Nat.sqrt Z) := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact hbase a ha
  have hcardImage := Finset.card_le_card himage
  have hIcc : (Finset.Icc 2 (Nat.sqrt Z)).card ≤ Nat.sqrt Z := by
    rw [Nat.card_Icc]
    omega
  calc
    P.card = (P.image Nat.minFac).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 2 (Nat.sqrt Z)).card := hcardImage
    _ ≤ Nat.sqrt Z := hIcc

/-- The certified candidate count welds any proof of Shiu's reciprocal tail
into the exact two-part tail interface used by the class-II fiber estimate. -/
theorem classIIPrimePowerTailEstimate_of_reciprocal
    (hrecip : ClassIIReciprocalLeastThresholdTailEstimate) :
    ClassIIPrimePowerTailEstimate := by
  obtain ⟨C, hC, hrecip⟩ := hrecip
  refine ⟨max C 1, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro Z X modulus hZ hZX
  constructor
  · have h := hrecip Z X modulus hZ hZX
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left C 1)
      (Real.rpow_nonneg (by positivity) _))
  · have hcardNat := classIIPrimePowers_card_le_sqrt
      (X := X) (modulus := modulus) hZ
    have hcardSqrt :
        ((classIIPrimePowers Z X modulus).card : ℝ) ≤ Nat.sqrt Z := by
      exact_mod_cast hcardNat
    have hsqrtRpow :
        ((Nat.sqrt Z : ℕ) : ℝ) ≤ (Z : ℝ) ^ (1 / 2 : ℝ) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
      apply (Real.le_rpow_inv_iff_of_pos
        (show (0 : ℝ) ≤ Nat.sqrt Z by positivity)
        (show (0 : ℝ) ≤ Z by positivity)
        (show (0 : ℝ) < 2 by norm_num)).2
      exact_mod_cast (by simpa [pow_two] using Nat.sqrt_le Z)
    calc
      ((classIIPrimePowers Z X modulus).card : ℝ) ≤ Nat.sqrt Z := hcardSqrt
      _ ≤ (Z : ℝ) ^ (1 / 2 : ℝ) := hsqrtRpow
      _ ≤ max C 1 * (Z : ℝ) ^ (1 / 2 : ℝ) := by
        nth_rewrite 1 [← one_mul ((Z : ℝ) ^ (1 / 2 : ℝ))]
        exact mul_le_mul_of_nonneg_right (le_max_right C 1)
          (Real.rpow_nonneg (by positivity) _)

/-- Shiu's elementary fourth-root split proves the reciprocal
least-threshold prime-power tail with the explicit constant `3`.  Small base
primes contribute at most `Z^(1/4) / Z^(1/2)`.  Above the fourth root,
minimality forces exponent two, and `sum_Ioc_inv_sq_le_sub` is the formal
telescoping estimate for the remaining inverse squares. -/
theorem certifiedClassIIReciprocalLeastThresholdTailEstimate :
    ClassIIReciprocalLeastThresholdTailEstimate := by
  classical
  refine ⟨3, by norm_num, ?_⟩
  intro Z X modulus hZ hZX
  let P := classIIPrimePowers Z X modulus
  let R : ℝ := (Z : ℝ) ^ (1 / 4 : ℝ)
  let Q : ℕ := ⌊R⌋₊
  let S := P.filter fun a ↦ a.minFac ≤ Q
  let L := P.filter fun a ↦ Q < a.minFac
  have hZR : 0 < R := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < Z by omega)) _
  have hRone : 1 ≤ R := by
    exact Real.one_le_rpow (by exact_mod_cast (show 1 ≤ Z by omega)) (by norm_num)
  have hQone : 1 ≤ Q := by
    exact Nat.le_floor (by exact_mod_cast hRone)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQone)
  have hinj : Set.InjOn Nat.minFac (P : Set ℕ) := by
    intro a ha b hb hab
    have haData := (Finset.mem_filter.mp ha).2.2
    have hbData := (Finset.mem_filter.mp hb).2.2
    obtain ⟨p, e, hp, haeq, hpSq, haLarge, haMin⟩ := haData
    obtain ⟨q, f, hq, hbeq, hqSq, hbLarge, hbMin⟩ := hbData
    have he : e ≠ 0 := by
      intro he0
      subst e
      simp at haeq
      subst a
      norm_num at haLarge
      omega
    have hf : f ≠ 0 := by
      intro hf0
      subst f
      simp at hbeq
      subst b
      norm_num at hbLarge
      omega
    have hpq : p = q := by
      have hap : a.minFac = p := by rw [haeq, hp.pow_minFac he]
      have hbq : b.minFac = q := by rw [hbeq, hq.pow_minFac hf]
      omega
    subst q
    have hef : e = f := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hef | hfe
      · have hle := hbMin e hef
        rw [haeq] at haLarge
        omega
      · have hle := haMin f hfe
        rw [hbeq] at hbLarge
        omega
    subst f
    simpa [haeq, hbeq]
  have hSsubset : S ⊆ P := Finset.filter_subset _ _
  have hLsubset : L ⊆ P := Finset.filter_subset _ _
  have hinjS' : Set.InjOn Nat.minFac (S : Set ℕ) := by
    intro a ha b hb hab
    exact hinj (hSsubset ha) (hSsubset hb) hab
  have hinjL : Set.InjOn Nat.minFac (L : Set ℕ) := by
    intro a ha b hb hab
    exact hinj (hLsubset ha) (hLsubset hb) hab
  have hSimage : S.image Nat.minFac ⊆ Finset.Icc 2 Q := by
    intro p hp
    obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp hp
    have haP := hSsubset haS
    have hbase := (Finset.mem_filter.mp haS).2
    have hdata := (Finset.mem_filter.mp haP).2.2
    obtain ⟨q, e, hq, haeq, hqSq, haLarge, haMin⟩ := hdata
    have he : e ≠ 0 := by
      intro he0
      subst e
      simp at haeq
      subst a
      norm_num at haLarge
      omega
    have hfac : a.minFac = q := by rw [haeq, hq.pow_minFac he]
    exact Finset.mem_Icc.mpr ⟨by rw [hfac]; exact hq.two_le, hbase⟩
  have hScard : S.card ≤ Q := by
    have hcardImage := Finset.card_le_card hSimage
    have hIcc : (Finset.Icc 2 Q).card ≤ Q := by
      rw [Nat.card_Icc]
      omega
    calc
      S.card = (S.image Nat.minFac).card :=
        (Finset.card_image_of_injOn hinjS').symm
      _ ≤ (Finset.Icc 2 Q).card := hcardImage
      _ ≤ Q := hIcc
  have hSterm (a : ℕ) (ha : a ∈ S) :
      (a : ℝ)⁻¹ ≤ (Z : ℝ) ^ (-1 / 2 : ℝ) := by
    have haP := hSsubset ha
    have haIcc := (Finset.mem_filter.mp haP).1
    have haPos : (0 : ℝ) < a := by
      exact_mod_cast (show 0 < a by
        have := (Finset.mem_Icc.mp haIcc).1
        omega)
    have haLarge := (Finset.mem_filter.mp haP).2.2.choose_spec.choose_spec.2.2.2.1
    have hsqrtLt : (Z : ℝ) ^ (1 / 2 : ℝ) < (a : ℝ) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
      apply (Real.rpow_inv_lt_iff_of_pos
        (show (0 : ℝ) ≤ Z by positivity)
        (show (0 : ℝ) ≤ a by positivity)
        (show (0 : ℝ) < 2 by norm_num)).2
      exact_mod_cast haLarge
    have hsqrtPos : 0 < (Z : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < Z by omega)) _
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_neg (show (0 : ℝ) ≤ Z by positivity)]
    exact (inv_le_inv₀ haPos hsqrtPos).2 hsqrtLt.le
  have hSsum0 := Finset.sum_le_card_nsmul S
    (fun a : ℕ ↦ (a : ℝ)⁻¹) ((Z : ℝ) ^ (-1 / 2 : ℝ)) hSterm
  have hSsum :
      (∑ a ∈ S, (a : ℝ)⁻¹) ≤ (Z : ℝ) ^ (-1 / 4 : ℝ) := by
    have hScardR : (S.card : ℝ) ≤ Q := by exact_mod_cast hScard
    have hQleR : (Q : ℝ) ≤ R := Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    calc
      (∑ a ∈ S, (a : ℝ)⁻¹) ≤
          (S.card : ℝ) * (Z : ℝ) ^ (-1 / 2 : ℝ) := by
        simpa [nsmul_eq_mul] using hSsum0
      _ ≤ (Q : ℝ) * (Z : ℝ) ^ (-1 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hScardR (Real.rpow_nonneg (by positivity) _)
      _ ≤ R * (Z : ℝ) ^ (-1 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hQleR (Real.rpow_nonneg (by positivity) _)
      _ = (Z : ℝ) ^ (-1 / 4 : ℝ) := by
        dsimp [R]
        rw [← Real.rpow_add (by exact_mod_cast (show 0 < Z by omega))]
        norm_num
  have hLterm (a : ℕ) (ha : a ∈ L) :
      (a : ℝ)⁻¹ = (((a.minFac : ℕ) : ℝ) ^ 2)⁻¹ := by
    have haP := hLsubset ha
    have hQfac := (Finset.mem_filter.mp ha).2
    have hdata := (Finset.mem_filter.mp haP).2.2
    obtain ⟨p, e, hp, haeq, hpSq, haLarge, haMin⟩ := hdata
    have he : e ≠ 0 := by
      intro he0
      subst e
      simp at haeq
      subst a
      norm_num at haLarge
      omega
    have hfac : a.minFac = p := by rw [haeq, hp.pow_minFac he]
    have hRltp : R < (p : ℝ) := by
      have hQltp : Q < p := by simpa [hfac] using hQfac
      exact (Nat.floor_lt (Real.rpow_nonneg (by positivity) _)).mp hQltp
    have hZp4 : Z < p ^ 4 := by
      have h := (Real.rpow_inv_lt_iff_of_pos
        (show (0 : ℝ) ≤ Z by positivity)
        (show (0 : ℝ) ≤ p by positivity)
        (show (0 : ℝ) < 4 by norm_num)).1 (by
          simpa [R, show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num] using hRltp)
      exact_mod_cast h
    have heTwoLe : e ≤ 2 := by
      by_contra h
      have htwo : 2 < e := Nat.lt_of_not_ge h
      have hp4Le := haMin 2 htwo
      have heq : (p ^ 2) ^ 2 = p ^ 4 := by ring
      rw [heq] at hp4Le
      omega
    have hTwoLe : 2 ≤ e := by
      by_contra h
      have heLeOne : e ≤ 1 := by omega
      have heOne : e = 1 := by omega
      subst e
      simp at haeq
      rw [haeq] at haLarge
      simpa [pow_two] using (not_lt_of_ge hpSq haLarge)
    have heTwo : e = 2 := by omega
    rw [haeq, heTwo, hp.pow_minFac (by norm_num : 2 ≠ 0)]
    norm_num
  have hLimage : L.image Nat.minFac ⊆ Finset.Ioc Q X := by
    intro p hp
    obtain ⟨a, haL, rfl⟩ := Finset.mem_image.mp hp
    have haP := hLsubset haL
    have hQp := (Finset.mem_filter.mp haL).2
    have haX := (Finset.mem_Icc.mp (Finset.mem_filter.mp haP).1).2
    have hdata := (Finset.mem_filter.mp haP).2.2
    obtain ⟨p, e, hpPrime, haeq, hpSq, haLarge, haMin⟩ := hdata
    have he : e ≠ 0 := by
      intro he0
      subst e
      simp at haeq
      subst a
      norm_num at haLarge
      omega
    have hfac : a.minFac = p := by rw [haeq, hpPrime.pow_minFac he]
    have hpLeA : p ≤ a := by
      rw [haeq]
      have hePos : 1 ≤ e := by omega
      have hdvd : p ^ 1 ∣ p ^ e := pow_dvd_pow p hePos
      exact Nat.le_of_dvd (pow_pos hpPrime.pos _) (by simpa using hdvd)
    exact Finset.mem_Ioc.mpr ⟨hQp, by simpa [hfac] using hpLeA.trans haX⟩
  have hLeq :
      (∑ a ∈ L, (a : ℝ)⁻¹) =
        ∑ p ∈ L.image Nat.minFac, ((p : ℝ) ^ 2)⁻¹ := by
    rw [Finset.sum_image hinjL]
    exact Finset.sum_congr rfl hLterm
  have hQleZ : Q ≤ Z := by
    have hRleZ : R ≤ (Z : ℝ) :=
      Real.rpow_le_self_of_one_le
        (by exact_mod_cast (show 1 ≤ Z by omega)) (by norm_num)
    have hQleR : (Q : ℝ) ≤ R := Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    exact_mod_cast hQleR.trans hRleZ
  have hQleX : Q ≤ X := hQleZ.trans hZX
  have hLsum :
      (∑ a ∈ L, (a : ℝ)⁻¹) ≤
        2 * (Z : ℝ) ^ (-1 / 4 : ℝ) := by
    have hsubsetSum :
        (∑ p ∈ L.image Nat.minFac, ((p : ℝ) ^ 2)⁻¹) ≤
          ∑ p ∈ Finset.Ioc Q X, ((p : ℝ) ^ 2)⁻¹ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hLimage (by
        intro i hi hin
        positivity)
    have htel := sum_Ioc_inv_sq_le_sub
      (α := ℝ) (show Q ≠ 0 by omega) hQleX
    have htailQ :
        (∑ p ∈ Finset.Ioc Q X, ((p : ℝ) ^ 2)⁻¹) ≤ (Q : ℝ)⁻¹ :=
      htel.trans (sub_le_self _ (by positivity))
    have hRltQ : R < (Q : ℝ) + 1 := Nat.lt_floor_add_one R
    have hRhalfLeQ : R / 2 ≤ (Q : ℝ) := by
      have hQcast : (1 : ℝ) ≤ Q := by exact_mod_cast hQone
      linarith
    have hRhalfPos : 0 < R / 2 := div_pos hZR (by norm_num)
    have hinv : (Q : ℝ)⁻¹ ≤ (R / 2)⁻¹ :=
      (inv_le_inv₀ hQpos hRhalfPos).2 hRhalfLeQ
    have hinvR : (R / 2)⁻¹ = 2 * (Z : ℝ) ^ (-1 / 4 : ℝ) := by
      rw [inv_div]
      dsimp [R]
      rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by norm_num,
        Real.rpow_neg (show (0 : ℝ) ≤ Z by positivity)]
      ring
    calc
      (∑ a ∈ L, (a : ℝ)⁻¹) =
          ∑ p ∈ L.image Nat.minFac, ((p : ℝ) ^ 2)⁻¹ := hLeq
      _ ≤ ∑ p ∈ Finset.Ioc Q X, ((p : ℝ) ^ 2)⁻¹ := hsubsetSum
      _ ≤ (Q : ℝ)⁻¹ := htailQ
      _ ≤ (R / 2)⁻¹ := hinv
      _ = 2 * (Z : ℝ) ^ (-1 / 4 : ℝ) := hinvR
  have hsplit := Finset.sum_filter_add_sum_filter_not P
    (fun a ↦ a.minFac ≤ Q) (fun a ↦ (a : ℝ)⁻¹)
  have hsplit' :
      (∑ a ∈ S, (a : ℝ)⁻¹) + (∑ a ∈ L, (a : ℝ)⁻¹) =
        ∑ a ∈ P, (a : ℝ)⁻¹ := by
    simpa [S, L, Nat.not_le] using hsplit
  rw [← hsplit']
  calc
    (∑ a ∈ S, (a : ℝ)⁻¹) + (∑ a ∈ L, (a : ℝ)⁻¹) ≤
        (Z : ℝ) ^ (-1 / 4 : ℝ) +
          2 * (Z : ℝ) ^ (-1 / 4 : ℝ) := add_le_add hSsum hLsum
    _ = 3 * (Z : ℝ) ^ (-1 / 4 : ℝ) := by ring

/-- Fully certified two-part tail input for the class-II estimate. -/
theorem certifiedClassIIPrimePowerTailEstimate :
    ClassIIPrimePowerTailEstimate :=
  classIIPrimePowerTailEstimate_of_reciprocal
    certifiedClassIIReciprocalLeastThresholdTailEstimate

/-- Elementary absorption of the four powers left after multiplying the raw
(5.6) bound by the progression modulus.  This is deliberately stated over
reals so the later natural-number adapter is only a cast. -/
theorem classIIIII_raw_expression_absorption
    {z q y Cweight Ctail : ℝ}
    (hz : 1 ≤ z) (hq : 0 < q) (hy : 0 ≤ y)
    (hCweight : 0 ≤ Cweight) (hCtail : 0 ≤ Ctail)
    (hqz : q * z ^ 2 ≤ y) :
    q * (Cweight * z ^ (1 / 8 : ℝ) *
      ((z + Ctail * (y / q * z ^ (-1 / 4 : ℝ) +
          z ^ (1 / 2 : ℝ))) +
        (z + z ^ (1 / 4 : ℝ) *
          (y / (q * z ^ (1 / 2 : ℝ)) + 1)))) ≤
      (Cweight * (4 + 2 * Ctail)) * y := by
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hA : z ^ (1 / 8 : ℝ) ≤ z := by
    simpa using Real.rpow_le_self_of_one_le hz (by norm_num : (1 / 8 : ℝ) ≤ 1)
  have hB : z ^ (1 / 4 : ℝ) ≤ z := by
    simpa using Real.rpow_le_self_of_one_le hz (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hD : z ^ (1 / 2 : ℝ) ≤ z := by
    simpa using Real.rpow_le_self_of_one_le hz (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hAE :
      z ^ (1 / 8 : ℝ) * z ^ (-1 / 4 : ℝ) ≤ 1 := by
    rw [← Real.rpow_add hzpos]
    exact Real.rpow_le_one_of_one_le_of_nonpos hz (by norm_num)
  have hABD :
      z ^ (1 / 8 : ℝ) * z ^ (1 / 4 : ℝ) ≤
        z ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hzpos]
    exact Real.rpow_le_rpow_of_exponent_le hz (by norm_num)
  have hDpos : 0 < z ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hzpos _
  have h1 : q * z ^ (1 / 8 : ℝ) * z ≤ y := by
    calc
      q * z ^ (1 / 8 : ℝ) * z ≤ q * z * z := by gcongr
      _ = q * z ^ 2 := by ring
      _ ≤ y := hqz
  have h2density :
      q * z ^ (1 / 8 : ℝ) *
          (y / q * z ^ (-1 / 4 : ℝ)) ≤ y := by
    have heq :
        q * z ^ (1 / 8 : ℝ) *
            (y / q * z ^ (-1 / 4 : ℝ)) =
          y * (z ^ (1 / 8 : ℝ) * z ^ (-1 / 4 : ℝ)) := by
      field_simp [ne_of_gt hq]
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hAE hy]
  have h2unit :
      q * z ^ (1 / 8 : ℝ) * z ^ (1 / 2 : ℝ) ≤ y := by
    calc
      q * z ^ (1 / 8 : ℝ) * z ^ (1 / 2 : ℝ) ≤ q * z * z := by
        gcongr
      _ = q * z ^ 2 := by ring
      _ ≤ y := hqz
  have h3density :
      q * z ^ (1 / 8 : ℝ) * z ^ (1 / 4 : ℝ) *
          (y / (q * z ^ (1 / 2 : ℝ))) ≤ y := by
    have heq :
        q * z ^ (1 / 8 : ℝ) * z ^ (1 / 4 : ℝ) *
            (y / (q * z ^ (1 / 2 : ℝ))) =
          y * ((z ^ (1 / 8 : ℝ) * z ^ (1 / 4 : ℝ)) /
            z ^ (1 / 2 : ℝ)) := by
      field_simp [ne_of_gt hq, ne_of_gt hDpos]
    rw [heq]
    have hratio :
        (z ^ (1 / 8 : ℝ) * z ^ (1 / 4 : ℝ)) /
            z ^ (1 / 2 : ℝ) ≤ 1 :=
      (div_le_one hDpos).2 hABD
    simpa using mul_le_mul_of_nonneg_left hratio hy
  have h3unit :
      q * z ^ (1 / 8 : ℝ) * z ^ (1 / 4 : ℝ) ≤ y := by
    calc
      q * z ^ (1 / 8 : ℝ) * z ^ (1 / 4 : ℝ) ≤ q * z * z := by
        gcongr
      _ = q * z ^ 2 := by ring
      _ ≤ y := hqz
  have hinside :
      ((q * z ^ (1 / 8 : ℝ) * z +
          Ctail *
            (q * z ^ (1 / 8 : ℝ) *
                (y / q * z ^ (-1 / 4 : ℝ)) +
              q * z ^ (1 / 8 : ℝ) * z ^ (1 / 2 : ℝ))) +
        (q * z ^ (1 / 8 : ℝ) * z +
          (q * z ^ (1 / 8 : ℝ) * z ^ (1 / 4 : ℝ) *
              (y / (q * z ^ (1 / 2 : ℝ))) +
            q * z ^ (1 / 8 : ℝ) * z ^ (1 / 4 : ℝ)))) ≤
        (4 + 2 * Ctail) * y := by
    have htailPair :
        Ctail *
            (q * z ^ (1 / 8 : ℝ) *
                (y / q * z ^ (-1 / 4 : ℝ)) +
              q * z ^ (1 / 8 : ℝ) * z ^ (1 / 2 : ℝ)) ≤
          Ctail * (y + y) :=
      mul_le_mul_of_nonneg_left (add_le_add h2density h2unit) hCtail
    have hlastPair := add_le_add h3density h3unit
    nlinarith
  have heq :
      q * (Cweight * z ^ (1 / 8 : ℝ) *
        ((z + Ctail * (y / q * z ^ (-1 / 4 : ℝ) +
            z ^ (1 / 2 : ℝ))) +
          (z + z ^ (1 / 4 : ℝ) *
            (y / (q * z ^ (1 / 2 : ℝ)) + 1)))) =
        Cweight *
          (((q * z ^ (1 / 8 : ℝ) * z +
              Ctail *
                (q * z ^ (1 / 8 : ℝ) *
                    (y / q * z ^ (-1 / 4 : ℝ)) +
                  q * z ^ (1 / 8 : ℝ) * z ^ (1 / 2 : ℝ))) +
            (q * z ^ (1 / 8 : ℝ) * z +
              (q * z ^ (1 / 8 : ℝ) * z ^ (1 / 4 : ℝ) *
                  (y / (q * z ^ (1 / 2 : ℝ))) +
                q * z ^ (1 / 8 : ℝ) * z ^ (1 / 4 : ℝ))))) := by
    ring
  rw [heq]
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left hinside hCweight

/-- The large members of literal class II are covered by the exact
prime-power divisibility fibers used in (5.4). -/
theorem classII_large_subset_primePowerCover
    {X Y modulus residue Z cutoff : ℕ}
    (hZ : 2 ≤ Z) (hcop : residue.Coprime modulus) :
    (classSet FourClass.II X Y modulus residue Z cutoff).filter
        (fun n ↦ Z < n) ⊆
      (classIIPrimePowers Z X modulus).biUnion
        (prefixFiber X Y modulus residue) := by
  classical
  intro n hn
  have hnII := (Finset.mem_filter.mp hn).1
  have hZn := (Finset.mem_filter.mp hn).2
  have hdata := mem_class_II_iff.mp hnII
  have hwin := hdata.1
  change n ∈ (Finset.Ioc (X - Y) X).filter
    (fun n ↦ n ≡ residue [MOD modulus]) at hwin
  have hnIoc := (Finset.mem_filter.mp hwin).1
  have hnmod := (Finset.mem_filter.mp hwin).2
  have hn0 : n ≠ 0 := by omega
  obtain ⟨p, e, hp, hpPowN, hpSq, hlarge⟩ :=
    classII_member_has_large_boundary_primePower (show 1 ≤ Z by omega) hZn hnII
  let hex : ∃ s : ℕ, Z < (p ^ s) ^ 2 := ⟨e, hlarge⟩
  let s := Nat.find hex
  let a := p ^ s
  have hsLarge : Z < (p ^ s) ^ 2 := Nat.find_spec hex
  have hsLe : s ≤ e := Nat.find_min' hex hlarge
  have hsMin : ∀ j < s, (p ^ j) ^ 2 ≤ Z := by
    intro j hj
    exact Nat.le_of_not_gt (Nat.find_min hex hj)
  have haPowDiv : a ∣ p ^ e := by
    exact pow_dvd_pow p hsLe
  have haDivN : a ∣ n := haPowDiv.trans hpPowN
  have haPos : 0 < a := pow_pos hp.pos _
  have haLeN : a ≤ n := Nat.le_of_dvd (by omega) haDivN
  have haLeX : a ≤ X := haLeN.trans (Finset.mem_Ioc.mp hnIoc).2
  have haTwo : 2 ≤ a := by
    change Z < a ^ 2 at hsLarge
    by_contra h
    have haLt : a < 2 := Nat.lt_of_not_ge h
    have haEq : a = 1 := by omega
    rw [haEq] at hsLarge
    norm_num at hsLarge
    omega
  have hncop : n.Coprime modulus :=
    ShiuSieveSlice.coprime_of_modEq_primitive hnmod hcop
  have hacop : a.Coprime modulus :=
    Nat.Coprime.of_dvd haDivN (dvd_refl modulus) hncop
  have hamem : a ∈ classIIPrimePowers Z X modulus := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨haTwo, haLeX⟩, hacop,
      ⟨p, s, hp, rfl, hpSq, hsLarge, hsMin⟩⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨a, hamem, ?_⟩
  exact Finset.mem_filter.mpr ⟨hnIoc, hnmod, haDivN⟩

/-- The literal class-II large-part estimate (5.4), conditional only on the
two elementary bounds for Shiu's reciprocal least-threshold prime-power tail.
The displayed terms are exactly the density contribution and the unit-error
contribution of the CRT fibers. -/
theorem classII_large_card_le_of_primePowerTail
    {X Y modulus residue Z cutoff : ℕ} {C : ℝ}
    (hmod : 0 < modulus) (hcop : residue.Coprime modulus)
    (hYX : Y ≤ X) (hZ : 2 ≤ Z)
    (htail :
      (∑ a ∈ classIIPrimePowers Z X modulus, (a : ℝ)⁻¹) ≤
        C * (Z : ℝ) ^ (-1 / 4 : ℝ))
    (hcount : ((classIIPrimePowers Z X modulus).card : ℝ) ≤
      C * (Z : ℝ) ^ (1 / 2 : ℝ)) :
    (((classSet FourClass.II X Y modulus residue Z cutoff).filter
        (fun n ↦ Z < n)).card : ℝ) ≤
      C * ((Y : ℝ) / (modulus : ℝ) *
          (Z : ℝ) ^ (-1 / 4 : ℝ) +
        (Z : ℝ) ^ (1 / 2 : ℝ)) := by
  classical
  let P := classIIPrimePowers Z X modulus
  let F := prefixFiber X Y modulus residue
  have hsubset := classII_large_subset_primePowerCover
    (X := X) (Y := Y) (modulus := modulus) (residue := residue)
    (Z := Z) (cutoff := cutoff) hZ hcop
  have hcardNat :
      ((classSet FourClass.II X Y modulus residue Z cutoff).filter
          (fun n ↦ Z < n)).card ≤ (P.biUnion F).card :=
    Finset.card_le_card hsubset
  have hcoverNat : (P.biUnion F).card ≤ ∑ a ∈ P, (F a).card :=
    Finset.card_biUnion_le
  have hterm (a : ℕ) (ha : a ∈ P) :
      ((F a).card : ℝ) ≤
        (Y : ℝ) / ((modulus : ℝ) * (a : ℝ)) + 1 := by
    have hadata := (Finset.mem_filter.mp ha).2
    have hapos : 0 < a := by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
      omega
    exact prefixFiber_card_le_density_add_one
      (X := X) (Y := Y) (modulus := modulus) (residue := residue) (b := a)
      hmod hapos hadata.1 hYX
  have hsum :
      (∑ a ∈ P, ((F a).card : ℝ)) ≤
        ∑ a ∈ P,
          ((Y : ℝ) / ((modulus : ℝ) * (a : ℝ)) + 1) :=
    Finset.sum_le_sum hterm
  have hsumIdentity :
      (∑ a ∈ P,
          ((Y : ℝ) / ((modulus : ℝ) * (a : ℝ)) + 1)) =
        (Y : ℝ) / (modulus : ℝ) *
            (∑ a ∈ P, (a : ℝ)⁻¹) + (P.card : ℝ) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    simp only [mul_one]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have ha0 : (a : ℝ) ≠ 0 := by
      have haTwo := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
      positivity
    have hm0 : (modulus : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmod)
    field_simp
  have hYmod : 0 ≤ (Y : ℝ) / (modulus : ℝ) := by positivity
  have hbound :
      (Y : ℝ) / (modulus : ℝ) *
            (∑ a ∈ P, (a : ℝ)⁻¹) + (P.card : ℝ) ≤
        (Y : ℝ) / (modulus : ℝ) *
            (C * (Z : ℝ) ^ (-1 / 4 : ℝ)) +
          C * (Z : ℝ) ^ (1 / 2 : ℝ) := by
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left
      · simpa [P] using htail
      · exact hYmod
    · simpa [P] using hcount
  calc
    (((classSet FourClass.II X Y modulus residue Z cutoff).filter
        (fun n ↦ Z < n)).card : ℝ) ≤ ((P.biUnion F).card : ℝ) := by
      exact_mod_cast hcardNat
    _ ≤ (∑ a ∈ P, ((F a).card : ℝ)) := by
      exact_mod_cast hcoverNat
    _ ≤ ∑ a ∈ P,
        ((Y : ℝ) / ((modulus : ℝ) * (a : ℝ)) + 1) := hsum
    _ = (Y : ℝ) / (modulus : ℝ) *
          (∑ a ∈ P, (a : ℝ)⁻¹) + (P.card : ℝ) := hsumIdentity
    _ ≤ (Y : ℝ) / (modulus : ℝ) *
          (C * (Z : ℝ) ^ (-1 / 4 : ℝ)) +
        C * (Z : ℝ) ^ (1 / 2 : ℝ) := hbound
    _ = C * ((Y : ℝ) / (modulus : ℝ) *
          (Z : ℝ) ^ (-1 / 4 : ℝ) +
        (Z : ℝ) ^ (1 / 2 : ℝ)) := by ring

/-- The `n ≤ Z` part of class II is the literal harmless small-number term. -/
theorem classII_small_card_le_Z
    (X Y modulus residue Z cutoff : ℕ) :
    ((classSet FourClass.II X Y modulus residue Z cutoff).filter
        (fun n ↦ n ≤ Z)).card ≤ Z := by
  have hsubset :
      (classSet FourClass.II X Y modulus residue Z cutoff).filter
          (fun n ↦ n ≤ Z) ⊆ Finset.Icc 1 Z := by
    intro n hn
    have hnII := (Finset.mem_filter.mp hn).1
    have hnZ := (Finset.mem_filter.mp hn).2
    have hwin := (mem_class_II_iff.mp hnII).1
    change n ∈ (Finset.Ioc (X - Y) X).filter
      (fun n ↦ n ≡ residue [MOD modulus]) at hwin
    have hnIoc := Finset.mem_Ioc.mp (Finset.mem_filter.mp hwin).1
    exact Finset.mem_Icc.mpr ⟨by omega, hnZ⟩
  simpa using Finset.card_le_card hsubset

/-- Equation (5.4), with the explicit `n ≤ Z` term retained, follows from
the exact reciprocal prime-power tail and candidate-count bounds. -/
theorem classII_card_le_raw_of_primePowerTail
    {X Y modulus residue Z cutoff : ℕ} {C : ℝ}
    (hmod : 0 < modulus) (hcop : residue.Coprime modulus)
    (hYX : Y ≤ X) (hZ : 2 ≤ Z)
    (htail :
      (∑ a ∈ classIIPrimePowers Z X modulus, (a : ℝ)⁻¹) ≤
        C * (Z : ℝ) ^ (-1 / 4 : ℝ))
    (hcount : ((classIIPrimePowers Z X modulus).card : ℝ) ≤
      C * (Z : ℝ) ^ (1 / 2 : ℝ)) :
    ((classSet FourClass.II X Y modulus residue Z cutoff).card : ℝ) ≤
      (Z : ℝ) +
        C * ((Y : ℝ) / (modulus : ℝ) *
            (Z : ℝ) ^ (-1 / 4 : ℝ) +
          (Z : ℝ) ^ (1 / 2 : ℝ)) := by
  let S := classSet FourClass.II X Y modulus residue Z cutoff
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := S) (fun n ↦ n ≤ Z)
  have hsmall := classII_small_card_le_Z X Y modulus residue Z cutoff
  have hlarge := classII_large_card_le_of_primePowerTail
    (cutoff := cutoff) hmod hcop hYX hZ htail hcount
  have hsplit' :
      ((S.filter fun n ↦ n ≤ Z).card : ℝ) +
        ((S.filter fun n ↦ Z < n).card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast (by simpa only [Nat.not_le] using hsplit)
  have hsmall' : ((S.filter fun n ↦ n ≤ Z).card : ℝ) ≤ Z := by
    exact_mod_cast hsmall
  simpa [S] using (show
    (S.card : ℝ) ≤
      (Z : ℝ) +
        C * ((Y : ℝ) / (modulus : ℝ) *
            (Z : ℝ) ^ (-1 / 4 : ℝ) +
          (Z : ℝ) ^ (1 / 2 : ℝ)) by
      rw [← hsplit']
      exact add_le_add hsmall' hlarge)

/-- Uniform literal class-II (5.4), exposing only Shiu's elementary
prime-power-tail estimate as an assumption. -/
theorem exists_classII_card_le_raw_of_primePowerTail
    (hTail : ClassIIPrimePowerTailEstimate) :
    ∃ C : ℝ, 0 < C ∧
      ∀ X Y modulus residue Z cutoff : ℕ,
        Z ≤ X → 0 < modulus → residue.Coprime modulus → Y ≤ X → 2 ≤ Z →
        ((classSet FourClass.II X Y modulus residue Z cutoff).card : ℝ) ≤
          (Z : ℝ) +
            C * ((Y : ℝ) / (modulus : ℝ) *
                (Z : ℝ) ^ (-1 / 4 : ℝ) +
              (Z : ℝ) ^ (1 / 2 : ℝ)) := by
  obtain ⟨C, hC, htail⟩ := hTail
  refine ⟨C, hC, ?_⟩
  intro X Y modulus residue Z cutoff hZX hmod hcop hYX hZ
  obtain ⟨hsum, hcount⟩ := htail Z X modulus hZ hZX
  exact classII_card_le_raw_of_primePowerTail
    hmod hcop hYX hZ hsum hcount

/-- A uniform pointwise bound converts the literal combined exceptional
cardinality to the literal divisor-square mass. -/
theorem exceptionalMass_le_pointwise_mul_card
    {k X Y modulus residue Z cutoff : ℕ} {W : ℝ}
    (hpoint : ∀ n ∈
      classSet FourClass.II X Y modulus residue Z cutoff ∪
        classSet FourClass.III X Y modulus residue Z cutoff,
      (tauAF k n ^ 2 : ℝ) ≤ W) :
    exceptionalMass k X Y modulus residue Z cutoff ≤
      W * exceptionalCard X Y modulus residue Z cutoff := by
  have hII :
      (∑ n ∈ classSet FourClass.II X Y modulus residue Z cutoff,
          (tauAF k n ^ 2 : ℝ)) ≤
        ∑ _n ∈ classSet FourClass.II X Y modulus residue Z cutoff, W := by
    apply Finset.sum_le_sum
    intro n hn
    exact hpoint n (Finset.mem_union_left _ hn)
  have hIII :
      (∑ n ∈ classSet FourClass.III X Y modulus residue Z cutoff,
          (tauAF k n ^ 2 : ℝ)) ≤
        ∑ _n ∈ classSet FourClass.III X Y modulus residue Z cutoff, W := by
    apply Finset.sum_le_sum
    intro n hn
    exact hpoint n (Finset.mem_union_right _ hn)
  calc
    exceptionalMass k X Y modulus residue Z cutoff ≤
        (∑ _n ∈ classSet FourClass.II X Y modulus residue Z cutoff, W) +
          ∑ _n ∈ classSet FourClass.III X Y modulus residue Z cutoff, W :=
      add_le_add hII hIII
    _ = W * exceptionalCard X Y modulus residue Z cutoff := by
      simp [exceptionalCard]
      ring

/-- Certified use of Shiu's condition (ii): before any counting estimate, the
combined exceptional mass is bounded by `Z^(1/8)` times its exact cardinality.
This is the deterministic weighted half of (5.6). -/
theorem exists_exceptionalMass_le_Z_rpow_mul_card
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧
      ∀ X Y modulus residue Z cutoff : ℕ,
        1 ≤ Z → X < Z ^ 90 →
        exceptionalMass k X Y modulus residue Z cutoff ≤
          C * (Z : ℝ) ^ (1 / 8 : ℝ) *
            exceptionalCard X Y modulus residue Z cutoff := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_tauSquare_le_const_mul_Z_rpow_one_eighth k hk
  refine ⟨C, hC, ?_⟩
  intro X Y modulus residue Z cutoff hZ hXZ
  apply exceptionalMass_le_pointwise_mul_card
  intro n hn
  have hn' : n ∈ progressionWindow X Y modulus residue := by
    rcases Finset.mem_union.mp hn with hnII | hnIII
    · exact (mem_class_II_iff.mp hnII).1
    · exact (mem_class_III_iff.mp hnIII).1
  have hnIoc : n ∈ Finset.Ioc (X - Y) X := by
    change n ∈ (Finset.Ioc (X - Y) X).filter
      (fun n ↦ n ≡ residue [MOD modulus]) at hn'
    exact (Finset.mem_filter.mp hn').1
  have hnrange := Finset.mem_Ioc.mp hnIoc
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hnrange.1
  exact hpoint X Z n hnpos hnrange.2 hXZ

/-- The literal class-II plus class-III weld behind (5.6).  No desired
progression estimate is assumed: the sole open input is the reciprocal
least-threshold prime-power tail used immediately before (5.4), while the
class-III fourth-power smooth count and condition (ii) are certified theorems.

The two `Z` summands retain the finite small-`n` correction.  The remaining
four displayed powers are exactly those in (5.4), (5.5), and the `Z^(1/8)`
weight loss preceding (5.6). -/
theorem exists_classIIIII56_raw_of_primePowerTail
    (k : ℕ) (hk : 1 ≤ k) (hTail : ClassIIPrimePowerTailEstimate) :
    ∃ Cweight Ctail : ℝ, 0 < Cweight ∧ 0 < Ctail ∧
      ∃ Z₀ : ℕ, 2 ≤ Z₀ ∧
        ∀ X Y modulus residue Z : ℕ,
          Z₀ ≤ Z → Z ≤ X → X < Z ^ 90 →
          0 < modulus → residue.Coprime modulus → Y ≤ X →
          exceptionalMass k X Y modulus residue Z
              (ShiuLemma1ClassIII.classIIICutoff X) ≤
            Cweight * (Z : ℝ) ^ (1 / 8 : ℝ) *
              (((Z : ℝ) +
                  Ctail * ((Y : ℝ) / (modulus : ℝ) *
                      (Z : ℝ) ^ (-1 / 4 : ℝ) +
                    (Z : ℝ) ^ (1 / 2 : ℝ))) +
                ((Z : ℝ) +
                  (Z : ℝ) ^ (1 / 4 : ℝ) *
                    ((Y : ℝ) /
                        ((modulus : ℝ) *
                          (Z : ℝ) ^ (1 / 2 : ℝ)) + 1))) := by
  obtain ⟨Cweight, hCweight, hweight⟩ :=
    exists_exceptionalMass_le_Z_rpow_mul_card k hk
  obtain ⟨Ctail, hCtail, htail⟩ := hTail
  obtain ⟨Z₀, hZ₀, hsmooth⟩ :=
    ShiuLemma1ClassIII.exists_classIII_smoothCount_pow_four
  refine ⟨Cweight, Ctail, hCweight, hCtail, Z₀, hZ₀, ?_⟩
  intro X Y modulus residue Z hZ₀Z hZX hXZ hmod hcop hYX
  obtain ⟨htailSum, htailCount⟩ := htail Z X modulus
    (hZ₀.trans hZ₀Z) hZX
  have hII := classII_card_le_raw_of_primePowerTail
    (cutoff := ShiuLemma1ClassIII.classIIICutoff X)
    hmod hcop hYX (hZ₀.trans hZ₀Z) htailSum htailCount
  have hIII := classIII_card_le_raw
    (cutoff := ShiuLemma1ClassIII.classIIICutoff X)
    hmod hcop hYX (by omega) (hsmooth X Z hZ₀Z hZX hXZ)
  have hcard :
      (exceptionalCard X Y modulus residue Z
          (ShiuLemma1ClassIII.classIIICutoff X) : ℝ) ≤
        (((Z : ℝ) +
            Ctail * ((Y : ℝ) / (modulus : ℝ) *
                (Z : ℝ) ^ (-1 / 4 : ℝ) +
              (Z : ℝ) ^ (1 / 2 : ℝ))) +
          ((Z : ℝ) +
            (Z : ℝ) ^ (1 / 4 : ℝ) *
              ((Y : ℝ) /
                  ((modulus : ℝ) * (Z : ℝ) ^ (1 / 2 : ℝ)) + 1))) := by
    simpa [exceptionalCard, Nat.cast_add] using add_le_add hII hIII
  have hmass := hweight X Y modulus residue Z
    (ShiuLemma1ClassIII.classIIICutoff X) (by omega) hXZ
  exact hmass.trans (mul_le_mul_of_nonneg_left hcard (by positivity))

/-- The same literal weld with Shiu's rounded choice
`Z = ceil (Y^(1/30))` and the exact logarithmic floor cutoff exposed in the
statement.  The three scale hypotheses are deliberately explicit: the
end-to-end Section-5 adapter derives them from its eventual `X` threshold. -/
theorem exists_classIIIII56_ceiling_of_primePowerTail
    (k : ℕ) (hk : 1 ≤ k) (hTail : ClassIIPrimePowerTailEstimate) :
    ∃ Cweight Ctail : ℝ, 0 < Cweight ∧ 0 < Ctail ∧
      ∃ Z₀ : ℕ, 2 ≤ Z₀ ∧
        ∀ X Y modulus residue : ℕ,
          Z₀ ≤ ShiuClassIBound.sectionFiveZ Y →
          ShiuClassIBound.sectionFiveZ Y ≤ X →
          X < ShiuClassIBound.sectionFiveZ Y ^ 90 →
          0 < modulus → residue.Coprime modulus → Y ≤ X →
          exceptionalMass k X Y modulus residue
              (ShiuClassIBound.sectionFiveZ Y)
              (ShiuClassIBound.smoothCutoff X) ≤
            Cweight *
              (ShiuClassIBound.sectionFiveZ Y : ℝ) ^ (1 / 8 : ℝ) *
              ((((ShiuClassIBound.sectionFiveZ Y : ℕ) : ℝ) +
                  Ctail * ((Y : ℝ) / (modulus : ℝ) *
                      (ShiuClassIBound.sectionFiveZ Y : ℝ) ^
                        (-1 / 4 : ℝ) +
                    (ShiuClassIBound.sectionFiveZ Y : ℝ) ^
                      (1 / 2 : ℝ))) +
                (((ShiuClassIBound.sectionFiveZ Y : ℕ) : ℝ) +
                  (ShiuClassIBound.sectionFiveZ Y : ℝ) ^
                      (1 / 4 : ℝ) *
                    ((Y : ℝ) /
                        ((modulus : ℝ) *
                          (ShiuClassIBound.sectionFiveZ Y : ℝ) ^
                            (1 / 2 : ℝ)) + 1))) := by
  obtain ⟨Cweight, Ctail, hCweight, hCtail, Z₀, hZ₀, hraw⟩ :=
    exists_classIIIII56_raw_of_primePowerTail k hk hTail
  refine ⟨Cweight, Ctail, hCweight, hCtail, Z₀, hZ₀, ?_⟩
  intro X Y modulus residue hZ₀ hZX hXZ hmod hcop hYX
  simpa [ShiuClassIBound.smoothCutoff,
    ShiuLemma1ClassIII.classIIICutoff] using
      hraw X Y modulus residue (ShiuClassIBound.sectionFiveZ Y)
        hZ₀ hZX hXZ hmod hcop hYX

/-- Unconditional source-structured class-II/class-III estimate at an
arbitrary legal Section-5 scale. -/
theorem exists_classIIIII56_raw (k : ℕ) (hk : 1 ≤ k) :
    ∃ Cweight Ctail : ℝ, 0 < Cweight ∧ 0 < Ctail ∧
      ∃ Z₀ : ℕ, 2 ≤ Z₀ ∧
        ∀ X Y modulus residue Z : ℕ,
          Z₀ ≤ Z → Z ≤ X → X < Z ^ 90 →
          0 < modulus → residue.Coprime modulus → Y ≤ X →
          exceptionalMass k X Y modulus residue Z
              (ShiuLemma1ClassIII.classIIICutoff X) ≤
            Cweight * (Z : ℝ) ^ (1 / 8 : ℝ) *
              (((Z : ℝ) +
                  Ctail * ((Y : ℝ) / (modulus : ℝ) *
                      (Z : ℝ) ^ (-1 / 4 : ℝ) +
                    (Z : ℝ) ^ (1 / 2 : ℝ))) +
                ((Z : ℝ) +
                  (Z : ℝ) ^ (1 / 4 : ℝ) *
                    ((Y : ℝ) /
                        ((modulus : ℝ) *
                          (Z : ℝ) ^ (1 / 2 : ℝ)) + 1))) :=
  exists_classIIIII56_raw_of_primePowerTail k hk
    certifiedClassIIPrimePowerTailEstimate

/-- Unconditional absorbed consequence of (5.6), with the source's logarithmic
floor cutoff and the robust ceiling choice `Z = ceil (Y^(1/30))`. -/
theorem exists_classIIIII56_ceiling (k : ℕ) (hk : 1 ≤ k) :
    ∃ Cweight Ctail : ℝ, 0 < Cweight ∧ 0 < Ctail ∧
      ∃ Z₀ : ℕ, 2 ≤ Z₀ ∧
        ∀ X Y modulus residue : ℕ,
          Z₀ ≤ ShiuClassIBound.sectionFiveZ Y →
          ShiuClassIBound.sectionFiveZ Y ≤ X →
          X < ShiuClassIBound.sectionFiveZ Y ^ 90 →
          0 < modulus → residue.Coprime modulus → Y ≤ X →
          exceptionalMass k X Y modulus residue
              (ShiuClassIBound.sectionFiveZ Y)
              (ShiuClassIBound.smoothCutoff X) ≤
            Cweight *
              (ShiuClassIBound.sectionFiveZ Y : ℝ) ^ (1 / 8 : ℝ) *
              ((((ShiuClassIBound.sectionFiveZ Y : ℕ) : ℝ) +
                  Ctail * ((Y : ℝ) / (modulus : ℝ) *
                      (ShiuClassIBound.sectionFiveZ Y : ℝ) ^
                        (-1 / 4 : ℝ) +
                    (ShiuClassIBound.sectionFiveZ Y : ℝ) ^
                      (1 / 2 : ℝ))) +
                (((ShiuClassIBound.sectionFiveZ Y : ℕ) : ℝ) +
                  (ShiuClassIBound.sectionFiveZ Y : ℝ) ^
                      (1 / 4 : ℝ) *
                    ((Y : ℝ) /
                        ((modulus : ℝ) *
                          (ShiuClassIBound.sectionFiveZ Y : ℝ) ^
                            (1 / 2 : ℝ)) + 1))) :=
  exists_classIIIII56_ceiling_of_primePowerTail k hk
    certifiedClassIIPrimePowerTailEstimate

/-- The unconditional natural-number class contract consumed by
`ShiuEndToEnd.SectionFiveClassEstimates`.  All additional inequalities are
absorbed into one explicit eventual threshold; the runtime hypotheses are
exactly the legal Section-5 range. -/
theorem certifiedClassIIIII56Estimate :
    ShiuEndToEnd.ClassIIIII56Estimate := by
  intro k hk
  obtain ⟨Cweight, Ctail, hCweight, hCtail, Z₀, hZ₀, hraw⟩ :=
    exists_classIIIII56_raw k hk
  let Kreal : ℝ := Cweight * (4 + 2 * Ctail)
  let C : ℕ := ⌈Kreal⌉₊
  let X₀ : ℕ := max ShiuClassIBound.sectionFiveFinalAbsorptionThreshold
    ((Z₀ ^ 30) ^ 3)
  have hKreal : 0 < Kreal := by
    dsimp [Kreal]
    positivity
  have hC : 0 < C := Nat.ceil_pos.mpr hKreal
  have hX₀ : 2 ≤ X₀ := by
    apply le_trans (show 2 ≤ ShiuClassIBound.sectionFiveFinalAbsorptionThreshold by
      norm_num [ShiuClassIBound.sectionFiveFinalAbsorptionThreshold])
    exact le_max_left _ _
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X Y modulus residue hX hmod hresidue hcop hYX hXY hmodcube
  let Z := ShiuClassIBound.sectionFiveZ Y
  have hFinal : ShiuClassIBound.sectionFiveFinalAbsorptionThreshold ≤ X :=
    (le_max_left _ _).trans hX
  have hZ₀cube : (Z₀ ^ 30) ^ 3 ≤ X :=
    (le_max_right _ _).trans hX
  have hZ₀powYcube : (Z₀ ^ 30) ^ 3 < Y ^ 3 :=
    hZ₀cube.trans_lt hXY
  have hZ₀powY : Z₀ ^ 30 < Y :=
    (Nat.pow_lt_pow_iff_left (by decide : (3 : ℕ) ≠ 0)).mp hZ₀powYcube
  have hZ₀root :
      (Z₀ : ℝ) ≤ (Y : ℝ) ^ (1 / 30 : ℝ) := by
    rw [show (1 / 30 : ℝ) = (30 : ℝ)⁻¹ by norm_num]
    apply (Real.le_rpow_inv_iff_of_pos
      (show (0 : ℝ) ≤ Z₀ by positivity)
      (show (0 : ℝ) ≤ Y by positivity)
      (show (0 : ℝ) < 30 by norm_num)).2
    exact_mod_cast hZ₀powY.le
  have hZ₀Z : Z₀ ≤ Z := by
    have hceil := Nat.le_ceil ((Y : ℝ) ^ (1 / 30 : ℝ))
    exact_mod_cast hZ₀root.trans hceil
  have hScaleThreshold :
      ShiuClassIBound.sectionFiveScaleThreshold ≤
        ShiuClassIBound.sectionFiveFinalAbsorptionThreshold := by
    unfold ShiuClassIBound.sectionFiveScaleThreshold
      ShiuClassIBound.sectionFiveFinalAbsorptionThreshold
    exact Nat.pow_le_pow_left
      (Nat.pow_le_pow_left (by norm_num : (4 : ℕ) ≤ 9) 30) 3
  have hscale := ShiuClassIBound.sectionFive_classI_scale_package
    (hScaleThreshold.trans hFinal) hYX hXY hmod hmodcube
  dsimp only at hscale
  obtain ⟨hZone, hXZ, hsieve, hfibers⟩ := hscale
  have habs := ShiuClassIBound.sectionFive_classI_final_absorption_package
    hFinal hXY hmodcube
  dsimp only at habs
  obtain ⟨hZY, hlog, hmodZsq⟩ := habs
  have hZX : Z ≤ X := hZY.trans hYX
  have hraw' := hraw X Y modulus residue Z hZ₀Z hZX hXZ hmod hcop hYX
  have hmodZsqR :
      (modulus : ℝ) * (Z : ℝ) ^ 2 ≤ (Y : ℝ) := by
    exact_mod_cast hmodZsq
  have habsorb := classIIIII_raw_expression_absorption
    (z := (Z : ℝ)) (q := (modulus : ℝ)) (y := (Y : ℝ))
    (Cweight := Cweight) (Ctail := Ctail)
    (by exact_mod_cast hZone) (by exact_mod_cast hmod)
    (by positivity) hCweight.le hCtail.le hmodZsqR
  have hmassR :
      (modulus : ℝ) *
          exceptionalMass k X Y modulus residue Z
            (ShiuLemma1ClassIII.classIIICutoff X) ≤
        Kreal * (Y : ℝ) := by
    calc
      (modulus : ℝ) *
          exceptionalMass k X Y modulus residue Z
            (ShiuLemma1ClassIII.classIIICutoff X) ≤
          (modulus : ℝ) *
            (Cweight * (Z : ℝ) ^ (1 / 8 : ℝ) *
              ((((Z : ℕ) : ℝ) +
                  Ctail * ((Y : ℝ) / (modulus : ℝ) *
                      (Z : ℝ) ^ (-1 / 4 : ℝ) +
                    (Z : ℝ) ^ (1 / 2 : ℝ))) +
                (((Z : ℕ) : ℝ) +
                  (Z : ℝ) ^ (1 / 4 : ℝ) *
                    ((Y : ℝ) /
                        ((modulus : ℝ) *
                          (Z : ℝ) ^ (1 / 2 : ℝ)) + 1)))) := by
        exact mul_le_mul_of_nonneg_left hraw' (by positivity)
      _ ≤ (Cweight * (4 + 2 * Ctail)) * (Y : ℝ) := by
        simpa using habsorb
      _ = Kreal * (Y : ℝ) := by rfl
  let massN : ℕ :=
    ShiuEndToEnd.classMass k X Y modulus residue Z
        (ShiuClassIBound.smoothCutoff X) FourClass.II +
      ShiuEndToEnd.classMass k X Y modulus residue Z
        (ShiuClassIBound.smoothCutoff X) FourClass.III
  have hmassCast :
      (massN : ℝ) =
        exceptionalMass k X Y modulus residue Z
          (ShiuLemma1ClassIII.classIIICutoff X) := by
    simp [massN, ShiuEndToEnd.classMass, exceptionalMass,
      ShiuClassIBound.smoothCutoff,
      ShiuLemma1ClassIII.classIIICutoff]
  have hKceil : Kreal ≤ (C : ℝ) := Nat.le_ceil Kreal
  have hnatR :
      ((modulus * massN : ℕ) : ℝ) ≤ ((C * Y : ℕ) : ℝ) := by
    calc
      ((modulus * massN : ℕ) : ℝ) =
          (modulus : ℝ) *
            exceptionalMass k X Y modulus residue Z
              (ShiuLemma1ClassIII.classIIICutoff X) := by
        push_cast
        rw [hmassCast]
      _ ≤ Kreal * (Y : ℝ) := hmassR
      _ ≤ (C : ℝ) * (Y : ℝ) :=
        mul_le_mul_of_nonneg_right hKceil (by positivity)
      _ = ((C * Y : ℕ) : ℝ) := by norm_num
  have hnat : modulus * massN ≤ C * Y := by exact_mod_cast hnatR
  have hlogPow :
      1 ≤ (Nat.log 2 (X + 2) + 1) ^ (k * k) := by
    exact one_le_pow₀ (by omega)
  have hbudget : C * Y ≤ C * ShiuEndToEnd.classBudgetBase k X Y := by
    simp only [ShiuEndToEnd.classBudgetBase]
    have hY : Y ≤ Y * (Nat.log 2 (X + 2) + 1) ^ (k * k) := by
      simpa using Nat.mul_le_mul_left Y hlogPow
    exact Nat.mul_le_mul_left C hY
  have hfinal : modulus * massN ≤ C * ShiuEndToEnd.classBudgetBase k X Y :=
    hnat.trans hbudget
  simpa [massN, Z, ShiuEndToEnd.sectionFiveZ,
    ShiuEndToEnd.smoothCutoff, ShiuClassIBound.sectionFiveZ,
    ShiuClassIBound.smoothCutoff] using hfinal

end

end ShiuClassIIIII

#print axioms ShiuClassIIIII.exists_tauSquare_le_const_mul_Z_rpow_one_eighth
#print axioms ShiuClassIIIII.exists_exceptionalMass_le_Z_rpow_mul_card
#print axioms ShiuClassIIIII.classII_large_card_le_of_primePowerTail
#print axioms ShiuClassIIIII.classII_card_le_raw_of_primePowerTail
#print axioms ShiuClassIIIII.exists_classIIIII56_raw_of_primePowerTail
#print axioms ShiuClassIIIII.exists_classIIIII56_ceiling_of_primePowerTail
#print axioms ShiuClassIIIII.certifiedClassIIReciprocalLeastThresholdTailEstimate
#print axioms ShiuClassIIIII.certifiedClassIIPrimePowerTailEstimate
#print axioms ShiuClassIIIII.exists_classIIIII56_raw
#print axioms ShiuClassIIIII.exists_classIIIII56_ceiling
#print axioms ShiuClassIIIII.certifiedClassIIIII56Estimate
