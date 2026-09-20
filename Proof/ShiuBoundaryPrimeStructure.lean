import ShiuSection5Structure

/-!
# Boundary prime in Shiu's canonical Section 5 split

The first complete prime-power block in the canonical suffix is proved to be
exactly the least-prime-factor `q(d_n)`.  Consequently all prime divisors of
the prefix are smaller, giving the literal class-III smoothness statement.
-/

namespace ShiuBoundaryPrimeStructure

open ArithmeticFunction MixedMellinCert ShiuFoundation ShiuAnalyticLayer
  ShiuSection5Split ShiuSection5Structure
open scoped BigOperators ArithmeticFunction.zeta

noncomputable section
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

end

end ShiuBoundaryPrimeStructure

#print axioms ShiuBoundaryPrimeStructure.exists_boundaryPrime_eq_leastPrimeFactor
#print axioms ShiuBoundaryPrimeStructure.prime_dvd_canonicalB_lt_boundaryPrime
#print axioms ShiuBoundaryPrimeStructure.canonicalB_mem_smoothNumbers_of_leastPrimeFactor_le
