import ShiuUniformContract

/-!
# Finite Selberg-sieve slice of Shiu's argument

This module proves the exact finite majorant and primitive-residue reductions
which precede Shiu's analytic sieve bound.  It does not assert the uniform
upper-bound sieve estimate itself.
-/

namespace ShiuSieveSlice

open ShiuFoundation
open scoped BigOperators

noncomputable section

/-- Primes at most `z` which are not already excluded by the primitive
progression modulus. -/
def sievingPrimes (z modulus : ℕ) : Finset ℕ :=
  (Finset.range (z + 1)).filter fun p => p.Prime ∧ ¬p ∣ modulus

/-- The squarefree product of the primes on which the sieve acts. -/
def sievingProduct (z modulus : ℕ) : ℕ :=
  ∏ p ∈ sievingPrimes z modulus, p

theorem sievingProduct_pos (z modulus : ℕ) : 0 < sievingProduct z modulus := by
  unfold sievingProduct
  apply Finset.prod_pos
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1.pos

/-- The sieve product is coprime to the progression modulus by construction. -/
theorem sievingProduct_coprime_modulus (z modulus : ℕ) :
    (sievingProduct z modulus).Coprime modulus := by
  unfold sievingProduct
  apply Nat.Coprime.prod_left
  intro p hp
  have h := (Finset.mem_filter.mp hp).2
  exact h.1.coprime_iff_not_dvd.mpr h.2

/-- Coprimality with the product is exactly exclusion of every selected
prime. -/
theorem coprime_sievingProduct_iff (n z modulus : ℕ) :
    n.Coprime (sievingProduct z modulus) ↔
      ∀ p ∈ sievingPrimes z modulus, ¬p ∣ n := by
  constructor
  · intro h p hp
    have hpdiv : p ∣ sievingProduct z modulus := by
      unfold sievingProduct
      exact Finset.dvd_prod_of_mem id hp
    have hpn : p.Coprime n := Nat.Coprime.of_dvd hpdiv (dvd_refl n) h.symm
    exact (Finset.mem_filter.mp hp).2.1.coprime_iff_not_dvd.mp hpn
  · intro h
    unfold sievingProduct
    apply Nat.Coprime.prod_right
    intro p hp
    exact ((Finset.mem_filter.mp hp).2.1.coprime_iff_not_dvd.mpr (h p hp)).symm

/-- A member of a primitive residue class is itself coprime to the modulus. -/
theorem coprime_of_modEq_primitive {n residue modulus : ℕ}
    (hn : n ≡ residue [MOD modulus]) (hres : residue.Coprime modulus) :
    n.Coprime modulus := by
  rw [Nat.coprime_iff_gcd_eq_one]
  exact hn.gcd_eq.trans hres.gcd_eq_one

/-- Primes dividing the modulus cannot divide a member of a primitive residue
class.  This is the exact residue-class restriction used before sieving. -/
theorem prime_not_dvd_of_modEq_primitive
    {n residue modulus p : ℕ}
    (hn : n ≡ residue [MOD modulus])
    (hres : residue.Coprime modulus)
    (hp : p.Prime) (hpmod : p ∣ modulus) :
    ¬p ∣ n := by
  have hcop := coprime_of_modEq_primitive hn hres
  have hpcop : p.Coprime n := Nat.Coprime.of_dvd hpmod (dvd_refl n) hcop.symm
  exact hp.coprime_iff_not_dvd.mp hpcop

/-- In a primitive residue class, sieving only primes not dividing the
modulus is equivalent to excluding every prime up to `z`. -/
theorem coprime_sievingProduct_iff_no_small_prime
    {n residue modulus z : ℕ}
    (hn : n ≡ residue [MOD modulus])
    (hres : residue.Coprime modulus) :
    n.Coprime (sievingProduct z modulus) ↔
      ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ n := by
  rw [coprime_sievingProduct_iff]
  constructor
  · intro h p hp hpz
    by_cases hpmod : p ∣ modulus
    · exact prime_not_dvd_of_modEq_primitive hn hres hp hpmod
    · apply h p
      simp [sievingPrimes, hp, hpmod, hpz]
  · intro h p hp
    have hdata := (Finset.mem_filter.mp hp).2
    exact h p hdata.1 (by
      have := (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
      omega)

/-! ## The literal sifted mass in Shiu's Lemma 2 -/

/-- Shiu's `Φ(x,y,z;q,a)`, with his convention that the least prime factor of
`1` is `1`.  Thus `1` is excluded when `z ≥ 2`. -/
def shiuPhi (x y z modulus residue : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ Finset.Ioc (x - y) x,
    if n ≡ residue [MOD modulus] ∧ 1 < n ∧
        ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ n
    then 1 else 0

/-! ## Selberg square majorant -/

/-- The finite divisor sum to which Selberg's square is applied. -/
def selbergDivisorSum (weights : ℕ → ℝ) (P n : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, if d ∣ n then weights d else 0

/-- On a number coprime to the sieve product, a normalized divisor sum is
exactly one. -/
theorem selbergDivisorSum_eq_one_of_coprime
    {weights : ℕ → ℝ} {P n : ℕ}
    (hP : 0 < P) (hcop : n.Coprime P) (hweight : weights 1 = 1) :
    selbergDivisorSum weights P n = 1 := by
  unfold selbergDivisorSum
  have h1mem : 1 ∈ P.divisors := Nat.mem_divisors.mpr ⟨one_dvd P, hP.ne'⟩
  rw [Finset.sum_eq_single_of_mem 1 h1mem]
  · simp [hweight]
  · intro d hd hd1
    have hdP : d ∣ P := (Nat.mem_divisors.mp hd).1
    have hnot : ¬d ∣ n := by
      intro hdn
      have hself : d.Coprime d := Nat.Coprime.of_dvd hdn hdP hcop
      exact hd1 (hself.eq_one_of_dvd (dvd_refl d))
    simp [hnot]

/-- Exact double-divisor expansion of Selberg's square. -/
theorem selbergDivisorSum_sq_expand
    (weights : ℕ → ℝ) (P n : ℕ) :
    selbergDivisorSum weights P n ^ 2 =
      ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
        if d.lcm e ∣ n then weights d * weights e else 0 := by
  unfold selbergDivisorSum
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [Nat.lcm_dvd_iff]
  by_cases hdn : d ∣ n <;> by_cases hen : e ∣ n <;> simp [hdn, hen]

/-- After expanding the square, the progression sum is exactly a double
divisor sum whose inner factor is a residue-and-divisibility count.  This is
the finite algebraic identity to which the Selberg weights are optimized. -/
theorem selbergSquare_progression_expand
    (weights : ℕ → ℝ) (x y modulus residue P : ℕ) :
    (∑ n ∈ Finset.Ioc (x - y) x,
        if n ≡ residue [MOD modulus]
        then selbergDivisorSum weights P n ^ 2 else 0) =
      ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
        weights d * weights e *
          (((Finset.Ioc (x - y) x).filter fun n =>
            n ≡ residue [MOD modulus] ∧ d.lcm e ∣ n).card : ℝ) := by
  classical
  calc
    (∑ n ∈ Finset.Ioc (x - y) x,
        if n ≡ residue [MOD modulus]
        then selbergDivisorSum weights P n ^ 2 else 0) =
        ∑ n ∈ Finset.Ioc (x - y) x,
          ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
            if n ≡ residue [MOD modulus] ∧ d.lcm e ∣ n
            then weights d * weights e else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [selbergDivisorSum_sq_expand]
      by_cases hmod : n ≡ residue [MOD modulus]
      · rw [if_pos hmod]
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro e he
        by_cases hdiv : d.lcm e ∣ n <;> simp [hmod, hdiv]
      · simp [hmod]
    _ = ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
          ∑ n ∈ Finset.Ioc (x - y) x,
            if n ≡ residue [MOD modulus] ∧ d.lcm e ∣ n
            then weights d * weights e else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
        weights d * weights e *
          (((Finset.Ioc (x - y) x).filter fun n =>
            n ≡ residue [MOD modulus] ∧ d.lcm e ∣ n).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.natCast_card_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h : n ≡ residue [MOD modulus] ∧ d.lcm e ∣ n <;> simp [h]

/-- The real indicator mass of a primitive progression after sifting by `P`. -/
def siftedProgressionMass
    (x y modulus residue P : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc (x - y) x,
    if n ≡ residue [MOD modulus] ∧ n.Coprime P then 1 else 0

/-- In a primitive progression, the literal `Φ` mass is bounded by the
coprimality indicator for the squarefree sieving product.  The only possible
difference is the deliberately excluded integer `1`. -/
theorem shiuPhi_le_siftedProgressionMass
    {x y z modulus residue : ℕ}
    (hres : residue.Coprime modulus) :
    shiuPhi x y z modulus residue ≤
      siftedProgressionMass x y modulus residue
        (sievingProduct z modulus) := by
  classical
  unfold shiuPhi siftedProgressionMass
  apply Finset.sum_le_sum
  intro n hn
  by_cases hmod : n ≡ residue [MOD modulus]
  · by_cases hone : 1 < n
    · by_cases hsmall : ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ n
      · have hcop : n.Coprime (sievingProduct z modulus) :=
          (coprime_sievingProduct_iff_no_small_prime hmod hres).2 hsmall
        rw [if_pos ⟨hmod, hone, hsmall⟩, if_pos ⟨hmod, hcop⟩]
      · rw [if_neg (fun h => hsmall h.2.2)]
        split <;> norm_num
    · rw [if_neg (fun h => hone h.2.1)]
      split <;> norm_num
  · rw [if_neg (fun h => hmod h.1), if_neg (fun h => hmod h.1)]

/-- Selberg's normalized square pointwise majorizes the sifted indicator. -/
theorem siftedProgressionMass_le_selbergSquare
    {weights : ℕ → ℝ} {x y modulus residue P : ℕ}
    (hP : 0 < P) (hweight : weights 1 = 1) :
    siftedProgressionMass x y modulus residue P ≤
      ∑ n ∈ Finset.Ioc (x - y) x,
        if n ≡ residue [MOD modulus]
        then selbergDivisorSum weights P n ^ 2 else 0 := by
  unfold siftedProgressionMass
  apply Finset.sum_le_sum
  intro n hn
  by_cases hmod : n ≡ residue [MOD modulus]
  · by_cases hcop : n.Coprime P
    · rw [if_pos ⟨hmod, hcop⟩, if_pos hmod,
        selbergDivisorSum_eq_one_of_coprime hP hcop hweight]
      norm_num
    · simp [hmod, hcop, sq_nonneg]
  · simp [hmod]

/-! ## Combining divisibility with the primitive progression -/

/-- The unique CRT residue used after expanding Selberg's square. -/
def combinedResidue {modulus l : ℕ} (hcop : modulus.Coprime l)
    (residue : ℕ) : ℕ :=
  Nat.chineseRemainder hcop residue 0

theorem modEq_combinedResidue_of_modEq_of_dvd
    {n residue modulus l : ℕ} (hcop : modulus.Coprime l)
    (hmod : n ≡ residue [MOD modulus]) (hdiv : l ∣ n) :
    n ≡ combinedResidue hcop residue [MOD modulus * l] := by
  exact Nat.chineseRemainder_modEq_unique hcop hmod
    (Nat.modEq_zero_iff_dvd.mpr hdiv)

/-- The intersection of one primitive residue class with one divisibility
condition is exactly one residue class modulo the product modulus. -/
theorem filter_modEq_and_dvd_eq_combined
    (lo hi residue modulus l : ℕ) (hcop : modulus.Coprime l) :
    (Finset.Ioc lo hi).filter
        (fun n => n ≡ residue [MOD modulus] ∧ l ∣ n) =
      (Finset.Ioc lo hi).filter
        (fun n => n ≡ combinedResidue hcop residue [MOD modulus * l]) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, and_congr_right_iff]
  intro hn
  constructor
  · rintro ⟨hmod, hdiv⟩
    exact modEq_combinedResidue_of_modEq_of_dvd hcop hmod hdiv
  · intro h
    have hk : n ≡ combinedResidue hcop residue [MOD modulus] :=
      h.of_mul_right l
    have hl : n ≡ combinedResidue hcop residue [MOD l] :=
      h.of_mul_left modulus
    have hcrt := (Nat.chineseRemainder hcop residue 0).prop
    exact ⟨hk.trans hcrt.1, Nat.modEq_zero_iff_dvd.mp (hl.trans hcrt.2)⟩

/-- Exact Mathlib progression count for each divisibility term appearing in
the expanded Selberg square. -/
theorem combined_filter_card_exact
    (lo hi residue modulus l : ℕ)
    (hmodulus : 0 < modulus) (hl : 0 < l)
    (hcop : modulus.Coprime l) :
    (((Finset.Ioc lo hi).filter
      (fun n => n ≡ residue [MOD modulus] ∧ l ∣ n)).card : ℤ) =
      max
        (⌊((hi : ℤ) - combinedResidue hcop residue) /
              (modulus * l : ℚ)⌋ -
          ⌊((lo : ℤ) - combinedResidue hcop residue) /
              (modulus * l : ℚ)⌋) 0 := by
  rw [filter_modEq_and_dvd_eq_combined lo hi residue modulus l hcop]
  simpa [Nat.cast_mul] using
    (progression_card_exact lo hi (modulus * l)
      (combinedResidue hcop residue) (Nat.mul_pos hmodulus hl))

/-- A residue class in an interval has discrepancy at most one from interval
length divided by the modulus.  This is the exact geometric error term used by
the Selberg sieve; it is derived from Mathlib's floor formula. -/
theorem progression_card_discrepancy_le_one
    (lo hi modulus residue : ℕ) (hmod : 0 < modulus) (hlo : lo ≤ hi) :
    |((((Finset.Ioc lo hi).filter
      (fun n => n ≡ residue [MOD modulus])).card : ℕ) : ℝ) -
        ((hi - lo : ℕ) : ℝ) / (modulus : ℝ)| ≤ 1 := by
  have hcard := progression_card_exact lo hi modulus residue hmod
  have hcardR := congrArg (fun z : ℤ => (z : ℝ)) hcard
  let A : ℚ := ((hi : ℤ) - residue) / (modulus : ℚ)
  let B : ℚ := ((lo : ℤ) - residue) / (modulus : ℚ)
  change ((((Finset.Ioc lo hi).filter
      (fun n => n ≡ residue [MOD modulus])).card : ℕ) : ℝ) =
    ((max (⌊A⌋ - ⌊B⌋) 0 : ℤ) : ℝ) at hcardR
  have hBA : B ≤ A := by
    dsimp [A, B]
    gcongr
  have hfloor : (0 : ℤ) ≤ ⌊A⌋ - ⌊B⌋ :=
    sub_nonneg.mpr (Int.floor_mono hBA)
  rw [max_eq_left hfloor] at hcardR
  norm_num at hcardR
  have hAfloorQ : (⌊A⌋ : ℚ) ≤ A := Int.floor_le A
  have hAceilQ : A < (⌊A⌋ : ℚ) + 1 := Int.lt_floor_add_one A
  have hBfloorQ : (⌊B⌋ : ℚ) ≤ B := Int.floor_le B
  have hBceilQ : B < (⌊B⌋ : ℚ) + 1 := Int.lt_floor_add_one B
  have hAfloorR : ((⌊A⌋ : ℤ) : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast hAfloorQ
  have hAceilR : (A : ℝ) < ((⌊A⌋ : ℤ) : ℝ) + 1 := by
    exact_mod_cast hAceilQ
  have hBfloorR : ((⌊B⌋ : ℤ) : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast hBfloorQ
  have hBceilR : (B : ℝ) < ((⌊B⌋ : ℤ) : ℝ) + 1 := by
    exact_mod_cast hBceilQ
  have hlen : (A : ℝ) - (B : ℝ) =
      ((hi - lo : ℕ) : ℝ) / (modulus : ℝ) := by
    dsimp [A, B]
    rw [Nat.cast_sub hlo]
    norm_num
    field_simp
    ring
  rw [hcardR, ← hlen, abs_le]
  constructor <;> norm_num <;> linarith

/-- CRT specialization of the discrepancy bound for one term in the expanded
Selberg square. -/
theorem combined_filter_card_discrepancy_le_one
    (x y residue modulus l : ℕ)
    (hmodulus : 0 < modulus) (hl : 0 < l)
    (hcop : modulus.Coprime l) (hyx : y ≤ x) :
    |((((Finset.Ioc (x - y) x).filter
      (fun n => n ≡ residue [MOD modulus] ∧ l ∣ n)).card : ℕ) : ℝ) -
        (y : ℝ) / ((modulus : ℝ) * (l : ℝ))| ≤ 1 := by
  rw [filter_modEq_and_dvd_eq_combined (x - y) x residue modulus l hcop]
  have h := progression_card_discrepancy_le_one (x - y) x
    (modulus * l) (combinedResidue hcop residue)
    (Nat.mul_pos hmodulus hl) (Nat.sub_le x y)
  have hlen : x - (x - y) = y := by omega
  simpa only [hlen, Nat.cast_mul] using h

/-! ## Exact reduction to the finite Selberg quadratic form -/

/-- The main quadratic form produced by the progression density terms. -/
def selbergMainQuadratic (weights : ℕ → ℝ) (P : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
    weights d * weights e / (d.lcm e : ℝ)

/-- The total absolute coefficient mass controlling the unit discrepancy in
each progression count. -/
def selbergErrorMass (weights : ℕ → ℝ) (P : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
    |weights d * weights e|

theorem weighted_discrepancy_term_le
    {weight count density : ℝ} (hdisc : |count - density| ≤ 1) :
    weight * count ≤ weight * density + |weight| := by
  have herr : weight * (count - density) ≤ |weight| := by
    calc
      weight * (count - density) ≤ |weight * (count - density)| :=
        le_abs_self _
      _ = |weight| * |count - density| := abs_mul _ _
      _ ≤ |weight| * 1 :=
        mul_le_mul_of_nonneg_left hdisc (abs_nonneg weight)
      _ = |weight| := mul_one _
  linarith

/-- Every analytic and residue-class issue in Shiu's Lemma 2 has now been
removed: arbitrary normalized Selberg weights give the main quadratic term
plus the exact unit-discrepancy error mass. -/
theorem shiuPhi_le_selbergQuadratic
    (weights : ℕ → ℝ) (x y z modulus residue : ℕ)
    (hweight : weights 1 = 1)
    (hmodulus : 0 < modulus)
    (hres : residue.Coprime modulus)
    (hyx : y ≤ x) :
    shiuPhi x y z modulus residue ≤
      (y : ℝ) / (modulus : ℝ) *
          selbergMainQuadratic weights (sievingProduct z modulus) +
        selbergErrorMass weights (sievingProduct z modulus) := by
  let P := sievingProduct z modulus
  have hP : 0 < P := sievingProduct_pos z modulus
  calc
    shiuPhi x y z modulus residue ≤
        siftedProgressionMass x y modulus residue P := by
      exact shiuPhi_le_siftedProgressionMass hres
    _ ≤ ∑ n ∈ Finset.Ioc (x - y) x,
        if n ≡ residue [MOD modulus]
        then selbergDivisorSum weights P n ^ 2 else 0 :=
      siftedProgressionMass_le_selbergSquare hP hweight
    _ = ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
        weights d * weights e *
          (((Finset.Ioc (x - y) x).filter fun n =>
            n ≡ residue [MOD modulus] ∧ d.lcm e ∣ n).card : ℝ) :=
      selbergSquare_progression_expand weights x y modulus residue P
    _ ≤ ∑ d ∈ P.divisors, ∑ e ∈ P.divisors, (
        ((y : ℝ) / (modulus : ℝ)) *
            (weights d * weights e / (d.lcm e : ℝ)) +
          |weights d * weights e|) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      have hdP : d ∣ P := (Nat.mem_divisors.mp hd).1
      have heP : e ∣ P := (Nat.mem_divisors.mp he).1
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdP hP
      have hepos : 0 < e := Nat.pos_of_dvd_of_pos heP hP
      have hlpos : 0 < d.lcm e := Nat.lcm_pos hdpos hepos
      have hlP : d.lcm e ∣ P := Nat.lcm_dvd hdP heP
      have hcop : modulus.Coprime (d.lcm e) :=
        Nat.Coprime.of_dvd (dvd_refl modulus) hlP
          (sievingProduct_coprime_modulus z modulus).symm
      have hdisc := combined_filter_card_discrepancy_le_one x y residue
        modulus (d.lcm e) hmodulus hlpos hcop hyx
      have hterm := weighted_discrepancy_term_le
        (weight := weights d * weights e)
        (count := (((Finset.Ioc (x - y) x).filter fun n =>
          n ≡ residue [MOD modulus] ∧ d.lcm e ∣ n).card : ℝ))
        (density := (y : ℝ) /
          ((modulus : ℝ) * (d.lcm e : ℝ))) hdisc
      calc
        weights d * weights e *
            (((Finset.Ioc (x - y) x).filter fun n =>
              n ≡ residue [MOD modulus] ∧ d.lcm e ∣ n).card : ℝ) ≤
            weights d * weights e *
                ((y : ℝ) / ((modulus : ℝ) * (d.lcm e : ℝ))) +
              |weights d * weights e| := hterm
        _ = ((y : ℝ) / (modulus : ℝ)) *
              (weights d * weights e / (d.lcm e : ℝ)) +
            |weights d * weights e| := by
          field_simp
    _ = (y : ℝ) / (modulus : ℝ) *
          selbergMainQuadratic weights P + selbergErrorMass weights P := by
      unfold selbergMainQuadratic selbergErrorMass
      simp_rw [Finset.sum_add_distrib]
      apply congrArg₂ (· + ·)
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.mul_sum]
      · rfl

/-! ## Exact first missing sieve theorem -/

/-- Level-`z`, coefficient-bounded weights automatically have `O(z²)` total
discrepancy mass.  Thus the error term is elementary once the standard Selberg
support and normalization properties are available. -/
theorem selbergErrorMass_le_sq
    (weights : ℕ → ℝ) (P z : ℕ) (hP : 0 < P)
    (hsupport : ∀ d : ℕ, z < d → weights d = 0)
    (hbounded : ∀ d : ℕ, d ≤ z → |weights d| ≤ 1) :
    selbergErrorMass weights P ≤ (z : ℝ) ^ 2 := by
  have hsum : (∑ d ∈ P.divisors, |weights d|) ≤ (z : ℝ) := by
    calc
      (∑ d ∈ P.divisors, |weights d|) ≤
          ∑ d ∈ P.divisors, if d ≤ z then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro d hd
        by_cases hdz : d ≤ z
        · simp [hdz, hbounded d hdz]
        · have hzero : weights d = 0 := hsupport d (lt_of_not_ge hdz)
          simp [hdz, hzero]
      _ = ((((P.divisors).filter fun d => d ≤ z).card : ℕ) : ℝ) := by
        exact Finset.sum_boole (R := ℝ) (fun d : ℕ => d ≤ z) P.divisors
      _ ≤ (z : ℝ) := by
        have hc := Finset.card_le_card (by
          intro d hd
          have hddata := Finset.mem_filter.mp hd
          have hdpos : 0 < d :=
            Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hddata.1).1 hP
          exact Finset.mem_Icc.mpr ⟨hdpos, hddata.2⟩ :
            (P.divisors.filter fun d => d ≤ z) ⊆ Finset.Icc 1 z)
        simpa using hc
  have herrEq : selbergErrorMass weights P =
      (∑ d ∈ P.divisors, |weights d|) ^ 2 := by
    unfold selbergErrorMass
    simp_rw [abs_mul]
    symm
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
  rw [herrEq]
  gcongr

/-- The precise finite diagonal-form theorem absent from the current Mathlib
Selberg-sieve framework: bounded, level-supported normalized weights with the
dimension-one main quadratic estimate. -/
def SelbergMainWeightBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ z modulus : ℕ, 0 < modulus → 2 ≤ z →
      ∃ weights : ℕ → ℝ,
        weights 1 = 1 ∧
        (∀ d : ℕ, z < d → weights d = 0) ∧
        (∀ d : ℕ, d ≤ z → |weights d| ≤ 1) ∧
        selbergMainQuadratic weights (sievingProduct z modulus) ≤
          C * (modulus : ℝ) /
            ((Nat.totient modulus : ℝ) * Real.log (z : ℝ))

/-- The genuinely sieve-theoretic finite statement still required after all
progression geometry has been discharged.  It asks for normalized weights with
the standard dimension-one quadratic bound and `O(z²)` discrepancy mass.  It
contains no interval, residue, or progression sum. -/
def SelbergWeightBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ z modulus : ℕ, 0 < modulus → 2 ≤ z →
      ∃ weights : ℕ → ℝ,
        weights 1 = 1 ∧
        selbergMainQuadratic weights (sievingProduct z modulus) ≤
          C * (modulus : ℝ) /
            ((Nat.totient modulus : ℝ) * Real.log (z : ℝ)) ∧
        selbergErrorMass weights (sievingProduct z modulus) ≤
          C * (z : ℝ) ^ 2

/-- The main quadratic weight theorem supplies the full finite weight package;
the `z²` error follows from support and coefficient boundedness. -/
theorem selbergWeightBound_of_mainWeightBound
    (hmainWeights : SelbergMainWeightBound) : SelbergWeightBound := by
  obtain ⟨C, hC, hmainWeights⟩ := hmainWeights
  let C' := max C 1
  have hC' : 0 < C' := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_max_right C 1)
  refine ⟨C', hC', ?_⟩
  intro z modulus hmodulus hz
  obtain ⟨weights, hweight, hsupport, hbounded, hmain⟩ :=
    hmainWeights z modulus hmodulus hz
  refine ⟨weights, hweight, ?_, ?_⟩
  · exact hmain.trans (by
      gcongr
      · exact le_max_left C 1)
  · have herr := selbergErrorMass_le_sq weights
      (sievingProduct z modulus) z (sievingProduct_pos z modulus)
      hsupport hbounded
    calc
      selbergErrorMass weights (sievingProduct z modulus) ≤ (z : ℝ) ^ 2 := herr
      _ ≤ C' * (z : ℝ) ^ 2 := by
        calc
          (z : ℝ) ^ 2 = 1 * (z : ℝ) ^ 2 := by ring
          _ ≤ C' * (z : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_right C 1) (sq_nonneg _)

/-- The literal natural-number form of Shiu's Lemma 2.  The constant is
absolute and uniform in all displayed variables.  This is a proposition which
locates the analytic boundary; it is not asserted as a theorem in this module.

The published hypotheses are `0 < a < q`, `(a,q)=1`, `q < y ≤ x`, and
`z ≥ 2`; the conclusion is `Φ ≪ y/(φ(q) log z) + z²`. -/
def SelbergUpperBoundSieveContract : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ x y z modulus residue : ℕ,
      0 < modulus →
      residue < modulus →
      residue.Coprime modulus →
      modulus < y →
      y ≤ x →
      2 ≤ z →
      shiuPhi x y z modulus residue ≤
        C * ((y : ℝ) /
            ((Nat.totient modulus : ℝ) * Real.log (z : ℝ)) +
          (z : ℝ) ^ 2)

/-- The finite Selberg weight bound implies Shiu's Lemma 2.  This theorem
shows that `SelbergWeightBound`, rather than any progression estimate, is the
first remaining input. -/
theorem selbergUpperBoundSieve_of_weightBound
    (hweights : SelbergWeightBound) :
    SelbergUpperBoundSieveContract := by
  obtain ⟨C, hC, hweights⟩ := hweights
  refine ⟨C, hC, ?_⟩
  intro x y z modulus residue hmodulus hresidue hres hmy hyx hz
  obtain ⟨weights, hweight, hmain, herror⟩ :=
    hweights z modulus hmodulus hz
  have hreduce := shiuPhi_le_selbergQuadratic weights x y z modulus residue
    hweight hmodulus hres hyx
  have hydiv : 0 ≤ (y : ℝ) / (modulus : ℝ) := by positivity
  have hzreal : (1 : ℝ) < z := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hz)
  have hlog : 0 < Real.log (z : ℝ) := Real.log_pos hzreal
  have hphiNat : 0 < Nat.totient modulus := Nat.totient_pos.mpr hmodulus
  have hphi : (0 : ℝ) < Nat.totient modulus := by exact_mod_cast hphiNat
  calc
    shiuPhi x y z modulus residue ≤
        (y : ℝ) / (modulus : ℝ) *
            selbergMainQuadratic weights (sievingProduct z modulus) +
          selbergErrorMass weights (sievingProduct z modulus) := hreduce
    _ ≤ (y : ℝ) / (modulus : ℝ) *
          (C * (modulus : ℝ) /
            ((Nat.totient modulus : ℝ) * Real.log (z : ℝ))) +
        C * (z : ℝ) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hmain hydiv) herror
    _ = C * ((y : ℝ) /
          ((Nat.totient modulus : ℝ) * Real.log (z : ℝ)) +
        (z : ℝ) ^ 2) := by
      field_simp [ne_of_gt hmodulus, ne_of_gt hphi, ne_of_gt hlog]

/-- Closing the single finite main-weight theorem closes Shiu's Lemma 2 with
no further analytic or progression input. -/
theorem selbergUpperBoundSieve_of_mainWeightBound
    (hmainWeights : SelbergMainWeightBound) :
    SelbergUpperBoundSieveContract :=
  selbergUpperBoundSieve_of_weightBound
    (selbergWeightBound_of_mainWeightBound hmainWeights)

end

end ShiuSieveSlice
