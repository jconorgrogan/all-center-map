import SelbergMainWeightClosure
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# An elementary lower-bound route for the finite Selberg denominator

The key observation is that the denominator already contains every squarefree
integer at most the sieve level which is coprime to the progression modulus.
Thus it dominates the corresponding squarefree harmonic sum term-by-term.
-/

noncomputable section

namespace ShiuSelbergDenominatorLower

open ShiuSieveSlice
open scoped BigOperators ArithmeticFunction.Moebius

def levelDivisors (P z : ℕ) : Finset ℕ :=
  P.divisors.filter fun r => r ≤ z

def selbergDenominator (P z : ℕ) : ℝ :=
  ∑ r ∈ levelDivisors P z,
    (ArithmeticFunction.moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ)

def squarefreeCoprimeHarmonic (modulus z : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 z).filter
      (fun n ↦ Squarefree n ∧ n.Coprime modulus),
    1 / (n : ℝ)

def squarefreeAvoidingSet (S : Finset ℕ) (z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 z).filter fun n ↦
    Squarefree n ∧ ∀ p ∈ S, ¬p ∣ n

def squarefreeAvoidingHarmonic (S : Finset ℕ) (z : ℕ) : ℝ :=
  ∑ n ∈ squarefreeAvoidingSet S z, 1 / (n : ℝ)

theorem squarefreeAvoidingHarmonic_nonneg (S : Finset ℕ) (z : ℕ) :
    0 ≤ squarefreeAvoidingHarmonic S z := by
  unfold squarefreeAvoidingHarmonic
  positivity

theorem div_image_subset_squarefreeAvoidingSet
    {S : Finset ℕ} {z p : ℕ} (hp : 0 < p) :
    ((squarefreeAvoidingSet S z).filter fun n ↦ p ∣ n).image
        (fun n ↦ n / p) ⊆ squarefreeAvoidingSet S z := by
  intro m hm
  rcases Finset.mem_image.mp hm with ⟨n, hnD, rfl⟩
  have hnS : n ∈ squarefreeAvoidingSet S z := (Finset.mem_filter.mp hnD).1
  have hpn : p ∣ n := (Finset.mem_filter.mp hnD).2
  have hnData := Finset.mem_filter.mp hnS
  have hnIcc := Finset.mem_Icc.mp hnData.1
  have hnpos : 0 < n := by omega
  have hdivpos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hnpos hpn) hp
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by omega, (Nat.div_le_self n p).trans hnIcc.2⟩, ?_⟩
  refine ⟨Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hpn) hnData.2.1, ?_⟩
  intro s hs hsd
  exact hnData.2.2 s hs (dvd_trans hsd (Nat.div_dvd_of_dvd hpn))

theorem div_on_multiples_injective
    {A : Finset ℕ} {p : ℕ} (hp : 0 < p) :
    Set.InjOn (fun n ↦ n / p) ↑(A.filter fun n ↦ p ∣ n) := by
  intro a ha b hb hab
  have hpa : p ∣ a := (Finset.mem_filter.mp ha).2
  have hpb : p ∣ b := (Finset.mem_filter.mp hb).2
  calc
    a = p * (a / p) := (Nat.mul_div_cancel' hpa).symm
    _ = p * (b / p) := congrArg (fun x ↦ p * x) hab
    _ = b := Nat.mul_div_cancel' hpb

theorem divisible_squarefreeAvoidingHarmonic_le
    {S : Finset ℕ} {z p : ℕ} (hp : 0 < p) :
    (∑ n ∈ (squarefreeAvoidingSet S z).filter fun n ↦ p ∣ n,
        1 / (n : ℝ)) ≤
      (1 / (p : ℝ)) * squarefreeAvoidingHarmonic S z := by
  let D := (squarefreeAvoidingSet S z).filter fun n ↦ p ∣ n
  let I := D.image fun n ↦ n / p
  have hI : I ⊆ squarefreeAvoidingSet S z := by
    dsimp [I, D]
    exact div_image_subset_squarefreeAvoidingSet hp
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  calc
    (∑ n ∈ D, 1 / (n : ℝ)) =
        (1 / (p : ℝ)) * ∑ m ∈ I, 1 / (m : ℝ) := by
      rw [Finset.sum_image (div_on_multiples_injective (A := squarefreeAvoidingSet S z) hp)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hnD
      have hpn : p ∣ n := (Finset.mem_filter.mp hnD).2
      rw [Nat.cast_div_charZero hpn]
      have hnpos : 0 < n := by
        have hnS := (Finset.mem_filter.mp hnD).1
        have hnIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hnS).1
        omega
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
      field_simp
    _ ≤ (1 / (p : ℝ)) *
        ∑ m ∈ squarefreeAvoidingSet S z, 1 / (m : ℝ) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg hI
        intro m hmS hmI
        positivity
      · positivity
    _ = (1 / (p : ℝ)) * squarefreeAvoidingHarmonic S z := by rfl

theorem squarefreeAvoidingSet_insert
    (S : Finset ℕ) (z p : ℕ) :
    squarefreeAvoidingSet (insert p S) z =
      squarefreeAvoidingSet S z \
        (squarefreeAvoidingSet S z).filter (fun n ↦ p ∣ n) := by
  ext n
  constructor
  · intro hn
    have hdata := Finset.mem_filter.mp hn
    have hav := hdata.2.2
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hdata.1, hdata.2.1, ?_⟩, ?_⟩
    · intro a ha
      exact hav a (Finset.mem_insert_of_mem ha)
    · intro hdiv
      exact (hav p (Finset.mem_insert_self p S)) (Finset.mem_filter.mp hdiv).2
  · intro hn
    have hdata := Finset.mem_sdiff.mp hn
    have hbase := Finset.mem_filter.mp hdata.1
    apply Finset.mem_filter.mpr
    refine ⟨hbase.1, hbase.2.1, ?_⟩
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | haS
    · intro hpa
      exact hdata.2 (Finset.mem_filter.mpr ⟨hdata.1, hpa⟩)
    · exact hbase.2.2 a haS

/-- Adjoining one forbidden positive integer costs at most its Euler factor
in squarefree harmonic mass.  Prime-ness is not needed for this one-step
inequality. -/
theorem eulerFactor_mul_squarefreeAvoidingHarmonic_le_insert
    (S : Finset ℕ) (z p : ℕ) (hp : 0 < p) :
    (1 - 1 / (p : ℝ)) * squarefreeAvoidingHarmonic S z ≤
      squarefreeAvoidingHarmonic (insert p S) z := by
  let A := squarefreeAvoidingSet S z
  let D := A.filter fun n ↦ p ∣ n
  have hD : D ⊆ A := Finset.filter_subset _ _
  have hsplit :
      (∑ n ∈ A \ D, 1 / (n : ℝ)) +
          (∑ n ∈ D, 1 / (n : ℝ)) =
        ∑ n ∈ A, 1 / (n : ℝ) :=
    Finset.sum_sdiff hD
  have hdiv := divisible_squarefreeAvoidingHarmonic_le (S := S) (z := z) hp
  change (∑ n ∈ D, 1 / (n : ℝ)) ≤
      (1 / (p : ℝ)) * (∑ n ∈ A, 1 / (n : ℝ)) at hdiv
  change (1 - 1 / (p : ℝ)) * (∑ n ∈ A, 1 / (n : ℝ)) ≤
    ∑ n ∈ squarefreeAvoidingSet (insert p S) z, 1 / (n : ℝ)
  rw [squarefreeAvoidingSet_insert]
  change (1 - 1 / (p : ℝ)) * (∑ n ∈ A, 1 / (n : ℝ)) ≤
    ∑ n ∈ A \ D, 1 / (n : ℝ)
  linarith

/-- Iterating the one-prime deletion inequality over a finite forbidden set. -/
theorem eulerProduct_mul_squarefreeAvoidingHarmonic_empty_le
    (S : Finset ℕ) (z : ℕ) (hpos : ∀ p ∈ S, 0 < p) :
    (∏ p ∈ S, (1 - 1 / (p : ℝ))) *
        squarefreeAvoidingHarmonic ∅ z ≤
      squarefreeAvoidingHarmonic S z := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
      have hp : 0 < p := hpos p (Finset.mem_insert_self p S)
      have hfac : 0 ≤ 1 - 1 / (p : ℝ) := by
        have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
        have hinv : 1 / (p : ℝ) ≤ 1 := by
          simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hpR)
        linarith
      have ih' := ih (fun q hq ↦ hpos q (Finset.mem_insert_of_mem hq))
      rw [Finset.prod_insert hpS]
      calc
        ((1 - 1 / (p : ℝ)) * ∏ q ∈ S, (1 - 1 / (q : ℝ))) *
            squarefreeAvoidingHarmonic ∅ z =
          (1 - 1 / (p : ℝ)) *
            ((∏ q ∈ S, (1 - 1 / (q : ℝ))) *
              squarefreeAvoidingHarmonic ∅ z) := by ring
        _ ≤ (1 - 1 / (p : ℝ)) *
              squarefreeAvoidingHarmonic S z :=
          mul_le_mul_of_nonneg_left ih' hfac
        _ ≤ squarefreeAvoidingHarmonic (insert p S) z :=
          eulerFactor_mul_squarefreeAvoidingHarmonic_le_insert S z p hp

theorem coprime_iff_avoids_primeFactors
    {n modulus : ℕ} (hmodulus : 0 < modulus) :
    n.Coprime modulus ↔ ∀ p ∈ modulus.primeFactors, ¬p ∣ n := by
  constructor
  · intro hcop p hpq hpn
    have hpprime := Nat.prime_of_mem_primeFactors hpq
    have hpm := Nat.dvd_of_mem_primeFactors hpq
    have hself : p.Coprime p := Nat.Coprime.of_dvd hpn hpm hcop
    exact hpprime.ne_one (hself.eq_one_of_dvd (dvd_refl p))
  · intro hav
    apply Nat.coprime_of_dvd
    intro p hpprime hpn hpm
    have hpq : p ∈ modulus.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpprime, hpm, hmodulus.ne'⟩
    exact hav p hpq hpn

theorem squarefreeCoprimeHarmonic_eq_avoidingPrimeFactors
    {modulus z : ℕ} (hmodulus : 0 < modulus) :
    squarefreeCoprimeHarmonic modulus z =
      squarefreeAvoidingHarmonic modulus.primeFactors z := by
  unfold squarefreeCoprimeHarmonic squarefreeAvoidingHarmonic
  congr 1
  ext n
  simp only [squarefreeAvoidingSet, Finset.mem_filter, Finset.mem_Icc]
  rw [coprime_iff_avoids_primeFactors hmodulus]

theorem totient_div_eq_eulerProduct {modulus : ℕ} (hmodulus : 0 < modulus) :
    (Nat.totient modulus : ℝ) / (modulus : ℝ) =
      ∏ p ∈ modulus.primeFactors, (1 - 1 / (p : ℝ)) := by
  have hQ := Nat.totient_eq_mul_prod_factors modulus
  have hR : (Nat.totient modulus : ℝ) =
      (modulus : ℝ) *
        ∏ p ∈ modulus.primeFactors, (1 - 1 / (p : ℝ)) := by
    have hR0 := congrArg (fun x : ℚ ↦ (x : ℝ)) hQ
    simpa [div_eq_mul_inv] using hR0
  rw [hR]
  field_simp

theorem eulerRatio_mul_squarefreeAvoidingHarmonic_empty_le_coprime
    {modulus z : ℕ} (hmodulus : 0 < modulus) :
    (Nat.totient modulus : ℝ) / (modulus : ℝ) *
        squarefreeAvoidingHarmonic ∅ z ≤
      squarefreeCoprimeHarmonic modulus z := by
  rw [totient_div_eq_eulerProduct hmodulus,
    squarefreeCoprimeHarmonic_eq_avoidingPrimeFactors hmodulus]
  apply eulerProduct_mul_squarefreeAvoidingHarmonic_empty_le
  intro p hp
  exact (Nat.prime_of_mem_primeFactors hp).pos

def realHarmonic (z : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 z, 1 / (n : ℝ)

theorem realHarmonic_nonneg (z : ℕ) : 0 ≤ realHarmonic z := by
  unfold realHarmonic
  positivity

theorem div_image_subset_Icc
    {z k : ℕ} (hk : 0 < k) :
    ((Finset.Icc 1 z).filter fun n ↦ k ∣ n).image (fun n ↦ n / k) ⊆
      Finset.Icc 1 z := by
  intro m hm
  rcases Finset.mem_image.mp hm with ⟨n, hnD, rfl⟩
  have hnIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hnD).1
  have hkn : k ∣ n := (Finset.mem_filter.mp hnD).2
  have hnpos : 0 < n := by omega
  have hdivpos : 0 < n / k := Nat.div_pos (Nat.le_of_dvd hnpos hkn) hk
  exact Finset.mem_Icc.mpr ⟨by omega, (Nat.div_le_self n k).trans hnIcc.2⟩

theorem divisible_realHarmonic_le
    {z k : ℕ} (hk : 0 < k) :
    (∑ n ∈ (Finset.Icc 1 z).filter fun n ↦ k ∣ n, 1 / (n : ℝ)) ≤
      (1 / (k : ℝ)) * realHarmonic z := by
  let D := (Finset.Icc 1 z).filter fun n ↦ k ∣ n
  let I := D.image fun n ↦ n / k
  have hI : I ⊆ Finset.Icc 1 z := by
    dsimp [I, D]
    exact div_image_subset_Icc hk
  calc
    (∑ n ∈ D, 1 / (n : ℝ)) =
        (1 / (k : ℝ)) * ∑ m ∈ I, 1 / (m : ℝ) := by
      rw [Finset.sum_image (div_on_multiples_injective (A := Finset.Icc 1 z) hk)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hnD
      have hkn : k ∣ n := (Finset.mem_filter.mp hnD).2
      rw [Nat.cast_div_charZero hkn]
      have hnpos : 0 < n := by
        have hnIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hnD).1
        omega
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
      field_simp
    _ ≤ (1 / (k : ℝ)) * ∑ m ∈ Finset.Icc 1 z, 1 / (m : ℝ) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg hI
        intro m hm hmI
        positivity
      · positivity
    _ = (1 / (k : ℝ)) * realHarmonic z := by rfl

theorem inv_sq_le_telescope {d : ℕ} (hd : 2 ≤ d) :
    1 / (d : ℝ) ^ 2 ≤ 1 / ((d - 1 : ℕ) : ℝ) - 1 / (d : ℝ) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdm1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hdm1]
  have hposd : (0 : ℝ) < d := by positivity
  have hposdm1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  field_simp
  nlinarith

theorem sum_inv_sq_Icc_three_le {z : ℕ} (hz : 2 ≤ z) :
    (∑ d ∈ Finset.Icc 3 z, 1 / (d : ℝ) ^ 2) ≤
      1 / 2 - 1 / (z : ℝ) := by
  induction z, hz using Nat.le_induction with
  | base => norm_num
  | succ z hz ih =>
      have h3 : 3 ≤ z + 1 := by omega
      rw [Finset.sum_Icc_succ_top h3]
      have hstep := inv_sq_le_telescope (d := z + 1) (by omega)
      have hzR : (z : ℝ) ≠ 0 := by exact_mod_cast (by omega : z ≠ 0)
      have hzsR : ((z + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hcast : (((z + 1 : ℕ) - 1 : ℕ) : ℝ) = (z : ℝ) := by
        norm_num
      rw [hcast] at hstep
      linarith

theorem sum_inv_sq_Icc_two_le_three_quarters (z : ℕ) :
    (∑ d ∈ Finset.Icc 2 z, 1 / (d : ℝ) ^ 2) ≤ 3 / 4 := by
  by_cases hz : z < 2
  · have hempty : Finset.Icc 2 z = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty]
    norm_num
  have hz2 : 2 ≤ z := by omega
  by_cases hzEq : z = 2
  · subst z
    norm_num
  have hz3 : 3 ≤ z := by omega
  have hsum := sum_inv_sq_Icc_three_le hz2
  have hsplit :
      (∑ d ∈ Finset.Icc 2 z, 1 / (d : ℝ) ^ 2) =
        1 / (2 : ℝ) ^ 2 + ∑ d ∈ Finset.Icc 3 z, 1 / (d : ℝ) ^ 2 := by
    have hset : Finset.Icc 2 z = insert 2 (Finset.Icc 3 z) := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert (by simp [Finset.mem_Icc])]
    simp
  rw [hsplit]
  have hzR : (0 : ℝ) ≤ 1 / (z : ℝ) := by positivity
  have hsum' : (∑ d ∈ Finset.Icc 3 z, 1 / (d : ℝ) ^ 2) ≤ 1 / 2 :=
    hsum.trans (sub_le_self _ hzR)
  norm_num at hsum ⊢
  norm_num at hsum'
  linarith

def nonSquarefreeHarmonic (z : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 z).filter (fun n ↦ ¬Squarefree n), 1 / (n : ℝ)

theorem bad_has_square_divisor
    {n : ℕ} (hnpos : 0 < n) (hbad : ¬Squarefree n) :
    ∃ d ∈ Finset.Icc 2 n, d * d ∣ n := by
  rw [Nat.squarefree_iff_prime_squarefree] at hbad
  push_neg at hbad
  rcases hbad with ⟨p, hpprime, hpsq⟩
  refine ⟨p, Finset.mem_Icc.mpr ⟨hpprime.two_le, ?_⟩, hpsq⟩
  have hpd : p ∣ n := dvd_trans (dvd_mul_right p p) hpsq
  exact Nat.le_of_dvd hnpos hpd

theorem nonSquarefreeHarmonic_le_squareDivisorDoubleSum (z : ℕ) :
    nonSquarefreeHarmonic z ≤
      ∑ d ∈ Finset.Icc 2 z,
        ∑ n ∈ (Finset.Icc 1 z).filter (fun n ↦ d * d ∣ n),
          1 / (n : ℝ) := by
  let B := (Finset.Icc 1 z).filter (fun n ↦ ¬Squarefree n)
  let I := Finset.Icc 1 z
  let D := Finset.Icc 2 z
  have hBI : B ⊆ I := Finset.filter_subset _ _
  calc
    nonSquarefreeHarmonic z = ∑ n ∈ B, 1 / (n : ℝ) := by rfl
    _ ≤ ∑ n ∈ B, ∑ d ∈ D,
          if d * d ∣ n then 1 / (n : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro n hnB
      have hnData := Finset.mem_filter.mp hnB
      have hnIcc := Finset.mem_Icc.mp hnData.1
      obtain ⟨d, hd, hdsq⟩ := bad_has_square_divisor (by omega) hnData.2
      have hdD : d ∈ D := by
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
          (Finset.mem_Icc.mp hd).2.trans hnIcc.2⟩
      calc
        1 / (n : ℝ) = if d * d ∣ n then 1 / (n : ℝ) else 0 := by simp [hdsq]
        _ ≤ ∑ e ∈ D, if e * e ∣ n then 1 / (n : ℝ) else 0 := by
          exact Finset.single_le_sum
            (s := D) (f := fun e ↦ if e * e ∣ n then 1 / (n : ℝ) else 0)
            (fun e he ↦ by
              by_cases h : e * e ∣ n <;> simp [h] <;> positivity) hdD
    _ ≤ ∑ n ∈ I, ∑ d ∈ D,
          if d * d ∣ n then 1 / (n : ℝ) else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hBI
      intro n hnI hnB
      positivity
    _ = ∑ d ∈ D, ∑ n ∈ I,
          if d * d ∣ n then 1 / (n : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ D,
        ∑ n ∈ I.filter (fun n ↦ d * d ∣ n), 1 / (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_filter]

theorem nonSquarefreeHarmonic_le_three_quarters (z : ℕ) :
    nonSquarefreeHarmonic z ≤ (3 / 4 : ℝ) * realHarmonic z := by
  calc
    nonSquarefreeHarmonic z ≤
        ∑ d ∈ Finset.Icc 2 z,
          ∑ n ∈ (Finset.Icc 1 z).filter (fun n ↦ d * d ∣ n),
            1 / (n : ℝ) := nonSquarefreeHarmonic_le_squareDivisorDoubleSum z
    _ ≤ ∑ d ∈ Finset.Icc 2 z,
          (1 / (d : ℝ) ^ 2) * realHarmonic z := by
      apply Finset.sum_le_sum
      intro d hd
      have hd2 : 2 ≤ d := (Finset.mem_Icc.mp hd).1
      have hmul := divisible_realHarmonic_le (z := z) (k := d * d) (by positivity)
      calc
        (∑ n ∈ (Finset.Icc 1 z).filter (fun n ↦ d * d ∣ n),
            1 / (n : ℝ)) ≤
          (1 / ((d * d : ℕ) : ℝ)) * realHarmonic z := hmul
        _ = (1 / (d : ℝ) ^ 2) * realHarmonic z := by
          push_cast
          ring
    _ = (∑ d ∈ Finset.Icc 2 z, 1 / (d : ℝ) ^ 2) *
          realHarmonic z := by rw [Finset.sum_mul]
    _ ≤ (3 / 4 : ℝ) * realHarmonic z := by
      apply mul_le_mul_of_nonneg_right (sum_inv_sq_Icc_two_le_three_quarters z)
      exact realHarmonic_nonneg z

theorem realHarmonic_eq_squarefree_add_bad (z : ℕ) :
    realHarmonic z =
      squarefreeAvoidingHarmonic ∅ z + nonSquarefreeHarmonic z := by
  unfold realHarmonic squarefreeAvoidingHarmonic nonSquarefreeHarmonic
  have hempty : squarefreeAvoidingSet ∅ z =
      (Finset.Icc 1 z).filter Squarefree := by
    ext n
    simp [squarefreeAvoidingSet]
  rw [hempty, Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hsq : Squarefree n <;> simp [hsq]

theorem one_quarter_realHarmonic_le_squarefreeAvoiding_empty (z : ℕ) :
    (1 / 4 : ℝ) * realHarmonic z ≤ squarefreeAvoidingHarmonic ∅ z := by
  have hbad := nonSquarefreeHarmonic_le_three_quarters z
  have hsplit := realHarmonic_eq_squarefree_add_bad z
  linarith

theorem log_le_realHarmonic (z : ℕ) :
    Real.log (z : ℝ) ≤ realHarmonic z := by
  by_cases hz : z = 0
  · subst z
    simp [realHarmonic]
  have hh := log_add_one_le_harmonic z
  have hcast : ((harmonic z : ℚ) : ℝ) = realHarmonic z := by
    rw [harmonic_eq_sum_Icc]
    simp [realHarmonic]
  have hlogmono : Real.log (z : ℝ) ≤ Real.log (z + 1 : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero hz
    · norm_num
  rw [hcast] at hh
  exact hlogmono.trans (by simpa using hh)

theorem quarter_eulerRatio_log_le_squarefreeCoprimeHarmonic
    {modulus z : ℕ} (hmodulus : 0 < modulus) :
    (1 / 4 : ℝ) * ((Nat.totient modulus : ℝ) / (modulus : ℝ)) *
        Real.log (z : ℝ) ≤ squarefreeCoprimeHarmonic modulus z := by
  have hratio : 0 ≤ (Nat.totient modulus : ℝ) / (modulus : ℝ) := by positivity
  have hlogH := log_le_realHarmonic z
  have hsq := one_quarter_realHarmonic_le_squarefreeAvoiding_empty z
  have hdel := eulerRatio_mul_squarefreeAvoidingHarmonic_empty_le_coprime
    (z := z) hmodulus
  calc
    (1 / 4 : ℝ) * ((Nat.totient modulus : ℝ) / (modulus : ℝ)) *
        Real.log (z : ℝ) ≤
      ((Nat.totient modulus : ℝ) / (modulus : ℝ)) *
        ((1 / 4 : ℝ) * realHarmonic z) := by
          nlinarith [mul_le_mul_of_nonneg_left hlogH hratio]
    _ ≤ ((Nat.totient modulus : ℝ) / (modulus : ℝ)) *
        squarefreeAvoidingHarmonic ∅ z :=
      mul_le_mul_of_nonneg_left hsq hratio
    _ ≤ squarefreeCoprimeHarmonic modulus z := hdel

theorem squarefree_coprime_dvd_sievingProduct
    {n z modulus : ℕ} (hnpos : 0 < n) (hnz : n ≤ z)
    (hnsq : Squarefree n) (hncop : n.Coprime modulus) :
    n ∣ sievingProduct z modulus := by
  rw [← Nat.prod_primeFactors_of_squarefree hnsq]
  apply Finset.prod_dvd_prod_of_subset n.primeFactors (sievingPrimes z modulus) id
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hppos : 0 < p := hpprime.pos
  have hple : p ≤ z := (Nat.le_of_dvd hnpos hpdvd).trans hnz
  have hpnot : ¬p ∣ modulus := by
    exact (hpprime.coprime_iff_not_dvd.mp
      (Nat.Coprime.of_dvd hpdvd (dvd_refl modulus) hncop))
  simp [sievingPrimes, hpprime, hpnot, hple]

theorem squarefree_coprime_mem_levelDivisors
    {n z modulus : ℕ} (hnpos : 0 < n) (hnz : n ≤ z)
    (hnsq : Squarefree n) (hncop : n.Coprime modulus) :
    n ∈ levelDivisors (sievingProduct z modulus) z := by
  apply Finset.mem_filter.mpr
  exact ⟨Nat.mem_divisors.mpr
    ⟨squarefree_coprime_dvd_sievingProduct hnpos hnz hnsq hncop,
      (sievingProduct_pos z modulus).ne'⟩, hnz⟩

theorem denominator_summand_eq_inv_totient_of_squarefree
    {n : ℕ} (hnsq : Squarefree n) :
    (ArithmeticFunction.moebius n : ℝ) ^ 2 / (Nat.totient n : ℝ) =
      1 / (Nat.totient n : ℝ) := by
  rw [show (ArithmeticFunction.moebius n : ℝ) ^ 2 = 1 by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hnsq]

theorem inv_nat_le_inv_totient {n : ℕ} (hnpos : 0 < n) :
    1 / (n : ℝ) ≤ 1 / (Nat.totient n : ℝ) := by
  have hphiPosNat : 0 < Nat.totient n := (Nat.totient_pos).2 hnpos
  have hphiPos : (0 : ℝ) < Nat.totient n := by exact_mod_cast hphiPosNat
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hnpos
  apply one_div_le_one_div_of_le hphiPos
  exact_mod_cast Nat.totient_le n

/-- The finite Selberg denominator termwise dominates the squarefree harmonic
mass of integers coprime to the progression modulus. -/
theorem squarefreeCoprimeHarmonic_le_selbergDenominator
    (modulus z : ℕ) :
    squarefreeCoprimeHarmonic modulus z ≤
      selbergDenominator (sievingProduct z modulus) z := by
  unfold squarefreeCoprimeHarmonic selbergDenominator
  let S := (Finset.Icc 1 z).filter
      (fun n ↦ Squarefree n ∧ n.Coprime modulus)
  let L := levelDivisors (sievingProduct z modulus) z
  have hSL : S ⊆ L := by
    intro n hn
    have hdata := Finset.mem_filter.mp hn
    have hnIcc := Finset.mem_Icc.mp hdata.1
    exact squarefree_coprime_mem_levelDivisors
      (by omega) hnIcc.2 hdata.2.1 hdata.2.2
  calc
    (∑ n ∈ S, 1 / (n : ℝ)) ≤
        ∑ n ∈ S,
          (ArithmeticFunction.moebius n : ℝ) ^ 2 /
            (Nat.totient n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hdata := Finset.mem_filter.mp hn
      have hnIcc := Finset.mem_Icc.mp hdata.1
      rw [denominator_summand_eq_inv_totient_of_squarefree hdata.2.1]
      exact inv_nat_le_inv_totient (by omega)
    _ ≤ ∑ n ∈ L,
          (ArithmeticFunction.moebius n : ℝ) ^ 2 /
            (Nat.totient n : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSL
      intro n hnL hnS
      positivity

/-- Fully elementary denominator lower bound with explicit absolute constant
`c=1/4`. -/
theorem quarter_totient_log_le_selbergDenominator
    {modulus z : ℕ} (hmodulus : 0 < modulus) :
    (1 / 4 : ℝ) * (Nat.totient modulus : ℝ) / (modulus : ℝ) *
        Real.log (z : ℝ) ≤
      selbergDenominator (sievingProduct z modulus) z := by
  have h := (quarter_eulerRatio_log_le_squarefreeCoprimeHarmonic
    (z := z) hmodulus).trans
      (squarefreeCoprimeHarmonic_le_selbergDenominator modulus z)
  convert h using 1 <;> ring

/-- The independently proved explicit denominator bound closes the public
Selberg main-weight contract used in the specialized Shiu theorem. -/
theorem certifiedSelbergMainWeightBound : SelbergMainWeightBound := by
  apply ShiuSelbergMainWeight.selbergMainWeightBound_of_uniform_denominator_lower
    (c := (1 / 4 : ℝ)) (by norm_num)
  intro z modulus hmodulus hz
  have h := quarter_totient_log_le_selbergDenominator
    (z := z) hmodulus
  simpa [selbergDenominator, levelDivisors,
    ShiuSelbergMainWeight.selbergDenominator,
    ShiuSelbergMainWeight.levelDivisors] using h

/-- Shiu's published finite upper-bound-sieve Lemma 2, now inhabited with no
remaining premise. -/
theorem certifiedSelbergUpperBoundSieve : SelbergUpperBoundSieveContract :=
  ShiuSieveSlice.selbergUpperBoundSieve_of_mainWeightBound
    certifiedSelbergMainWeightBound

end ShiuSelbergDenominatorLower

#print axioms ShiuSelbergDenominatorLower.squarefree_coprime_dvd_sievingProduct
#print axioms ShiuSelbergDenominatorLower.squarefreeCoprimeHarmonic_le_selbergDenominator
#print axioms ShiuSelbergDenominatorLower.quarter_totient_log_le_selbergDenominator

#print axioms ShiuSelbergDenominatorLower.certifiedSelbergMainWeightBound
#print axioms ShiuSelbergDenominatorLower.certifiedSelbergUpperBoundSieve
