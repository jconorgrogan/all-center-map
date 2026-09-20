import ShiuSection5Structure

/-!
# Shiu Section 5: the class-I contribution

This file develops the literal class-I branch of Shiu's Section 5 split for
the MAP weight `tau_k^2`.  The first structural issue is that the promoted
canonical prefix and suffix must be shown coprime: they are products of
disjoint portions of the ordered complete prime-power blocks.  This is needed
before multiplicativity can turn the weight of `n = b_n d_n` into the product
of the two source weights.
-/

namespace ShiuClassIBound

open ArithmeticFunction MixedMellinCert ShiuFoundation ShiuSection5Split
  ShiuSection5Structure
open scoped ArithmeticFunction.zeta BigOperators

noncomputable section

/-- Literal natural cutoff `floor (log X * log log X)` used by the promoted
Section-5 classifier. -/
def smoothCutoff (X : ℕ) : ℕ :=
  ⌊Real.log (X : ℝ) * Real.log (Real.log (X : ℝ))⌋₊

/-- The rounded MAP choice corresponding to Shiu's `z = y^(1/30)`. -/
def sectionFiveZ (Y : ℕ) : ℕ :=
  ⌈(Y : ℝ) ^ (1 / 30 : ℝ)⌉₊

/-- Natural mass of the literal canonical class-I set. -/
def classIMass (k X Y modulus residue Z cutoff : ℕ) : ℕ :=
  ∑ n ∈ classSet FourClass.I X Y modulus residue Z cutoff, tauAF k n ^ 2

/-- Shiu's class-I Selberg level, the integer implementation of `sqrt z`. -/
def classISieveLevel (Z : ℕ) : ℕ := Nat.sqrt Z

/-- Safe natural quotient length.  Away from the lower endpoint this is the
source length `Y / b` with one rounding unit; `min` only prevents the rounded
length from exceeding its upper endpoint, as required by the certified
natural-number Lemma 2 interface. -/
def quotientLength (X Y b : ℕ) : ℕ := min (Y / b + 1) (X / b)

/-- The class-I fiber having a fixed canonical prefix `b_n = b`. -/
def classIFiber (X Y modulus residue Z cutoff b : ℕ) : Finset ℕ :=
  (classSet FourClass.I X Y modulus residue Z cutoff).filter fun n ↦
    canonicalB n Z = b

/-- The outer `b`-range in (5.3), including its coprimality mask. -/
def classIOuterPrefixes (Z modulus : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Z).filter fun b ↦ b.Coprime modulus

/-- The exact harmonic prefix factor in Shiu's line immediately before
equation (5.3). -/
def classIHarmonicPrefix (k Z modulus : ℕ) : ℝ :=
  ∑ b ∈ classIOuterPrefixes Z modulus,
    (tauAF k b ^ 2 : ℝ) / (b : ℝ)

/-- The exact rounded quotient set injected into Shiu's `Phi` after fixing
the canonical prefix `b`. -/
def classIQuotientSet
    (X Y modulus residue' Z b : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (X / b - quotientLength X Y b) (X / b)).filter fun d ↦
    d ≡ residue' [MOD modulus] ∧ 1 < d ∧
      ∀ p : ℕ, p.Prime → p ≤ classISieveLevel Z → ¬p ∣ d

/-- Exact equation-(5.3) analytic surface.  The hidden source constant is made
explicit as `C`; the logarithm and the omitted-prime exponential are kept at
the manuscript parameter `Z`, not silently enlarged to `X`. -/
def classIFiveThreeRHS
    (k Y modulus Z : ℕ) (C : ℝ) : ℝ :=
  C * ((Y : ℝ) /
        ((Nat.totient modulus : ℝ) * Real.log (Z : ℝ)) +
      (Z : ℝ) ^ 2) *
    Real.exp
      (ShiuUniformContract.omittedPrimeSum
        ((tauAF k).pmul (tauAF k)) Z modulus)

/-- Literal eventual class-I contribution (5.3), specialized to `tau_k^2`
and to the exact promoted class set. -/
def ClassIFiveThreeBound : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ C : ℝ, 0 < C ∧
      ∃ X₀ : ℕ, 3 ≤ X₀ ∧
        ∀ X Y modulus residue : ℕ,
          X₀ ≤ X →
          0 < modulus →
          residue < modulus →
          residue.Coprime modulus →
          Y ≤ X →
          X < Y ^ 3 →
          modulus ^ 3 < Y ^ 2 →
          let Z := sectionFiveZ Y
          let cutoff := smoothCutoff X
          (classIMass k X Y modulus residue Z cutoff : ℝ) ≤
            classIFiveThreeRHS k Y modulus Z C

/-- The exact natural class-I conjunct requested by
`ShiuEndToEnd.SectionFiveClassEstimates`: same set, rounded `Z`, cutoff,
base-two logarithm, exponent `k*k`, and uniform eventual quantifiers. -/
def ClassIContributionBound : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ C X₀ : ℕ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ X Y modulus residue : ℕ,
        X₀ ≤ X →
        0 < modulus →
        residue < modulus →
        residue.Coprime modulus →
        Y ≤ X →
        X < Y ^ 3 →
        modulus ^ 3 < Y ^ 2 →
        let Z := sectionFiveZ Y
        let cutoff := smoothCutoff X
        modulus * classIMass k X Y modulus residue Z cutoff ≤
          C * Y * (Nat.log 2 (X + 2) + 1) ^ (k * k)

/-- The exact class-I mass is the sum over the manuscript's outer variable
`1 ≤ b ≤ Z` of the fixed-canonical-prefix fibers. -/
theorem classIMass_eq_sum_fibers
    (k X Y modulus residue Z cutoff : ℕ) (hZ : 1 ≤ Z) :
    classIMass k X Y modulus residue Z cutoff =
      ∑ b ∈ Finset.Icc 1 Z,
        ∑ n ∈ classIFiber X Y modulus residue Z cutoff b,
          tauAF k n ^ 2 := by
  classical
  unfold classIMass classIFiber
  symm
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hbmem : canonicalB n Z ∈ Finset.Icc 1 Z :=
    Finset.mem_Icc.mpr ⟨canonicalB_pos n Z, canonicalB_le hZ⟩
  rw [Finset.sum_eq_single_of_mem (canonicalB n Z) hbmem]
  · simp
  · intro b hb hne
    simp [hne.symm]

lemma mem_classSet_pos
    {c : FourClass} {X Y modulus residue Z cutoff n : ℕ}
    (hn : n ∈ classSet c X Y modulus residue Z cutoff) : 0 < n := by
  have hwin := (mem_classSet_iff.mp hn).1
  have hIoc := Finset.mem_Ioc.mp (Finset.mem_filter.mp hwin).1
  omega

/-- Every canonical prefix occurring in class I belongs to the literal
outer range `1 ≤ b ≤ Z` in Shiu's displayed sum. -/
lemma canonicalB_mem_Icc_of_mem_classI
    {X Y modulus residue Z cutoff n : ℕ} (hZ : 1 ≤ Z)
    (hn : n ∈ classSet FourClass.I X Y modulus residue Z cutoff) :
    canonicalB n Z ∈ Finset.Icc 1 Z := by
  exact Finset.mem_Icc.mpr
    ⟨canonicalB_pos n Z, canonicalB_le hZ⟩

/-- In a primitive progression the canonical prefix is coprime to the
progression modulus, as required by the harmonic `b`-sum in (5.3). -/
lemma canonicalB_coprime_modulus_of_mem_classI
    {X Y modulus residue Z cutoff n : ℕ} (hZ : 1 ≤ Z)
    (hres : residue.Coprime modulus)
    (hn : n ∈ classSet FourClass.I X Y modulus residue Z cutoff) :
    (canonicalB n Z).Coprime modulus := by
  have hn0 : n ≠ 0 := (mem_classSet_pos hn).ne'
  have hmod := (Finset.mem_filter.mp (mem_classSet_iff.mp hn).1).2
  have hncop := ShiuSieveSlice.coprime_of_modEq_primitive hmod hres
  exact Nat.Coprime.of_dvd_left (canonicalB_dvd hn0 hZ) hncop

/-- The class-I least-prime-factor inequality itself rules out the exceptional
suffix `1`: for that suffix it would assert `Z < 1`. -/
lemma canonicalD_ne_one_of_mem_classI
    {X Y modulus residue Z cutoff n : ℕ} (hZ : 1 ≤ Z)
    (hn : n ∈ classSet FourClass.I X Y modulus residue Z cutoff) :
    canonicalD n Z ≠ 1 := by
  intro hd
  have hclass := (mem_class_I_iff.mp hn).2
  simp [leastPrimeFactor, hd] at hclass
  omega

/-- The class-I least-prime-factor condition is exactly the no-small-prime
predicate consumed by `ShiuSieveSlice.shiuPhi` at level `floor(sqrt Z)`. -/
lemma no_small_prime_dvd_canonicalD_of_mem_classI
    {X Y modulus residue Z cutoff n : ℕ}
    (hd1 : canonicalD n Z ≠ 1)
    (hn : n ∈ classSet FourClass.I X Y modulus residue Z cutoff) :
    ∀ p : ℕ, p.Prime → p ≤ classISieveLevel Z →
      ¬ p ∣ canonicalD n Z := by
  intro p hp hpZ hpd
  have hclass := (mem_class_I_iff.mp hn).2
  have hlpf : leastPrimeFactor (canonicalD n Z) = (canonicalD n Z).minFac := by
    simp [leastPrimeFactor, hd1]
  have hminle : (canonicalD n Z).minFac ≤ p :=
    Nat.minFac_le_of_dvd hp.two_le hpd
  have hsqrt : (Nat.sqrt Z) ^ 2 ≤ Z := by
    simpa [pow_two] using Nat.sqrt_le Z
  have hpSq : p ^ 2 ≤ Z := by
    exact (Nat.pow_le_pow_left hpZ 2).trans hsqrt
  rw [hlpf] at hclass
  nlinarith

/-- Division by a positive fixed prefix sends the original half-open window
into the safe rounded quotient window of length `Y / b + 1`. -/
lemma canonicalD_mem_rounded_quotientWindow
    {X Y n b : ℕ} (hb : 0 < b) (hYX : Y ≤ X)
    (hnlo : X - Y < n) (hnhi : n ≤ X) (hnb : b ∣ n) :
    n / b ∈ Finset.Ioc (X / b - quotientLength X Y b) (X / b) := by
  have hnpos : 0 < n := by omega
  have hdpos : 0 < n / b := Nat.div_pos (Nat.le_of_dvd hnpos hnb) hb
  have hupper : n / b ≤ X / b := Nat.div_le_div_right hnhi
  by_cases hlen : Y / b + 1 ≤ X / b
  · have hq : quotientLength X Y b = Y / b + 1 := min_eq_left hlen
    rw [hq]
    apply Finset.mem_Ioc.mpr ⟨?_, hupper⟩
    by_contra hnot
    have hle : n / b ≤ X / b - (Y / b + 1) := Nat.le_of_not_gt hnot
    have hnEq : b * (n / b) = n := Nat.mul_div_cancel' hnb
    have hYlt : Y < b * (Y / b + 1) := by
      have hmodlt : Y % b < b := Nat.mod_lt Y hb
      have hmodEq : Y % b + b * (Y / b) = Y := Nat.mod_add_div Y b
      rw [mul_add]
      omega
    have hXlt : X < b * (n / b + (Y / b + 1)) := by
      rw [mul_add, hnEq]
      have hnX : X < Y + n := (Nat.sub_lt_iff_lt_add' hYX).mp hnlo
      omega
    have hdivlt : X / b < n / b + (Y / b + 1) := by
      rw [Nat.div_lt_iff_lt_mul hb]
      simpa [mul_comm] using hXlt
    omega
  · have hq : quotientLength X Y b = X / b :=
      min_eq_right (Nat.le_of_not_ge hlen)
    rw [hq, Nat.sub_self]
    exact Finset.mem_Ioc.mpr ⟨hdpos, hupper⟩

/-- A prefix coprime to the modulus has a unique quotient residue.  This is
the source's `a'`, characterized by `b a' = a (mod modulus)`. -/
theorem exists_quotientResidue
    {b residue modulus : ℕ} (hmodulus : 0 < modulus)
    (hbmod : b.Coprime modulus) :
    ∃ residue' : ℕ, residue' < modulus ∧
      b * residue' ≡ residue [MOD modulus] ∧
      ∀ d : ℕ, b * d ≡ residue [MOD modulus] →
        d ≡ residue' [MOD modulus] := by
  let u : (ZMod modulus)ˣ := ZMod.unitOfCoprime b hbmod
  let aZ : ZMod modulus := (u⁻¹ : (ZMod modulus)ˣ) * (residue : ZMod modulus)
  letI : NeZero modulus := ⟨hmodulus.ne'⟩
  let residue' := aZ.val
  have hreslt : residue' < modulus := ZMod.val_lt aZ
  have hbaZ : (b : ZMod modulus) * (residue' : ZMod modulus) =
      (residue : ZMod modulus) := by
    have hu : ((u : (ZMod modulus)ˣ) : ZMod modulus) = (b : ZMod modulus) :=
      ZMod.coe_unitOfCoprime b hbmod
    change (b : ZMod modulus) * (aZ.val : ZMod modulus) = _
    rw [ZMod.natCast_zmod_val]
    dsimp [aZ]
    rw [← hu]
    simp
  have hba : b * residue' ≡ residue [MOD modulus] :=
    (ZMod.natCast_eq_natCast_iff (b * residue') residue modulus).mp (by
      simpa using hbaZ)
  refine ⟨residue', hreslt, hba, ?_⟩
  intro d hd
  apply Nat.ModEq.cancel_left_of_coprime hbmod.symm.gcd_eq_one
  exact hd.trans hba.symm

/-- Chosen natural representative of the source quotient residue `a'`.  Its
specification is used only under the displayed positivity/coprimality
hypotheses. -/
noncomputable def quotientResidue (b residue modulus : ℕ) : ℕ :=
  if h : 0 < modulus ∧ b.Coprime modulus then
    Classical.choose (exists_quotientResidue (residue := residue) h.1 h.2)
  else 0

theorem quotientResidue_spec
    {b residue modulus : ℕ} (hmodulus : 0 < modulus)
    (hbmod : b.Coprime modulus) :
    quotientResidue b residue modulus < modulus ∧
      b * quotientResidue b residue modulus ≡ residue [MOD modulus] ∧
      ∀ d : ℕ, b * d ≡ residue [MOD modulus] →
        d ≡ quotientResidue b residue modulus [MOD modulus] := by
  rw [quotientResidue, dif_pos ⟨hmodulus, hbmod⟩]
  exact Classical.choose_spec
    (exists_quotientResidue (residue := residue) hmodulus hbmod)

/-- Primitivity is preserved when passing from `a` to the quotient residue
`a'`. -/
theorem quotientResidue_coprime
    {b residue modulus : ℕ} (hmodulus : 0 < modulus)
    (hbmod : b.Coprime modulus) (hresidue : residue.Coprime modulus) :
    (quotientResidue b residue modulus).Coprime modulus := by
  have hba := (quotientResidue_spec (residue := residue) hmodulus hbmod).2.1
  have hprod := ShiuSieveSlice.coprime_of_modEq_primitive hba hresidue
  exact Nat.Coprime.of_dvd_left (dvd_mul_left _ _) hprod

/-- Exact fiber partition with the source mask `(b,modulus)=1`; prefixes not
coprime to the modulus cannot occur in a primitive progression. -/
theorem classIMass_eq_sum_coprime_fibers
    (k X Y modulus residue Z cutoff : ℕ) (hZ : 1 ≤ Z)
    (hresidue : residue.Coprime modulus) :
    classIMass k X Y modulus residue Z cutoff =
      ∑ b ∈ classIOuterPrefixes Z modulus,
        ∑ n ∈ classIFiber X Y modulus residue Z cutoff b,
          tauAF k n ^ 2 := by
  classical
  rw [classIMass_eq_sum_fibers k X Y modulus residue Z cutoff hZ]
  symm
  unfold classIOuterPrefixes
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hbmod : b.Coprime modulus
  · simp [hbmod]
  · rw [if_neg hbmod]
    symm
    apply Finset.sum_eq_zero
    intro n hn
    have hnData := Finset.mem_filter.mp hn
    have hbcop := canonicalB_coprime_modulus_of_mem_classI
      hZ hresidue hnData.1
    exact (hbmod (hnData.2 ▸ hbcop)).elim

/-- The rounded quotient set is literally the indicator set counted by the
certified Selberg-sieve `shiuPhi`. -/
theorem shiuPhi_rounded_eq_card_classIQuotientSet
    (X Y modulus residue' Z b : ℕ) :
    ShiuSieveSlice.shiuPhi
        (X / b) (quotientLength X Y b) (classISieveLevel Z) modulus residue' =
      ((classIQuotientSet X Y modulus residue' Z b).card : ℝ) := by
  classical
  simp [ShiuSieveSlice.shiuPhi, classIQuotientSet]

/-- Every integer in a fixed class-I prefix fiber maps to the literal quotient
set counted by `Phi`. -/
theorem canonicalD_mem_classIQuotientSet
    {X Y modulus residue residue' Z cutoff b n : ℕ}
    (hZ : 1 ≤ Z) (hYX : Y ≤ X)
    (hquotient : ∀ d : ℕ, b * d ≡ residue [MOD modulus] →
      d ≡ residue' [MOD modulus])
    (hn : n ∈ classIFiber X Y modulus residue Z cutoff b) :
    canonicalD n Z ∈ classIQuotientSet X Y modulus residue' Z b := by
  classical
  have hndata := Finset.mem_filter.mp hn
  have hnclass := hndata.1
  have hb : canonicalB n Z = b := hndata.2
  have hnpos := mem_classSet_pos hnclass
  have hn0 : n ≠ 0 := hnpos.ne'
  have hbpos : 0 < b := by rw [← hb]; exact canonicalB_pos n Z
  have hwin := (mem_classSet_iff.mp hnclass).1
  have hwinData := Finset.mem_filter.mp hwin
  have hnIoc := Finset.mem_Ioc.mp hwinData.1
  have hdiv : b ∣ n := by rw [← hb]; exact canonicalB_dvd hn0 hZ
  have hdEq : canonicalD n Z = n / b := by simp [canonicalD, hb]
  have hdwin : canonicalD n Z ∈
      Finset.Ioc (X / b - quotientLength X Y b) (X / b) := by
    rw [hdEq]
    exact canonicalD_mem_rounded_quotientWindow hbpos hYX
      hnIoc.1 hnIoc.2 hdiv
  have hmodD : canonicalD n Z ≡ residue' [MOD modulus] := by
    apply hquotient
    rw [← hb, canonicalB_mul_canonicalD hn0 hZ]
    exact hwinData.2
  have hd1 := canonicalD_ne_one_of_mem_classI hZ hnclass
  have hdpos : 0 < canonicalD n Z := by
    have hmul := canonicalB_mul_canonicalD hn0 hZ
    nlinarith [canonicalB_pos n Z]
  have hdgt : 1 < canonicalD n Z := by omega
  refine Finset.mem_filter.mpr ⟨hdwin, ?_⟩
  exact ⟨hmodD, hdgt,
    no_small_prime_dvd_canonicalD_of_mem_classI hd1 hnclass⟩

/-- On a fixed canonical prefix fiber, the quotient map is injective. -/
theorem canonicalD_injectiveOn_classIFiber
    {X Y modulus residue Z cutoff b : ℕ} (hZ : 1 ≤ Z) :
    Set.InjOn (fun n ↦ canonicalD n Z)
      ↑(classIFiber X Y modulus residue Z cutoff b) := by
  intro n hn m hm heq
  have hnData := Finset.mem_filter.mp hn
  have hmData := Finset.mem_filter.mp hm
  have hn0 : n ≠ 0 := (mem_classSet_pos hnData.1).ne'
  have hm0 : m ≠ 0 := (mem_classSet_pos hmData.1).ne'
  change canonicalD n Z = canonicalD m Z at heq
  calc
    n = canonicalB n Z * canonicalD n Z :=
      (canonicalB_mul_canonicalD hn0 hZ).symm
    _ = b * canonicalD n Z := by rw [hnData.2]
    _ = b * canonicalD m Z := by rw [heq]
    _ = canonicalB m Z * canonicalD m Z := by rw [hmData.2]
    _ = m := canonicalB_mul_canonicalD hm0 hZ

/-- Exact fixed-`b` finite reduction preceding Lemma 2.  The sole parameter
`D` is a pointwise class-I bound for the suffix weight; no progression or
class contribution estimate is assumed. -/
theorem classIFiber_tauSquare_cast_le_phi
    (k X Y modulus residue residue' Z cutoff b D : ℕ)
    (hZ : 1 ≤ Z) (hYX : Y ≤ X)
    (hquotient : ∀ d : ℕ, b * d ≡ residue [MOD modulus] →
      d ≡ residue' [MOD modulus])
    (hDbound : ∀ n ∈ classIFiber X Y modulus residue Z cutoff b,
      tauAF k (canonicalD n Z) ^ 2 ≤ D) :
    ((∑ n ∈ classIFiber X Y modulus residue Z cutoff b,
        tauAF k n ^ 2 : ℕ) : ℝ) ≤
      (D : ℝ) * (tauAF k b ^ 2 : ℝ) *
        ShiuSieveSlice.shiuPhi
          (X / b) (quotientLength X Y b) (classISieveLevel Z) modulus residue' := by
  let F := classIFiber X Y modulus residue Z cutoff b
  let Q := classIQuotientSet X Y modulus residue' Z b
  have hmaps : Set.MapsTo (fun n ↦ canonicalD n Z) ↑F ↑Q := by
    intro n hn
    exact canonicalD_mem_classIQuotientSet hZ hYX hquotient hn
  have hcard : F.card ≤ Q.card :=
    Finset.card_le_card_of_injOn (fun n ↦ canonicalD n Z) hmaps
      (canonicalD_injectiveOn_classIFiber hZ)
  have hsum : (∑ n ∈ F, tauAF k n ^ 2) ≤
      F.card * (tauAF k b ^ 2 * D) := by
    refine (Finset.sum_le_card_nsmul F (fun n ↦ tauAF k n ^ 2)
      (tauAF k b ^ 2 * D) ?_).trans_eq ?_
    · intro n hn
      have hnData := Finset.mem_filter.mp hn
      have hn0 : n ≠ 0 := (mem_classSet_pos hnData.1).ne'
      change tauAF k n ^ 2 ≤ tauAF k b ^ 2 * D
      rw [tauSquare_canonical_factorization k hn0 hZ, hnData.2]
      exact Nat.mul_le_mul_left _ (hDbound n hn)
    · simp
  have hsum' : (∑ n ∈ F, tauAF k n ^ 2) ≤
      Q.card * (tauAF k b ^ 2 * D) :=
    hsum.trans (Nat.mul_le_mul_right _ hcard)
  have hsumR : ((∑ n ∈ F, tauAF k n ^ 2 : ℕ) : ℝ) ≤
      ((Q.card * (tauAF k b ^ 2 * D) : ℕ) : ℝ) := by
    exact_mod_cast hsum'
  calc
    ((∑ n ∈ classIFiber X Y modulus residue Z cutoff b,
        tauAF k n ^ 2 : ℕ) : ℝ) ≤
        ((Q.card * (tauAF k b ^ 2 * D) : ℕ) : ℝ) := by
      simpa [F] using hsumR
    _ = (D : ℝ) * (tauAF k b ^ 2 : ℝ) *
        ShiuSieveSlice.shiuPhi
          (X / b) (quotientLength X Y b) (classISieveLevel Z) modulus residue' := by
      rw [shiuPhi_rounded_eq_card_classIQuotientSet]
      dsimp [Q]
      push_cast
      ring

/-- Complete finite reduction of the exact class-I mass to the manuscript's
outer harmonic-prefix sum of Selberg `Phi` terms.  What remains before applying
Lemma 2 is only the source pointwise constant bound for `f(d_n)`. -/
theorem classIMass_cast_le_phi_sum
    (k X Y modulus residue Z cutoff D : ℕ)
    (hZ : 1 ≤ Z) (hYX : Y ≤ X)
    (hmodulus : 0 < modulus) (hresidue : residue.Coprime modulus)
    (hDbound : ∀ n ∈ classSet FourClass.I X Y modulus residue Z cutoff,
      tauAF k (canonicalD n Z) ^ 2 ≤ D) :
    (classIMass k X Y modulus residue Z cutoff : ℝ) ≤
      (D : ℝ) *
        ∑ b ∈ classIOuterPrefixes Z modulus,
          (tauAF k b ^ 2 : ℝ) *
            ShiuSieveSlice.shiuPhi
              (X / b) (quotientLength X Y b) (classISieveLevel Z)
              modulus (quotientResidue b residue modulus) := by
  rw [classIMass_eq_sum_coprime_fibers k X Y modulus residue Z cutoff hZ hresidue]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have hbmod : b.Coprime modulus :=
    (Finset.mem_filter.mp hb).2
  have hquotient :=
    (quotientResidue_spec (residue := residue) hmodulus hbmod).2.2
  have hfiber := classIFiber_tauSquare_cast_le_phi
    k X Y modulus residue (quotientResidue b residue modulus) Z cutoff b D
    hZ hYX hquotient
    (fun n hn ↦ hDbound n (Finset.mem_filter.mp hn).1)
  simpa [mul_assoc, mul_left_comm, mul_comm] using hfiber

/-- A fixed absolute constant extracted once from the certified Selberg
upper-bound sieve.  Fixing it here, rather than choosing it separately for
every parameter tuple, preserves the uniform eventual quantifiers in (5.3). -/
noncomputable def classISelbergConstant : ℝ :=
  Classical.choose
    ShiuSelbergDenominatorLower.certifiedSelbergUpperBoundSieve

theorem classISelbergConstant_pos : 0 < classISelbergConstant :=
  (Classical.choose_spec
    ShiuSelbergDenominatorLower.certifiedSelbergUpperBoundSieve).1

theorem classISelbergUpperBound :
    ∀ x y z modulus residue : ℕ,
      0 < modulus → residue < modulus → residue.Coprime modulus →
      modulus < y → y ≤ x → 2 ≤ z →
      ShiuSieveSlice.shiuPhi x y z modulus residue ≤
        classISelbergConstant *
          ((y : ℝ) /
              ((Nat.totient modulus : ℝ) * Real.log (z : ℝ)) +
            (z : ℝ) ^ 2) :=
  (Classical.choose_spec
    ShiuSelbergDenominatorLower.certifiedSelbergUpperBoundSieve).2

/-- The exact finite Selberg envelope after applying the fixed certified
Shiu Lemma-2 constant to every fixed-prefix quotient progression. -/
theorem classIMass_cast_le_selberg_sum_fixed
    (k X Y modulus residue Z cutoff D : ℕ)
    (hZ : 1 ≤ Z) (hYX : Y ≤ X)
    (hmodulus : 0 < modulus) (hresidueLt : residue < modulus)
    (hresidue : residue.Coprime modulus)
    (hsieve : 2 ≤ classISieveLevel Z)
    (hmodLength : ∀ b ∈ classIOuterPrefixes Z modulus,
      modulus < quotientLength X Y b)
    (hDbound : ∀ n ∈ classSet FourClass.I X Y modulus residue Z cutoff,
      tauAF k (canonicalD n Z) ^ 2 ≤ D) :
    (classIMass k X Y modulus residue Z cutoff : ℝ) ≤
      (D : ℝ) * classISelbergConstant *
        ∑ b ∈ classIOuterPrefixes Z modulus,
          (tauAF k b ^ 2 : ℝ) *
            (((quotientLength X Y b : ℕ) : ℝ) /
                ((Nat.totient modulus : ℝ) *
                  Real.log (classISieveLevel Z : ℝ)) +
              (classISieveLevel Z : ℝ) ^ 2) := by
  have hphi := classIMass_cast_le_phi_sum k X Y modulus residue Z cutoff D
    hZ hYX hmodulus hresidue hDbound
  refine hphi.trans ?_
  have hDnonneg : (0 : ℝ) ≤ D := by positivity
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hDnonneg
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have hbData := Finset.mem_filter.mp hb
  have hbmod : b.Coprime modulus := hbData.2
  have hqspec := quotientResidue_spec (residue := residue) hmodulus hbmod
  have hqcop := quotientResidue_coprime hmodulus hbmod hresidue
  have hqYX : quotientLength X Y b ≤ X / b := min_le_right _ _
  have hselberg := classISelbergUpperBound
    (X / b) (quotientLength X Y b) (classISieveLevel Z)
    modulus (quotientResidue b residue modulus)
    hmodulus hqspec.1 hqcop (hmodLength b hb) hqYX hsieve
  calc
    (tauAF k b ^ 2 : ℝ) *
        ShiuSieveSlice.shiuPhi
          (X / b) (quotientLength X Y b) (classISieveLevel Z)
          modulus (quotientResidue b residue modulus) ≤
      (tauAF k b ^ 2 : ℝ) *
        (classISelbergConstant *
          (((quotientLength X Y b : ℕ) : ℝ) /
              ((Nat.totient modulus : ℝ) *
                Real.log (classISieveLevel Z : ℝ)) +
            (classISieveLevel Z : ℝ) ^ 2)) := by
      gcongr
    _ = classISelbergConstant *
        ((tauAF k b ^ 2 : ℝ) *
          (((quotientLength X Y b : ℕ) : ℝ) /
              ((Nat.totient modulus : ℝ) *
                Real.log (classISieveLevel Z : ℝ)) +
            (classISieveLevel Z : ℝ) ^ 2)) := by ring

/-- Existential presentation of the same fixed Selberg envelope, convenient
for compatibility with the published `≪` notation. -/
theorem classIMass_cast_le_selberg_sum
    (k X Y modulus residue Z cutoff D : ℕ)
    (hZ : 1 ≤ Z) (hYX : Y ≤ X)
    (hmodulus : 0 < modulus) (hresidueLt : residue < modulus)
    (hresidue : residue.Coprime modulus)
    (hsieve : 2 ≤ classISieveLevel Z)
    (hmodLength : ∀ b ∈ classIOuterPrefixes Z modulus,
      modulus < quotientLength X Y b)
    (hDbound : ∀ n ∈ classSet FourClass.I X Y modulus residue Z cutoff,
      tauAF k (canonicalD n Z) ^ 2 ≤ D) :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      (classIMass k X Y modulus residue Z cutoff : ℝ) ≤
        (D : ℝ) * C₂ *
          ∑ b ∈ classIOuterPrefixes Z modulus,
            (tauAF k b ^ 2 : ℝ) *
              (((quotientLength X Y b : ℕ) : ℝ) /
                  ((Nat.totient modulus : ℝ) *
                    Real.log (classISieveLevel Z : ℝ)) +
                (classISieveLevel Z : ℝ) ^ 2) := by
  exact ⟨classISelbergConstant, classISelbergConstant_pos,
    classIMass_cast_le_selberg_sum_fixed
      k X Y modulus residue Z cutoff D hZ hYX hmodulus hresidueLt
      hresidue hsieve hmodLength hDbound⟩

/-! ## The source constant bound for the class-I suffix -/

/-- If every member of a list is at least `q`, its product dominates the
corresponding power of `q`. -/
lemma pow_length_le_list_prod
    {q : ℕ} {l : List ℕ} (h : ∀ p ∈ l, q ≤ p) :
    q ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.length_cons, List.prod_cons, pow_succ]
      calc
        q ^ l.length * q ≤ l.prod * p :=
          Nat.mul_le_mul
            (ih (fun a ha ↦ h a (List.mem_cons_of_mem p ha)))
            (h p List.mem_cons_self)
        _ = p * l.prod := by ac_rfl

/-- Repeated submultiplicativity over a list of primes. -/
lemma tauAF_list_prod_le_pow
    (k : ℕ) {l : List ℕ} (hprime : ∀ p ∈ l, p.Prime) :
    tauAF k l.prod ≤ k ^ l.length := by
  induction l with
  | nil => simp [tauAF_isMultiplicative]
  | cons p l ih =>
      have hp := hprime p (List.mem_cons_self)
      have htail : ∀ q ∈ l, q.Prime :=
        fun q hq ↦ hprime q (List.mem_cons_of_mem p hq)
      have hpval : tauAF k p = k := by
        simpa using tauAF_prime_pow_eq_multichoose k 1 p hp
      simp only [List.prod_cons, List.length_cons, pow_succ]
      calc
        tauAF k (p * l.prod) ≤ tauAF k p * tauAF k l.prod :=
          tauAF_submultiplicative k p l.prod
        _ ≤ k * k ^ l.length := by
          rw [hpval]
          exact Nat.mul_le_mul_left k (ih htail)
        _ = k ^ l.length * k := by ac_rfl

/-- The manuscript's class-I condition gives the fixed suffix bound
`f(d_n) ≤ (k²)^179`.  The number 180 is literal: `X < Z^90` and
`Z < q(d_n)^2` imply that the prime-factor list of `d_n` has length `< 180`.
-/
theorem classI_suffix_tauSquare_le
    (k : ℕ) (hk : 1 ≤ k)
    {X Y modulus residue Z cutoff n : ℕ}
    (hZ : 1 ≤ Z) (hXZ : X < Z ^ 90)
    (hn : n ∈ classSet FourClass.I X Y modulus residue Z cutoff) :
    tauAF k (canonicalD n Z) ^ 2 ≤ (k * k) ^ 179 := by
  let d := canonicalD n Z
  change tauAF k d ^ 2 ≤ (k * k) ^ 179
  have hnpos := mem_classSet_pos hn
  have hn0 : n ≠ 0 := hnpos.ne'
  have hbpos := canonicalB_pos n Z
  have hmul := canonicalB_mul_canonicalD hn0 hZ
  have hdpos : 0 < d := by dsimp [d]; nlinarith
  have hd0 : d ≠ 0 := hdpos.ne'
  by_cases hd1 : d = 1
  · change tauAF k d ^ 2 ≤ (k * k) ^ 179
    rw [hd1, (tauAF_isMultiplicative k).map_one]
    have hkk : 1 ≤ k * k := by
      simpa using Nat.mul_le_mul hk hk
    simpa using
      (one_le_pow₀ hkk : 1 ≤ (k * k) ^ 179)
  let L := d.primeFactorsList
  have hprime : ∀ p ∈ L, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactorsList hp
  have hlpf : leastPrimeFactor d = d.minFac := by
    simp [leastPrimeFactor, hd1]
  have hminLower : ∀ p ∈ L, d.minFac ≤ p := by
    intro p hp
    exact Nat.minFac_le_of_dvd (hprime p hp).two_le
      (Nat.dvd_of_mem_primeFactorsList hp)
  have hpowProd : d.minFac ^ L.length ≤ d := by
    calc
      d.minFac ^ L.length ≤ L.prod := pow_length_le_list_prod hminLower
      _ = d := Nat.prod_primeFactorsList hd0
  have hdX : d ≤ X := by
    have hdle : d ≤ n := by
      dsimp [d, canonicalD]
      exact Nat.div_le_self n (canonicalB n Z)
    have hnX := Finset.mem_Ioc.mp
      (Finset.mem_filter.mp (mem_classSet_iff.mp hn).1).1 |>.2
    exact hdle.trans hnX
  have hclass := (mem_class_I_iff.mp hn).2
  rw [hlpf] at hclass
  have hlen : L.length < 180 := by
    by_contra hnot
    have h180 : 180 ≤ L.length := Nat.le_of_not_gt hnot
    have hqpos : 0 < d.minFac := Nat.minFac_pos d
    have hq180 : d.minFac ^ 180 ≤ d.minFac ^ L.length :=
      Nat.pow_le_pow_right hqpos h180
    have hZq : Z ^ 90 < d.minFac ^ 180 := by
      have hp := Nat.pow_lt_pow_left hclass (by omega : 90 ≠ 0)
      norm_num [← pow_mul] at hp ⊢
      exact hp
    omega
  have htau : tauAF k d ≤ k ^ L.length := by
    have ht := tauAF_list_prod_le_pow k hprime
    simpa [L, Nat.prod_primeFactorsList hd0] using ht
  have htauSq : tauAF k d ^ 2 ≤ (k * k) ^ L.length := by
    calc
      tauAF k d ^ 2 ≤ (k ^ L.length) ^ 2 :=
        Nat.pow_le_pow_left htau 2
      _ = (k * k) ^ L.length := by
        rw [pow_two, ← mul_pow]
  have hkk : 1 ≤ k * k := by
    simpa using Nat.mul_le_mul hk hk
  exact htauSq.trans
    (Nat.pow_le_pow_right hkk (show L.length ≤ 179 by omega))

/-- Lemma 3 applies to exactly the harmonic prefix appearing after the
class-I Selberg reduction. -/
theorem classIHarmonicPrefix_le_lemmaThree
    (k Z modulus : ℕ) (hk : 1 ≤ k) :
    classIHarmonicPrefix k Z modulus ≤
      Real.exp (4 * (k * k : ℕ)) *
        Real.exp
          (ShiuUniformContract.omittedPrimeSum
            ((tauAF k).pmul (tauAF k)) Z modulus) := by
  have hThree := ShiuLemma3TauMean.tauSquare_coprime_harmonic_mean
    k hk Z modulus
  simpa [classIHarmonicPrefix, classIOuterPrefixes,
    ShiuLemma3TauMean.tauSquareCoprimeHarmonicSum,
    Finset.sum_filter] using hThree

/-- The sharper finite-Euler-product form of Lemma 3.  Keeping this form is
essential for the exact cancellation of `modulus / φ(modulus)`: converting the
omitted product to a logarithm before that cancellation would lose an extra
logarithmic power when `k = 1`. -/
theorem classIHarmonicPrefix_le_localEulerProduct
    (k Z modulus : ℕ) (hk : 1 ≤ k) :
    classIHarmonicPrefix k Z modulus ≤
      ∏ p ∈ (Z + 1).primesBelow,
        (if p ∣ modulus then 1 else
          1 / (1 - (p : ℝ)⁻¹) ^ (k * k)) := by
  have hEuler :=
    ShiuLemma3TauMean.tauSquareCoprimeHarmonicSum_le_localEulerProduct
      k Z modulus hk
  simpa [classIHarmonicPrefix, classIOuterPrefixes,
    ShiuLemma3TauMean.tauSquareCoprimeHarmonicSum,
    Finset.sum_filter] using hEuler

/-- Certified Lemmas 2 and the literal suffix constant give the full
pre-harmonic class-I Selberg sum, with no class estimate assumed. -/
theorem classIMass_cast_le_selberg_sum_certifiedSuffix_fixed
    (k X Y modulus residue Z cutoff : ℕ) (hk : 1 ≤ k)
    (hZ : 1 ≤ Z) (hYX : Y ≤ X)
    (hXZ : X < Z ^ 90)
    (hmodulus : 0 < modulus) (hresidueLt : residue < modulus)
    (hresidue : residue.Coprime modulus)
    (hsieve : 2 ≤ classISieveLevel Z)
    (hmodLength : ∀ b ∈ classIOuterPrefixes Z modulus,
      modulus < quotientLength X Y b) :
    (classIMass k X Y modulus residue Z cutoff : ℝ) ≤
      ((k * k) ^ 179 : ℕ) * classISelbergConstant *
        ∑ b ∈ classIOuterPrefixes Z modulus,
          (tauAF k b ^ 2 : ℝ) *
            (((quotientLength X Y b : ℕ) : ℝ) /
                ((Nat.totient modulus : ℝ) *
                  Real.log (classISieveLevel Z : ℝ)) +
              (classISieveLevel Z : ℝ) ^ 2) := by
  exact classIMass_cast_le_selberg_sum_fixed
    k X Y modulus residue Z cutoff ((k * k) ^ 179)
    hZ hYX hmodulus hresidueLt hresidue hsieve hmodLength
    (fun n hn ↦ classI_suffix_tauSquare_le k hk hZ hXZ hn)

/-- Existential presentation of the same fixed-constant bound. -/
theorem classIMass_cast_le_selberg_sum_certifiedSuffix
    (k X Y modulus residue Z cutoff : ℕ) (hk : 1 ≤ k)
    (hZ : 1 ≤ Z) (hYX : Y ≤ X)
    (hXZ : X < Z ^ 90)
    (hmodulus : 0 < modulus) (hresidueLt : residue < modulus)
    (hresidue : residue.Coprime modulus)
    (hsieve : 2 ≤ classISieveLevel Z)
    (hmodLength : ∀ b ∈ classIOuterPrefixes Z modulus,
      modulus < quotientLength X Y b) :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      (classIMass k X Y modulus residue Z cutoff : ℝ) ≤
        ((k * k) ^ 179 : ℕ) * C₂ *
          ∑ b ∈ classIOuterPrefixes Z modulus,
            (tauAF k b ^ 2 : ℝ) *
              (((quotientLength X Y b : ℕ) : ℝ) /
                  ((Nat.totient modulus : ℝ) *
                    Real.log (classISieveLevel Z : ℝ)) +
                (classISieveLevel Z : ℝ) ^ 2) := by
  exact classIMass_cast_le_selberg_sum
    k X Y modulus residue Z cutoff ((k * k) ^ 179)
    hZ hYX hmodulus hresidueLt hresidue hsieve hmodLength
    (fun n hn ↦ classI_suffix_tauSquare_le k hk hZ hXZ hn)

/-- Pointwise arithmetic compression of the rounded Lemma-2 term into the
harmonic `f(b)/b` factor.  The sieve error uses
`floor(sqrt Z)^2 * b ≤ Z^2`, exactly matching Shiu's `z^2`. -/
theorem classI_selbergSummand_le_harmonic
    (k X Y modulus Z b : ℕ)
    (hmodulus : 0 < modulus) (hsieve : 2 ≤ classISieveLevel Z)
    (hZY : Z ≤ Y) (hb : b ∈ classIOuterPrefixes Z modulus) :
    (tauAF k b ^ 2 : ℝ) *
        (((quotientLength X Y b : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) *
              Real.log (classISieveLevel Z : ℝ)) +
          (classISieveLevel Z : ℝ) ^ 2) ≤
      ((2 * Y : ℕ) : ℝ) /
          ((Nat.totient modulus : ℝ) *
            Real.log (classISieveLevel Z : ℝ)) *
          ((tauAF k b ^ 2 : ℝ) / (b : ℝ)) +
        (Z : ℝ) ^ 2 * ((tauAF k b ^ 2 : ℝ) / (b : ℝ)) := by
  have hbData := Finset.mem_filter.mp hb
  have hbIcc := Finset.mem_Icc.mp hbData.1
  have hbpos : 0 < b := by omega
  have hbY : b ≤ Y := hbIcc.2.trans hZY
  have hYdiv : 1 ≤ Y / b := Nat.le_div_iff_mul_le hbpos |>.2 (by simpa using hbY)
  have hlenNat : quotientLength X Y b ≤ 2 * (Y / b) := by
    calc
      quotientLength X Y b ≤ Y / b + 1 := min_le_left _ _
      _ ≤ 2 * (Y / b) := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hbpos
  have hlenR : ((quotientLength X Y b : ℕ) : ℝ) ≤
      (2 * (Y : ℝ)) / (b : ℝ) := by
    calc
      ((quotientLength X Y b : ℕ) : ℝ) ≤
          (2 * (Y / b) : ℕ) := by exact_mod_cast hlenNat
      _ = 2 * ((Y / b : ℕ) : ℝ) := by norm_num
      _ ≤ 2 * ((Y : ℝ) / (b : ℝ)) := by
        gcongr
        exact Nat.cast_div_le
      _ = (2 * (Y : ℝ)) / (b : ℝ) := by ring
  have hphiNat : 0 < Nat.totient modulus := Nat.totient_pos.mpr hmodulus
  have hphi : (0 : ℝ) < Nat.totient modulus := by exact_mod_cast hphiNat
  have hsieveR : (1 : ℝ) < classISieveLevel Z := by exact_mod_cast (by omega)
  have hlog : 0 < Real.log (classISieveLevel Z : ℝ) := Real.log_pos hsieveR
  let den : ℝ := (Nat.totient modulus : ℝ) *
    Real.log (classISieveLevel Z : ℝ)
  have hden : 0 < den := mul_pos hphi hlog
  have hmain : ((quotientLength X Y b : ℕ) : ℝ) / den ≤
      (((2 * Y : ℕ) : ℝ) / den) / (b : ℝ) := by
    apply (div_le_iff₀ hden).2
    calc
      ((quotientLength X Y b : ℕ) : ℝ) ≤
          (2 * (Y : ℝ)) / (b : ℝ) := hlenR
      _ = ((((2 * Y : ℕ) : ℝ) / den) / (b : ℝ)) * den := by
        push_cast
        field_simp
  have hsqrtNat : classISieveLevel Z ^ 2 ≤ Z := by
    simpa [classISieveLevel, pow_two] using Nat.sqrt_le Z
  have herrNat : classISieveLevel Z ^ 2 * b ≤ Z ^ 2 := by
    calc
      classISieveLevel Z ^ 2 * b ≤ Z * Z :=
        Nat.mul_le_mul hsqrtNat hbIcc.2
      _ = Z ^ 2 := by ring
  have herr : ((classISieveLevel Z : ℕ) : ℝ) ^ 2 ≤
      (Z : ℝ) ^ 2 / (b : ℝ) := by
    apply (le_div_iff₀ hbR).2
    exact_mod_cast herrNat
  have hweight : (0 : ℝ) ≤ tauAF k b ^ 2 := by positivity
  dsimp [den] at hmain hden ⊢
  calc
    (tauAF k b ^ 2 : ℝ) *
        (((quotientLength X Y b : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) *
              Real.log (classISieveLevel Z : ℝ)) +
          (classISieveLevel Z : ℝ) ^ 2) ≤
      (tauAF k b ^ 2 : ℝ) *
        (((((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) *
              Real.log (classISieveLevel Z : ℝ))) / (b : ℝ)) +
          (Z : ℝ) ^ 2 / (b : ℝ)) := by
        gcongr
    _ = ((2 * Y : ℕ) : ℝ) /
          ((Nat.totient modulus : ℝ) *
            Real.log (classISieveLevel Z : ℝ)) *
          ((tauAF k b ^ 2 : ℝ) / (b : ℝ)) +
        (Z : ℝ) ^ 2 * ((tauAF k b ^ 2 : ℝ) / (b : ℝ)) := by
      field_simp

/-- Summing the pointwise compression produces exactly the (5.3) bracket
times the harmonic prefix. -/
theorem classI_selbergSum_le_fiveThreeBracket
    (k X Y modulus Z : ℕ)
    (hmodulus : 0 < modulus) (hsieve : 2 ≤ classISieveLevel Z)
    (hZY : Z ≤ Y) :
    (∑ b ∈ classIOuterPrefixes Z modulus,
      (tauAF k b ^ 2 : ℝ) *
        (((quotientLength X Y b : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) *
              Real.log (classISieveLevel Z : ℝ)) +
          (classISieveLevel Z : ℝ) ^ 2)) ≤
      ((((2 * Y : ℕ) : ℝ) /
          ((Nat.totient modulus : ℝ) *
            Real.log (classISieveLevel Z : ℝ))) + (Z : ℝ) ^ 2) *
        classIHarmonicPrefix k Z modulus := by
  calc
    _ ≤ ∑ b ∈ classIOuterPrefixes Z modulus,
        ((((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) *
              Real.log (classISieveLevel Z : ℝ))) *
            ((tauAF k b ^ 2 : ℝ) / (b : ℝ)) +
          (Z : ℝ) ^ 2 * ((tauAF k b ^ 2 : ℝ) / (b : ℝ))) := by
      apply Finset.sum_le_sum
      intro b hb
      exact classI_selbergSummand_le_harmonic
        k X Y modulus Z b hmodulus hsieve hZY hb
    _ = ((((2 * Y : ℕ) : ℝ) /
          ((Nat.totient modulus : ℝ) *
            Real.log (classISieveLevel Z : ℝ))) + (Z : ℝ) ^ 2) *
        classIHarmonicPrefix k Z modulus := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rfl

/-- Certified Lemmas 2 and 3 give the complete analytic class-I estimate
before the elementary Section-5 parameter absorption.  The harmonic factor is
deliberately kept as the omitted local Euler product so that multiplication by
the progression modulus can use prime-by-prime `q / φ(q)` cancellation. -/
theorem classIMass_cast_le_localEulerProductBracket
    (k X Y modulus residue Z cutoff : ℕ) (hk : 1 ≤ k)
    (hZ : 1 ≤ Z) (hYX : Y ≤ X)
    (hXZ : X < Z ^ 90) (hZY : Z ≤ Y)
    (hmodulus : 0 < modulus) (hresidueLt : residue < modulus)
    (hresidue : residue.Coprime modulus)
    (hsieve : 2 ≤ classISieveLevel Z)
    (hmodLength : ∀ b ∈ classIOuterPrefixes Z modulus,
      modulus < quotientLength X Y b) :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      (classIMass k X Y modulus residue Z cutoff : ℝ) ≤
        ((k * k) ^ 179 : ℕ) * C₂ *
          (((((2 * Y : ℕ) : ℝ) /
              ((Nat.totient modulus : ℝ) *
                Real.log (classISieveLevel Z : ℝ))) + (Z : ℝ) ^ 2) *
            (∏ p ∈ (Z + 1).primesBelow,
              (if p ∣ modulus then 1 else
                1 / (1 - (p : ℝ)⁻¹) ^ (k * k)))) := by
  obtain ⟨C₂, hC₂, hmass⟩ :=
    classIMass_cast_le_selberg_sum_certifiedSuffix
      k X Y modulus residue Z cutoff hk hZ hYX hXZ
      hmodulus hresidueLt hresidue hsieve hmodLength
  refine ⟨C₂, hC₂, hmass.trans ?_⟩
  have hsum := classI_selbergSum_le_fiveThreeBracket
    k X Y modulus Z hmodulus hsieve hZY
  have hEuler := classIHarmonicPrefix_le_localEulerProduct k Z modulus hk
  have hphi : (0 : ℝ) < Nat.totient modulus := by
    exact_mod_cast Nat.totient_pos.mpr hmodulus
  have hsieveR : (1 : ℝ) < classISieveLevel Z := by
    exact_mod_cast (show 1 < classISieveLevel Z by omega)
  have hlog : 0 < Real.log (classISieveLevel Z : ℝ) :=
    Real.log_pos hsieveR
  have hbracket :
      0 ≤ (((2 * Y : ℕ) : ℝ) /
          ((Nat.totient modulus : ℝ) *
            Real.log (classISieveLevel Z : ℝ)) + (Z : ℝ) ^ 2) := by
    positivity
  have hfactor :
      0 ≤ ((k * k) ^ 179 : ℕ) * C₂ :=
    mul_nonneg (by positivity) hC₂.le
  calc
    ((k * k) ^ 179 : ℕ) * C₂ *
        (∑ b ∈ classIOuterPrefixes Z modulus,
          (tauAF k b ^ 2 : ℝ) *
            (((quotientLength X Y b : ℕ) : ℝ) /
                ((Nat.totient modulus : ℝ) *
                  Real.log (classISieveLevel Z : ℝ)) +
              (classISieveLevel Z : ℝ) ^ 2)) ≤
      ((k * k) ^ 179 : ℕ) * C₂ *
        (((((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) *
              Real.log (classISieveLevel Z : ℝ))) + (Z : ℝ) ^ 2) *
          classIHarmonicPrefix k Z modulus) := by
            exact mul_le_mul_of_nonneg_left hsum hfactor
    _ ≤ ((k * k) ^ 179 : ℕ) * C₂ *
        (((((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) *
              Real.log (classISieveLevel Z : ℝ))) + (Z : ℝ) ^ 2) *
          (∏ p ∈ (Z + 1).primesBelow,
            (if p ∣ modulus then 1 else
              1 / (1 - (p : ℝ)⁻¹) ^ (k * k)))) := by
            apply mul_le_mul_of_nonneg_left _ hfactor
            exact mul_le_mul_of_nonneg_left hEuler hbracket

/-- Uniform fixed-constant version of the complete Lemma-2/Lemma-3 class-I
estimate.  This is the form consumed by the eventual Section-5 adapter. -/
theorem classIMass_cast_le_localEulerProductBracket_fixed
    (k X Y modulus residue Z cutoff : ℕ) (hk : 1 ≤ k)
    (hZ : 1 ≤ Z) (hYX : Y ≤ X)
    (hXZ : X < Z ^ 90) (hZY : Z ≤ Y)
    (hmodulus : 0 < modulus) (hresidueLt : residue < modulus)
    (hresidue : residue.Coprime modulus)
    (hsieve : 2 ≤ classISieveLevel Z)
    (hmodLength : ∀ b ∈ classIOuterPrefixes Z modulus,
      modulus < quotientLength X Y b) :
    (classIMass k X Y modulus residue Z cutoff : ℝ) ≤
      ((k * k) ^ 179 : ℕ) * classISelbergConstant *
        (((((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) *
              Real.log (classISieveLevel Z : ℝ))) + (Z : ℝ) ^ 2) *
          (∏ p ∈ (Z + 1).primesBelow,
            (if p ∣ modulus then 1 else
              1 / (1 - (p : ℝ)⁻¹) ^ (k * k)))) := by
  have hmass := classIMass_cast_le_selberg_sum_certifiedSuffix_fixed
    k X Y modulus residue Z cutoff hk hZ hYX hXZ
    hmodulus hresidueLt hresidue hsieve hmodLength
  have hsum := classI_selbergSum_le_fiveThreeBracket
    k X Y modulus Z hmodulus hsieve hZY
  have hEuler := classIHarmonicPrefix_le_localEulerProduct k Z modulus hk
  have hphi : (0 : ℝ) < Nat.totient modulus := by
    exact_mod_cast Nat.totient_pos.mpr hmodulus
  have hsieveR : (1 : ℝ) < classISieveLevel Z := by
    exact_mod_cast (show 1 < classISieveLevel Z by omega)
  have hlog : 0 < Real.log (classISieveLevel Z : ℝ) :=
    Real.log_pos hsieveR
  have hbracket :
      0 ≤ (((2 * Y : ℕ) : ℝ) /
          ((Nat.totient modulus : ℝ) *
            Real.log (classISieveLevel Z : ℝ)) + (Z : ℝ) ^ 2) := by
    positivity
  have hfactor :
      0 ≤ ((k * k) ^ 179 : ℕ) * classISelbergConstant :=
    mul_nonneg (by positivity) classISelbergConstant_pos.le
  calc
    (classIMass k X Y modulus residue Z cutoff : ℝ) ≤
      ((k * k) ^ 179 : ℕ) * classISelbergConstant *
        (∑ b ∈ classIOuterPrefixes Z modulus,
          (tauAF k b ^ 2 : ℝ) *
            (((quotientLength X Y b : ℕ) : ℝ) /
                ((Nat.totient modulus : ℝ) *
                  Real.log (classISieveLevel Z : ℝ)) +
              (classISieveLevel Z : ℝ) ^ 2)) := hmass
    _ ≤ ((k * k) ^ 179 : ℕ) * classISelbergConstant *
        (((((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) *
              Real.log (classISieveLevel Z : ℝ))) + (Z : ℝ) ^ 2) *
          classIHarmonicPrefix k Z modulus) := by
            exact mul_le_mul_of_nonneg_left hsum hfactor
    _ ≤ ((k * k) ^ 179 : ℕ) * classISelbergConstant *
        (((((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) *
              Real.log (classISieveLevel Z : ℝ))) + (Z : ℝ) ^ 2) *
          (∏ p ∈ (Z + 1).primesBelow,
            (if p ∣ modulus then 1 else
              1 / (1 - (p : ℝ)⁻¹) ^ (k * k)))) := by
            apply mul_le_mul_of_nonneg_left _ hfactor
            exact mul_le_mul_of_nonneg_left hEuler hbracket

end

end ShiuClassIBound
