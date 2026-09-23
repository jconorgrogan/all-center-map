import FiniteEulerDistortion
import ShiuEndToEndScaffold
import ShiuBoundaryPrimeStructure

/-!
# Shiu Section 5, class IV

This file follows the literal class-IV argument on Shiu (1980), p. 168.  It
keeps the dyadic index `r`, the factor `(r+1) A₅^r` from the suffix, and the
finite Lemma-4 harmonic tail separate.  In particular, the convergence lemma
below is the exact final absorption in (5.8), rather than a renamed form of the
desired progression estimate.
-/

namespace ShiuClassIVBound

open ArithmeticFunction MixedMellinCert ShiuFoundation ShiuSection5Split
  ShiuSection5Structure ShiuLemma4TauTail ShiuLemma4EndpointWeld
open ShiuBoundaryPrimeStructure
open ShiuClassIBound
open scoped ArithmeticFunction.zeta ArithmeticFunction.Omega BigOperators Topology

noncomputable section

/-- The numerical series occurring at the end of (5.8). -/
def classIVSeriesTerm (A : ℝ) (r : ℕ) : ℝ :=
  (r : ℝ) * A ^ r *
    Real.exp (-(1 / 10 : ℝ) * (r : ℝ) * Real.log (r : ℝ))

theorem classIVSeriesTerm_nonneg {A : ℝ} (hA : 0 ≤ A) (r : ℕ) :
    0 ≤ classIVSeriesTerm A r := by
  unfold classIVSeriesTerm
  positivity

/-- Shiu's final `r`-sum is bounded uniformly in its upper endpoint.  The
constant may depend on the fixed growth constant `A`, exactly as in the
source. -/
theorem summable_classIVSeriesTerm (A : ℝ) (hA : 0 < A) :
    Summable (classIVSeriesTerm A) := by
  have hlog :
      Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ))
        Filter.atTop Filter.atTop := by
    simpa only [Function.comp_def] using
      Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      10 * (Real.log A + 1) ≤ Real.log (n : ℝ) :=
    hlog.eventually_ge_atTop (10 * (Real.log A + 1))
  have hmajorant := Real.summable_pow_mul_exp_neg_nat_mul 1
    (show (0 : ℝ) < 1 by norm_num)
  refine hmajorant.of_norm_bounded_eventually_nat ?_
  filter_upwards [hevent] with n hn
  have hterm : 0 ≤ classIVSeriesTerm A n :=
    classIVSeriesTerm_nonneg hA.le n
  rw [Real.norm_of_nonneg hterm]
  have hApow : A ^ n = Real.exp ((n : ℝ) * Real.log A) := by
    rw [Real.exp_nat_mul, Real.exp_log hA]
  calc
    classIVSeriesTerm A n =
        (n : ℝ) * Real.exp
          ((n : ℝ) * Real.log A -
            (1 / 10 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) := by
      rw [classIVSeriesTerm, hApow, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (n : ℝ) * Real.exp (-(n : ℝ)) := by
      gcongr
      nlinarith
    _ = (n : ℝ) ^ 1 * Real.exp (-(1 : ℝ) * (n : ℝ)) := by ring

/-- Every finite source range `2 <= r <= r₀` is absorbed by one constant
independent of `r₀`. -/
theorem finite_classIVSeries_le_tsum (A : ℝ) (hA : 0 < A) (r₀ : ℕ) :
    (∑ r ∈ Finset.Icc 2 r₀, classIVSeriesTerm A r) ≤
      ∑' r : ℕ, classIVSeriesTerm A r := by
  exact (summable_classIVSeriesTerm A hA).sum_le_tsum
    (Finset.Icc 2 r₀)
    (fun r hr => classIVSeriesTerm_nonneg hA.le r)

theorem exists_uniform_classIVSeries_bound (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r₀ : ℕ,
      (∑ r ∈ Finset.Icc 2 r₀, classIVSeriesTerm A r) ≤ C := by
  refine ⟨∑' r : ℕ, classIVSeriesTerm A r, ?_, ?_⟩
  · exact tsum_nonneg (fun r => classIVSeriesTerm_nonneg hA.le r)
  · exact finite_classIVSeries_le_tsum A hA

/-! ## The literal `r`-bin -/

/-- Natural-power implementation of the source conditions
`Z^(1/(r+1)) < q <= Z^(1/r)`. -/
def admissibleClassIVIndices (Z q : ℕ) : Finset ℕ :=
  (Finset.Icc 2 Z).filter fun r => q ^ r ≤ Z

theorem admissibleClassIVIndices_nonempty
    {Z q : ℕ} (hZ : 3 ≤ Z) (hq : 2 ≤ q) (hqsq : q ^ 2 ≤ Z) :
    (admissibleClassIVIndices Z q).Nonempty := by
  refine ⟨2, ?_⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, hqsq⟩

/-- The largest natural exponent for which `q^r <= Z`.  The source's bins
are exactly the successive intervals cut out by this index. -/
def classIVIndex (Z q : ℕ) : ℕ := by
  classical
  exact if h : (admissibleClassIVIndices Z q).Nonempty then
    (admissibleClassIVIndices Z q).max' h
  else 2

theorem classIVIndex_mem
    {Z q : ℕ} (hZ : 3 ≤ Z) (hq : 2 ≤ q) (hqsq : q ^ 2 ≤ Z) :
    classIVIndex Z q ∈ admissibleClassIVIndices Z q := by
  classical
  rw [classIVIndex, dif_pos (admissibleClassIVIndices_nonempty hZ hq hqsq)]
  exact Finset.max'_mem _ _

theorem le_classIVIndex_of_mem
    {Z q s : ℕ} (hZ : 3 ≤ Z) (hq : 2 ≤ q) (hqsq : q ^ 2 ≤ Z)
    (hs : s ∈ admissibleClassIVIndices Z q) :
    s ≤ classIVIndex Z q := by
  classical
  rw [classIVIndex, dif_pos (admissibleClassIVIndices_nonempty hZ hq hqsq)]
  exact Finset.le_max' _ _ hs

theorem classIVIndex_bounds
    {Z q : ℕ} (hZ : 3 ≤ Z) (hq : 2 ≤ q) (hqsq : q ^ 2 ≤ Z) :
    2 ≤ classIVIndex Z q ∧ classIVIndex Z q < Z ∧
      q ^ classIVIndex Z q ≤ Z ∧
      Z < q ^ (classIVIndex Z q + 1) := by
  classical
  let r := classIVIndex Z q
  have hrmem := classIVIndex_mem hZ hq hqsq
  have hrdata := Finset.mem_filter.mp hrmem
  have hrIcc := Finset.mem_Icc.mp hrdata.1
  have hrpow := hrdata.2
  have hrlt : r < Z := by
    apply lt_of_le_of_ne hrIcc.2
    intro hrZ
    have htwo : 2 ^ Z ≤ q ^ Z := Nat.pow_le_pow_left hq Z
    have hZlt : Z < 2 ^ Z := Z.lt_two_pow_self
    have hqZ : Z < q ^ Z := hZlt.trans_le htwo
    have hqZle : q ^ Z ≤ Z := by simpa [r, hrZ] using hrpow
    exact (not_lt_of_ge hqZle) hqZ
  have hsuccNot : r + 1 ∉ admissibleClassIVIndices Z q := by
    intro hmem
    have hmax : r + 1 ≤ r := by
      simpa [r] using le_classIVIndex_of_mem hZ hq hqsq hmem
    omega
  have hsuccIcc : r + 1 ∈ Finset.Icc 2 Z := by
    simp only [Finset.mem_Icc]
    omega
  have hsuccpow : Z < q ^ (r + 1) := by
    by_contra hnot
    have hle : q ^ (r + 1) ≤ Z := Nat.le_of_not_gt hnot
    exact hsuccNot (Finset.mem_filter.mpr ⟨hsuccIcc, hle⟩)
  exact ⟨hrIcc.1, hrlt, hrpow, hsuccpow⟩

/-- Exact real-radical form printed on p. 168. -/
theorem classIVIndex_source_interval
    {Z q : ℕ} (hZ : 3 ≤ Z) (hq : 2 ≤ q) (hqsq : q ^ 2 ≤ Z) :
    (Z : ℝ) ^ ((classIVIndex Z q + 1 : ℕ) : ℝ)⁻¹ < (q : ℝ) ∧
      (q : ℝ) ≤ (Z : ℝ) ^ ((classIVIndex Z q : ℕ) : ℝ)⁻¹ := by
  obtain ⟨hr2, hrZ, hrpow, hsuccpow⟩ := classIVIndex_bounds hZ hq hqsq
  have hZnonneg : (0 : ℝ) ≤ Z := by positivity
  have hqnonneg : (0 : ℝ) ≤ q := by positivity
  constructor
  · rw [Real.rpow_inv_lt_iff_of_pos hZnonneg hqnonneg]
    · rw [Real.rpow_natCast]
      exact_mod_cast hsuccpow
    · exact_mod_cast (show 0 < classIVIndex Z q + 1 by omega)
  · rw [Real.le_rpow_inv_iff_of_pos hqnonneg hZnonneg]
    · rw [Real.rpow_natCast]
      exact_mod_cast hrpow
    · exact_mod_cast (show 0 < classIVIndex Z q by omega)

/-- The source's logarithmic lower cutoff is used only to ensure that the
chosen bin index is no larger than its boundary prime.  This formulation
isolates the exact elementary inequality needed for that step. -/
theorem classIVIndex_le_boundaryPrime_of_log
    {Z q : ℕ} (hZ : 3 ≤ Z) (hq : 2 ≤ q) (hqsq : q ^ 2 ≤ Z)
    (hlog : Real.log (Z : ℝ) < (q : ℝ) * Real.log (q : ℝ)) :
    classIVIndex Z q ≤ q := by
  obtain ⟨hr2, hrZ, hrpow, hsuccpow⟩ := classIVIndex_bounds hZ hq hqsq
  by_contra hnot
  have hqr : q < classIVIndex Z q := Nat.lt_of_not_ge hnot
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hZpos : (0 : ℝ) < Z := by exact_mod_cast (by omega : 0 < Z)
  have hpowR :
      ((q : ℝ) ^ (classIVIndex Z q : ℕ)) ≤ (Z : ℝ) := by
    exact_mod_cast hrpow
  have hlogs := Real.log_le_log (by positivity : (0 : ℝ) < (q : ℝ) ^ classIVIndex Z q)
    hpowR
  rw [Real.log_pow] at hlogs
  have hqlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hstrict : (q : ℝ) * Real.log (q : ℝ) <
      (classIVIndex Z q : ℝ) * Real.log (q : ℝ) := by
    gcongr
  linarith

/-- Once the bin index is at most its least prime, its Rankin range is exactly
the hypothesis of the unconditional finite Lemma 4. -/
theorem classIVIndex_rankin_range
    {Z q : ℕ} (hZ : 3 ≤ Z) (hq : 2 ≤ q) (hqsq : q ^ 2 ≤ Z)
    (hrq : classIVIndex Z q ≤ q) :
    (classIVIndex Z q : ℝ) * Real.log (classIVIndex Z q : ℝ) ≤
      Real.log (Z : ℝ) := by
  obtain ⟨hr2, hrZ, hrpow, hsuccpow⟩ := classIVIndex_bounds hZ hq hqsq
  have hpowR :
      ((q : ℝ) ^ (classIVIndex Z q : ℕ)) ≤ (Z : ℝ) := by
    exact_mod_cast hrpow
  have hlogs := Real.log_le_log
    (by positivity : (0 : ℝ) < (q : ℝ) ^ classIVIndex Z q) hpowR
  rw [Real.log_pow] at hlogs
  have hlogmono : Real.log (classIVIndex Z q : ℝ) ≤ Real.log (q : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < classIVIndex Z q by omega)
    · exact_mod_cast hrq
  have hrnonneg : (0 : ℝ) ≤ classIVIndex Z q := by positivity
  exact (mul_le_mul_of_nonneg_left hlogmono hrnonneg).trans hlogs

/-- Integer root cutoff used both by the sieve and by Lemma 4 in bin `r`. -/
def classIVRootCutoff (Z r : ℕ) : ℕ :=
  ⌊(Z : ℝ) ^ ((r : ℝ)⁻¹)⌋₊

theorem boundaryPrime_le_classIVRootCutoff
    {Z q : ℕ} (hZ : 3 ≤ Z) (hq : 2 ≤ q) (hqsq : q ^ 2 ≤ Z) :
    q ≤ classIVRootCutoff Z (classIVIndex Z q) := by
  have hsource := (classIVIndex_source_interval hZ hq hqsq).2
  unfold classIVRootCutoff
  exact_mod_cast (Nat.le_floor hsource)

theorem two_le_classIVRootCutoff
    {Z q : ℕ} (hZ : 3 ≤ Z) (hq : 2 ≤ q) (hqsq : q ^ 2 ≤ Z) :
    2 ≤ classIVRootCutoff Z (classIVIndex Z q) :=
  hq.trans (boundaryPrime_le_classIVRootCutoff hZ hq hqsq)

/-- The exact class-IV prefix is supported on the smooth-number set consumed
by finite Lemma 4 at the source bin index. -/
theorem canonicalB_mem_classIVRootSmooth
    {n Z : ℕ} (hn : n ≠ 0) (hZ : 3 ≤ Z) (hZn : Z < n)
    (hq2 : 2 ≤ leastPrimeFactor (canonicalD n Z))
    (hqsq : leastPrimeFactor (canonicalD n Z) ^ 2 ≤ Z) :
    canonicalB n Z ∈ Nat.smoothNumbers
      (classIVRootCutoff Z
        (classIVIndex Z (leastPrimeFactor (canonicalD n Z))) + 1) := by
  apply canonicalB_mem_smoothNumbers_of_leastPrimeFactor_le hn (by omega) hZn
  exact boundaryPrime_le_classIVRootCutoff hZ hq2 hqsq

/-! ## Exact finite reindexing of the promoted class-IV set -/

def classIVBinSet
    (X Y modulus residue Z cutoff r : ℕ) : Finset ℕ :=
  (classSet FourClass.IV X Y modulus residue Z cutoff).filter fun n =>
    classIVIndex Z (leastPrimeFactor (canonicalD n Z)) = r

def classIVPrefixFiber
    (X Y modulus residue Z cutoff r b : ℕ) : Finset ℕ :=
  (classIVBinSet X Y modulus residue Z cutoff r).filter fun n =>
    canonicalB n Z = b

def classIVBinMass
    (k X Y modulus residue Z cutoff r : ℕ) : ℕ :=
  ∑ n ∈ classIVBinSet X Y modulus residue Z cutoff r, tauAF k n ^ 2

theorem classIVMass_eq_sum_bins
    (k X Y modulus residue Z cutoff : ℕ)
    (hZ : 3 ≤ Z) (hcutoff : 1 ≤ cutoff) :
    ShiuEndToEnd.classMass k X Y modulus residue Z cutoff FourClass.IV =
      ∑ r ∈ Finset.Icc 2 Z,
        classIVBinMass k X Y modulus residue Z cutoff r := by
  classical
  unfold ShiuEndToEnd.classMass classIVBinMass classIVBinSet
  symm
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hdata := mem_class_IV_iff.mp hn
  let q := leastPrimeFactor (canonicalD n Z)
  have hq : 2 ≤ q := by dsimp [q]; omega
  have hqsq : q ^ 2 ≤ Z := hdata.2.1
  have hrmem : classIVIndex Z q ∈ Finset.Icc 2 Z :=
    (Finset.mem_filter.mp (classIVIndex_mem hZ hq hqsq)).1
  rw [Finset.sum_eq_single_of_mem (classIVIndex Z q) hrmem]
  · simp [q]
  · intro r hr hne
    simp [q, hne.symm]

theorem classIVBinMass_eq_sum_prefixFibers
    (k X Y modulus residue Z cutoff r : ℕ) (hZ : 1 ≤ Z) :
    classIVBinMass k X Y modulus residue Z cutoff r =
      ∑ b ∈ Finset.Icc 1 Z,
        ∑ n ∈ classIVPrefixFiber X Y modulus residue Z cutoff r b,
          tauAF k n ^ 2 := by
  classical
  unfold classIVBinMass classIVPrefixFiber
  symm
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hnIV := (Finset.mem_filter.mp hn).1
  have hbmem : canonicalB n Z ∈ Finset.Icc 1 Z :=
    Finset.mem_Icc.mpr ⟨canonicalB_pos n Z, canonicalB_le hZ⟩
  rw [Finset.sum_eq_single_of_mem (canonicalB n Z) hbmem]
  · simp
  · intro b hb hne
    simp [hne.symm]

/-- Literal two-stage reindex in (5.8): first the source `r`-bin, then the
canonical prefix `b`. -/
theorem classIVMass_eq_sum_bins_prefixes
    (k X Y modulus residue Z cutoff : ℕ)
    (hZ : 3 ≤ Z) (hcutoff : 1 ≤ cutoff) :
    ShiuEndToEnd.classMass k X Y modulus residue Z cutoff FourClass.IV =
      ∑ r ∈ Finset.Icc 2 Z, ∑ b ∈ Finset.Icc 1 Z,
        ∑ n ∈ classIVPrefixFiber X Y modulus residue Z cutoff r b,
          tauAF k n ^ 2 := by
  rw [classIVMass_eq_sum_bins k X Y modulus residue Z cutoff hZ hcutoff]
  apply Finset.sum_congr rfl
  intro r hr
  exact classIVBinMass_eq_sum_prefixFibers
    k X Y modulus residue Z cutoff r (by omega)

/-! ## Fixed `(r,b)` suffix sieve -/

def classIVQuotientSet
    (X Y modulus residue' Z r b : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc
      (X / b - quotientLength X Y b) (X / b)).filter fun d =>
    d ≡ residue' [MOD modulus] ∧ 1 < d ∧
      ∀ p : ℕ, p.Prime → p ≤ classIVRootCutoff Z (r + 1) → ¬p ∣ d

theorem shiuPhi_eq_card_classIVQuotientSet
    (X Y modulus residue' Z r b : ℕ) :
    ShiuSieveSlice.shiuPhi (X / b) (quotientLength X Y b)
        (classIVRootCutoff Z (r + 1)) modulus residue' =
      ((classIVQuotientSet X Y modulus residue' Z r b).card : ℝ) := by
  classical
  simp [ShiuSieveSlice.shiuPhi, classIVQuotientSet]

lemma classMember_pos
    {c : FourClass} {X Y modulus residue Z cutoff n : ℕ}
    (hn : n ∈ classSet c X Y modulus residue Z cutoff) : 0 < n := by
  have hwin := (mem_classSet_iff.mp hn).1
  have hIoc := Finset.mem_Ioc.mp (Finset.mem_filter.mp hwin).1
  omega

theorem canonicalD_mem_classIVQuotientSet
    {X Y modulus residue residue' Z cutoff r b n : ℕ}
    (hZ : 3 ≤ Z) (hcutoff : 1 ≤ cutoff) (hYX : Y ≤ X)
    (hquotient : ∀ d : ℕ, b * d ≡ residue [MOD modulus] →
      d ≡ residue' [MOD modulus])
    (hn : n ∈ classIVPrefixFiber X Y modulus residue Z cutoff r b) :
    canonicalD n Z ∈
      classIVQuotientSet X Y modulus residue' Z r b := by
  classical
  have hnfiber := Finset.mem_filter.mp hn
  have hnbin := hnfiber.1
  have hb : canonicalB n Z = b := hnfiber.2
  have hnbindata := Finset.mem_filter.mp hnbin
  have hnIV := hnbindata.1
  have hr : classIVIndex Z (leastPrimeFactor (canonicalD n Z)) = r :=
    hnbindata.2
  have hIV := mem_class_IV_iff.mp hnIV
  let q := leastPrimeFactor (canonicalD n Z)
  have hq2 : 2 ≤ q := by dsimp [q]; omega
  have hqsq : q ^ 2 ≤ Z := hIV.2.1
  have hnpos := classMember_pos hnIV
  have hn0 : n ≠ 0 := hnpos.ne'
  have hbpos : 0 < b := by rw [← hb]; exact canonicalB_pos n Z
  have hwinData := Finset.mem_filter.mp hIV.1
  have hnIoc := Finset.mem_Ioc.mp hwinData.1
  have hdiv : b ∣ n := by rw [← hb]; exact canonicalB_dvd hn0 (by omega)
  have hdEq : canonicalD n Z = n / b := by simp [canonicalD, hb]
  have hdwin : canonicalD n Z ∈
      Finset.Ioc (X / b - quotientLength X Y b) (X / b) := by
    rw [hdEq]
    exact canonicalD_mem_rounded_quotientWindow hbpos hYX
      hnIoc.1 hnIoc.2 hdiv
  have hmodD : canonicalD n Z ≡ residue' [MOD modulus] := by
    apply hquotient
    rw [← hb, canonicalB_mul_canonicalD hn0 (by omega)]
    exact hwinData.2
  have hd1 : canonicalD n Z ≠ 1 := by
    intro hdone
    have : q = 1 := by simp [q, leastPrimeFactor, hdone]
    omega
  have hdgt : 1 < canonicalD n Z := by
    have hdpos : 0 < canonicalD n Z := by
      have hmul := canonicalB_mul_canonicalD hn0 (by omega : 1 ≤ Z)
      nlinarith [canonicalB_pos n Z]
    omega
  have hlower : classIVRootCutoff Z (r + 1) < q := by
    have hsource := (classIVIndex_source_interval hZ hq2 hqsq).1
    rw [hr] at hsource
    unfold classIVRootCutoff
    rw [Nat.floor_lt (Real.rpow_nonneg (by positivity) _)]
    exact hsource
  have hnoprime :
      ∀ p : ℕ, p.Prime → p ≤ classIVRootCutoff Z (r + 1) →
        ¬p ∣ canonicalD n Z := by
    intro p hp hple hpd
    have hminle : (canonicalD n Z).minFac ≤ p :=
      Nat.minFac_le_of_dvd hp.two_le hpd
    have hqmin : q = (canonicalD n Z).minFac := by
      simp [q, leastPrimeFactor, hd1]
    rw [hqmin] at hlower
    omega
  exact Finset.mem_filter.mpr ⟨hdwin, hmodD, hdgt, hnoprime⟩

theorem canonicalD_injectiveOn_classIVPrefixFiber
    {X Y modulus residue Z cutoff r b : ℕ} (hZ : 1 ≤ Z) :
    Set.InjOn (fun n => canonicalD n Z)
      ↑(classIVPrefixFiber X Y modulus residue Z cutoff r b) := by
  intro n hn m hm heq
  have hnData := Finset.mem_filter.mp hn
  have hmData := Finset.mem_filter.mp hm
  have hnIV := (Finset.mem_filter.mp hnData.1).1
  have hmIV := (Finset.mem_filter.mp hmData.1).1
  have hn0 : n ≠ 0 := (classMember_pos hnIV).ne'
  have hm0 : m ≠ 0 := (classMember_pos hmIV).ne'
  change canonicalD n Z = canonicalD m Z at heq
  calc
    n = canonicalB n Z * canonicalD n Z :=
      (canonicalB_mul_canonicalD hn0 hZ).symm
    _ = b * canonicalD n Z := by rw [hnData.2]
    _ = b * canonicalD m Z := by rw [heq]
    _ = canonicalB m Z * canonicalD m Z := by rw [hmData.2]
    _ = m := canonicalB_mul_canonicalD hm0 hZ

/-- Exact fixed-`(r,b)` reduction immediately before applying Shiu's Lemma 2.
`D` is only a pointwise suffix-weight bound; no class-IV total estimate is a
premise. -/
theorem classIVPrefixFiber_tauSquare_cast_le_phi
    (k X Y modulus residue residue' Z cutoff r b D : ℕ)
    (hZ : 3 ≤ Z) (hcutoff : 1 ≤ cutoff) (hYX : Y ≤ X)
    (hquotient : ∀ d : ℕ, b * d ≡ residue [MOD modulus] →
      d ≡ residue' [MOD modulus])
    (hDbound : ∀ n ∈ classIVPrefixFiber
        X Y modulus residue Z cutoff r b,
      tauAF k (canonicalD n Z) ^ 2 ≤ D) :
    ((∑ n ∈ classIVPrefixFiber X Y modulus residue Z cutoff r b,
        tauAF k n ^ 2 : ℕ) : ℝ) ≤
      (D : ℝ) * (tauAF k b ^ 2 : ℝ) *
        ShiuSieveSlice.shiuPhi (X / b) (quotientLength X Y b)
          (classIVRootCutoff Z (r + 1)) modulus residue' := by
  let F := classIVPrefixFiber X Y modulus residue Z cutoff r b
  let Q := classIVQuotientSet X Y modulus residue' Z r b
  have hmaps : Set.MapsTo (fun n => canonicalD n Z) ↑F ↑Q := by
    intro n hn
    exact canonicalD_mem_classIVQuotientSet hZ hcutoff hYX hquotient hn
  have hcard : F.card ≤ Q.card :=
    Finset.card_le_card_of_injOn (fun n => canonicalD n Z) hmaps
      (canonicalD_injectiveOn_classIVPrefixFiber (by omega))
  have hsum : (∑ n ∈ F, tauAF k n ^ 2) ≤
      F.card * (tauAF k b ^ 2 * D) := by
    refine (Finset.sum_le_card_nsmul F (fun n => tauAF k n ^ 2)
      (tauAF k b ^ 2 * D) ?_).trans_eq ?_
    · intro n hn
      have hnData := Finset.mem_filter.mp hn
      have hnIV := (Finset.mem_filter.mp hnData.1).1
      have hn0 : n ≠ 0 := (classMember_pos hnIV).ne'
      change tauAF k n ^ 2 ≤ tauAF k b ^ 2 * D
      rw [tauSquare_canonical_factorization (n := n) (z := Z) k hn0 (by omega),
        hnData.2]
      exact Nat.mul_le_mul_left _ (hDbound n hn)
    · simp
  have hsum' : (∑ n ∈ F, tauAF k n ^ 2) ≤
      Q.card * (tauAF k b ^ 2 * D) :=
    hsum.trans (Nat.mul_le_mul_right _ hcard)
  have hsumR : ((∑ n ∈ F, tauAF k n ^ 2 : ℕ) : ℝ) ≤
      ((Q.card * (tauAF k b ^ 2 * D) : ℕ) : ℝ) := by
    exact_mod_cast hsum'
  calc
    ((∑ n ∈ classIVPrefixFiber X Y modulus residue Z cutoff r b,
        tauAF k n ^ 2 : ℕ) : ℝ) ≤
      ((Q.card * (tauAF k b ^ 2 * D) : ℕ) : ℝ) := by simpa [F] using hsumR
    _ = (D : ℝ) * (tauAF k b ^ 2 : ℝ) *
        ShiuSieveSlice.shiuPhi (X / b) (quotientLength X Y b)
          (classIVRootCutoff Z (r + 1)) modulus residue' := by
      rw [shiuPhi_eq_card_classIVQuotientSet]
      dsimp [Q]
      push_cast
      ring

/-! ## Literal suffix-weight factor `A₅^r` -/

theorem tauAF_list_prod_le_pow_length
    (k : ℕ) (l : List ℕ) (hl : ∀ p ∈ l, p.Prime) :
    tauAF k l.prod ≤ k ^ l.length := by
  induction l with
  | nil => simpa using (tauAF_isMultiplicative k).map_one.le
  | cons p l ih =>
      have hp := hl p (List.mem_cons_self)
      have htail : ∀ q ∈ l, q.Prime := by
        intro q hq
        exact hl q (List.mem_cons_of_mem p hq)
      have hpTau : tauAF k p = k := by
        simpa using tauAF_prime_pow_eq_multichoose k 1 p hp
      calc
        tauAF k (p :: l).prod = tauAF k (p * l.prod) := by simp
        _ ≤ tauAF k p * tauAF k l.prod := tauAF_submultiplicative k p l.prod
        _ ≤ k * k ^ l.length := by
          rw [hpTau]
          exact Nat.mul_le_mul_left k (ih htail)
        _ = k ^ (p :: l).length := by simp [pow_succ, mul_comm]

theorem tauAF_le_pow_cardFactors (k n : ℕ) (hn : n ≠ 0) :
    tauAF k n ≤ k ^ Ω n := by
  calc
    tauAF k n = tauAF k n.primeFactorsList.prod := by
      rw [Nat.prod_primeFactorsList hn]
    _ ≤ k ^ n.primeFactorsList.length :=
      tauAF_list_prod_le_pow_length k n.primeFactorsList
        (fun p hp => Nat.prime_of_mem_primeFactorsList hp)
    _ = k ^ Ω n := by rw [ArithmeticFunction.cardFactors_apply]

theorem tauSquare_le_pow_cardFactors (k n : ℕ) (hn : n ≠ 0) :
    tauAF k n ^ 2 ≤ (k * k) ^ Ω n := by
  calc
    tauAF k n ^ 2 ≤ (k ^ Ω n) ^ 2 :=
      Nat.pow_le_pow_left (tauAF_le_pow_cardFactors k n hn) 2
    _ = (k * k) ^ Ω n := by
      rw [pow_two, mul_pow]

/-- Every prime factor is at least the least prime factor, so its `Ω`-fold
power is bounded by the number itself. -/
theorem minFac_pow_cardFactors_le (n : ℕ) (hn : n ≠ 0) :
    n.minFac ^ Ω n ≤ n := by
  have hpoint : ∀ p ∈ n.primeFactorsList, n.minFac ≤ p := by
    intro p hp
    exact Nat.minFac_le_of_dvd
      (Nat.prime_of_mem_primeFactorsList hp).two_le
      (Nat.dvd_of_mem_primeFactorsList hp)
  have hprod := List.prod_le_prod'
    (l := n.primeFactorsList) (f := fun _ => n.minFac) (g := fun p => p)
    hpoint
  simpa [ArithmeticFunction.cardFactors_apply, Nat.prod_primeFactorsList hn]
    using hprod

/-- The source estimate `Ω(d_n) < 180 r` for the specialized
`alpha=beta=1/3` range.  The constant is a safe integer version of the printed
`20/(alpha beta)`. -/
theorem canonicalD_cardFactors_lt_oneEighty_mul_index
    {n X Z r : ℕ} (hn : n ≠ 0) (hZ : 3 ≤ Z) (hZn : Z < n)
    (hnX : n ≤ X) (hXZ : X < Z ^ 90)
    (hr : classIVIndex Z (leastPrimeFactor (canonicalD n Z)) = r)
    (hq2 : 2 ≤ leastPrimeFactor (canonicalD n Z))
    (hqsq : leastPrimeFactor (canonicalD n Z) ^ 2 ≤ Z) :
    Ω (canonicalD n Z) < 180 * r := by
  let d := canonicalD n Z
  let q := leastPrimeFactor d
  have hdpos : 0 < d := by
    have hmul := canonicalB_mul_canonicalD hn (by omega : 1 ≤ Z)
    dsimp [d]
    nlinarith [canonicalB_pos n Z]
  have hd1 : d ≠ 1 := by
    intro hd
    have : q = 1 := by simp [q, leastPrimeFactor, hd]
    have hq2' : 2 ≤ q := by simpa [q, d] using hq2
    omega
  have hqmin : q = d.minFac := by simp [q, leastPrimeFactor, hd1]
  have hqOmega : q ^ Ω d ≤ d := by
    rw [hqmin]
    exact minFac_pow_cardFactors_le d hdpos.ne'
  have hdle : d ≤ n := by
    apply Nat.le_of_dvd (by omega)
    refine ⟨canonicalB n Z, ?_⟩
    rw [mul_comm, canonicalB_mul_canonicalD hn (by omega)]
  have hsource := classIVIndex_bounds hZ hq2 hqsq
  have hZpow : Z ^ 90 < q ^ ((classIVIndex Z q + 1) * 90) := by
    have hpow := Nat.pow_lt_pow_left hsource.2.2.2 (by omega : 90 ≠ 0)
    simpa [pow_mul] using hpow
  have hqOmegaLt : q ^ Ω d < q ^ ((classIVIndex Z q + 1) * 90) :=
    lt_of_le_of_lt hqOmega
      ((hdle.trans hnX).trans_lt (hXZ.trans hZpow))
  have hOmega : Ω d < (classIVIndex Z q + 1) * 90 :=
    (Nat.pow_lt_pow_iff_right (by
      have : 2 ≤ q := by simpa [q, d] using hq2
      omega : 1 < q)).mp hqOmegaLt
  have hr' : classIVIndex Z q = r := by simpa [q, d] using hr
  rw [hr'] at hOmega
  have hOmega' : Ω (canonicalD n Z) < (r + 1) * 90 := by
    simpa [d] using hOmega
  have hr2 : 2 ≤ r := by
    rw [hr'] at hsource
    exact hsource.1
  omega

def classIVSuffixBase (k : ℕ) : ℕ := (k * k) ^ 180

/-- The exact fixed-bin pointwise suffix bound used before Lemma 2. -/
theorem classIVPrefixFiber_suffixWeight_le
    {k X Y modulus residue Z cutoff r b n : ℕ}
    (hk : 1 ≤ k) (hZ : 3 ≤ Z) (hcutoff : 1 ≤ cutoff) (hZn : Z < n)
    (hXZ : X < Z ^ 90)
    (hn : n ∈ classIVPrefixFiber X Y modulus residue Z cutoff r b) :
    tauAF k (canonicalD n Z) ^ 2 ≤ classIVSuffixBase k ^ r := by
  have hnfiber := Finset.mem_filter.mp hn
  have hnbin := Finset.mem_filter.mp hnfiber.1
  have hnIV := hnbin.1
  have hr := hnbin.2
  have hIV := mem_class_IV_iff.mp hnIV
  have hnpos := classMember_pos hnIV
  have hn0 := hnpos.ne'
  have hnX : n ≤ X :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hIV.1).1).2
  have hq2 : 2 ≤ leastPrimeFactor (canonicalD n Z) := by
    exact (Nat.succ_le_iff.mpr (hcutoff.trans_lt hIV.2.2.2))
  have hOmega := canonicalD_cardFactors_lt_oneEighty_mul_index
    hn0 hZ hZn hnX hXZ hr hq2 hIV.2.1
  have hbasepos : 0 < k * k := by nlinarith
  calc
    tauAF k (canonicalD n Z) ^ 2 ≤
        (k * k) ^ Ω (canonicalD n Z) :=
      tauSquare_le_pow_cardFactors k (canonicalD n Z) (by
        intro hd
        have hmul := canonicalB_mul_canonicalD hn0 (by omega : 1 ≤ Z)
        rw [hd, mul_zero] at hmul
        exact hn0 hmul.symm)
    _ ≤ (k * k) ^ (180 * r) :=
      Nat.pow_le_pow_right hbasepos hOmega.le
    _ = classIVSuffixBase k ^ r := by
      simp [classIVSuffixBase, pow_mul]

/-! ## The literal harmonic prefix in a fixed `r`-bin -/

/-- Prefixes which actually occur in the `r`-th class-IV bin.  Filtering out
empty fibers is what permits the class-IV information of a witness to be
transported to the prefix before Lemma 4 is applied. -/
def classIVActivePrefixes
    (X Y modulus residue Z cutoff r : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Z).filter fun b =>
    (classIVPrefixFiber X Y modulus residue Z cutoff r b).Nonempty

/-- The harmonic prefix mass which appears literally in (5.8). -/
def classIVHarmonicPrefix
    (k X Y modulus residue Z cutoff r : ℕ) : ℝ :=
  ∑ b ∈ classIVActivePrefixes X Y modulus residue Z cutoff r,
    (tauAF k b ^ 2 : ℝ) / (b : ℝ)

theorem classIVBinMass_eq_sum_active_prefixFibers
    (k X Y modulus residue Z cutoff r : ℕ) (hZ : 1 ≤ Z) :
    classIVBinMass k X Y modulus residue Z cutoff r =
      ∑ b ∈ classIVActivePrefixes X Y modulus residue Z cutoff r,
        ∑ n ∈ classIVPrefixFiber X Y modulus residue Z cutoff r b,
          tauAF k n ^ 2 := by
  rw [classIVBinMass_eq_sum_prefixFibers
    k X Y modulus residue Z cutoff r hZ]
  unfold classIVActivePrefixes
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hnonempty :
      (classIVPrefixFiber X Y modulus residue Z cutoff r b).Nonempty
  · simp [hnonempty]
  · have hempty :
        classIVPrefixFiber X Y modulus residue Z cutoff r b = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    simp [hnonempty, hempty]

lemma activePrefix_witness
    {X Y modulus residue Z cutoff r b : ℕ}
    (hb : b ∈ classIVActivePrefixes X Y modulus residue Z cutoff r) :
    ∃ n, n ∈ classIVPrefixFiber X Y modulus residue Z cutoff r b := by
  exact (Finset.mem_filter.mp hb).2

lemma activePrefix_mem_Icc
    {X Y modulus residue Z cutoff r b : ℕ}
    (hb : b ∈ classIVActivePrefixes X Y modulus residue Z cutoff r) :
    b ∈ Finset.Icc 1 Z :=
  (Finset.mem_filter.mp hb).1

lemma cutoff_lt_of_canonicalD_boundaryPrime
    {n Z cutoff : ℕ} (hn : n ≠ 0) (hZ : 1 ≤ Z)
    (hcutoff : 1 ≤ cutoff)
    (hq : cutoff < leastPrimeFactor (canonicalD n Z)) :
    Z < n := by
  by_contra hnot
  have hnZ : n ≤ Z := Nat.le_of_not_gt hnot
  have hfull : (primePowerBlocks n).length ∈ admissiblePrefixLengths n Z := by
    apply Finset.mem_filter.mpr
    constructor
    · simp
    · simp [prefixProduct, primePowerBlocks_prod hn, hnZ]
  have hge := le_canonicalIndex_of_mem hZ hfull
  have hle := canonicalIndex_le_length (n := n) hZ
  have hidx : canonicalIndex n Z = (primePowerBlocks n).length := by omega
  have hb : canonicalB n Z = n := by
    simp [canonicalB, prefixProduct, hidx, primePowerBlocks_prod hn]
  have hd : canonicalD n Z = 1 := by
    simpa [canonicalD, hb] using Nat.div_self (Nat.pos_of_ne_zero hn)
  simp [hd, leastPrimeFactor] at hq
  omega

/-- Every active prefix is one of the finite terms in the promoted Lemma-4
tail, with exactly the source cutoff `floor (Z^(1/r))`. -/
theorem activePrefix_mem_tauSquareSmoothTailSupport
    {X Y modulus residue Z cutoff r b : ℕ}
    (hZ : 3 ≤ Z) (hcutoff : 1 ≤ cutoff)
    (hresidue : residue.Coprime modulus)
    (hb : b ∈ classIVActivePrefixes X Y modulus residue Z cutoff r) :
    ((Z : ℝ) ^ (1 / 2 : ℝ) ≤ (b : ℝ)) ∧
      b ∈ Nat.smoothNumbers (classIVRootCutoff Z r + 1) ∧
      b.Coprime modulus := by
  obtain ⟨n, hn⟩ := activePrefix_witness hb
  have hnfiber := Finset.mem_filter.mp hn
  have hnbin := Finset.mem_filter.mp hnfiber.1
  have hnIV := hnbin.1
  have hr := hnbin.2
  have hbEq := hnfiber.2
  have hIV := mem_class_IV_iff.mp hnIV
  have hn0 : n ≠ 0 := (classMember_pos hnIV).ne'
  have hq2 : 2 ≤ leastPrimeFactor (canonicalD n Z) := by omega
  have hsmooth := canonicalB_mem_classIVRootSmooth
    hn0 hZ (cutoff_lt_of_canonicalD_boundaryPrime hn0 (by omega) hcutoff hIV.2.2.2)
      hq2 hIV.2.1
  have hsqrt : (Z : ℝ) ^ (1 / 2 : ℝ) ≤ (canonicalB n Z : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by exact_mod_cast hIV.2.2.1.le⟩
  have hcop := ShiuEndToEnd.canonicalB_coprime_modulus_of_classMember
    (c := FourClass.IV) (by omega : 1 ≤ Z) hresidue hnIV
  rw [hr] at hsmooth
  simpa [hbEq] using And.intro hsqrt (And.intro hsmooth hcop)

/-- The active harmonic prefix is a literal sub-sum of the unconditional
finite Lemma-4 tail. -/
theorem classIVHarmonicPrefix_le_tauSquareSmoothTail
    (k X Y modulus residue Z cutoff r : ℕ)
    (hZ : 3 ≤ Z) (hcutoff : 1 ≤ cutoff)
    (hresidue : residue.Coprime modulus) :
    classIVHarmonicPrefix k X Y modulus residue Z cutoff r ≤
      ShiuEndToEnd.tauSquareSmoothTail k Z
        (classIVRootCutoff Z r) modulus := by
  classical
  rw [ShiuEndToEnd.tauSquareSmoothTail_eq_promoted,
    ShiuLemma4TauTail.tauSquareSmoothTail_eq_filterSum]
  unfold classIVHarmonicPrefix
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro b hb
    have hbIcc := activePrefix_mem_Icc hb
    have hsupp := activePrefix_mem_tauSquareSmoothTailSupport
      hZ hcutoff hresidue hb
    exact Finset.mem_filter.mpr ⟨hbIcc, hsupp⟩
  · intro b hbTail hbActive
    positivity

lemma two_pow_succ_le_three_pow (r : ℕ) (hr : 2 ≤ r) :
    2 ^ (r + 1) ≤ 3 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
      calc
        2 ^ (r + 1 + 1) = 2 ^ (r + 1) * 2 := by rw [pow_succ]
        _ ≤ 3 ^ r * 3 := Nat.mul_le_mul ih (by norm_num)
        _ = 3 ^ (r + 1) := by rw [pow_succ]

/-- In a nonempty class-IV bin the lower sieve cutoff
`floor(Z^(1/(r+1)))` is at least two.  This is the integer rounding fact used
implicitly just before (5.8). -/
theorem two_le_classIVLowerRootCutoff_of_active
    {X Y modulus residue Z cutoff r : ℕ}
    (hZ : 3 ≤ Z) (hcutoff : 2 ≤ cutoff)
    (hactive :
      (classIVActivePrefixes X Y modulus residue Z cutoff r).Nonempty) :
    2 ≤ classIVRootCutoff Z (r + 1) := by
  obtain ⟨b, hb⟩ := hactive
  obtain ⟨n, hn⟩ := activePrefix_witness hb
  have hnfiber := Finset.mem_filter.mp hn
  have hnbin := Finset.mem_filter.mp hnfiber.1
  have hnIV := hnbin.1
  have hrEq := hnbin.2
  have hIV := mem_class_IV_iff.mp hnIV
  let q := leastPrimeFactor (canonicalD n Z)
  have hq3 : 3 ≤ q := by dsimp [q]; omega
  have hq2 : 2 ≤ q := by omega
  have hqsq : q ^ 2 ≤ Z := by simpa [q] using hIV.2.1
  have hr2' := (classIVIndex_bounds hZ hq2 hqsq).1
  have hrpow' := (classIVIndex_bounds hZ hq2 hqsq).2.2.1
  have hr2 : 2 ≤ r := by simpa [q, hrEq] using hr2'
  have hrpow : q ^ r ≤ Z := by simpa [q, hrEq] using hrpow'
  have htwoPow : 2 ^ (r + 1) ≤ Z := by
    calc
      2 ^ (r + 1) ≤ 3 ^ r := two_pow_succ_le_three_pow r hr2
      _ ≤ q ^ r := Nat.pow_le_pow_left hq3 r
      _ ≤ Z := hrpow
  have htwoRoot : (2 : ℝ) ≤ (Z : ℝ) ^ (((r + 1 : ℕ) : ℝ)⁻¹) := by
    rw [Real.le_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 2)
      (by positivity : (0 : ℝ) ≤ Z)]
    · rw [Real.rpow_natCast]
      exact_mod_cast htwoPow
    · exact_mod_cast (show 0 < r + 1 by omega)
  unfold classIVRootCutoff
  exact_mod_cast (Nat.le_floor htwoRoot)

theorem classIVLowerRootCutoff_sq_le_Z_of_active
    {X Y modulus residue Z cutoff r : ℕ}
    (hZ : 3 ≤ Z) (hcutoff : 2 ≤ cutoff)
    (hactive :
      (classIVActivePrefixes X Y modulus residue Z cutoff r).Nonempty) :
    classIVRootCutoff Z (r + 1) ^ 2 ≤ Z := by
  let L := classIVRootCutoff Z (r + 1)
  have hL2 : 2 ≤ L :=
    two_le_classIVLowerRootCutoff_of_active hZ hcutoff hactive
  have hfloorR : (L : ℝ) ≤
      (Z : ℝ) ^ ((((r + 1 : ℕ) : ℝ))⁻¹) := by
    dsimp [L, classIVRootCutoff]
    exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  have hpowR : (L : ℝ) ^ (r + 1) ≤ (Z : ℝ) := by
    calc
      (L : ℝ) ^ (r + 1) ≤
          ((Z : ℝ) ^ ((((r + 1 : ℕ) : ℝ))⁻¹)) ^ (r + 1) :=
        pow_le_pow_left₀ (by positivity) hfloorR _
      _ = (Z : ℝ) :=
        Real.rpow_inv_natCast_pow (by positivity)
          (show r + 1 ≠ 0 by omega)
  have hpowNat : L ^ (r + 1) ≤ Z := by exact_mod_cast hpowR
  have htwoexp : 2 ≤ r + 1 := by
    obtain ⟨b, hb⟩ := hactive
    obtain ⟨n, hn⟩ := activePrefix_witness hb
    have hnbin := Finset.mem_filter.mp (Finset.mem_filter.mp hn).1
    have hIV := mem_class_IV_iff.mp hnbin.1
    let q := leastPrimeFactor (canonicalD n Z)
    have hq2 : 2 ≤ q := by dsimp [q]; omega
    have hqsq : q ^ 2 ≤ Z := by simpa [q] using hIV.2.1
    have hr2 := (classIVIndex_bounds hZ hq2 hqsq).1
    have hrEq := hnbin.2
    have : 2 ≤ r := by simpa [q, hrEq] using hr2
    omega
  exact (Nat.pow_le_pow_right (by omega : 0 < L) htwoexp).trans hpowNat

/-- Literal Lemma-4 saving in one nonempty source bin.  The only scale input
not internal to the bin is the published elementary comparison
`log Z < cutoff * log cutoff`. -/
theorem classIVHarmonicPrefix_le_oneTenth
    (k X Y modulus residue Z cutoff r : ℕ)
    (hk : 1 ≤ k) (hZ : 3 ≤ Z) (hcutoff : 2 ≤ cutoff)
    (hlogcutoff : Real.log (Z : ℝ) <
      (cutoff : ℝ) * Real.log (cutoff : ℝ))
    (hresidue : residue.Coprime modulus) :
    classIVHarmonicPrefix k X Y modulus residue Z cutoff r ≤
      ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k *
        Real.exp
          ((k * k : ℕ) * ShiuLemma4EndpointWeld.omittedPrimeInvSum
              (classIVRootCutoff Z r) modulus -
            (1 / 10 : ℝ) * (r : ℝ) * Real.log (r : ℝ)) := by
  classical
  by_cases hactive :
      (classIVActivePrefixes X Y modulus residue Z cutoff r).Nonempty
  · obtain ⟨b, hb⟩ := hactive
    obtain ⟨n, hn⟩ := activePrefix_witness hb
    have hnfiber := Finset.mem_filter.mp hn
    have hnbin := Finset.mem_filter.mp hnfiber.1
    have hnIV := hnbin.1
    have hrEq := hnbin.2
    have hIV := mem_class_IV_iff.mp hnIV
    let q := leastPrimeFactor (canonicalD n Z)
    have hq2 : 2 ≤ q := by dsimp [q]; omega
    have hqsq : q ^ 2 ≤ Z := by simpa [q] using hIV.2.1
    have hcutq : cutoff < q := by simpa [q] using hIV.2.2.2
    have hcutR : (0 : ℝ) ≤ cutoff := by positivity
    have hqR : (0 : ℝ) ≤ q := by positivity
    have hlogmono : Real.log (cutoff : ℝ) ≤ Real.log (q : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast (show 0 < cutoff by omega)
      · exact_mod_cast hcutq.le
    have hqlog : Real.log (Z : ℝ) < (q : ℝ) * Real.log (q : ℝ) := by
      calc
        Real.log (Z : ℝ) <
            (cutoff : ℝ) * Real.log (cutoff : ℝ) := hlogcutoff
        _ ≤ (q : ℝ) * Real.log (q : ℝ) := by
          apply mul_le_mul
          · exact_mod_cast hcutq.le
          · exact hlogmono
          · exact Real.log_nonneg (by
              exact_mod_cast (show 1 ≤ cutoff by omega))
          · exact hqR
    have hrq := classIVIndex_le_boundaryPrime_of_log hZ hq2 hqsq hqlog
    have hrange0 := classIVIndex_rankin_range hZ hq2 hqsq hrq
    have hrange : (r : ℝ) * Real.log (r : ℝ) ≤ Real.log (Z : ℝ) := by
      simpa [q, hrEq] using hrange0
    have hr2 : 2 ≤ r := by
      have := (classIVIndex_bounds hZ hq2 hqsq).1
      simpa [q, hrEq] using this
    have hy2 : 2 ≤ classIVRootCutoff Z r := by
      have := two_le_classIVRootCutoff hZ hq2 hqsq
      simpa [q, hrEq] using this
    have hyroot :
        (classIVRootCutoff Z r : ℝ) ≤ (Z : ℝ) ^ ((r : ℝ)⁻¹) := by
      unfold classIVRootCutoff
      exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    have htail :=
      ShiuFiniteEulerDistortion.tauSquareSmoothTail_le_oneTenth
        k Z (classIVRootCutoff Z r) modulus (r : ℝ)
        hk hZ (by exact_mod_cast (show 1 ≤ r by omega))
        hrange hy2 hyroot
    have htail' :
        ShiuEndToEnd.tauSquareSmoothTail k Z
            (classIVRootCutoff Z r) modulus ≤
          ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k *
            Real.exp
              ((k * k : ℕ) * ShiuLemma4EndpointWeld.omittedPrimeInvSum
                  (classIVRootCutoff Z r) modulus -
                (1 / 10 : ℝ) * (r : ℝ) * Real.log (r : ℝ)) := by
      rw [ShiuEndToEnd.tauSquareSmoothTail_eq_promoted]
      exact htail
    exact (classIVHarmonicPrefix_le_tauSquareSmoothTail
      k X Y modulus residue Z cutoff r hZ (by omega) hresidue).trans htail'
  · have hempty :
        classIVActivePrefixes X Y modulus residue Z cutoff r = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hactive
    rw [classIVHarmonicPrefix, hempty]
    simp only [Finset.sum_empty]
    exact mul_nonneg
      (ShiuFiniteEulerDistortion.explicitEulerDistortionConstant_pos k).le
      (Real.exp_pos _).le

/-! ## Fixed-bin Selberg envelope -/

/-- Applying certified Lemma 2 to every nonempty fixed-prefix fiber in one
class-IV bin.  This is the first line of the displayed estimate (5.8), before
the elementary conversion to the harmonic prefix. -/
theorem classIVBinMass_cast_le_selbergSum
    (k X Y modulus residue Z cutoff r : ℕ)
    (hk : 1 ≤ k) (hZ : 3 ≤ Z) (hcutoff : 2 ≤ cutoff)
    (hYX : Y ≤ X) (hXZ : X < Z ^ 90)
    (hmodulus : 0 < modulus) (hresidueLt : residue < modulus)
    (hresidue : residue.Coprime modulus)
    (hactive :
      (classIVActivePrefixes X Y modulus residue Z cutoff r).Nonempty)
    (hmodLength : ∀ b ∈
      classIVActivePrefixes X Y modulus residue Z cutoff r,
      modulus < quotientLength X Y b) :
    (classIVBinMass k X Y modulus residue Z cutoff r : ℝ) ≤
      (classIVSuffixBase k ^ r : ℕ) *
        ShiuClassIBound.classISelbergConstant *
          ∑ b ∈ classIVActivePrefixes X Y modulus residue Z cutoff r,
            (tauAF k b ^ 2 : ℝ) *
              (((quotientLength X Y b : ℕ) : ℝ) /
                  ((Nat.totient modulus : ℝ) *
                    Real.log (classIVRootCutoff Z (r + 1) : ℝ)) +
                (classIVRootCutoff Z (r + 1) : ℝ) ^ 2) := by
  rw [classIVBinMass_eq_sum_active_prefixFibers
    k X Y modulus residue Z cutoff r (by omega)]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  obtain ⟨n₀, hn₀⟩ := activePrefix_witness hb
  have hn₀fiber := Finset.mem_filter.mp hn₀
  have hn₀bin := Finset.mem_filter.mp hn₀fiber.1
  have hbEq := hn₀fiber.2
  have hbCop0 := ShiuEndToEnd.canonicalB_coprime_modulus_of_classMember
    (c := FourClass.IV) (by omega : 1 ≤ Z) hresidue hn₀bin.1
  have hbCop : b.Coprime modulus := by simpa [hbEq] using hbCop0
  have hqspec := quotientResidue_spec
    (residue := residue) hmodulus hbCop
  have hqcop := quotientResidue_coprime hmodulus hbCop hresidue
  have hfiber := classIVPrefixFiber_tauSquare_cast_le_phi
    k X Y modulus residue (quotientResidue b residue modulus)
    Z cutoff r b (classIVSuffixBase k ^ r)
    hZ (by omega) hYX hqspec.2.2
    (fun n hn => classIVPrefixFiber_suffixWeight_le
      hk hZ (by omega) (cutoff_lt_of_canonicalD_boundaryPrime
        (classMember_pos (Finset.mem_filter.mp
          (Finset.mem_filter.mp hn).1).1).ne'
        (by omega) (by omega)
        (mem_class_IV_iff.mp (Finset.mem_filter.mp
          (Finset.mem_filter.mp hn).1).1).2.2.2)
      hXZ hn)
  have hsieve : 2 ≤ classIVRootCutoff Z (r + 1) :=
    two_le_classIVLowerRootCutoff_of_active hZ hcutoff hactive
  have hselberg := ShiuClassIBound.classISelbergUpperBound
    (X / b) (quotientLength X Y b) (classIVRootCutoff Z (r + 1))
    modulus (quotientResidue b residue modulus)
    hmodulus hqspec.1 hqcop (hmodLength b hb)
    (min_le_right _ _) hsieve
  calc
    (∑ n ∈ classIVPrefixFiber X Y modulus residue Z cutoff r b,
        (tauAF k n ^ 2 : ℝ)) ≤
      (classIVSuffixBase k : ℝ) ^ r * (tauAF k b ^ 2 : ℝ) *
        ShiuSieveSlice.shiuPhi (X / b) (quotientLength X Y b)
          (classIVRootCutoff Z (r + 1)) modulus
          (quotientResidue b residue modulus) := by
      simpa only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] using hfiber
    _ ≤ (classIVSuffixBase k : ℝ) ^ r * (tauAF k b ^ 2 : ℝ) *
        (ShiuClassIBound.classISelbergConstant *
          (((quotientLength X Y b : ℕ) : ℝ) /
              ((Nat.totient modulus : ℝ) *
                Real.log (classIVRootCutoff Z (r + 1) : ℝ)) +
            (classIVRootCutoff Z (r + 1) : ℝ) ^ 2)) := by
      gcongr
    _ = (classIVSuffixBase k : ℝ) ^ r *
        ShiuClassIBound.classISelbergConstant *
          ((tauAF k b ^ 2 : ℝ) *
            (((quotientLength X Y b : ℕ) : ℝ) /
                ((Nat.totient modulus : ℝ) *
                  Real.log (classIVRootCutoff Z (r + 1) : ℝ)) +
              (classIVRootCutoff Z (r + 1) : ℝ) ^ 2)) := by ring

/-- The Lemma-2 summand is compressed into the harmonic prefix.  We retain a
fixed `log 2` denominator; this is a harmless weakening of the printed
`(r+1)/log Z` factor and the same negative `r log r` saving makes the final
series converge. -/
theorem classIV_selbergSummand_le_harmonic
    (k X Y modulus residue Z cutoff r b : ℕ)
    (hZ : 3 ≤ Z) (hcutoff : 2 ≤ cutoff) (hZY : Z ≤ Y)
    (hmodulus : 0 < modulus)
    (hactive :
      (classIVActivePrefixes X Y modulus residue Z cutoff r).Nonempty)
    (hb : b ∈ classIVActivePrefixes X Y modulus residue Z cutoff r) :
    (tauAF k b ^ 2 : ℝ) *
        (((quotientLength X Y b : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) *
              Real.log (classIVRootCutoff Z (r + 1) : ℝ)) +
          (classIVRootCutoff Z (r + 1) : ℝ) ^ 2) ≤
      ((((2 * Y : ℕ) : ℝ) /
          ((Nat.totient modulus : ℝ) * Real.log 2)) + (Z : ℝ) ^ 2) *
        ((tauAF k b ^ 2 : ℝ) / (b : ℝ)) := by
  have hbIcc := activePrefix_mem_Icc hb
  have hbIcc' := Finset.mem_Icc.mp hbIcc
  have hbpos : 0 < b := by omega
  have hbY : b ≤ Y := hbIcc'.2.trans hZY
  have hYdiv : 1 ≤ Y / b :=
    (Nat.le_div_iff_mul_le hbpos).2 (by simpa using hbY)
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
  let L := classIVRootCutoff Z (r + 1)
  have hL2 : 2 ≤ L :=
    two_le_classIVLowerRootCutoff_of_active hZ hcutoff hactive
  have hphi : (0 : ℝ) < Nat.totient modulus := by
    exact_mod_cast Nat.totient_pos.mpr hmodulus
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogL : (0 : ℝ) < Real.log (L : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogmono : Real.log 2 ≤ Real.log (L : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hL2)
  let denL : ℝ := (Nat.totient modulus : ℝ) * Real.log (L : ℝ)
  let den2 : ℝ := (Nat.totient modulus : ℝ) * Real.log 2
  have hdenL : 0 < denL := mul_pos hphi hlogL
  have hden2 : 0 < den2 := mul_pos hphi hlog2
  have hdenle : den2 ≤ denL := by
    dsimp [den2, denL]
    exact mul_le_mul_of_nonneg_left hlogmono hphi.le
  have hmain : ((quotientLength X Y b : ℕ) : ℝ) / denL ≤
      ((((2 * Y : ℕ) : ℝ) / den2) / (b : ℝ)) := by
    calc
      ((quotientLength X Y b : ℕ) : ℝ) / denL ≤
          ((quotientLength X Y b : ℕ) : ℝ) / den2 :=
        div_le_div_of_nonneg_left (by positivity) hden2 hdenle
      _ ≤ (((2 * Y : ℕ) : ℝ) / den2) / (b : ℝ) := by
        apply (div_le_iff₀ hden2).2
        calc
          ((quotientLength X Y b : ℕ) : ℝ) ≤
              (2 * (Y : ℝ)) / (b : ℝ) := hlenR
          _ = (((((2 * Y : ℕ) : ℝ) / den2) / (b : ℝ)) * den2) := by
            push_cast
            field_simp
  have hLsq : L ^ 2 ≤ Z :=
    classIVLowerRootCutoff_sq_le_Z_of_active hZ hcutoff hactive
  have herrNat : L ^ 2 * b ≤ Z ^ 2 := by
    calc
      L ^ 2 * b ≤ Z * Z :=
        Nat.mul_le_mul hLsq (Finset.mem_Icc.mp hbIcc).2
      _ = Z ^ 2 := by ring
  have herr : (L : ℝ) ^ 2 ≤ (Z : ℝ) ^ 2 / (b : ℝ) := by
    apply (le_div_iff₀ hbR).2
    exact_mod_cast herrNat
  have hweight : (0 : ℝ) ≤ tauAF k b ^ 2 := by positivity
  dsimp [L, denL, den2] at hmain hdenL hden2 hdenle ⊢
  calc
    (tauAF k b ^ 2 : ℝ) *
        (((quotientLength X Y b : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) *
              Real.log (classIVRootCutoff Z (r + 1) : ℝ)) +
          (classIVRootCutoff Z (r + 1) : ℝ) ^ 2) ≤
      (tauAF k b ^ 2 : ℝ) *
        (((((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) * Real.log 2)) / (b : ℝ)) +
          (Z : ℝ) ^ 2 / (b : ℝ)) := by
        gcongr
    _ = ((((2 * Y : ℕ) : ℝ) /
          ((Nat.totient modulus : ℝ) * Real.log 2)) + (Z : ℝ) ^ 2) *
        ((tauAF k b ^ 2 : ℝ) / (b : ℝ)) := by
      field_simp

theorem classIV_selbergSum_le_bracket_mul_harmonic
    (k X Y modulus residue Z cutoff r : ℕ)
    (hZ : 3 ≤ Z) (hcutoff : 2 ≤ cutoff) (hZY : Z ≤ Y)
    (hmodulus : 0 < modulus)
    (hactive :
      (classIVActivePrefixes X Y modulus residue Z cutoff r).Nonempty) :
    (∑ b ∈ classIVActivePrefixes X Y modulus residue Z cutoff r,
      (tauAF k b ^ 2 : ℝ) *
        (((quotientLength X Y b : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) *
              Real.log (classIVRootCutoff Z (r + 1) : ℝ)) +
          (classIVRootCutoff Z (r + 1) : ℝ) ^ 2)) ≤
      ((((2 * Y : ℕ) : ℝ) /
          ((Nat.totient modulus : ℝ) * Real.log 2)) + (Z : ℝ) ^ 2) *
        classIVHarmonicPrefix k X Y modulus residue Z cutoff r := by
  calc
    _ ≤ ∑ b ∈ classIVActivePrefixes X Y modulus residue Z cutoff r,
        (((((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) * Real.log 2)) + (Z : ℝ) ^ 2) *
          ((tauAF k b ^ 2 : ℝ) / (b : ℝ))) := by
      apply Finset.sum_le_sum
      intro b hb
      exact classIV_selbergSummand_le_harmonic
        k X Y modulus residue Z cutoff r b hZ hcutoff hZY
        hmodulus hactive hb
    _ = ((((2 * Y : ℕ) : ℝ) /
          ((Nat.totient modulus : ℝ) * Real.log 2)) + (Z : ℝ) ^ 2) *
        classIVHarmonicPrefix k X Y modulus residue Z cutoff r := by
      unfold classIVHarmonicPrefix
      rw [Finset.mul_sum]

/-- Complete literal fixed-bin estimate: suffix weight, certified Lemma 2,
harmonic prefix, and unconditional Lemma 4. -/
theorem classIVBinMass_cast_le_oneTenth
    (k X Y modulus residue Z cutoff r : ℕ)
    (hk : 1 ≤ k) (hZ : 3 ≤ Z) (hcutoff : 2 ≤ cutoff)
    (hlogcutoff : Real.log (Z : ℝ) <
      (cutoff : ℝ) * Real.log (cutoff : ℝ))
    (hYX : Y ≤ X) (hXZ : X < Z ^ 90) (hZY : Z ≤ Y)
    (hmodulus : 0 < modulus) (hresidueLt : residue < modulus)
    (hresidue : residue.Coprime modulus)
    (hmodLength : ∀ b ∈
      classIVActivePrefixes X Y modulus residue Z cutoff r,
      modulus < quotientLength X Y b) :
    (classIVBinMass k X Y modulus residue Z cutoff r : ℝ) ≤
      ((classIVSuffixBase k : ℝ) ^ r *
        ShiuClassIBound.classISelbergConstant) *
          (((((2 * Y : ℕ) : ℝ) /
              ((Nat.totient modulus : ℝ) * Real.log 2)) + (Z : ℝ) ^ 2) *
            (ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k *
              Real.exp
                ((k * k : ℕ) * ShiuLemma4EndpointWeld.omittedPrimeInvSum
                    (classIVRootCutoff Z r) modulus -
                  (1 / 10 : ℝ) * (r : ℝ) * Real.log (r : ℝ)))) := by
  classical
  by_cases hactive :
      (classIVActivePrefixes X Y modulus residue Z cutoff r).Nonempty
  · have hselberg := classIVBinMass_cast_le_selbergSum
      k X Y modulus residue Z cutoff r hk hZ hcutoff hYX hXZ
      hmodulus hresidueLt hresidue hactive hmodLength
    have hcompress := classIV_selbergSum_le_bracket_mul_harmonic
      k X Y modulus residue Z cutoff r hZ hcutoff hZY hmodulus hactive
    have htail := classIVHarmonicPrefix_le_oneTenth
      k X Y modulus residue Z cutoff r hk hZ hcutoff hlogcutoff hresidue
    have hselberg' :
        (classIVBinMass k X Y modulus residue Z cutoff r : ℝ) ≤
          (classIVSuffixBase k : ℝ) ^ r *
            ShiuClassIBound.classISelbergConstant *
              ∑ b ∈ classIVActivePrefixes X Y modulus residue Z cutoff r,
                (tauAF k b ^ 2 : ℝ) *
                  (((quotientLength X Y b : ℕ) : ℝ) /
                      ((Nat.totient modulus : ℝ) *
                        Real.log (classIVRootCutoff Z (r + 1) : ℝ)) +
                    (classIVRootCutoff Z (r + 1) : ℝ) ^ 2) := by
      simpa only [Nat.cast_pow] using hselberg
    have hbase : (0 : ℝ) ≤ (classIVSuffixBase k : ℝ) ^ r := by positivity
    have hC2 : 0 ≤ ShiuClassIBound.classISelbergConstant :=
      ShiuClassIBound.classISelbergConstant_pos.le
    have hphi : (0 : ℝ) < Nat.totient modulus := by
      exact_mod_cast Nat.totient_pos.mpr hmodulus
    have hbracket : 0 ≤ ((((2 * Y : ℕ) : ℝ) /
          ((Nat.totient modulus : ℝ) * Real.log 2)) + (Z : ℝ) ^ 2) := by
      have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    refine hselberg'.trans ?_
    calc
      (classIVSuffixBase k : ℝ) ^ r *
          ShiuClassIBound.classISelbergConstant *
            (∑ b ∈ classIVActivePrefixes X Y modulus residue Z cutoff r,
              (tauAF k b ^ 2 : ℝ) *
                (((quotientLength X Y b : ℕ) : ℝ) /
                    ((Nat.totient modulus : ℝ) *
                      Real.log (classIVRootCutoff Z (r + 1) : ℝ)) +
                  (classIVRootCutoff Z (r + 1) : ℝ) ^ 2)) ≤
        (classIVSuffixBase k : ℝ) ^ r *
          ShiuClassIBound.classISelbergConstant *
            (((((2 * Y : ℕ) : ℝ) /
                ((Nat.totient modulus : ℝ) * Real.log 2)) + (Z : ℝ) ^ 2) *
              classIVHarmonicPrefix k X Y modulus residue Z cutoff r) := by
          gcongr
      _ ≤ (classIVSuffixBase k : ℝ) ^ r *
          ShiuClassIBound.classISelbergConstant *
            (((((2 * Y : ℕ) : ℝ) /
                ((Nat.totient modulus : ℝ) * Real.log 2)) + (Z : ℝ) ^ 2) *
              (ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k *
                Real.exp
                  ((k * k : ℕ) * ShiuLemma4EndpointWeld.omittedPrimeInvSum
                      (classIVRootCutoff Z r) modulus -
                    (1 / 10 : ℝ) * (r : ℝ) * Real.log (r : ℝ)))) := by
          gcongr
  · have hactiveEmpty :
        classIVActivePrefixes X Y modulus residue Z cutoff r = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hactive
    have hbin := classIVBinMass_eq_sum_active_prefixFibers
      k X Y modulus residue Z cutoff r (by omega : 1 ≤ Z)
    have hbin0 : classIVBinMass k X Y modulus residue Z cutoff r = 0 := by
      simpa [hactiveEmpty] using hbin
    rw [hbin0]
    have hphi : (0 : ℝ) < Nat.totient modulus := by
      exact_mod_cast Nat.totient_pos.mpr hmodulus
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hC2 : 0 ≤ ShiuClassIBound.classISelbergConstant :=
      ShiuClassIBound.classISelbergConstant_pos.le
    have hbase : (0 : ℝ) ≤ (classIVSuffixBase k : ℝ) ^ r := by positivity
    have hbracket : 0 ≤ ((((2 * Y : ℕ) : ℝ) /
        ((Nat.totient modulus : ℝ) * Real.log 2)) + (Z : ℝ) ^ 2) := by
      positivity
    norm_num only [Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hbase hC2)
      (mul_nonneg hbracket
        (mul_nonneg
          (ShiuFiniteEulerDistortion.explicitEulerDistortionConstant_pos k).le
          (Real.exp_pos _).le))

end
end ShiuClassIVBound

#print axioms ShiuClassIVBound.summable_classIVSeriesTerm
#print axioms ShiuClassIVBound.exists_uniform_classIVSeries_bound
#print axioms ShiuClassIVBound.classIVMass_eq_sum_bins_prefixes
#print axioms ShiuClassIVBound.classIVPrefixFiber_suffixWeight_le
#print axioms ShiuClassIVBound.classIVHarmonicPrefix_le_oneTenth
#print axioms ShiuClassIVBound.classIVBinMass_cast_le_selbergSum
#print axioms ShiuClassIVBound.classIVBinMass_cast_le_oneTenth
