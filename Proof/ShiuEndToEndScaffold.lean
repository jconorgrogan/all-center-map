import SelbergDenominatorLower
import ShiuSection5Structure
import ShiuSection5ScaleRounding
import ShiuLemma3TauMean
import ShiuLemma1ClassIII
import FiniteEulerDistortion

/-!
# End-to-end contract for the specialized Shiu input

This file is a scaffold rather than a claimed proof of Shiu's Theorem 1. It
fixes concrete interfaces for the four published lemmas and formalizes the
deterministic last step: four separately bounded classes in Shiu's canonical
factorization imply DyadicTauSquareShiuTarget.

The only theorem-valued premise left by the end-to-end entry point is
SpecializedSectionFiveWeld. Its conclusion is not the MAP target: it is a
class-by-class estimate for four explicit disjoint pieces, together with the
canonical prefix/suffix factorization used on pages 166--169 of Shiu (1980).
-/

namespace ShiuEndToEnd

open ArithmeticFunction MixedMellinCert ShiuFoundation ShiuAnalyticLayer
  ShiuUniformContract ShiuSieveSlice
open ShiuSection5Split
open scoped ArithmeticFunction.zeta BigOperators

noncomputable section

/-! ## Lemma 1: exact smooth-number object and Section 5 surface -/

/-- Natural version of Shiu's smooth-number counting function Psi(x,y).
Membership in smoothNumbers (y+1) means that every prime factor is at most y. -/
def smoothCount (x y : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter fun n => n ∈ Nat.smoothNumbers (y + 1)).card

/-- Literal natural cutoff corresponding to log X * log log X. -/
def smoothCutoff (X : ℕ) : ℕ :=
  ⌊Real.log (X : ℝ) * Real.log (Real.log (X : ℝ))⌋₊

/-- Shiu's published Lemma 1, with the eventual quantifier and coefficient
3 retained. -/
def PublishedLemmaOne : Prop :=
  ∃ X₀ : ℕ, 3 ≤ X₀ ∧
    ∀ X : ℕ, X₀ ≤ X →
      (smoothCount X (smoothCutoff X) : ℝ) ≤
        Real.exp
          (3 * Real.log (X : ℝ) /
            Real.sqrt (Real.log (Real.log (X : ℝ))))

/-- Exact weakening of Lemma 1 used in Shiu's class III at alpha=beta=1/3.
A Chebyshev-level Rankin proof can establish this without reproducing the
published coefficient 3. -/
def LemmaOneClassIII : Prop :=
  ∃ Z₀ : ℕ, 3 ≤ Z₀ ∧
    ∀ X Z : ℕ, Z₀ ≤ Z → Z ≤ X → X < Z ^ 90 →
      smoothCount Z (smoothCutoff X) ^ 4 ≤ Z

/-- The promoted Rankin/Chebyshev proof inhabits the exact class-III
contract. -/
theorem certifiedLemmaOneClassIII : LemmaOneClassIII := by
  obtain ⟨Z₀, hZ₀, hbound⟩ :=
    ShiuLemma1ClassIII.exists_classIII_smoothCount_pow_four
  refine ⟨max Z₀ 3, by omega, ?_⟩
  intro X Z hZ hZX hXZ
  have hZ₀Z : Z₀ ≤ Z := (le_max_left Z₀ 3).trans hZ
  simpa [smoothCount, smoothCutoff,
    ShiuLemma1Rankin.smoothCount,
    ShiuLemma1ClassIII.classIIICutoff] using
      hbound X Z hZ₀Z hZX hXZ

/-! ## Lemma 3: exact harmonic mean surface -/

/-- Literal harmonic coprime sum occurring in Shiu's Lemma 3, specialized
to tau_k squared. -/
def tauSquareCoprimeHarmonicSum (k X modulus : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X,
    if n.Coprime modulus then (tauAF k n ^ 2 : ℝ) / (n : ℝ) else 0

/-- Exact specialized endpoint targeted by the Lemma-3 proof.
The constant exp(4*k^2) is explicit and uniform in X and the modulus. -/
def LemmaThreeTauSquare : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∀ X modulus : ℕ,
      tauSquareCoprimeHarmonicSum k X modulus ≤
        Real.exp (4 * (k * k : ℕ)) *
          Real.exp
            (omittedPrimeSum ((tauAF k).pmul (tauAF k)) X modulus)

/-- The promoted Lemma-3 artifact inhabits the exact harmonic contract. -/
theorem certifiedLemmaThreeTauSquare : LemmaThreeTauSquare := by
  intro k hk X modulus
  simpa [tauSquareCoprimeHarmonicSum,
    ShiuLemma3TauMean.tauSquareCoprimeHarmonicSum] using
      ShiuLemma3TauMean.tauSquare_coprime_harmonic_mean k hk X modulus

/-! ## Exact modulus/totient cancellation

Shiu's class bounds contain `modulus / phi(modulus)` from the sieve and an
Euler product omitting primes dividing the modulus from Lemma 3.  Treating the
ratio crudely would add a logarithmic loss and fail to preserve the literal
`k^2` exponent when `k = 1`.  The next lemmas prove the source cancellation
prime by prime. -/

/-- Reciprocal Mertens Euler factor. -/
def eulerInvFactor (p : ℕ) : ℝ := 1 / (1 - 1 / (p : ℝ))

theorem one_le_eulerInvFactor {p : ℕ} (hp : p.Prime) :
    1 ≤ eulerInvFactor p := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hdenpos : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hpR
    linarith
  dsimp [eulerInvFactor]
  rw [one_div]
  exact (one_le_inv₀ hdenpos).2 (by
    have : 0 ≤ 1 / (p : ℝ) := by positivity
    linarith)

/-- When the progression modulus is at most the Euler cutoff, all its prime
divisors occur in the ambient finite prime product. -/
theorem modulusPrimeFactors_eq_filter_primesBelow
    {x modulus : ℕ} (hmodulus : 0 < modulus) (hmodx : modulus ≤ x) :
    modulus.primeFactors =
      (x + 1).primesBelow.filter (fun p ↦ p ∣ modulus) := by
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_filter, Nat.mem_primesBelow]
  constructor
  · rintro ⟨hp, hpdvd, _⟩
    have hple : p ≤ modulus := Nat.le_of_dvd hmodulus hpdvd
    exact ⟨⟨by omega, hp⟩, hpdvd⟩
  · rintro ⟨⟨_, hp⟩, hpdvd⟩
    exact ⟨hp, hpdvd, hmodulus.ne'⟩

/-- The legal Shiu range forces the progression modulus below the ambient
Euler cutoff `X`; this discharges the side condition needed for exact
modulus/totient cancellation. -/
theorem modulus_le_ambient_of_shiuRange
    {X Y modulus : ℕ} (hX : 2 ≤ X) (hYX : Y ≤ X)
    (hqY : modulus ^ 3 < Y ^ 2) :
    modulus ≤ X := by
  by_contra hnot
  have hqX : X < modulus := Nat.lt_of_not_ge hnot
  have hXpos : 0 < X := by omega
  have hqpos : 0 < modulus := by omega
  have hYsq : Y ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hYX 2
  have hXsq_lt_qcube : X ^ 2 < modulus ^ 3 := by
    calc
      X ^ 2 < modulus ^ 2 :=
        Nat.pow_lt_pow_left hqX (by norm_num)
      _ ≤ modulus ^ 3 := by
        have : 1 ≤ modulus := by omega
        nlinarith
  omega

/-- Exact reciprocal of the standard Euler product for `phi(q)/q`. -/
theorem modulus_div_totient_eq_eulerInvProduct
    {modulus : ℕ} (hmodulus : 0 < modulus) :
    (modulus : ℝ) / (Nat.totient modulus : ℝ) =
      ∏ p ∈ modulus.primeFactors, eulerInvFactor p := by
  have hphi :=
    ShiuSelbergDenominatorLower.totient_div_eq_eulerProduct hmodulus
  have hmodR : (modulus : ℝ) ≠ 0 := by exact_mod_cast hmodulus.ne'
  have hphiR : (Nat.totient modulus : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hmodulus).ne'
  calc
    (modulus : ℝ) / (Nat.totient modulus : ℝ) =
        ((Nat.totient modulus : ℝ) / (modulus : ℝ))⁻¹ := by
      field_simp
    _ = (∏ p ∈ modulus.primeFactors,
        (1 - 1 / (p : ℝ)))⁻¹ := by rw [hphi]
    _ = ∏ p ∈ modulus.primeFactors, eulerInvFactor p := by
      rw [← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      simp [eulerInvFactor]

/-- Enlarging the finite prime cutoff only adds Euler factors at least one. -/
theorem omittedEulerProduct_mono_cutoff
    (k modulus : ℕ) {z x : ℕ} (hzx : z ≤ x) :
    (∏ p ∈ (z + 1).primesBelow,
        (if p ∣ modulus then 1 else
          eulerInvFactor p ^ (k * k))) ≤
      ∏ p ∈ (x + 1).primesBelow,
        (if p ∣ modulus then 1 else
          eulerInvFactor p ^ (k * k)) := by
  have hsubset : (z + 1).primesBelow ⊆ (x + 1).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨by omega, hp.2⟩
  apply Finset.prod_le_prod_of_subset_of_one_le hsubset
  · intro p hp
    by_cases hpd : p ∣ modulus
    · simp [hpd]
    · simp only [hpd, if_false]
      exact pow_nonneg
        ((one_le_eulerInvFactor
          (Nat.prime_of_mem_primesBelow hp)).trans' (by norm_num)) _
  · intro p hp hpn
    by_cases hpd : p ∣ modulus
    · simp [hpd]
    · simp only [hpd, if_false]
      exact one_le_pow₀
        (one_le_eulerInvFactor (Nat.prime_of_mem_primesBelow hp))

/-- Exact prime-by-prime cancellation: the sieve factor `q/phi(q)` fills the
Euler factors omitted at primes dividing `q`, and `k^2 ≥ 1` absorbs their
coefficient without increasing the full logarithmic exponent. -/
theorem modulusTotient_omittedEulerProduct_le_fullEulerProduct
    (k x modulus : ℕ) (hk : 1 ≤ k) (hmodulus : 0 < modulus)
    (hmodx : modulus ≤ x) :
    ((modulus : ℝ) / (Nat.totient modulus : ℝ)) *
        (∏ p ∈ (x + 1).primesBelow,
          (if p ∣ modulus then 1 else
            eulerInvFactor p ^ (k * k))) ≤
      ∏ p ∈ (x + 1).primesBelow,
        eulerInvFactor p ^ (k * k) := by
  let S := (x + 1).primesBelow
  let T := S.filter (fun p ↦ p ∣ modulus)
  have hT : modulus.primeFactors = T := by
    simpa [S, T] using
      modulusPrimeFactors_eq_filter_primesBelow hmodulus hmodx
  rw [modulus_div_totient_eq_eulerInvProduct hmodulus, hT]
  have hr : 1 ≤ k * k := by nlinarith
  have hsmall :
      (∏ p ∈ T, eulerInvFactor p) ≤
        ∏ p ∈ T, eulerInvFactor p ^ (k * k) := by
    apply Finset.prod_le_prod
    · intro p hp
      have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
      exact (one_le_eulerInvFactor
        (Nat.prime_of_mem_primesBelow (by simpa [S] using hpS))).trans'
          (by norm_num)
    · intro p hp
      have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
      simpa using (pow_le_pow_right₀
        (one_le_eulerInvFactor
          (Nat.prime_of_mem_primesBelow (by simpa [S] using hpS))) hr)
  have homit :
      (∏ p ∈ S,
        (if p ∣ modulus then 1 else
          eulerInvFactor p ^ (k * k))) =
        ∏ p ∈ S.filter (fun p ↦ ¬ p ∣ modulus),
          eulerInvFactor p ^ (k * k) := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p hp
    by_cases hpd : p ∣ modulus <;> simp [hpd]
  rw [show (x + 1).primesBelow = S by rfl, homit]
  calc
    (∏ p ∈ T, eulerInvFactor p) *
        ∏ p ∈ S.filter (fun p ↦ ¬p ∣ modulus),
          eulerInvFactor p ^ (k * k) ≤
      (∏ p ∈ T, eulerInvFactor p ^ (k * k)) *
        ∏ p ∈ S.filter (fun p ↦ ¬p ∣ modulus),
          eulerInvFactor p ^ (k * k) := by
      apply mul_le_mul_of_nonneg_right hsmall
      apply Finset.prod_nonneg
      intro p hp
      have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
      exact pow_nonneg
        ((one_le_eulerInvFactor
          (Nat.prime_of_mem_primesBelow (by simpa [S] using hpS))).trans'
            (by norm_num)) _
    _ = ∏ p ∈ S, eulerInvFactor p ^ (k * k) := by
      simpa [T] using Finset.prod_filter_mul_prod_filter_not S
        (fun p ↦ p ∣ modulus)
        (fun p ↦ eulerInvFactor p ^ (k * k))

/-- The cancellation followed by the already-certified full finite Euler
product estimate.  This is the no-extra-log-loss surface used in (5.3) and
(5.8). -/
theorem modulusTotient_omittedEulerProduct_le_fullPrimeExponential
    (k x modulus : ℕ) (hk : 1 ≤ k) (hmodulus : 0 < modulus)
    (hmodx : modulus ≤ x) :
    ((modulus : ℝ) / (Nat.totient modulus : ℝ)) *
        (∏ p ∈ (x + 1).primesBelow,
          (if p ∣ modulus then 1 else
            eulerInvFactor p ^ (k * k))) ≤
      Real.exp (4 * (k * k : ℕ)) *
        Real.exp
          (omittedPrimeSum ((tauAF k).pmul (tauAF k)) x 1) := by
  refine (modulusTotient_omittedEulerProduct_le_fullEulerProduct
    k x modulus hk hmodulus hmodx).trans ?_
  have hfull :
      (∏ p ∈ (x + 1).primesBelow,
        eulerInvFactor p ^ (k * k)) =
      ∏ p ∈ (x + 1).primesBelow,
        (if p ∣ 1 then 1 else
          1 / (1 - (p : ℝ)⁻¹) ^ (k * k)) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hprime := Nat.prime_of_mem_primesBelow hp
    simp [eulerInvFactor, one_div, inv_pow, hprime.ne_one]
  rw [hfull]
  exact ShiuLemma3TauMean.localEulerProduct_le_exp_omittedPrimeSum k x 1 hk

/-- Explicit Mertens endpoint of the exact cancellation.  The exponent remains
exactly `k^2`, including `k = 1`. -/
theorem modulusTotient_omittedEulerProduct_le_logPow
    (k x modulus : ℕ) (hk : 1 ≤ k) (hx : 3 ≤ x)
    (hmodulus : 0 < modulus) (hmodx : modulus ≤ x) :
    ((modulus : ℝ) / (Nat.totient modulus : ℝ)) *
        (∏ p ∈ (x + 1).primesBelow,
          (if p ∣ modulus then 1 else
            eulerInvFactor p ^ (k * k))) ≤
      Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4)) *
        (Real.log (x : ℝ)) ^ (k * k) := by
  calc
    ((modulus : ℝ) / (Nat.totient modulus : ℝ)) *
        (∏ p ∈ (x + 1).primesBelow,
          (if p ∣ modulus then 1 else
            eulerInvFactor p ^ (k * k))) ≤
      Real.exp (4 * (k * k : ℕ)) *
        Real.exp
          (omittedPrimeSum ((tauAF k).pmul (tauAF k)) x 1) :=
      modulusTotient_omittedEulerProduct_le_fullPrimeExponential
        k x modulus hk hmodulus hmodx
    _ ≤ Real.exp (4 * (k * k : ℕ)) *
        (Real.exp ((k ^ 2 : ℕ) * (1 + 2 * Real.log 4)) *
          (Real.log (x : ℝ)) ^ (k ^ 2)) := by
      gcongr
      exact ShiuUniformContract.exp_omittedPrimeSum_tauAFSquare_le_explicit
        k x 1 hx
    _ = Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4)) *
        (Real.log (x : ℝ)) ^ (k * k) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      · norm_num [pow_two]
        ring
      · norm_num [pow_two]

/-! ## Lemma 4: exact finite tail used by Section 5 -/

/-- Finite portion of Shiu's Lemma-4 sum used in class IV. The published
sum is infinite; restricting it to n <= Z is the literal subset in Section 5.
Y is the integer r-th-root cutoff. -/
def tauSquareSmoothTail
    (k Z Y modulus : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Z,
    if ((Z : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ)) ∧
        n ∈ Nat.smoothNumbers (Y + 1) ∧ n.Coprime modulus
    then (tauAF k n ^ 2 : ℝ) / (n : ℝ)
    else 0

theorem tauSquareSmoothTail_eq_promoted
    (k Z Y modulus : ℕ) :
    tauSquareSmoothTail k Z Y modulus =
      ShiuLemma4TauTail.tauSquareSmoothTail k Z Y modulus := by
  classical
  rw [ShiuLemma4TauTail.tauSquareSmoothTail_eq_filterSum]
  unfold tauSquareSmoothTail
  rw [Finset.sum_filter]

/-- One term of the literal infinite harmonic tail in published Lemma 4. -/
def tauSquareInfiniteTailTerm
    (k Z Y modulus n : ℕ) : ℝ :=
  if ((Z : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ)) ∧
      n ∈ Nat.smoothNumbers (Y + 1) ∧ n.Coprime modulus
  then (tauAF k n ^ 2 : ℝ) / (n : ℝ)
  else 0

/-- Published Lemma 4, specialized to tau_k squared.  The root cutoff is
kept as the explicit integer Y together with Y <= Z^(1/r); Section 5 chooses
the floor of that real root.  Summability is included because it is part of
the content needed to compare the infinite source sum to its finite subset. -/
def PublishedLemmaFourTauSquare : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 < Z₀ ∧
      ∀ Z Y modulus : ℕ, ∀ r : ℝ,
        Z₀ ≤ (Z : ℝ) →
        2 ≤ Y →
        1 ≤ r →
        r * Real.log r ≤ Real.log (Z : ℝ) →
        (Y : ℝ) ≤ (Z : ℝ) ^ r⁻¹ →
        Summable (tauSquareInfiniteTailTerm k Z Y modulus) ∧
        (∑' n : ℕ, tauSquareInfiniteTailTerm k Z Y modulus n) ≤
          C * Real.exp
            (omittedPrimeSum ((tauAF k).pmul (tauAF k)) Y modulus -
              (1 / 10 : ℝ) * r * Real.log r)

/-- Specialized finite consequence of Lemma 4 used by Section 5. -/
def LemmaFourTauSquare : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 < Z₀ ∧
      ∀ Z Y modulus : ℕ, ∀ r : ℝ,
        Z₀ ≤ (Z : ℝ) →
        2 ≤ Y →
        1 ≤ r →
        r * Real.log r ≤ Real.log (Z : ℝ) →
        (Y : ℝ) ≤ (Z : ℝ) ^ r⁻¹ →
        tauSquareSmoothTail k Z Y modulus ≤
          C * Real.exp
            (omittedPrimeSum ((tauAF k).pmul (tauAF k)) Y modulus -
              (1 / 10 : ℝ) * r * Real.log r)

/-- Restricting the published infinite Lemma-4 sum to the finite Section-5
subrange is a fully deterministic implication. -/
theorem lemmaFourTauSquare_of_published
    (hFour : PublishedLemmaFourTauSquare) :
    LemmaFourTauSquare := by
  intro k hk
  obtain ⟨C, Z₀, hC, hZ₀, hbound⟩ := hFour k hk
  refine ⟨C, Z₀, hC, hZ₀, ?_⟩
  intro Z Y modulus r hZ hY hr hrange hroot
  obtain ⟨hsum, htail⟩ := hbound Z Y modulus r hZ hY hr hrange hroot
  have hfinite :
      tauSquareSmoothTail k Z Y modulus ≤
        ∑' n : ℕ, tauSquareInfiniteTailTerm k Z Y modulus n := by
    unfold tauSquareSmoothTail
    have hle := hsum.sum_le_tsum (Finset.Icc 1 Z) (fun n hn => by
      unfold tauSquareInfiniteTailTerm
      split <;> positivity)
    simpa [tauSquareInfiniteTailTerm] using hle
  exact hfinite.trans htail

/-- The promoted finite Euler-distortion proof closes the specialized Lemma 4
with no analytic premise. -/
theorem certifiedLemmaFourTauSquare : LemmaFourTauSquare := by
  intro k hk
  let C := ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k
  refine ⟨C, 3, ShiuFiniteEulerDistortion.explicitEulerDistortionConstant_pos k,
    by norm_num, ?_⟩
  intro Z Y modulus r hZ hY hr hrange hroot
  have hZ3 : 3 ≤ Z := by exact_mod_cast hZ
  have htail :=
    ShiuFiniteEulerDistortion.tauSquareSmoothTail_le_oneTenth
      k Z Y modulus r hk hZ3 hr hrange hY hroot
  rw [tauSquareSmoothTail_eq_promoted]
  simpa [C,
    ShiuLemma4EndpointWeld.omittedPrimeInvSum,
    ShiuLemma3TauMean.omittedPrimeSum_tauSquare_eq,
    ShiuLemma3TauMean.omittedPrimeReciprocalSum] using htail

/-- The promoted finite Rankin proof plus the exact `-1/8 + 1/40 = -1/10`
weld reduce Lemma 4 to the single finite Euler-distortion target isolated by
the Lemma-4 development. -/
theorem certifiedLemmaFourTauSquare_of_eulerDistortion
    (hDist : ShiuLemma4TauTail.TauEulerDistortionTarget) :
    LemmaFourTauSquare := by
  intro k hk
  obtain ⟨C, Z₀, hC, hZ₀, hdist⟩ := hDist k hk
  refine ⟨C, max Z₀ 3, hC, ?_, ?_⟩
  · exact hZ₀.trans_le (le_max_left Z₀ 3)
  intro Z Y modulus r hZ hY hr hrange hroot
  have hZ₀Z : Z₀ ≤ (Z : ℝ) :=
    (le_max_left Z₀ 3).trans hZ
  have hZ3R : (3 : ℝ) ≤ (Z : ℝ) :=
    (le_max_right Z₀ 3).trans hZ
  have hZ3 : 3 ≤ Z := by exact_mod_cast hZ3R
  have hdist' := hdist (Z : ℝ) r Y modulus hZ₀Z hr hrange hroot
  have htail :=
    ShiuLemma4EndpointWeld.tauSquareSmoothTail_le_oneTenth_of_eulerDistortion
      k Z Y modulus r C hk hZ3 hr hrange hC.le hdist'
  rw [tauSquareSmoothTail_eq_promoted]
  simpa [
    ShiuLemma4EndpointWeld.omittedPrimeInvSum,
    ShiuLemma3TauMean.omittedPrimeSum_tauSquare_eq,
    ShiuLemma3TauMean.omittedPrimeReciprocalSum] using htail

/-! ## Class-IV finite-series absorption -/

/-- The literal `r A^r exp(-(1/10) r log r)` factor left after applying
Lemma 4 in Shiu's equation (5.8). -/
def classIVSeriesTerm (A : ℝ) (r : ℕ) : ℝ :=
  (r : ℝ) * A ^ r *
    Real.exp (-(1 / 10 : ℝ) * (r : ℝ) * Real.log (r : ℝ))

/-- The class-IV `r`-series is summable for every fixed positive source
constant `A`; the proof compares its tail with `r exp(-2r)`. -/
theorem classIVSeriesTerm_summable (A : ℝ) (hA : 0 < A) :
    Summable (classIVSeriesTerm A) := by
  have hlog : Filter.Tendsto (fun r : ℕ ↦ Real.log (r : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ r : ℕ in Filter.atTop,
      10 * (max 0 (Real.log A) + 2) ≤ Real.log (r : ℝ) :=
    hlog.eventually_ge_atTop _
  apply Summable.of_norm_bounded_eventually_nat
    (Real.summable_pow_mul_exp_neg_nat_mul 1
      (by norm_num : (0 : ℝ) < 2))
  filter_upwards [hevent] with r hr
  have hrR : (0 : ℝ) ≤ r := by positivity
  have hexp :
      (r : ℝ) * Real.log A -
          (1 / 10 : ℝ) * (r : ℝ) * Real.log (r : ℝ) ≤
        -2 * (r : ℝ) := by
    have : Real.log A + 2 ≤
        (1 / 10 : ℝ) * Real.log (r : ℝ) := by
      nlinarith [le_max_right 0 (Real.log A)]
    nlinarith
  have hterm_nonneg : 0 ≤ classIVSeriesTerm A r := by
    unfold classIVSeriesTerm
    positivity
  rw [Real.norm_of_nonneg hterm_nonneg]
  have hApow : A ^ r = Real.exp ((r : ℝ) * Real.log A) := by
    rw [Real.exp_nat_mul, Real.exp_log hA]
  unfold classIVSeriesTerm
  rw [hApow]
  have hexple := Real.exp_le_exp.mpr hexp
  have hexple' :
      Real.exp ((r : ℝ) * Real.log A +
        (-(1 / 10 : ℝ) * (r : ℝ) * Real.log (r : ℝ))) ≤
        Real.exp (-2 * (r : ℝ)) := by
    simpa [sub_eq_add_neg] using hexple
  calc
    (r : ℝ) * Real.exp ((r : ℝ) * Real.log A) *
        Real.exp (-(1 / 10 : ℝ) * (r : ℝ) * Real.log (r : ℝ)) =
      (r : ℝ) * (Real.exp ((r : ℝ) * Real.log A) *
        Real.exp (-(1 / 10 : ℝ) * (r : ℝ) * Real.log (r : ℝ))) := by ring
    _ = (r : ℝ) * Real.exp ((r : ℝ) * Real.log A +
        (-(1 / 10 : ℝ) * (r : ℝ) * Real.log (r : ℝ))) := by
      rw [Real.exp_add]
    _ ≤ (r : ℝ) * Real.exp (-2 * (r : ℝ)) :=
      mul_le_mul_of_nonneg_left hexple' hrR
    _ = (r : ℝ) ^ 1 * Real.exp (-2 * (r : ℝ)) := by ring

/-- Uniform bound for every finite partial class-IV `r`-sum. -/
theorem classIVFiniteSeries_bounded (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ,
      (∑ r ∈ Finset.Icc 2 R, classIVSeriesTerm A r) ≤ C := by
  have hsum := classIVSeriesTerm_summable A hA
  have hnonneg : ∀ r : ℕ, 0 ≤ classIVSeriesTerm A r := by
    intro r
    unfold classIVSeriesTerm
    positivity
  let C := (∑' r : ℕ, classIVSeriesTerm A r) + 1
  have htsum0 : 0 ≤ ∑' r : ℕ, classIVSeriesTerm A r :=
    tsum_nonneg hnonneg
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro R
  calc
    (∑ r ∈ Finset.Icc 2 R, classIVSeriesTerm A r) ≤
        ∑' r : ℕ, classIVSeriesTerm A r :=
      hsum.sum_le_tsum (Finset.Icc 2 R) (fun r hr ↦ hnonneg r)
    _ ≤ C := by dsimp [C]; linarith

/-! ## The exact promoted prefix/suffix split and four classes -/

/-- Natural mass of one of the four exact classes from
ShiuSection5Split.  That module constructs b_n and d_n from the ordered full
prime-power blocks and uses the source-correct least prime factor q(d_n). -/
def classMass (k X Y modulus residue Z cutoff : ℕ)
    (c : FourClass) : ℕ :=
  ∑ n ∈ classSet c X Y modulus residue Z cutoff, tauAF k n ^ 2

/-- Membership in any exact class preserves coprimality with the progression
modulus when the residue is primitive. -/
theorem classMember_coprime_modulus
    {c : FourClass} {X Y modulus residue Z cutoff n : ℕ}
    (hres : residue.Coprime modulus)
    (hn : n ∈ classSet c X Y modulus residue Z cutoff) :
    n.Coprime modulus := by
  have hwin := (mem_classSet_iff.mp hn).1
  have hmodeq : n ≡ residue [MOD modulus] :=
    (Finset.mem_filter.mp hwin).2
  rw [Nat.coprime_iff_gcd_eq_one, hmodeq.gcd_eq]
  exact hres.gcd_eq_one

/-- The canonical prefix is primitive modulo the progression modulus. -/
theorem canonicalB_coprime_modulus_of_classMember
    {c : FourClass} {X Y modulus residue Z cutoff n : ℕ}
    (hZ : 1 ≤ Z) (hres : residue.Coprime modulus)
    (hn : n ∈ classSet c X Y modulus residue Z cutoff) :
    (canonicalB n Z).Coprime modulus := by
  have hwin := (mem_classSet_iff.mp hn).1
  have hnIoc : n ∈ Finset.Ioc (X - Y) X :=
    (Finset.mem_filter.mp hwin).1
  have hn0 : n ≠ 0 := by
    have : X - Y < n := (Finset.mem_Ioc.mp hnIoc).1
    omega
  exact Nat.Coprime.of_dvd_left (canonicalB_dvd hn0 hZ)
    (classMember_coprime_modulus hres hn)

/-- The canonical suffix is primitive modulo the progression modulus. -/
theorem canonicalD_coprime_modulus_of_classMember
    {c : FourClass} {X Y modulus residue Z cutoff n : ℕ}
    (hZ : 1 ≤ Z) (hres : residue.Coprime modulus)
    (hn : n ∈ classSet c X Y modulus residue Z cutoff) :
    (canonicalD n Z).Coprime modulus := by
  have hwin := (mem_classSet_iff.mp hn).1
  have hnIoc : n ∈ Finset.Ioc (X - Y) X :=
    (Finset.mem_filter.mp hwin).1
  have hn0 : n ≠ 0 := by
    have : X - Y < n := (Finset.mem_Ioc.mp hnIoc).1
    omega
  have hDdvd : canonicalD n Z ∣ n := by
    refine ⟨canonicalB n Z, ?_⟩
    rw [mul_comm, canonicalB_mul_canonicalD hn0 hZ]
  exact Nat.Coprime.of_dvd_left hDdvd
    (classMember_coprime_modulus hres hn)

/-- The literal class mass can be reindexed with Shiu's exact multiplicative
prefix/suffix weight.  This is the structural bridge used before applying the
sieve to `d_n` and the harmonic estimate to `b_n`; it is not implicit source
reasoning. -/
theorem classMass_eq_factorizedMass
    (k X Y modulus residue Z cutoff : ℕ) (c : FourClass)
    (hZ : 1 ≤ Z) :
    classMass k X Y modulus residue Z cutoff c =
      ∑ n ∈ classSet c X Y modulus residue Z cutoff,
        tauAF k (canonicalB n Z) ^ 2 *
          tauAF k (canonicalD n Z) ^ 2 := by
  classical
  unfold classMass
  apply Finset.sum_congr rfl
  intro n hn
  have hwin := (mem_classSet_iff.mp hn).1
  have hnIoc : n ∈ Finset.Ioc (X - Y) X :=
    (Finset.mem_filter.mp hwin).1
  have hn0 : n ≠ 0 := by
    have : X - Y < n := (Finset.mem_Ioc.mp hnIoc).1
    omega
  exact ShiuSection5Structure.tauSquare_canonical_factorization k hn0 hZ

/-- Progression sum rewritten as the exact progression window. -/
theorem progressionSum_eq_progressionWindow
    (k X Y modulus residue : ℕ) :
    progressionSum ((tauAF k).pmul (tauAF k)) X Y modulus residue =
      ∑ n ∈ progressionWindow X Y modulus residue, tauAF k n ^ 2 := by
  classical
  unfold progressionSum progressionWindow
  simp only [Finset.sum_filter, ArithmeticFunction.pmul_apply, pow_two]

/-- Exact finite identity supplied by the promoted canonical split. -/
theorem progressionSum_eq_fourClassMass
    (k X Y modulus residue Z cutoff : ℕ) :
    progressionSum ((tauAF k).pmul (tauAF k)) X Y modulus residue =
      classMass k X Y modulus residue Z cutoff FourClass.I +
      classMass k X Y modulus residue Z cutoff FourClass.II +
      classMass k X Y modulus residue Z cutoff FourClass.III +
      classMass k X Y modulus residue Z cutoff FourClass.IV := by
  rw [progressionSum_eq_progressionWindow]
  simpa [classMass] using
    ShiuSection5Split.sum_four_classes
      (fun n => tauAF k n ^ 2) X Y modulus residue Z cutoff

/-- Robust rounded version of Shiu's choice z=y^(1/30).  Ceiling, rather
than floor, preserves the lower inequality needed for X < z^90. -/
def sectionFiveZ (Y : ℕ) : ℕ :=
  ⌈(Y : ℝ) ^ (1 / 30 : ℝ)⌉₊

/-- The promoted rounded-scale proof supplies exactly the Selberg range used
on every class-I canonical-prefix fiber.  In particular, it does not assume
the false/unneeded inequality `Z < X - Y` when `Y = X`. -/
theorem certifiedClassIScalePackage
    {X Y modulus : ℕ}
    (hX : ShiuClassIBound.sectionFiveScaleThreshold ≤ X)
    (hYX : Y ≤ X) (hXY : X < Y ^ 3)
    (hmodulus : 0 < modulus) (hmodcube : modulus ^ 3 < Y ^ 2) :
    let Z := sectionFiveZ Y
    1 ≤ Z ∧ X < Z ^ 90 ∧
      2 ≤ ShiuClassIBound.classISieveLevel Z ∧
      ∀ b ∈ ShiuClassIBound.classIOuterPrefixes Z modulus,
        modulus < ShiuClassIBound.quotientLength X Y b := by
  simpa [sectionFiveZ, ShiuClassIBound.sectionFiveZ] using
    ShiuClassIBound.sectionFive_classI_scale_package
      hX hYX hXY hmodulus hmodcube

/-- The second promoted rounded-scale package absorbs the class-I Selberg
square error and gives the lower logarithm bound needed for the main term. -/
theorem certifiedClassIFinalAbsorptionPackage
    {X Y modulus : ℕ}
    (hX : ShiuClassIBound.sectionFiveFinalAbsorptionThreshold ≤ X)
    (hXY : X < Y ^ 3) (hmodcube : modulus ^ 3 < Y ^ 2) :
    let Z := sectionFiveZ Y
    Z ≤ Y ∧
      (1 : ℝ) ≤ Real.log (ShiuClassIBound.classISieveLevel Z : ℝ) ∧
      modulus * Z ^ 2 ≤ Y := by
  simpa [sectionFiveZ, ShiuClassIBound.sectionFiveZ] using
    ShiuClassIBound.sectionFive_classI_final_absorption_package
      hX hXY hmodcube

/-- Ceiling preserves the lower scale needed by class III. -/
theorem sectionFiveZ_rpow_le (Y : ℕ) :
    (Y : ℝ) ^ (1 / 30 : ℝ) ≤ (sectionFiveZ Y : ℕ) := by
  exact Nat.le_ceil _

/-- The rounded Section-5 parameter retains the decisive implication
Y^3 <= Z^90.  This is why the definition uses a ceiling. -/
theorem cube_le_sectionFiveZ_pow_ninety (Y : ℕ) :
    Y ^ 3 ≤ sectionFiveZ Y ^ 90 := by
  have hbase := sectionFiveZ_rpow_le Y
  have hpow := Real.rpow_le_rpow
    (Real.rpow_nonneg (Nat.cast_nonneg Y) (1 / 30 : ℝ))
    hbase (show (0 : ℝ) ≤ 90 by norm_num)
  have hleft :
      (((Y : ℝ) ^ (1 / 30 : ℝ)) ^ (90 : ℝ)) = (Y : ℝ) ^ 3 := by
    rw [← Real.rpow_mul (Nat.cast_nonneg Y)]
    have hexp : (1 / 30 : ℝ) * 90 = 3 := by norm_num
    rw [hexp]
    exact Real.rpow_natCast (Y : ℝ) 3
  have hright :
      (((sectionFiveZ Y : ℕ) : ℝ) ^ (90 : ℝ)) =
        ((sectionFiveZ Y ^ 90 : ℕ) : ℝ) := by
    calc
      (((sectionFiveZ Y : ℕ) : ℝ) ^ (90 : ℝ)) =
          (((sectionFiveZ Y : ℕ) : ℝ) ^ (90 : ℕ)) :=
        Real.rpow_natCast _ 90
      _ = ((sectionFiveZ Y ^ 90 : ℕ) : ℝ) := by norm_num
  rw [hleft, hright] at hpow
  exact_mod_cast hpow

/-- Exact natural bridge from the target short-interval hypothesis to the
class-III scale condition. -/
theorem lt_sectionFiveZ_pow_ninety
    {X Y : ℕ} (hXY : X < Y ^ 3) :
    X < sectionFiveZ Y ^ 90 :=
  hXY.trans_le (cube_le_sectionFiveZ_pow_ninety Y)

/-! ## Honest Section-5 boundary -/

/-- Common natural budget used by the three literal Section-5 outputs. -/
def classBudgetBase (k X Y : ℕ) : ℕ :=
  Y * (Nat.log 2 (X + 2) + 1) ^ (k * k)

/-- First unresolved source inequality in the present Section-5 order.
For class I, every prime divisor of the canonical suffix exceeds `sqrt Z`,
while the suffix is at most `X < Z^90`; hence its total prime-power exponent
is below `180` and the fixed divisor-square weight is uniformly bounded.
This proposition records that exact arithmetic conclusion without assuming a
progression estimate. -/
def ClassICanonicalSuffixWeightBound : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ D : ℕ, 0 < D ∧
      ∀ X Y modulus residue Z cutoff n : ℕ,
        1 ≤ Z → X < Z ^ 90 →
        n ∈ classSet FourClass.I X Y modulus residue Z cutoff →
        tauAF k (canonicalD n Z) ^ 2 ≤ D

/-- The promoted class-I prime-factor-length argument inhabits the exact
canonical suffix bound with explicit constant `(k^2)^179`. -/
theorem certifiedClassICanonicalSuffixWeightBound :
    ClassICanonicalSuffixWeightBound := by
  intro k hk
  refine ⟨(k * k) ^ 179, ?_, ?_⟩
  · have hkk : 1 ≤ k * k := Nat.mul_le_mul hk hk
    exact Nat.zero_lt_one.trans_le (one_le_pow₀ hkk)
  intro X Y modulus residue Z cutoff n hZ hXZ hn
  exact ShiuClassIBound.classI_suffix_tauSquare_le k hk hZ hXZ hn

/-- Literal class-I estimate corresponding to equation (5.3), after the
already-certified Lemmas 2 and 3 and elementary parameter absorption. -/
def ClassI53Estimate : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ C X₀ : ℕ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ X Y modulus residue : ℕ,
        X₀ ≤ X → 0 < modulus → residue < modulus →
        residue.Coprime modulus → Y ≤ X → X < Y ^ 3 →
        modulus ^ 3 < Y ^ 2 →
        modulus * classMass k X Y modulus residue
            (sectionFiveZ Y) (smoothCutoff X) FourClass.I ≤
          C * classBudgetBase k X Y

/-- Literal combined class-II/class-III estimate corresponding to (5.6),
after inserting the certified class-III smooth-number bound. -/
def ClassIIIII56Estimate : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ C X₀ : ℕ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ X Y modulus residue : ℕ,
        X₀ ≤ X → 0 < modulus → residue < modulus →
        residue.Coprime modulus → Y ≤ X → X < Y ^ 3 →
        modulus ^ 3 < Y ^ 2 →
        modulus *
            (classMass k X Y modulus residue
                (sectionFiveZ Y) (smoothCutoff X) FourClass.II +
              classMass k X Y modulus residue
                (sectionFiveZ Y) (smoothCutoff X) FourClass.III) ≤
          C * classBudgetBase k X Y

/-- Literal class-IV estimate corresponding to equation (5.8), after the
Lemma-4 negative r log r saving and the finite r-sum absorption. -/
def ClassIV58Estimate : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ C X₀ : ℕ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ X Y modulus residue : ℕ,
        X₀ ≤ X → 0 < modulus → residue < modulus →
        residue.Coprime modulus → Y ≤ X → X < Y ^ 3 →
        modulus ^ 3 < Y ^ 2 →
        modulus * classMass k X Y modulus residue
            (sectionFiveZ Y) (smoothCutoff X) FourClass.IV ≤
          C * classBudgetBase k X Y

/-- The three analytic outputs which actually occur in Shiu Section 5:
class I (equation 5.3), classes II and III together (equation 5.6), and
class IV (equation 5.8).  The exact promoted class sets appear in every
inequality.  Thus this is not a renamed copy of the total progression target.

Constants and sufficiently-large thresholds are allowed to absorb the fixed
numerical factors introduced in the published proof. -/
def SectionFiveClassEstimates : Prop :=
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
        let B := C * Y * (Nat.log 2 (X + 2) + 1) ^ (k * k)
        modulus * classMass k X Y modulus residue Z cutoff FourClass.I ≤ B ∧
          modulus *
              (classMass k X Y modulus residue Z cutoff FourClass.II +
                classMass k X Y modulus residue Z cutoff FourClass.III) ≤
            2 * B ∧
          modulus * classMass k X Y modulus residue Z cutoff FourClass.IV ≤ B

/-- Fully deterministic common-constant/common-threshold absorption of the
three literal source estimates. -/
theorem sectionFiveClassEstimates_of_literalClasses
    (hI : ClassI53Estimate)
    (hIIIII : ClassIIIII56Estimate)
    (hIV : ClassIV58Estimate) :
    SectionFiveClassEstimates := by
  intro k hk
  obtain ⟨CI, XI, hCI, hXI, hIbound⟩ := hI k hk
  obtain ⟨CE, XE, hCE, hXE, hEbound⟩ := hIIIII k hk
  obtain ⟨CV, XV, hCV, hXV, hVbound⟩ := hIV k hk
  let C := max CI (max CE CV)
  let X₀ := max XI (max XE XV)
  have hC : 0 < C := hCI.trans_le (le_max_left CI (max CE CV))
  have hX₀ : 2 ≤ X₀ := hXI.trans (le_max_left XI (max XE XV))
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X Y modulus residue hX hmod hres hcop hYX hXY hqY
  have hXI' : XI ≤ X :=
    (le_max_left XI (max XE XV)).trans (show X₀ ≤ X from hX)
  have hXE' : XE ≤ X :=
    (le_max_of_le_right (le_max_left XE XV)).trans
      (show X₀ ≤ X from hX)
  have hXV' : XV ≤ X :=
    (le_max_of_le_right (le_max_right XE XV)).trans
      (show X₀ ≤ X from hX)
  have hIb := hIbound X Y modulus residue hXI' hmod hres hcop hYX hXY hqY
  have hEb := hEbound X Y modulus residue hXE' hmod hres hcop hYX hXY hqY
  have hVb := hVbound X Y modulus residue hXV' hmod hres hcop hYX hXY hqY
  have hCIle : CI ≤ C := le_max_left _ _
  have hCEle : CE ≤ C := le_max_of_le_right (le_max_left _ _)
  have hCVle : CV ≤ C := le_max_of_le_right (le_max_right _ _)
  have hbase : 0 ≤ classBudgetBase k X Y := Nat.zero_le _
  refine ⟨?_, ?_, ?_⟩
  · calc
      modulus * classMass k X Y modulus residue
          (sectionFiveZ Y) (smoothCutoff X) FourClass.I ≤
          CI * classBudgetBase k X Y := hIb
      _ ≤ C * classBudgetBase k X Y := Nat.mul_le_mul_right _ hCIle
      _ = C * Y * (Nat.log 2 (X + 2) + 1) ^ (k * k) := by
        simp [classBudgetBase, mul_assoc]
  · calc
      modulus *
          (classMass k X Y modulus residue
              (sectionFiveZ Y) (smoothCutoff X) FourClass.II +
            classMass k X Y modulus residue
              (sectionFiveZ Y) (smoothCutoff X) FourClass.III) ≤
          CE * classBudgetBase k X Y := hEb
      _ ≤ C * classBudgetBase k X Y := Nat.mul_le_mul_right _ hCEle
      _ ≤ 2 * (C * classBudgetBase k X Y) := by omega
      _ = 2 * (C * Y * (Nat.log 2 (X + 2) + 1) ^ (k * k)) := by
        simp [classBudgetBase, mul_assoc]
  · calc
      modulus * classMass k X Y modulus residue
          (sectionFiveZ Y) (smoothCutoff X) FourClass.IV ≤
          CV * classBudgetBase k X Y := hVb
      _ ≤ C * classBudgetBase k X Y := Nat.mul_le_mul_right _ hCVle
      _ = C * Y * (Nat.log 2 (X + 2) + 1) ^ (k * k) := by
        simp [classBudgetBase, mul_assoc]

/-! ## Fully proved deterministic final weld -/

/-- The three exact Section-5 outputs imply the natural target, with constant
loss 4. -/
theorem dyadicTauSquareShiuTarget_of_sectionFiveClassEstimates
    (hclasses : SectionFiveClassEstimates) :
    DyadicTauSquareShiuTarget := by
  intro k hk
  obtain ⟨C, X₀, hC, hX₀, hbound⟩ := hclasses k hk
  refine ⟨4 * C, X₀, by omega, hX₀, ?_⟩
  intro X Y modulus residue hX hmod hres hcop hYX hXY hqY
  obtain ⟨hI, hIIIII, hIV⟩ :=
    hbound X Y modulus residue hX hmod hres hcop hYX hXY hqY
  let Z := sectionFiveZ Y
  let cutoff := smoothCutoff X
  let B : ℕ := C * Y * (Nat.log 2 (X + 2) + 1) ^ (k * k)
  have hI' :
      modulus * classMass k X Y modulus residue Z cutoff FourClass.I ≤ B := by
    simpa [Z, cutoff, B] using hI
  have hIIIII' :
      modulus *
          (classMass k X Y modulus residue Z cutoff FourClass.II +
            classMass k X Y modulus residue Z cutoff FourClass.III) ≤ 2 * B := by
    simpa [Z, cutoff, B] using hIIIII
  have hIV' :
      modulus * classMass k X Y modulus residue Z cutoff FourClass.IV ≤ B := by
    simpa [Z, cutoff, B] using hIV
  calc
    modulus *
        progressionSum ((tauAF k).pmul (tauAF k))
          X Y modulus residue =
        modulus * classMass k X Y modulus residue Z cutoff FourClass.I +
        modulus * classMass k X Y modulus residue Z cutoff FourClass.II +
        modulus * classMass k X Y modulus residue Z cutoff FourClass.III +
        modulus * classMass k X Y modulus residue Z cutoff FourClass.IV := by
          rw [progressionSum_eq_fourClassMass]
          ring
    _ = modulus * classMass k X Y modulus residue Z cutoff FourClass.I +
        modulus *
          (classMass k X Y modulus residue Z cutoff FourClass.II +
            classMass k X Y modulus residue Z cutoff FourClass.III) +
        modulus * classMass k X Y modulus residue Z cutoff FourClass.IV := by
          ring
    _ ≤ 4 * B := by omega
    _ = (4 * C) * Y *
        (Nat.log 2 (X + 2) + 1) ^ (k * k) := by
          dsimp [B]
          ring

/-- End-to-end conditional entry point. Lemmas 1--4, canonical
multiplicativity, the exact modulus/totient cancellation, and the finite
class-IV `r`-series are now certified. The remaining premises are precisely
the three source-facing Section-5 class consequences associated with (5.3),
(5.6), and (5.8). -/
theorem dyadicTauSquareShiuTarget_of_specializedShiu
    (hI : ClassI53Estimate)
    (hIIIII : ClassIIIII56Estimate)
    (hIV : ClassIV58Estimate) :
    DyadicTauSquareShiuTarget :=
  dyadicTauSquareShiuTarget_of_sectionFiveClassEstimates
    (sectionFiveClassEstimates_of_literalClasses hI hIIIII hIV)

end

end ShiuEndToEnd

#print axioms ShiuEndToEnd.certifiedLemmaThreeTauSquare
#print axioms ShiuEndToEnd.certifiedLemmaOneClassIII
#print axioms ShiuEndToEnd.certifiedLemmaFourTauSquare
#print axioms ShiuEndToEnd.certifiedClassICanonicalSuffixWeightBound
#print axioms ShiuEndToEnd.certifiedClassIScalePackage
#print axioms ShiuEndToEnd.certifiedClassIFinalAbsorptionPackage
#print axioms ShiuEndToEnd.modulusTotient_omittedEulerProduct_le_logPow
#print axioms ShiuEndToEnd.omittedEulerProduct_mono_cutoff
#print axioms ShiuEndToEnd.classIVFiniteSeries_bounded
#print axioms ShiuEndToEnd.cube_le_sectionFiveZ_pow_ninety
#print axioms ShiuEndToEnd.classMass_eq_factorizedMass
#print axioms ShiuEndToEnd.progressionSum_eq_fourClassMass
#print axioms ShiuEndToEnd.sectionFiveClassEstimates_of_literalClasses
#print axioms ShiuEndToEnd.dyadicTauSquareShiuTarget_of_sectionFiveClassEstimates
#print axioms ShiuEndToEnd.dyadicTauSquareShiuTarget_of_specializedShiu
