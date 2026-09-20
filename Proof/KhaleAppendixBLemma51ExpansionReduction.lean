import KhaleAppendixBFirstPartAnalyticReduction
import KhaleAppendixBLemma51KernelCertified
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Exact Euler/Fourier reduction of Khale Lemma 5.1

This file reduces the specialized logarithmic-integral estimate to the two
literal identities used in the published proof:

* the absolutely convergent Euler-product expansion after integrating the
  `cosh^{-2}` kernel term by term;
* the corresponding prime-power expansion of `log zeta(1+eta)`.

The order and sign comparison after those identities is certified here.  Thus
neither remaining source statement is a reformulation of the desired
inequality.
-/

namespace MAPKhaleAppendixBLemma51ExpansionReduction

open MAPKhaleAppendixB1ZetaReduction
open MAPKhaleAppendixBFirstPartAnalyticReduction
open MAPKhaleAppendixBLemma51KernelCertified

noncomputable section

/-- A prime together with a positive exponent, represented as `m+1`. -/
abbrev PrimePowerIndex := Nat.Primes × ℕ

def ppExponent (k : PrimePowerIndex) : ℕ := k.2 + 1

/-- The positive prime-power term in `log zeta(1+eta)`. -/
def appendixBZetaPrimePowerTerm (eta : ℝ) (k : PrimePowerIndex) : ℝ :=
  Real.rpow (k.1 : ℝ)
      (-((ppExponent k : ℝ) * (1 + eta))) / (ppExponent k : ℝ)

/-- The character-weighted prime-power coefficient before the Fourier kernel. -/
def appendixBCharacterPrimePowerWeight {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma eta : ℝ)
    (k : PrimePowerIndex) : ℝ :=
  Real.rpow (k.1 : ℝ)
      (-((ppExponent k : ℝ) * (sigma + eta))) *
    ‖chi k.1‖ ^ ppExponent k / (ppExponent k : ℝ)

/-- The phase left after extracting the character norm.  Its exact convention
is immaterial to the comparison, but this is the convention obtained from
`p^{-m(s+i t)} chi(p)^m`. -/
def appendixBPrimePowerPhase {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (gamma : ℝ)
    (k : PrimePowerIndex) : ℝ :=
  (ppExponent k : ℝ) *
    (gamma * Real.log (k.1 : ℝ) - Complex.arg (chi k.1))

/-- The integrated prime-power term in Khale Lemma 5.1. -/
def appendixBLemma51PrimePowerTerm {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma eta gamma : ℝ)
    (k : PrimePowerIndex) : ℝ :=
  appendixBCharacterPrimePowerWeight chi sigma eta k *
    coshSqFourier
      (2 * eta * (ppExponent k : ℝ) * Real.log (k.1 : ℝ) / Real.pi) *
    (17.145 * Real.cos (appendixBPrimePowerPhase chi gamma k) +
      10.6825 * Real.cos (2 * appendixBPrimePowerPhase chi gamma k) +
      4.5 * Real.cos (3 * appendixBPrimePowerPhase chi gamma k) +
      Real.cos (4 * appendixBPrimePowerPhase chi gamma k))

/-- Literal output of the Euler-product expansion and Tonelli/Fubini step in
Khale Lemma 5.1.  The first conjunct records absolute convergence; the second
is the exact identity, not the desired lower bound. -/
abbrev AppendixBLemma51EulerFourierExpansion : Prop :=
  ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (sigma eta gamma : ℝ),
    1 ≤ sigma → 0 < eta →
    Summable (appendixBLemma51PrimePowerTerm chi sigma eta gamma) ∧
    appendixBIntegralCombination chi sigma eta gamma =
      ∑' k : PrimePowerIndex,
        appendixBLemma51PrimePowerTerm chi sigma eta gamma k

/-- Literal prime-power Euler expansion of `log zeta(1+eta)`. -/
abbrev AppendixBZetaPrimePowerIdentity : Prop :=
  ∀ eta : ℝ, 0 < eta →
    Summable (appendixBZetaPrimePowerTerm eta) ∧
    (∑' k : PrimePowerIndex, appendixBZetaPrimePowerTerm eta k) = zetaLog eta

private theorem ppExponent_pos (k : PrimePowerIndex) : 0 < ppExponent k := by
  simp [ppExponent]

private theorem prime_one_le (k : PrimePowerIndex) : (1 : ℝ) ≤ (k.1 : ℝ) := by
  exact_mod_cast k.1.property.one_le

private theorem character_weight_nonneg {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma eta : ℝ)
    (k : PrimePowerIndex) :
    0 ≤ appendixBCharacterPrimePowerWeight chi sigma eta k := by
  unfold appendixBCharacterPrimePowerWeight
  exact div_nonneg
    (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (pow_nonneg (norm_nonneg _) _))
    (Nat.cast_nonneg _)

private theorem character_weight_le_zeta_term {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {sigma eta : ℝ}
    (hsigma : 1 ≤ sigma) (k : PrimePowerIndex) :
    appendixBCharacterPrimePowerWeight chi sigma eta k ≤
      appendixBZetaPrimePowerTerm eta k := by
  have hm : (0 : ℝ) < (ppExponent k : ℝ) := by
    exact_mod_cast ppExponent_pos k
  have hexp :
      -((ppExponent k : ℝ) * (sigma + eta)) ≤
        -((ppExponent k : ℝ) * (1 + eta)) := by
    nlinarith
  have hrpow := Real.rpow_le_rpow_of_exponent_le (prime_one_le k) hexp
  have hchi : ‖chi k.1‖ ≤ 1 := chi.norm_le_one k.1
  have hchipow : ‖chi k.1‖ ^ ppExponent k ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) hchi
  have hrpow0 : 0 ≤ Real.rpow (k.1 : ℝ)
      (-((ppExponent k : ℝ) * (sigma + eta))) :=
    Real.rpow_nonneg (by positivity) _
  have hmul :
      Real.rpow (k.1 : ℝ)
          (-((ppExponent k : ℝ) * (sigma + eta))) *
          ‖chi k.1‖ ^ ppExponent k ≤
        Real.rpow (k.1 : ℝ)
          (-((ppExponent k : ℝ) * (1 + eta))) := by
    calc
      _ ≤ Real.rpow (k.1 : ℝ)
          (-((ppExponent k : ℝ) * (sigma + eta))) * 1 :=
        mul_le_mul_of_nonneg_left hchipow hrpow0
      _ ≤ Real.rpow (k.1 : ℝ)
          (-((ppExponent k : ℝ) * (1 + eta))) := by simpa using hrpow
  unfold appendixBCharacterPrimePowerWeight appendixBZetaPrimePowerTerm
  exact (div_le_div_iff_of_pos_right hm).2 hmul

theorem zeta_prime_power_term_nonneg
    (eta : ℝ) (k : PrimePowerIndex) :
    0 ≤ appendixBZetaPrimePowerTerm eta k := by
  unfold appendixBZetaPrimePowerTerm
  exact div_nonneg (Real.rpow_nonneg (by positivity) _) (Nat.cast_nonneg _)

private theorem prime_power_term_lower {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {sigma eta gamma : ℝ}
    (hsigma : 1 ≤ sigma) (hFourier : CoshSqFourierPosBound)
    (k : PrimePowerIndex) :
    -2 * 10.01055 * appendixBZetaPrimePowerTerm eta k ≤
      appendixBLemma51PrimePowerTerm chi sigma eta gamma k := by
  let w := appendixBCharacterPrimePowerWeight chi sigma eta k
  let U := coshSqFourier
    (2 * eta * (ppExponent k : ℝ) * Real.log (k.1 : ℝ) / Real.pi)
  let theta := appendixBPrimePowerPhase chi gamma k
  have hw0 : 0 ≤ w := character_weight_nonneg chi sigma eta k
  have hwle : w ≤ appendixBZetaPrimePowerTerm eta k :=
    character_weight_le_zeta_term chi hsigma k
  have hU := hFourier
    (2 * eta * (ppExponent k : ℝ) * Real.log (k.1 : ℝ) / Real.pi)
  have hk := weighted_prime_power_kernel_lower
    (w := w) (U := U) (theta := theta) hw0 hU.1 hU.2
  have hneg :
      -2 * 10.01055 * appendixBZetaPrimePowerTerm eta k ≤
        -2 * 10.01055 * w := by
    nlinarith
  exact hneg.trans (by
    simpa only [appendixBLemma51PrimePowerTerm, w, U, theta] using hk)

/-- The exact Euler/Fourier identity, Ford's transform, and the zeta Euler
identity imply Khale's specialized Lemma 5.1. -/
theorem lemma51Specialized_of_expansions_and_ford
    (hEuler : AppendixBLemma51EulerFourierExpansion)
    (hFord : FordCoshSqFourierIdentity)
    (hZeta : AppendixBZetaPrimePowerIdentity) :
    AppendixBLemma51Specialized := by
  intro q _inst chi sigma eta gamma hsigma heta
  have hE := hEuler q chi sigma eta gamma hsigma heta
  have hZ := hZeta eta heta
  have hFourier : CoshSqFourierPosBound :=
    coshSqFourierPosBound_of_identity hFord
  have hLowerSummable : Summable (fun k : PrimePowerIndex =>
      -2 * 10.01055 * appendixBZetaPrimePowerTerm eta k) :=
    hZ.1.mul_left (-2 * 10.01055)
  have hsum := Summable.tsum_le_tsum
    (fun k => prime_power_term_lower chi hsigma hFourier k)
    hLowerSummable hE.1
  rw [hZ.1.tsum_mul_left, ← hE.2, hZ.2] at hsum
  exact hsum

end
end MAPKhaleAppendixBLemma51ExpansionReduction

#print axioms MAPKhaleAppendixBLemma51ExpansionReduction.lemma51Specialized_of_expansions_and_ford
