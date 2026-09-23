import MRTLemma210DyadicMeanSquare
import MRTProposition61TypeD1FirstInequality
import MRTCorollary25Minkowski
import HarmonicRowGrouping
import Mathlib.Algebra.Order.Chebyshev

/-!
# MRT Lemma 2.11 and Corollary 2.12: corrected source boundary

MRT Lemma 2.10 is now finite and premise-free in
`MRTLemma210DyadicMeanSquare`.  The first genuinely analytic statement in the
published descent is the all-character discrete fourth moment below.  It is
Baker--Harman--Pintz Lemma 9 with the restriction `chi ∉ E_q` removed exactly
as its proof permits, and with the ambient logarithm retained.

At MRT pp. 60--61 the displayed character-summed estimate cited as Lemma 2.8
is the estimate of Lemma 2.10.  Lemma 2.8 is fixed-character and cannot produce
the displayed `(q₁ λ H + N)` scale.
-/

namespace MAPMRTLemma211AllCharacterSource

open scoped BigOperators
open MAPMRTLemma210OrthogonalityReduction
open MAPMRTProposition61TypeD1FirstInequality
open MAPMRTCorollary25Minkowski
open MAPHarmonicRowGrouping

noncomputable section

def prefixSupport (X : ℕ) : Finset ℕ := Finset.Icc 1 X

def criticalPrefixCoefficient (n : ℕ) : ℂ :=
  (Real.sqrt (n : ℝ) : ℂ)⁻¹

def criticalPrefixPolynomial
    (q X : ℕ) (chi : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  twistedFinitePolynomial q (prefixSupport X) criticalPrefixCoefficient chi t

def selectedPrefixFourthMass
    {q : ℕ} (X : ℕ)
    (S : Finset (DirichletCharacter ℂ q × ℝ)) : ℝ :=
  ∑ z ∈ S, ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4

/-- Characterization of the principal character which does not require a
typeclass instance generated from the quantified hypothesis `1 ≤ q`. -/
def IsPrincipalCharacter {q : ℕ} (chi : DirichletCharacter ℂ q) : Prop :=
  ∀ n : ℕ, IsUnit (n : ZMod q) → chi n = 1

def selectedPrincipalDecayMass
    {q : ℕ} (S : Finset (DirichletCharacter ℂ q × ℝ)) : ℝ := by
  classical
  exact ∑ z ∈ S,
    if IsPrincipalCharacter z.1 then 1 / (1 + |z.2|) ^ 4 else 0

def SameCharacterOneSeparated
    {q : ℕ} (S : Finset (DirichletCharacter ℂ q × ℝ)) : Prop :=
  ∀ z ∈ S, ∀ w ∈ S, z ≠ w → z.1 = w.1 → 1 ≤ |z.2 - w.2|

/-- The first exact analytic inequality left after all finite reductions.

The ambient parameter `x0` is explicit because BHP requires
`q,T,X ≤ x0` and proves a power of `log x0`.  At the MRT Proposition 6.1 call
site one has `q,T ≤ X`, so `x0=X` recovers the manuscript's `log X` loss.
The quantification is over every character modulo `q`, including principal,
imprimitive, and the characters in BHP's standing exceptional set `E_q`.
-/
def MRTLemma211AllCharacterFourthMoment : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ,
    ∀ (q X : ℕ) (T x0 : ℝ)
      (S : Finset (DirichletCharacter ℂ q × ℝ)),
      1 ≤ q → 2 ≤ X → 2 ≤ T →
      (q : ℝ) ≤ x0 → (X : ℝ) ≤ x0 → T ≤ x0 →
      (∀ z ∈ S, |z.2| ≤ T) →
      SameCharacterOneSeparated S →
      selectedPrefixFourthMass X S ≤ C *
        ((q : ℝ) * T * Real.log x0 ^ B +
          Real.log x0 ^ 4 * (S.card : ℝ) *
            ((q : ℝ) ^ 2 / T ^ 2 + (X : ℝ) ^ 2 / T ^ 4) +
          (X : ℝ) ^ 2 * selectedPrincipalDecayMass S)

/-- Exact MRT-range specialization of the corrected BHP statement.  This
derivation is deterministic; the only premise is the analytic theorem above. -/
theorem mrtLemma211_of_allCharacterFourthMoment
    (hBHP : MRTLemma211AllCharacterFourthMoment) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ,
      ∀ (q X : ℕ) (T : ℝ)
        (S : Finset (DirichletCharacter ℂ q × ℝ)),
        1 ≤ q → 2 ≤ X → 2 ≤ T →
        (q : ℝ) ≤ X → T ≤ X →
        (∀ z ∈ S, |z.2| ≤ T) →
        SameCharacterOneSeparated S →
        selectedPrefixFourthMass X S ≤ C *
          ((q : ℝ) * T * Real.log X ^ B +
            Real.log X ^ 4 * (S.card : ℝ) *
              ((q : ℝ) ^ 2 / T ^ 2 + (X : ℝ) ^ 2 / T ^ 4) +
            (X : ℝ) ^ 2 * selectedPrincipalDecayMass S) := by
  obtain ⟨C, hC, B, h⟩ := hBHP
  refine ⟨C, hC, B, ?_⟩
  intro q X T S hq hX hT hqX hTX hannulus hsep
  exact h q X T X S hq hX hT hqX (le_refl _) hTX hannulus hsep

/-- Unrestricted all-character version of the deterministic sampled-piece
reduction behind Corollary 2.12.  Clipped pieces retain the annular lower bound;
the construction of the finite cover and the analytic selected-point estimate
are deliberately separate. -/
theorem allCharacterSampledPieces_to_annulus_rhs
    {q : ℕ} [NeZero q]
    {F : DirichletCharacter ℂ q → ℝ → ℝ}
    {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {left right : DirichletCharacter ℂ q × ℝ → ℝ}
    {T N L C A : ℝ} {B : ℕ}
    (hT : 0 < T) (hC : 0 ≤ C)
    (hF : ∀ chi, Continuous (F chi))
    (hlength : ∀ z ∈ S, 0 ≤ right z - left z ∧ right z - left z ≤ 1)
    (hmax : ∀ z ∈ S, ∀ t ∈ Set.Icc (left z) (right z),
      (F z.1 t) ^ 4 ≤ (F z.1 z.2) ^ 4)
    (hannulus : ∀ z ∈ S, T / 2 ≤ |z.2|)
    (hcard : (S.card : ℝ) ≤ A * (q : ℝ) * T)
    (hspacing : ∀ z ∈ S, ∀ w ∈ S, z ≠ w → z.1 = w.1 →
      1 ≤ |z.2 - w.2|)
    (hBHP :
      (∀ z ∈ S, ∀ w ∈ S, z ≠ w → z.1 = w.1 →
        1 ≤ |z.2 - w.2|) →
      bhpSelectedFourthMass F S ≤ C *
        ((q : ℝ) * T * L ^ B +
          L ^ 4 * (S.card : ℝ) *
            ((q : ℝ) ^ 2 / T ^ 2 + N ^ 2 / T ^ 4) +
          N ^ 2 * bhpPrincipalDecayMass S)) :
    bhpSampledPieceMass F S left right ≤ C *
      ((q : ℝ) * T * L ^ B +
        L ^ 4 * (A * (q : ℝ) * T) *
          ((q : ℝ) ^ 2 / T ^ 2 + N ^ 2 / T ^ 4) +
        N ^ 2 * ((A * (q : ℝ) * T) * (16 / T ^ 4))) := by
  have hdisc := bhpSampledPieceMass_le_selectedFourthMass
    hF hlength hmax
  have hanalytic := hBHP hspacing
  have hreduced := bhpLemma9_rhs_annulus_reduction
    hT hC hannulus hcard hanalytic
  exact hdisc.trans hreduced

/-! ## Descent through BHP Lemmas 7--9

The next definitions expose the two analytic inputs actually used in the
proof of BHP Lemma 9.  Equation (3.36), together with the elementary Holder
and one-spacing argument on the following page, reduces the prefix fourth
moment to a continuous all-character fourth moment.  BHP Lemma 7 is exactly
that lower mean-value estimate and cites Ramachandra.

Keeping these two statements separate prevents the citation to BHP Lemma 9
from hiding both Perron's contour shift and the classical mean-value theorem.
-/

/-- The critical-line `L`-norm occurring throughout BHP Lemmas 7--9. -/
def criticalLineLNorm {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  ‖DirichletCharacter.LFunction chi
    (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖

/-- The fourth power of the critical-line `L`-value occurring in BHP Lemma 7. -/
def criticalLineLFourth {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  criticalLineLNorm chi t ^ 4

/-- The literal all-character integral in BHP Lemma 7. -/
def allCharacterCriticalLineFourthIntegral
    (q : ℕ) [NeZero q] (U : ℝ) : ℝ :=
  ∑ chi : DirichletCharacter ℂ q,
    ∫ t in (-U)..U, criticalLineLFourth chi t

theorem allCharacterCriticalLineFourthIntegral_nonneg
    (q : ℕ) [NeZero q] {U : ℝ} (hU : 0 ≤ U) :
    0 ≤ allCharacterCriticalLineFourthIntegral q U := by
  classical
  unfold allCharacterCriticalLineFourthIntegral
  apply Finset.sum_nonneg
  intro chi _hchi
  apply intervalIntegral.integral_nonneg
  · linarith
  · intro t _ht
    unfold criticalLineLFourth
    positivity

/-- The lower classical mean-value inequality used by BHP.  This is the exact
quantifier order of Lemma 7, with an explicit ambient parameter carrying the
paper's `mathcal L = log x`.  The family includes all characters modulo `q`;
BHP explicitly notes that Ramachandra's result has no primitive restriction.

This proposition is intentionally not inhabited here. -/
def BHPLemma7RamachandraAllCharacterMeanValue : Prop :=
  ∃ C₇ : ℝ, 0 < C₇ ∧ ∃ B₇ : ℕ,
    ∀ (q : ℕ) [NeZero q] (U x0 : ℝ),
      2 ≤ U → (q : ℝ) ≤ x0 → U ≤ x0 →
      allCharacterCriticalLineFourthIntegral q U ≤
        C₇ * (q : ℝ) * U * Real.log x0 ^ B₇

/-- The principal-character factor in the residue term of BHP (3.36). -/
def principalPerronWeight {q : ℕ}
    (z : DirichletCharacter ℂ q × ℝ) : ℝ := by
  classical
  exact if IsPrincipalCharacter z.1 then 1 / (1 + |z.2|) else 0

theorem principalPerronWeight_nonneg {q : ℕ}
    (z : DirichletCharacter ℂ q × ℝ) :
    0 ≤ principalPerronWeight z := by
  classical
  unfold principalPerronWeight
  split_ifs
  · positivity
  · exact le_rfl

theorem sum_principalPerronWeight_fourth {q : ℕ}
    (S : Finset (DirichletCharacter ℂ q × ℝ)) :
    (∑ z ∈ S, principalPerronWeight z ^ 4) =
      selectedPrincipalDecayMass S := by
  classical
  unfold principalPerronWeight selectedPrincipalDecayMass
  apply Finset.sum_congr rfl
  intro z hz
  split_ifs <;> simp

/-- The exact source layer below BHP Lemma 9: equation (3.36) supplies the
three displayed errors, while Holder and same-character one-spacing bound the
fourth powers of its contour term `J` by the continuous family moment.

The first error has no logarithm in (3.36); the final `log^4` harmlessly
dominates it because `x0 >= 2`, at the cost of an absolute constant.  The
second error is exactly `log x0 * sqrt X / T`, and the third is the explicit
principal residue.  The exponent `K` records only the Holder/kernel loss.

This proposition is strictly below Lemma 9: its right side still contains the
continuous mean-value integral from Lemma 7. -/
def BHPEquation336AndHolderReduction : Prop :=
  ∃ C₃₆ : ℝ, 0 < C₃₆ ∧ ∃ K : ℕ,
    ∀ (q X : ℕ) [NeZero q] (T x0 : ℝ)
      (S : Finset (DirichletCharacter ℂ q × ℝ)),
      1 ≤ q → 2 ≤ X → 2 ≤ T →
      (q : ℝ) ≤ x0 → (X : ℝ) ≤ x0 → T ≤ x0 →
      (∀ z ∈ S, |z.2| ≤ T) →
      SameCharacterOneSeparated S →
      ∃ J : DirichletCharacter ℂ q × ℝ → ℝ,
        (∀ z ∈ S, 0 ≤ J z) ∧
        (∀ z ∈ S,
          ‖criticalPrefixPolynomial q X z.1 z.2‖ ≤
            J z + C₃₆ *
              (Real.sqrt (q : ℝ) / Real.sqrt T +
                Real.log x0 * Real.sqrt (X : ℝ) / T +
                Real.sqrt (X : ℝ) * principalPerronWeight z)) ∧
        (∑ z ∈ S, J z ^ 4) ≤
          C₃₆ * Real.log x0 ^ K *
            allCharacterCriticalLineFourthIntegral q (2 * T)

/-- Four-term convexity in the exact form used to raise equation (3.36) to
the fourth power. -/
theorem fourth_power_sum_four_le
    {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (a + b + c + d) ^ 4 ≤
      64 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) := by
  let f : Fin 4 → ℝ := fun i => match i with
    | 0 => a
    | 1 => b
    | 2 => c
    | 3 => d
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin 4)), 0 ≤ f i := by
    intro i hi
    fin_cases i <;> simp [f, ha, hb, hc, hd]
  have h := pow_sum_le_card_mul_sum_pow hf 3
  simp [f, Fin.sum_univ_succ] at h
  convert h using 1 <;> ring

theorem sqrt_ratio_fourth
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    (Real.sqrt a / Real.sqrt b) ^ 4 = a ^ 2 / b ^ 2 := by
  rw [div_pow]
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  rw [show Real.sqrt a ^ 4 = (Real.sqrt a ^ 2) ^ 2 by ring,
    show Real.sqrt b ^ 4 = (Real.sqrt b ^ 2) ^ 2 by ring,
    hsa, hsb]

theorem log_sqrt_ratio_fourth
    {L a T : ℝ} (ha : 0 ≤ a) :
    (L * Real.sqrt a / T) ^ 4 = L ^ 4 * a ^ 2 / T ^ 4 := by
  rw [div_pow, mul_pow]
  rw [show Real.sqrt a ^ 4 = (Real.sqrt a ^ 2) ^ 2 by ring,
    Real.sq_sqrt ha]

/-- Purely finite summation of the three errors in (3.36).  This is the
deterministic algebra between the pointwise contour estimate and BHP's
displayed Lemma 9. -/
theorem selectedPrefixFourthMass_le_equation336
    {q X : ℕ} {T x0 C : ℝ}
    {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {J : DirichletCharacter ℂ q × ℝ → ℝ}
    (hq : 1 ≤ q) (hT : 0 < T) (hx0 : 1 ≤ x0) (hC : 0 ≤ C)
    (hJ : ∀ z ∈ S, 0 ≤ J z)
    (h336 : ∀ z ∈ S,
      ‖criticalPrefixPolynomial q X z.1 z.2‖ ≤
        J z + C *
          (Real.sqrt (q : ℝ) / Real.sqrt T +
            Real.log x0 * Real.sqrt (X : ℝ) / T +
            Real.sqrt (X : ℝ) * principalPerronWeight z)) :
    selectedPrefixFourthMass X S ≤
      64 * ((∑ z ∈ S, J z ^ 4) + C ^ 4 *
        ((S.card : ℝ) * ((q : ℝ) ^ 2 / T ^ 2) +
          Real.log x0 ^ 4 * (S.card : ℝ) *
            ((X : ℝ) ^ 2 / T ^ 4) +
          (X : ℝ) ^ 2 * selectedPrincipalDecayMass S)) := by
  classical
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hX0 : 0 ≤ (X : ℝ) := by positivity
  let a : ℝ := Real.sqrt (q : ℝ) / Real.sqrt T
  let b : ℝ := Real.log x0 * Real.sqrt (X : ℝ) / T
  let c : DirichletCharacter ℂ q × ℝ → ℝ :=
    fun z => Real.sqrt (X : ℝ) * principalPerronWeight z
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb (hlog : 0 ≤ Real.log x0) : 0 ≤ b := by
    dsimp [b]
    positivity
  have hc (z : DirichletCharacter ℂ q × ℝ) : 0 ≤ c z := by
    dsimp [c]
    exact mul_nonneg (Real.sqrt_nonneg _) (principalPerronWeight_nonneg z)
  have hlog : 0 ≤ Real.log x0 := Real.log_nonneg hx0
  unfold selectedPrefixFourthMass
  calc
    (∑ z ∈ S, ‖criticalPrefixPolynomial q X z.1 z.2‖ ^ 4) ≤
        ∑ z ∈ S, 64 *
          (J z ^ 4 + (C * a) ^ 4 + (C * b) ^ 4 + (C * c z) ^ 4) := by
      apply Finset.sum_le_sum
      intro z hz
      have hupper := h336 z hz
      have hupper' :
          ‖criticalPrefixPolynomial q X z.1 z.2‖ ≤
            J z + C * a + C * b + C * c z := by
        dsimp [a, b, c]
        linarith
      have hp := pow_le_pow_left₀
        (norm_nonneg (criticalPrefixPolynomial q X z.1 z.2)) hupper' 4
      exact hp.trans (fourth_power_sum_four_le
        (hJ z hz) (mul_nonneg hC ha) (mul_nonneg hC (hb hlog))
        (mul_nonneg hC (hc z)))
    _ = 64 * ((∑ z ∈ S, J z ^ 4) + C ^ 4 *
        ((S.card : ℝ) * ((q : ℝ) ^ 2 / T ^ 2) +
          Real.log x0 ^ 4 * (S.card : ℝ) *
            ((X : ℝ) ^ 2 / T ^ 4) +
          (X : ℝ) ^ 2 * selectedPrincipalDecayMass S)) := by
      have ha4 : a ^ 4 = (q : ℝ) ^ 2 / T ^ 2 := by
        dsimp [a]
        exact sqrt_ratio_fourth hq0 hT
      have hb4 : b ^ 4 = Real.log x0 ^ 4 * (X : ℝ) ^ 2 / T ^ 4 := by
        dsimp [b]
        exact log_sqrt_ratio_fourth hX0
      have hc4 (z : DirichletCharacter ℂ q × ℝ) :
          c z ^ 4 = (X : ℝ) ^ 2 * principalPerronWeight z ^ 4 := by
        dsimp [c]
        rw [mul_pow]
        rw [show Real.sqrt (X : ℝ) ^ 4 =
          (Real.sqrt (X : ℝ) ^ 2) ^ 2 by ring,
          Real.sq_sqrt hX0]
      simp_rw [mul_pow, ha4, hb4, hc4]
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hpull :
          (∑ z ∈ S, C ^ 4 *
            ((X : ℝ) ^ 2 * principalPerronWeight z ^ 4)) =
            C ^ 4 * (X : ℝ) ^ 2 * selectedPrincipalDecayMass S := by
        rw [← Finset.mul_sum, ← Finset.mul_sum,
          sum_principalPerronWeight_fourth]
        ring
      rw [hpull]
      ring

/-- BHP Lemma 9 with its lower continuous fourth moment still visible.  The
`q^2/T^2` term is deliberately left without a logarithm because that is the
literal first error in (3.36). -/
def BHPLemma9ContinuousReduction : Prop :=
  ∃ C₉ : ℝ, 0 < C₉ ∧ ∃ K : ℕ,
    ∀ (q X : ℕ) [NeZero q] (T x0 : ℝ)
      (S : Finset (DirichletCharacter ℂ q × ℝ)),
      1 ≤ q → 2 ≤ X → 2 ≤ T →
      (q : ℝ) ≤ x0 → (X : ℝ) ≤ x0 → T ≤ x0 →
      (∀ z ∈ S, |z.2| ≤ T) →
      SameCharacterOneSeparated S →
      selectedPrefixFourthMass X S ≤ C₉ *
        (Real.log x0 ^ K *
            allCharacterCriticalLineFourthIntegral q (2 * T) +
          (S.card : ℝ) * ((q : ℝ) ^ 2 / T ^ 2) +
          Real.log x0 ^ 4 * (S.card : ℝ) *
            ((X : ℝ) ^ 2 / T ^ 4) +
          (X : ℝ) ^ 2 * selectedPrincipalDecayMass S)

/-- Equation (3.36), Holder, and same-character kernel packing imply the exact
continuous reduction used before invoking BHP Lemma 7.  Every step here after
the source hypothesis is finite nonnegative algebra. -/
theorem bhpLemma9ContinuousReduction_of_equation336AndHolder
    (hsource : BHPEquation336AndHolderReduction) :
    BHPLemma9ContinuousReduction := by
  classical
  obtain ⟨C₃₆, hC₃₆, K, hsource⟩ := hsource
  let C₉ : ℝ := 64 * (C₃₆ + C₃₆ ^ 4)
  have hC₉ : 0 < C₉ := by
    dsimp [C₉]
    positivity
  refine ⟨C₉, hC₉, K, ?_⟩
  intro q X _inst T x0 S hq hX hT hqx hXx hTx hheight hsep
  obtain ⟨J, hJnonneg, h336, hJfourth⟩ :=
    hsource q X T x0 S hq hX hT hqx hXx hTx hheight hsep
  have hTpos : 0 < T := by linarith
  have hqreal : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hxone : 1 ≤ x0 := hqreal.trans hqx
  have hlog : 0 ≤ Real.log x0 := Real.log_nonneg hxone
  have hfinite := selectedPrefixFourthMass_le_equation336
    (q := q) (X := X) (T := T) (x0 := x0) (C := C₃₆)
    (S := S) (J := J) hq hTpos hxone hC₃₆.le hJnonneg h336
  let A : ℝ := Real.log x0 ^ K *
    allCharacterCriticalLineFourthIntegral q (2 * T)
  let E₁ : ℝ := (S.card : ℝ) * ((q : ℝ) ^ 2 / T ^ 2)
  let E₂ : ℝ := Real.log x0 ^ 4 * (S.card : ℝ) *
    ((X : ℝ) ^ 2 / T ^ 4)
  let P : ℝ := (X : ℝ) ^ 2 * selectedPrincipalDecayMass S
  have hfamily : 0 ≤ allCharacterCriticalLineFourthIntegral q (2 * T) :=
    allCharacterCriticalLineFourthIntegral_nonneg q (by linarith)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE₁ : 0 ≤ E₁ := by dsimp [E₁]; positivity
  have hE₂ : 0 ≤ E₂ := by dsimp [E₂]; positivity
  have hprincipal : 0 ≤ selectedPrincipalDecayMass S := by
    rw [← sum_principalPerronWeight_fourth]
    positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hJfourth' : (∑ z ∈ S, J z ^ 4) ≤ C₃₆ * A := by
    simpa [A, mul_assoc] using hJfourth
  have hfirst :
      (∑ z ∈ S, J z ^ 4) + C₃₆ ^ 4 * (E₁ + E₂ + P) ≤
        C₃₆ * A + C₃₆ ^ 4 * (E₁ + E₂ + P) := by
    exact add_le_add hJfourth' (le_refl _)
  have hscale :
      C₃₆ * A + C₃₆ ^ 4 * (E₁ + E₂ + P) ≤
        (C₃₆ + C₃₆ ^ 4) * (A + E₁ + E₂ + P) := by
    nlinarith [mul_nonneg hC₃₆.le (add_nonneg hE₁ (add_nonneg hE₂ hP)),
      mul_nonneg (pow_nonneg hC₃₆.le 4) hA]
  calc
    selectedPrefixFourthMass X S ≤
        64 * ((∑ z ∈ S, J z ^ 4) + C₃₆ ^ 4 *
          (E₁ + E₂ + P)) := by
      simpa [E₁, E₂, P] using hfinite
    _ ≤ 64 * (C₃₆ * A + C₃₆ ^ 4 * (E₁ + E₂ + P)) := by
      exact mul_le_mul_of_nonneg_left hfirst (by norm_num)
    _ ≤ 64 * ((C₃₆ + C₃₆ ^ 4) * (A + E₁ + E₂ + P)) := by
      exact mul_le_mul_of_nonneg_left hscale (by norm_num)
    _ = C₉ * (Real.log x0 ^ K *
          allCharacterCriticalLineFourthIntegral q (2 * T) +
        (S.card : ℝ) * ((q : ℝ) ^ 2 / T ^ 2) +
        Real.log x0 ^ 4 * (S.card : ℝ) *
          ((X : ℝ) ^ 2 / T ^ 4) +
        (X : ℝ) ^ 2 * selectedPrincipalDecayMass S) := by
      dsimp [C₉, A, E₁, E₂, P]
      ring

/-- Source-faithful call of BHP Lemma 7 at height `2T`.  The paper's ambient
parameter is correspondingly doubled; `log (2*x0)` is converted back to
`log x0` using `x0 >= 2`, with the exact absolute factor `2^(B₇+1)`. -/
theorem bhpLemma7_doubledHeight
    {C₇ : ℝ} {B₇ : ℕ}
    (hC₇ : 0 ≤ C₇)
    (hsource : ∀ (q : ℕ) [NeZero q] (U x0 : ℝ),
      2 ≤ U → (q : ℝ) ≤ x0 → U ≤ x0 →
      allCharacterCriticalLineFourthIntegral q U ≤
        C₇ * (q : ℝ) * U * Real.log x0 ^ B₇)
    (q : ℕ) [NeZero q] {T x0 : ℝ}
    (hT : 2 ≤ T) (hx0 : 2 ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hTx : T ≤ x0) :
    allCharacterCriticalLineFourthIntegral q (2 * T) ≤
      (2 * C₇ * (2 : ℝ) ^ B₇) * (q : ℝ) * T *
        Real.log x0 ^ B₇ := by
  have hcall := hsource q (2 * T) (2 * x0)
    (by linarith) (by linarith) (by linarith)
  have hxpos : 0 < x0 := by linarith
  have hlog2le : Real.log 2 ≤ Real.log x0 :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hxpos hx0
  have hlogmul : Real.log (2 * x0) = Real.log 2 + Real.log x0 :=
    Real.log_mul (by norm_num) hxpos.ne'
  have hlogx : 0 ≤ Real.log x0 := Real.log_nonneg (by linarith)
  have hlog2x : 0 ≤ Real.log (2 * x0) := by
    rw [hlogmul]
    positivity
  have hlogbound : Real.log (2 * x0) ≤ 2 * Real.log x0 := by
    rw [hlogmul]
    linarith
  have hpow : Real.log (2 * x0) ^ B₇ ≤
      (2 * Real.log x0) ^ B₇ :=
    pow_le_pow_left₀ hlog2x hlogbound B₇
  calc
    allCharacterCriticalLineFourthIntegral q (2 * T) ≤
        C₇ * (q : ℝ) * (2 * T) * Real.log (2 * x0) ^ B₇ := hcall
    _ ≤ C₇ * (q : ℝ) * (2 * T) * (2 * Real.log x0) ^ B₇ := by
      gcongr
    _ = (2 * C₇ * (2 : ℝ) ^ B₇) * (q : ℝ) * T *
          Real.log x0 ^ B₇ := by
      rw [mul_pow]
      ring

/-- The published BHP/Ramachandra chain, with all deterministic substitutions
made explicit.  The only premises are now the contour/Holder reduction below
Lemma 9 and the lower all-character continuous mean value of Lemma 7. -/
theorem mrtLemma211_of_bhpEquation336_and_ramachandraMeanValue
    (hcontour : BHPEquation336AndHolderReduction)
    (hmean : BHPLemma7RamachandraAllCharacterMeanValue) :
    MRTLemma211AllCharacterFourthMoment := by
  classical
  obtain ⟨C₉, hC₉, K, hreduce⟩ :=
    bhpLemma9ContinuousReduction_of_equation336AndHolder hcontour
  obtain ⟨C₇, hC₇, B₇, hlemma7⟩ := hmean
  let C₇d : ℝ := 2 * C₇ * (2 : ℝ) ^ B₇
  let Dlog : ℝ := 1 / Real.log 2 ^ 4
  let M : ℝ := C₇d + (Dlog + 1) + 1
  let C : ℝ := C₉ * M
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC₇d : 0 < C₇d := by dsimp [C₇d]; positivity
  have hDlog : 0 < Dlog := by dsimp [Dlog]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, K + B₇, ?_⟩
  intro q X T x0 S hq hX hT hqx hXx hTx hheight hsep
  letI : NeZero q := ⟨by omega⟩
  have hqreal : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hx0two : 2 ≤ x0 := by
    have hXreal : (2 : ℝ) ≤ X := by exact_mod_cast hX
    exact hXreal.trans hXx
  have hx0one : 1 ≤ x0 := by linarith
  have hx0pos : 0 < x0 := by linarith
  have hlog : 0 ≤ Real.log x0 := Real.log_nonneg hx0one
  have hraw := hreduce q X T x0 S hq hX hT hqx hXx hTx
    hheight hsep
  have hmean2 :
      allCharacterCriticalLineFourthIntegral q (2 * T) ≤
        C₇d * (q : ℝ) * T * Real.log x0 ^ B₇ := by
    simpa [C₇d] using bhpLemma7_doubledHeight hC₇.le hlemma7 q
      hT hx0two hqx hTx
  let A : ℝ := (q : ℝ) * T * Real.log x0 ^ (K + B₇)
  let E₁ : ℝ := (S.card : ℝ) * ((q : ℝ) ^ 2 / T ^ 2)
  let E₂ : ℝ := Real.log x0 ^ 4 * (S.card : ℝ) *
    ((X : ℝ) ^ 2 / T ^ 4)
  let R : ℝ := Real.log x0 ^ 4 * (S.card : ℝ) *
    ((q : ℝ) ^ 2 / T ^ 2 + (X : ℝ) ^ 2 / T ^ 4)
  let P : ℝ := (X : ℝ) ^ 2 * selectedPrincipalDecayMass S
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE₁ : 0 ≤ E₁ := by dsimp [E₁]; positivity
  have hE₂ : 0 ≤ E₂ := by dsimp [E₂]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hprincipal : 0 ≤ selectedPrincipalDecayMass S := by
    rw [← sum_principalPerronWeight_fourth]
    positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hmain :
      Real.log x0 ^ K *
          allCharacterCriticalLineFourthIntegral q (2 * T) ≤
        C₇d * A := by
    calc
      Real.log x0 ^ K *
          allCharacterCriticalLineFourthIntegral q (2 * T) ≤
          Real.log x0 ^ K *
            (C₇d * (q : ℝ) * T * Real.log x0 ^ B₇) :=
        mul_le_mul_of_nonneg_left hmean2 (pow_nonneg hlog K)
      _ = C₇d * A := by
        dsimp [A]
        rw [pow_add]
        ring
  have hsourceInside :
      Real.log x0 ^ K *
          allCharacterCriticalLineFourthIntegral q (2 * T) +
          E₁ + E₂ + P ≤
        C₇d * A + E₁ + E₂ + P := by
    linarith
  have hlog2le : Real.log 2 ≤ Real.log x0 :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hx0pos hx0two
  have hlogfour : Real.log 2 ^ 4 ≤ Real.log x0 ^ 4 :=
    pow_le_pow_left₀ hlog2.le hlog2le 4
  have hDlogOne : 1 ≤ Dlog * Real.log x0 ^ 4 := by
    have hmpos : 0 < Real.log 2 ^ 4 := pow_pos hlog2 4
    calc
      1 = Dlog * Real.log 2 ^ 4 := by
        dsimp [Dlog]
        field_simp
      _ ≤ Dlog * Real.log x0 ^ 4 :=
        mul_le_mul_of_nonneg_left hlogfour hDlog.le
  have hcomponent₁ : Real.log x0 ^ 4 * E₁ ≤ R := by
    dsimp [E₁, R]
    have hxratio : 0 ≤ (X : ℝ) ^ 2 / T ^ 4 := by positivity
    calc
      Real.log x0 ^ 4 *
          ((S.card : ℝ) * ((q : ℝ) ^ 2 / T ^ 2)) =
          Real.log x0 ^ 4 * (S.card : ℝ) *
            ((q : ℝ) ^ 2 / T ^ 2) := by ring
      _ ≤ Real.log x0 ^ 4 * (S.card : ℝ) *
          ((q : ℝ) ^ 2 / T ^ 2 + (X : ℝ) ^ 2 / T ^ 4) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right hxratio)
          (mul_nonneg (pow_nonneg hlog 4) (by positivity))
      _ = R := rfl
  have hcomponent₂ : E₂ ≤ R := by
    dsimp [E₂, R]
    have hqratio : 0 ≤ (q : ℝ) ^ 2 / T ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left hqratio)
      (mul_nonneg (pow_nonneg hlog 4) (by positivity))
  have hE₁R : E₁ ≤ Dlog * R := by
    calc
      E₁ = 1 * E₁ := by ring
      _ ≤ (Dlog * Real.log x0 ^ 4) * E₁ :=
        mul_le_mul_of_nonneg_right hDlogOne hE₁
      _ = Dlog * (Real.log x0 ^ 4 * E₁) := by ring
      _ ≤ Dlog * R := mul_le_mul_of_nonneg_left hcomponent₁ hDlog.le
  have herrors : E₁ + E₂ ≤ (Dlog + 1) * R := by
    calc
      E₁ + E₂ ≤ Dlog * R + R := add_le_add hE₁R hcomponent₂
      _ = (Dlog + 1) * R := by ring
  have hinside :
      C₇d * A + E₁ + E₂ + P ≤ M * (A + R + P) := by
    have hMA : C₇d * A ≤ M * A := by
      apply mul_le_mul_of_nonneg_right _ hA
      dsimp [M]
      linarith
    have hMR : (Dlog + 1) * R ≤ M * R := by
      apply mul_le_mul_of_nonneg_right _ hR
      dsimp [M]
      linarith [hC₇d]
    have hMP : P ≤ M * P := by
      calc
        P = 1 * P := by ring
        _ ≤ M * P := by
          apply mul_le_mul_of_nonneg_right _ hP
          dsimp [M]
          linarith [hC₇d, hDlog]
    calc
      C₇d * A + E₁ + E₂ + P ≤
          C₇d * A + (Dlog + 1) * R + P := by linarith
      _ ≤ M * A + M * R + M * P := by
        exact add_le_add (add_le_add hMA hMR) hMP
      _ = M * (A + R + P) := by ring
  calc
    selectedPrefixFourthMass X S ≤ C₉ *
        (Real.log x0 ^ K *
            allCharacterCriticalLineFourthIntegral q (2 * T) +
          E₁ + E₂ + P) := by
      simpa [E₁, E₂, P] using hraw
    _ ≤ C₉ * (C₇d * A + E₁ + E₂ + P) :=
      mul_le_mul_of_nonneg_left hsourceInside hC₉.le
    _ ≤ C₉ * (M * (A + R + P)) :=
      mul_le_mul_of_nonneg_left hinside hC₉.le
    _ = C * ((q : ℝ) * T * Real.log x0 ^ (K + B₇) +
        Real.log x0 ^ 4 * (S.card : ℝ) *
          ((q : ℝ) ^ 2 / T ^ 2 + (X : ℝ) ^ 2 / T ^ 4) +
        (X : ℝ) ^ 2 * selectedPrincipalDecayMass S) := by
      dsimp [C, A, R, P]
      ring

/-! ## Certified Holder and one-spacing kernel layer -/

/-- The critical-line norm is continuous for every character, including the
principal character: the line `Re s = 1/2` never meets the sole possible pole
at `s=1`. -/
theorem continuous_criticalLineLNorm
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    Continuous (criticalLineLNorm chi) := by
  unfold criticalLineLNorm
  apply Continuous.norm
  rw [continuous_iff_continuousAt]
  intro t
  have hinner : ContinuousAt
      (fun x : ℝ => (((1 / 2 : ℝ) : ℂ) + x * Complex.I)) t := by
    fun_prop
  have houter : ContinuousAt (DirichletCharacter.LFunction chi)
      (((1 / 2 : ℝ) : ℂ) + t * Complex.I) :=
    (DirichletCharacter.differentiableAt_LFunction chi
    (((1 / 2 : ℝ) : ℂ) + t * Complex.I) (.inl (by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre))).continuousAt
  have hc : ContinuousAt
      ((DirichletCharacter.LFunction chi) ∘
        (fun x : ℝ => (((1 / 2 : ℝ) : ℂ) + x * Complex.I))) t :=
    ContinuousAt.comp houter hinner
  simpa only [Function.comp_def] using hc

/-- Pairs selected for one fixed character. -/
def characterFiber {q : ℕ}
    (S : Finset (DirichletCharacter ℂ q × ℝ))
    (chi : DirichletCharacter ℂ q) :
    Finset (DirichletCharacter ℂ q × ℝ) := by
  classical
  exact S.filter fun z => z.1 = chi

@[simp] theorem mem_characterFiber {q : ℕ}
    {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {chi : DirichletCharacter ℂ q}
    {z : DirichletCharacter ℂ q × ℝ} :
    z ∈ characterFiber S chi ↔ z ∈ S ∧ z.1 = chi := by
  classical
  simp [characterFiber]

/-- Ordinates selected for one fixed character. -/
def characterOrdinateSet {q : ℕ}
    (S : Finset (DirichletCharacter ℂ q × ℝ))
    (chi : DirichletCharacter ℂ q) : Finset ℝ := by
  classical
  exact (characterFiber S chi).image Prod.snd

theorem characterOrdinateSet_oneSeparated
    {q : ℕ} {S : Finset (DirichletCharacter ℂ q × ℝ)}
    (hsep : SameCharacterOneSeparated S)
    (chi : DirichletCharacter ℂ q) :
    ∀ t ∈ characterOrdinateSet S chi,
      ∀ u ∈ characterOrdinateSet S chi,
        t ≠ u → 1 ≤ |t - u| := by
  classical
  intro t ht u hu htu
  rw [characterOrdinateSet, Finset.mem_image] at ht hu
  obtain ⟨z, hz, rfl⟩ := ht
  obtain ⟨w, hw, rfl⟩ := hu
  have hz' := Finset.mem_filter.mp hz
  have hw' := Finset.mem_filter.mp hw
  have hzw : z ≠ w := by
    intro h
    apply htu
    rw [h]
  exact hsep z hz'.1 w hw'.1 hzw (hz'.2.trans hw'.2.symm)

theorem characterOrdinateSet_height
    {q : ℕ} {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {T : ℝ} (hheight : ∀ z ∈ S, |z.2| ≤ T)
    (chi : DirichletCharacter ℂ q) :
    ∀ t ∈ characterOrdinateSet S chi, |t| ≤ T := by
  classical
  intro t ht
  rw [characterOrdinateSet, Finset.mem_image] at ht
  obtain ⟨z, hz, rfl⟩ := ht
  exact hheight z (Finset.mem_filter.mp hz).1

theorem sum_characterOrdinateSet
    {q : ℕ} {S : Finset (DirichletCharacter ℂ q × ℝ)}
    (chi : DirichletCharacter ℂ q) (F : ℝ → ℝ) :
    (∑ t ∈ characterOrdinateSet S chi, F t) =
      ∑ z ∈ characterFiber S chi, F z.2 := by
  classical
  unfold characterOrdinateSet
  rw [Finset.sum_image]
  intro z hz w hw hzw
  have hz' := (Finset.mem_filter.mp hz).2
  have hw' := (Finset.mem_filter.mp hw).2
  apply Prod.ext
  · exact hz'.trans hw'.symm
  · exact hzw

/-- Regroup a finite set of character/ordinate pairs by character, using the
proof-irrelevant filtered fiber fixed above. -/
theorem sum_characterFiber_fiberwise
    {q : ℕ} (S : Finset (DirichletCharacter ℂ q × ℝ))
    (F : DirichletCharacter ℂ q × ℝ → ℝ) :
    (∑ chi : DirichletCharacter ℂ q,
      ∑ z ∈ characterFiber S chi, F z) = ∑ z ∈ S, F z := by
  classical
  rw [← Finset.sum_fiberwise S Prod.fst F]
  apply Finset.sum_congr rfl
  intro chi hchi
  apply Finset.sum_congr
  · ext z
    simp
  · intro z hz
    rfl

/-- Same-character spacing bounds the Perron kernel row for each character by
the exact finite harmonic factor supplied by `HarmonicRowGrouping`. -/
theorem characterFiber_perronKernel_sum_le_harmonic
    {q : ℕ} {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {T : ℝ} (hT : 0 ≤ T)
    (hheight : ∀ z ∈ S, |z.2| ≤ T)
    (hsep : SameCharacterOneSeparated S)
    (chi : DirichletCharacter ℂ q) {u : ℝ} (hu : |u| ≤ 2 * T) :
    (∑ z ∈ characterFiber S chi,
      perronWeight (u - z.2)) ≤
      4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ) := by
  have hpack := oneSeparated_perronKernel_sum_le_harmonic
    (characterOrdinateSet S chi) hT
    (characterOrdinateSet_oneSeparated hsep chi)
    (characterOrdinateSet_height hheight chi) hu
  rw [sum_characterOrdinateSet chi
    (fun t => 1 / (1 + |t - u|))] at hpack
  simpa [perronWeight, abs_sub_comm] using hpack

/-- The fourth power integrand in BHP Lemma 7 is continuous on the critical
line. -/
theorem continuous_criticalLineLFourth
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    Continuous (criticalLineLFourth chi) := by
  unfold criticalLineLFourth
  exact (continuous_criticalLineLNorm chi).pow 4

/-- Translation of one Perron convolution to an interval centered at its
ordinate.  This is the change of variables used before packing the kernel
rows. -/
theorem perronConvolution_eq_translatedIntegral
    (G : ℝ → ℝ) (T t : ℝ) :
    perronConvolution G T t =
      ∫ s in (-T + t)..(T + t), perronWeight (s - t) * G s := by
  unfold perronConvolution
  have hshift := intervalIntegral.integral_comp_add_right
    (fun s : ℝ => perronWeight (s - t) * G s) t
    (a := -T) (b := T)
  simpa [add_comm] using hshift

/-- For one character, summing the translated fourth-power convolutions over
one-spaced ordinates costs exactly the finite harmonic kernel row. -/
theorem sum_characterFiber_perronConvolution_fourth_le
    {q : ℕ} [NeZero q]
    {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {T : ℝ} (hT : 0 ≤ T)
    (hheight : ∀ z ∈ S, |z.2| ≤ T)
    (hsep : SameCharacterOneSeparated S)
    (chi : DirichletCharacter ℂ q) :
    (∑ z ∈ characterFiber S chi,
      perronConvolution (criticalLineLFourth chi) T z.2) ≤
      4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ) *
        (∫ s in (-2 * T)..(2 * T), criticalLineLFourth chi s) := by
  classical
  let H : ℝ := 4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ)
  have hG : Continuous (criticalLineLFourth chi) :=
    continuous_criticalLineLFourth chi
  have hlocal :
      (∑ z ∈ characterFiber S chi,
        perronConvolution (criticalLineLFourth chi) T z.2) ≤
      ∑ z ∈ characterFiber S chi,
        ∫ s in (-2 * T)..(2 * T),
          perronWeight (s - z.2) * criticalLineLFourth chi s := by
    apply Finset.sum_le_sum
    intro z hz
    rw [perronConvolution_eq_translatedIntegral]
    have hzS : z ∈ S := (mem_characterFiber.mp hz).1
    have hzt := hheight z hzS
    have hzt' := (abs_le.mp hzt)
    apply intervalIntegral.integral_mono_interval
    · linarith [hzt'.1]
    · linarith
    · linarith [hzt'.2]
    · exact Filter.Eventually.of_forall fun s =>
        mul_nonneg (perronWeight_pos _).le (by
          unfold criticalLineLFourth
          positivity)
    · exact ((continuous_perronWeight.comp
          (continuous_id.sub continuous_const)).mul hG).intervalIntegrable _ _
  have hswap :
      (∑ z ∈ characterFiber S chi,
        ∫ s in (-2 * T)..(2 * T),
          perronWeight (s - z.2) * criticalLineLFourth chi s) =
      ∫ s in (-2 * T)..(2 * T),
        ∑ z ∈ characterFiber S chi,
          perronWeight (s - z.2) * criticalLineLFourth chi s := by
    rw [intervalIntegral.integral_finset_sum]
    intro z hz
    exact ((continuous_perronWeight.comp
      (continuous_id.sub continuous_const)).mul hG).intervalIntegrable _ _
  have hpoint : ∀ s ∈ Set.Icc (-2 * T) (2 * T),
      (∑ z ∈ characterFiber S chi,
        perronWeight (s - z.2) * criticalLineLFourth chi s) ≤
      H * criticalLineLFourth chi s := by
    intro s hs
    have hsabs : |s| ≤ 2 * T := (abs_le).2 ⟨by linarith [hs.1], hs.2⟩
    have hkernel := characterFiber_perronKernel_sum_le_harmonic
      hT hheight hsep chi hsabs
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hkernel (by
      unfold criticalLineLFourth
      positivity)
  calc
    (∑ z ∈ characterFiber S chi,
        perronConvolution (criticalLineLFourth chi) T z.2) ≤
        ∑ z ∈ characterFiber S chi,
          ∫ s in (-2 * T)..(2 * T),
            perronWeight (s - z.2) * criticalLineLFourth chi s := hlocal
    _ = ∫ s in (-2 * T)..(2 * T),
          ∑ z ∈ characterFiber S chi,
            perronWeight (s - z.2) * criticalLineLFourth chi s := hswap
    _ ≤ ∫ s in (-2 * T)..(2 * T),
          H * criticalLineLFourth chi s := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact (continuous_finset_sum _ fun z hz =>
          (continuous_perronWeight.comp
            (continuous_id.sub continuous_const)).mul hG).intervalIntegrable _ _
      · exact (continuous_const.mul hG).intervalIntegrable _ _
      · exact hpoint
    _ = H * (∫ s in (-2 * T)..(2 * T),
          criticalLineLFourth chi s) := by
      rw [intervalIntegral.integral_const_mul]
    _ = 4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ) *
          (∫ s in (-2 * T)..(2 * T), criticalLineLFourth chi s) := rfl

/-- Holder followed by the preceding one-spacing row estimate, summed over
all characters.  The kernel loss is kept exact: one cube of the Perron
`L¹`-mass and one finite harmonic row. -/
theorem sum_perronConvolution_fourth_le_exactKernel
    {q : ℕ} [NeZero q]
    {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {T : ℝ} (hT : 0 < T)
    (hheight : ∀ z ∈ S, |z.2| ≤ T)
    (hsep : SameCharacterOneSeparated S) :
    (∑ z ∈ S,
      perronConvolution (criticalLineLNorm z.1) T z.2 ^ 4) ≤
      (∫ u in (-T)..T, perronWeight u) ^ 3 *
        (4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ)) *
          allCharacterCriticalLineFourthIntegral q (2 * T) := by
  classical
  let W : ℝ := ∫ u in (-T)..T, perronWeight u
  let H : ℝ := 4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ)
  let F : DirichletCharacter ℂ q × ℝ → ℝ := fun z =>
    perronConvolution (criticalLineLFourth z.1) T z.2
  have hholder :
      (∑ z ∈ S,
        perronConvolution (criticalLineLNorm z.1) T z.2 ^ 4) ≤
        W ^ 3 * ∑ z ∈ S, F z := by
    calc
      (∑ z ∈ S,
          perronConvolution (criticalLineLNorm z.1) T z.2 ^ 4) ≤
          ∑ z ∈ S, W ^ 3 * F z := by
        apply Finset.sum_le_sum
        intro z hz
        have hh := perronConvolution_fourth_le_cubeWeightMass_mul
          (t := z.2) (continuous_criticalLineLNorm z.1) hT
        simpa [W, F, criticalLineLFourth] using! hh
      _ = W ^ 3 * ∑ z ∈ S, F z := by
        rw [Finset.mul_sum]
  have hfiber :
      (∑ chi : DirichletCharacter ℂ q,
        ∑ z ∈ characterFiber S chi, F z) = ∑ z ∈ S, F z := by
    exact sum_characterFiber_fiberwise S F
  have hpack :
      (∑ z ∈ S, F z) ≤
        H * allCharacterCriticalLineFourthIntegral q (2 * T) := by
    rw [← hfiber]
    calc
      (∑ chi : DirichletCharacter ℂ q,
          ∑ z ∈ characterFiber S chi, F z) ≤
          ∑ chi : DirichletCharacter ℂ q,
            H * (∫ s in (-2 * T)..(2 * T),
              criticalLineLFourth chi s) := by
        apply Finset.sum_le_sum
        intro chi hchi
        have hrow := sum_characterFiber_perronConvolution_fourth_le
          hT.le hheight hsep chi
        have heq : (∑ z ∈ characterFiber S chi, F z) =
            ∑ z ∈ characterFiber S chi,
              perronConvolution (criticalLineLFourth chi) T z.2 := by
          apply Finset.sum_congr rfl
          intro z hz
          have hzchi : z.1 = chi := (mem_characterFiber.mp hz).2
          simp [F, hzchi]
        rw [heq]
        simpa [H] using hrow
      _ = H * allCharacterCriticalLineFourthIntegral q (2 * T) := by
        unfold allCharacterCriticalLineFourthIntegral
        rw [← Finset.mul_sum]
        simp only [neg_mul]
  have hW0 : 0 ≤ W := by
    dsimp [W]
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun u hu => (perronWeight_pos u).le)
  calc
    (∑ z ∈ S,
        perronConvolution (criticalLineLNorm z.1) T z.2 ^ 4) ≤
        W ^ 3 * ∑ z ∈ S, F z := hholder
    _ ≤ W ^ 3 * (H * allCharacterCriticalLineFourthIntegral q (2 * T)) :=
      mul_le_mul_of_nonneg_left hpack (pow_nonneg hW0 3)
    _ = (∫ u in (-T)..T, perronWeight u) ^ 3 *
        (4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ)) *
          allCharacterCriticalLineFourthIntegral q (2 * T) := by
      dsimp [W, H]
      ring

/-- The exact Holder/kernel factor is at most an absolute constant times the
fourth power of the ambient logarithm.  This is the harmless `\mathcal L^C`
loss in the last line of the proof of BHP Lemma 9. -/
theorem perronHolderKernel_le_log_four
    {T x0 : ℝ} (hT : 2 ≤ T) (hTx : T ≤ x0) :
    (∫ u in (-T)..T, perronWeight u) ^ 3 *
        (4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ)) ≤
      (256 * (1 / Real.log 2 + 4)) * Real.log x0 ^ 4 := by
  let L : ℝ := Real.log x0
  let W : ℝ := ∫ u in (-T)..T, perronWeight u
  let H : ℝ := 4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ)
  let D : ℝ := 1 / Real.log 2 + 4
  have hx : 2 ≤ x0 := hT.trans hTx
  have hxpos : 0 < x0 := by linarith
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by linarith)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ L := by
    dsimp [L]
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) hxpos hx
  have hlog2x : Real.log (2 * x0) = Real.log 2 + L := by
    dsimp [L]
    exact Real.log_mul (by norm_num) hxpos.ne'
  have hlog2x_le : Real.log (2 * x0) ≤ 2 * L := by
    rw [hlog2x]
    linarith
  have hlog1T_le : Real.log (1 + T) ≤ 2 * L := by
    have hbounds : 0 < 1 + T ∧ 0 < 2 * x0 := by
      constructor <;> positivity
    have harg : 1 + T ≤ 2 * x0 := by linarith
    exact (Real.strictMonoOn_log.monotoneOn hbounds.1 hbounds.2 harg).trans hlog2x_le
  have hW0 : 0 ≤ W := by
    dsimp [W]
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun u hu => (perronWeight_pos u).le)
  have hWle : W ≤ 4 * L := by
    dsimp [W]
    rw [integral_perronWeight (by linarith : 0 ≤ T)]
    linarith
  let n : ℕ := ⌊4 * T⌋₊ + 1
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    dsimp [n]
    positivity
  have hfloor : ((⌊4 * T⌋₊ : ℕ) : ℝ) ≤ 4 * T :=
    Nat.floor_le (by positivity)
  have hnle5x : (n : ℝ) ≤ 5 * x0 := by
    dsimp [n]
    push_cast
    linarith
  have hx3 : (5 : ℝ) ≤ x0 ^ 3 := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 3
    norm_num at hpow ⊢
    linarith
  have h5xpow : 5 * x0 ≤ x0 ^ 4 := by
    calc
      5 * x0 ≤ x0 ^ 3 * x0 :=
        mul_le_mul_of_nonneg_right hx3 hxpos.le
      _ = x0 ^ 4 := by ring
  have hlogn : Real.log (n : ℝ) ≤ 4 * L := by
    have hmono := Real.strictMonoOn_log.monotoneOn hnpos
      (pow_pos hxpos 4) (hnle5x.trans h5xpow)
    rw [Real.log_pow] at hmono
    simpa [L] using hmono
  have hone : 1 ≤ (1 / Real.log 2) * L := by
    rw [one_div_mul_eq_div, le_div_iff₀ hlog2pos]
    simpa using hlog2le
  have hHle : H ≤ 4 * D * L := by
    have hharm : (harmonic n : ℝ) ≤ D * L := by
      calc
        (harmonic n : ℝ) ≤ 1 + Real.log (n : ℝ) :=
          harmonic_le_one_add_log n
        _ ≤ (1 / Real.log 2) * L + 4 * L := add_le_add hone hlogn
        _ = D * L := by dsimp [D]; ring
    dsimp [H, n] at hharm ⊢
    nlinarith
  have hH0 : 0 ≤ H := by
    dsimp [H]
    exact mul_nonneg (by norm_num) (by
      exact_mod_cast (harmonic_pos (by omega : ⌊4 * T⌋₊ + 1 ≠ 0)).le)
  have hWpow : W ^ 3 ≤ (4 * L) ^ 3 :=
    pow_le_pow_left₀ hW0 hWle 3
  calc
    (∫ u in (-T)..T, perronWeight u) ^ 3 *
        (4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ)) = W ^ 3 * H := rfl
    _ ≤ (4 * L) ^ 3 * (4 * D * L) :=
      mul_le_mul hWpow hHle hH0
        (pow_nonneg (mul_nonneg (by norm_num) hL0) 3)
    _ = (256 * D) * L ^ 4 := by ring
    _ = (256 * (1 / Real.log 2 + 4)) * Real.log x0 ^ 4 := rfl

/-! ## The remaining pointwise Perron--Rademacher source leaf -/

/-- The exact analytic leaf left by the certified Holder/kernel descent.
BHP (3.36), obtained from Perron's formula and Rademacher's convexity lemma,
bounds each critical prefix by a translated critical-line convolution plus
the three displayed errors.  No fourth-moment or spacing conclusion is built
into this premise. -/
def BHPEquation336PerronRademacher : Prop :=
  ∃ C₃₆ : ℝ, 0 < C₃₆ ∧
    ∀ (q X : ℕ) [NeZero q] (T x0 : ℝ)
      (S : Finset (DirichletCharacter ℂ q × ℝ)),
      1 ≤ q → 2 ≤ X → 2 ≤ T →
      (q : ℝ) ≤ x0 → (X : ℝ) ≤ x0 → T ≤ x0 →
      (∀ z ∈ S, |z.2| ≤ T) →
      SameCharacterOneSeparated S →
      ∀ z ∈ S,
        ‖criticalPrefixPolynomial q X z.1 z.2‖ ≤ C₃₆ *
          (perronConvolution (criticalLineLNorm z.1) T z.2 +
            (Real.sqrt (q : ℝ) / Real.sqrt T +
              Real.log x0 * Real.sqrt (X : ℝ) / T +
              Real.sqrt (X : ℝ) * principalPerronWeight z))

/-- The pointwise Perron--Rademacher estimate implies the former combined
equation-(3.36)-and-Holder interface.  Holder, character regrouping,
one-spacing kernel packing, and logarithmic absorption are all certified in
the proof. -/
theorem bhpEquation336AndHolderReduction_of_perronRademacher
    (hsource : BHPEquation336PerronRademacher) :
    BHPEquation336AndHolderReduction := by
  classical
  obtain ⟨C₀, hC₀, hsource⟩ := hsource
  let Cκ : ℝ := 256 * (1 / Real.log 2 + 4)
  let C₃₆ : ℝ := C₀ + C₀ ^ 4 * Cκ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCκ : 0 < Cκ := by
    dsimp [Cκ]
    positivity
  have hC₃₆ : 0 < C₃₆ := by
    dsimp [C₃₆]
    positivity
  refine ⟨C₃₆, hC₃₆, 4, ?_⟩
  intro q X _inst T x0 S hq hX hT hqx hXx hTx hheight hsep
  let J : DirichletCharacter ℂ q × ℝ → ℝ := fun z =>
    C₀ * perronConvolution (criticalLineLNorm z.1) T z.2
  refine ⟨J, ?_, ?_, ?_⟩
  · intro z hz
    dsimp [J]
    exact mul_nonneg hC₀.le
      (perronConvolution_nonneg (fun s => norm_nonneg _) (by linarith))
  · intro z hz
    have hraw := hsource q X T x0 S hq hX hT hqx hXx hTx
      hheight hsep z hz
    let E : ℝ := Real.sqrt (q : ℝ) / Real.sqrt T +
      Real.log x0 * Real.sqrt (X : ℝ) / T +
      Real.sqrt (X : ℝ) * principalPerronWeight z
    have hx0 : 2 ≤ x0 := by
      have hXreal : (2 : ℝ) ≤ X := by exact_mod_cast hX
      exact hXreal.trans hXx
    have hE : 0 ≤ E := by
      dsimp [E]
      have hlog : 0 ≤ Real.log x0 := Real.log_nonneg (by linarith)
      have hTpos : 0 < T := by linarith
      have hq0 : 0 ≤ (q : ℝ) := by positivity
      have hX0 : 0 ≤ (X : ℝ) := by positivity
      have hfirst : 0 ≤ Real.sqrt (q : ℝ) / Real.sqrt T := by positivity
      have hsecond : 0 ≤ Real.log x0 * Real.sqrt (X : ℝ) / T := by
        positivity
      have hthird : 0 ≤ Real.sqrt (X : ℝ) * principalPerronWeight z :=
        mul_nonneg (Real.sqrt_nonneg _) (principalPerronWeight_nonneg z)
      exact add_nonneg (add_nonneg hfirst hsecond) hthird
    have hcoeff : C₀ ≤ C₃₆ := by
      dsimp [C₃₆]
      exact le_add_of_nonneg_right
        (mul_nonneg (pow_nonneg hC₀.le 4) hCκ.le)
    calc
      ‖criticalPrefixPolynomial q X z.1 z.2‖ ≤
          C₀ * (perronConvolution (criticalLineLNorm z.1) T z.2 + E) := by
        simpa [E] using hraw
      _ = J z + C₀ * E := by dsimp [J]; ring
      _ ≤ J z + C₃₆ * E :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcoeff hE)
      _ = J z + C₃₆ *
          (Real.sqrt (q : ℝ) / Real.sqrt T +
            Real.log x0 * Real.sqrt (X : ℝ) / T +
            Real.sqrt (X : ℝ) * principalPerronWeight z) := by
        rfl
  · have hTpos : 0 < T := by linarith
    have hfamily :
        0 ≤ allCharacterCriticalLineFourthIntegral q (2 * T) :=
      allCharacterCriticalLineFourthIntegral_nonneg q (by linarith)
    have hagg := sum_perronConvolution_fourth_le_exactKernel
      hTpos hheight hsep
    have hkernel := perronHolderKernel_le_log_four hT hTx
    have hkernelFamily :
        (∫ u in (-T)..T, perronWeight u) ^ 3 *
            (4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ)) *
              allCharacterCriticalLineFourthIntegral q (2 * T) ≤
          Cκ * Real.log x0 ^ 4 *
              allCharacterCriticalLineFourthIntegral q (2 * T) := by
      exact mul_le_mul_of_nonneg_right hkernel hfamily
    have hconv :
        (∑ z ∈ S,
          perronConvolution (criticalLineLNorm z.1) T z.2 ^ 4) ≤
          Cκ * Real.log x0 ^ 4 *
            allCharacterCriticalLineFourthIntegral q (2 * T) :=
      hagg.trans hkernelFamily
    have hJrewrite :
        (∑ z ∈ S, J z ^ 4) = C₀ ^ 4 *
          ∑ z ∈ S,
            perronConvolution (criticalLineLNorm z.1) T z.2 ^ 4 := by
      dsimp [J]
      simp_rw [mul_pow]
      rw [Finset.mul_sum]
    have hnonnegRight : 0 ≤ Real.log x0 ^ 4 *
        allCharacterCriticalLineFourthIntegral q (2 * T) := by
      positivity
    calc
      (∑ z ∈ S, J z ^ 4) = C₀ ^ 4 *
          ∑ z ∈ S,
            perronConvolution (criticalLineLNorm z.1) T z.2 ^ 4 := hJrewrite
      _ ≤ C₀ ^ 4 *
          (Cκ * Real.log x0 ^ 4 *
            allCharacterCriticalLineFourthIntegral q (2 * T)) :=
        mul_le_mul_of_nonneg_left hconv (pow_nonneg hC₀.le 4)
      _ = (C₀ ^ 4 * Cκ) *
          (Real.log x0 ^ 4 *
            allCharacterCriticalLineFourthIntegral q (2 * T)) := by ring
      _ ≤ C₃₆ * (Real.log x0 ^ 4 *
          allCharacterCriticalLineFourthIntegral q (2 * T)) := by
        apply mul_le_mul_of_nonneg_right _ hnonnegRight
        dsimp [C₃₆]
        linarith [hC₀.le]
      _ = C₃₆ * Real.log x0 ^ 4 *
          allCharacterCriticalLineFourthIntegral q (2 * T) := by ring

/-- Consumer theorem for the fully descended BHP chain: the two remaining
analytic premises are exactly pointwise (3.36)/Rademacher and BHP Lemma 7's
Ramachandra mean value. -/
theorem mrtLemma211_of_perronRademacher_and_ramachandraMeanValue
    (hperron : BHPEquation336PerronRademacher)
    (hmean : BHPLemma7RamachandraAllCharacterMeanValue) :
    MRTLemma211AllCharacterFourthMoment :=
  mrtLemma211_of_bhpEquation336_and_ramachandraMeanValue
    (bhpEquation336AndHolderReduction_of_perronRademacher hperron) hmean


end
end MAPMRTLemma211AllCharacterSource

#print axioms MAPMRTLemma211AllCharacterSource.mrtLemma211_of_allCharacterFourthMoment
#print axioms MAPMRTLemma211AllCharacterSource.allCharacterSampledPieces_to_annulus_rhs
#print axioms MAPMRTLemma211AllCharacterSource.fourth_power_sum_four_le
#print axioms MAPMRTLemma211AllCharacterSource.selectedPrefixFourthMass_le_equation336
#print axioms MAPMRTLemma211AllCharacterSource.bhpLemma9ContinuousReduction_of_equation336AndHolder
#print axioms MAPMRTLemma211AllCharacterSource.bhpLemma7_doubledHeight
#print axioms MAPMRTLemma211AllCharacterSource.mrtLemma211_of_bhpEquation336_and_ramachandraMeanValue
#print axioms MAPMRTLemma211AllCharacterSource.sum_perronConvolution_fourth_le_exactKernel
#print axioms MAPMRTLemma211AllCharacterSource.perronHolderKernel_le_log_four
#print axioms MAPMRTLemma211AllCharacterSource.bhpEquation336AndHolderReduction_of_perronRademacher
#print axioms MAPMRTLemma211AllCharacterSource.mrtLemma211_of_perronRademacher_and_ramachandraMeanValue
