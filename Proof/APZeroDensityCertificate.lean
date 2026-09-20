import APFoundation
import ZeroDensityInterface
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Honest certification boundary for the MAP arithmetic-progression input

This module fixes the exact propositions that a full Palomar certificate must
eventually inhabit.  It also proves the finite, divisor-backed reductions that
mathlib supports today.  The density estimate and the short-interval prime
number theorem are definitions of propositions, not axioms and not theorems.
-/

namespace MAPAPZeroDensityCert

open MeasureTheory Set
open scoped BigOperators ENNReal ArithmeticFunction

noncomputable section

open APFoundation ZeroDensityArithmetic DirichletZeros ZeroDensityInterface

/-! ## Exact Palomar-facing propositions -/

/--
The appendix's polylogarithmic-conductor density statement, phrased using the
literal divisor-backed primitive zero count.  `Q` is a natural cutoff, and the
sum contains every ambient character at every positive level at most `Q`.
-/
def zeroCountAtLevel (q : ℕ) (σ T : ℝ) : ℕ :=
  if hq : q = 0 then 0
  else
    letI : NeZero q := ⟨hq⟩
    ∑ χ : DirichletCharacter ℂ q, primitiveDirichletZeroCount χ σ T

def polylogFamilyZeroCount (Q : ℕ) (σ T : ℝ) : ℕ :=
  ∑ q ∈ Finset.Icc 1 Q, zeroCountAtLevel q σ T

/-- Ambient-character zero count in one positive level, matching equation
`(A.1)` before reduction to primitive inducers. -/
def ambientZeroCountAtLevel (q : ℕ) (σ T : ℝ) : ℕ :=
  if hq : q = 0 then 0
  else
    letI : NeZero q := ⟨hq⟩
    ∑ χ : DirichletCharacter ℂ q, dirichletZeroCount χ σ T

def ambientPolylogFamilyZeroCount (Q : ℕ) (σ T : ℝ) : ℕ :=
  ∑ q ∈ Finset.Icc 1 Q, ambientZeroCountAtLevel q σ T

/-- Equation `(A.1)` of the appendix, with its literal ambient-character
divisors and multiplicities. -/
def AppendixPolylogConductorDensity : Prop :=
  ∀ K δ η : ℝ, 0 < K → 0 < δ → 0 < η →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (Q : ℕ) (σ : ℝ), T₀ ≤ T →
        (Q : ℝ) ≤ Real.rpow (Real.log T) K →
        1 / 2 + δ ≤ σ → σ ≤ 4 / 5 →
        (ambientPolylogFamilyZeroCount Q σ T : ℝ) ≤
          C * Real.rpow T (uniformCoeff * (1 - σ) + η)

/-- The reduced `30/13` density input required by the compact-strip AP proof,
after replacing each ambient character by its primitive inducer. -/
def PolylogConductorDensity : Prop :=
  ∀ K δ η : ℝ, 0 < K → 0 < δ → 0 < η →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (Q : ℕ) (σ : ℝ), T₀ ≤ T →
        (Q : ℝ) ≤ Real.rpow (Real.log T) K →
        1 / 2 + δ ≤ σ → σ ≤ 4 / 5 →
        (polylogFamilyZeroCount Q σ T : ℝ) ≤
          C * Real.rpow T (uniformCoeff * (1 - σ) + η)

/--
The exact simultaneous short-interval AP proposition used in the MAP collars.
This alias makes the Palomar goal explicit without asserting it.
-/
def SimultaneousShortIntervalAP : Prop :=
  APFoundation.SimultaneousShortIntervalAP

/-- Proposition 2.4 exactly as quantified in the paper, with no artificial
upper bound on `ε`. -/
def PaperSimultaneousShortIntervalAP : Prop :=
  ∀ K D ε : ℝ, 0 < K → 0 < D → 0 < ε →
    ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        (∫⁻ x in Set.Icc (X / 2) (4 * X), simultaneousAPMax K ε X x) ≤
          ENNReal.ofReal (C * X * Real.rpow (Real.log X) (-D))

/-! ## Divisor support really is the zero set -/

variable {q : ℕ} [NeZero q]

/-- The regularized Dirichlet L-function is not identically zero: it is
nonzero at `s = 1` in both the principal and nonprincipal cases. -/
theorem regularizedLFunction_one_ne_zero (χ : DirichletCharacter ℂ q) :
    regularizedLFunction χ 1 ≠ 0 := by
  classical
  by_cases hχ : χ = 1
  · simp only [regularizedLFunction, if_pos hχ]
    exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
  · simp only [regularizedLFunction, if_neg hχ]
    exact DirichletCharacter.LFunction_apply_one_ne_zero hχ

/-- Inside the counting rectangle, divisor support is equivalent to literal
vanishing of the regularized Dirichlet L-function. -/
theorem mem_zeroSupport_iff_eq_zero (χ : DirichletCharacter ℂ q)
    (σ T : ℝ) {ρ : ℂ} (hρ : ρ ∈ zeroRectangle σ T) :
    ρ ∈ zeroSupport χ σ T ↔ regularizedLFunction χ ρ = 0 := by
  constructor
  · exact regularizedLFunction_eq_zero_of_mem_zeroSupport χ σ T
  · intro hz
    rw [zeroSupport_mem_iff, zeroDivisor_apply_of_mem χ σ T hρ]
    intro hdiv
    have hone : meromorphicOrderAt (regularizedLFunction χ) 1 = 0 :=
      ((differentiable_regularizedLFunction χ).analyticAt 1).meromorphicNFAt
        |>.meromorphicOrderAt_eq_zero_iff.mpr
          (regularizedLFunction_one_ne_zero χ)
    have hfinite : meromorphicOrderAt (regularizedLFunction χ) ρ ≠ ⊤ :=
      (meromorphicOn_regularizedLFunction χ Set.univ)
        |>.meromorphicOrderAt_ne_top_of_isPreconnected
          isPreconnected_univ (Set.mem_univ 1) (Set.mem_univ ρ) (by simp [hone])
    have hord : meromorphicOrderAt (regularizedLFunction χ) ρ = 0 := by
      calc
        meromorphicOrderAt (regularizedLFunction χ) ρ =
            ((meromorphicOrderAt (regularizedLFunction χ) ρ).untop₀ : ℤ) :=
          (WithTop.coe_untop₀_of_ne_top hfinite).symm
        _ = 0 := by rw [hdiv]; simp
    have hne : regularizedLFunction χ ρ ≠ 0 :=
      ((differentiable_regularizedLFunction χ).analyticAt ρ).meromorphicNFAt
        |>.meromorphicOrderAt_eq_zero_iff.mp hord
    exact hne hz

/-- Every supported zero has strictly positive analytic multiplicity. -/
theorem zeroMultiplicity_pos_of_mem (χ : DirichletCharacter ℂ q)
    (σ T : ℝ) {ρ : ℂ} (hρ : ρ ∈ zeroSupport χ σ T) :
    0 < zeroMultiplicity χ σ T ρ := by
  have hne : zeroDivisor χ σ T ρ ≠ 0 :=
    (zeroSupport_mem_iff χ σ T ρ).mp hρ
  have hrect : ρ ∈ zeroRectangle σ T :=
    (zeroDivisor χ σ T).supportWithinDomain hne
  have hnonneg : 0 ≤ zeroDivisor χ σ T ρ :=
    zeroDivisor_nonneg_of_mem χ σ T hrect
  have hpos : 0 < zeroDivisor χ σ T ρ := lt_of_le_of_ne hnonneg (Ne.symm hne)
  rw [← Int.ofNat_lt]
  simpa [zeroMultiplicity, Int.toNat_of_nonneg hnonneg] using hpos

/-! ## Finite family reductions -/

theorem zeroCountAtLevel_eq (σ T : ℝ) :
    zeroCountAtLevel q σ T =
      ∑ ψ : DirichletCharacter ℂ q, primitiveDirichletZeroCount ψ σ T := by
  simp [zeroCountAtLevel, NeZero.ne q]

/-- A single primitive-inducer zero count is bounded by the full family sum. -/
theorem primitiveZeroCount_le_polylogFamilyZeroCount
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) {Q : ℕ} (hqQ : q ≤ Q) :
    primitiveDirichletZeroCount χ σ T ≤
      polylogFamilyZeroCount Q σ T := by
  unfold polylogFamilyZeroCount
  have hqpos : 1 ≤ q := NeZero.pos q
  calc
    primitiveDirichletZeroCount χ σ T ≤ zeroCountAtLevel q σ T := by
      rw [zeroCountAtLevel_eq (q := q) σ T]
      exact Finset.single_le_sum
        (f := fun ψ : DirichletCharacter ℂ q =>
          primitiveDirichletZeroCount ψ σ T) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ χ)
    _ ≤ ∑ r ∈ Finset.Icc 1 Q, zeroCountAtLevel r σ T := by
      exact Finset.single_le_sum
        (f := fun r => zeroCountAtLevel r σ T) (fun _ _ => Nat.zero_le _)
        (Finset.mem_Icc.mpr ⟨hqpos, hqQ⟩)

/-- The family density proposition yields its fixed-character consequence
without a hidden character-family axiom. -/
theorem PolylogConductorDensity.fixedCharacter
    (hDensity : PolylogConductorDensity)
    (K δ η : ℝ) (hK : 0 < K) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (Q : ℕ) (σ : ℝ), T₀ ≤ T →
        (Q : ℝ) ≤ Real.rpow (Real.log T) K →
        1 / 2 + δ ≤ σ → σ ≤ 4 / 5 →
        ∀ {r : ℕ} [NeZero r], r ≤ Q →
          ∀ χ : DirichletCharacter ℂ r,
            (primitiveDirichletZeroCount χ σ T : ℝ) ≤
              C * Real.rpow T (uniformCoeff * (1 - σ) + η) := by
  obtain ⟨C, T₀, hC, hT₀, hfamily⟩ := hDensity K δ η hK hδ hη
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T Q σ hT hQ hσlow hσhigh r _ hrQ χ
  have hone : (primitiveDirichletZeroCount χ σ T : ℝ) ≤
      (polylogFamilyZeroCount Q σ T : ℝ) := by
    exact_mod_cast primitiveZeroCount_le_polylogFamilyZeroCount χ σ T hrQ
  exact hone.trans (hfamily T Q σ hT hQ hσlow hσhigh)

/-! ## What the maximal AP proposition immediately controls -/

/-- Any one legal modulus/residue/aperture error is pointwise below the
simultaneous maximum appearing under the integral. -/
theorem individualAPError_le_simultaneousAPMax
    {K ε X x : ℝ} {q a : ℕ} {Y : ℝ}
    (hqpos : 1 ≤ q)
    (hqcap : (q : ℝ) ≤ Real.rpow (Real.log X) K)
    (haq : a < q) (ha : a.Coprime q)
    (hYlow : Real.rpow X (2 / 15 + ε) ≤ Y) (hYhigh : Y ≤ X) :
    ENNReal.ofReal |normalizedAPError x Y q a| ^ 2 ≤
      simultaneousAPMax K ε X x := by
  unfold simultaneousAPMax
  exact le_iSup_of_le q <| le_iSup_of_le hqpos <| le_iSup_of_le hqcap <|
    le_iSup_of_le a <| le_iSup_of_le haq <| le_iSup_of_le ha <|
      le_iSup_of_le Y <| le_iSup_of_le hYlow <| le_iSup_of_le hYhigh le_rfl

/-- Increasing the aperture exponent can only shrink the pointwise maximum. -/
theorem simultaneousAPMax_antitone_epsilon
    {K ε₀ ε₁ X x : ℝ} (hX : 1 ≤ X) (hε : ε₀ ≤ ε₁) :
    simultaneousAPMax K ε₁ X x ≤ simultaneousAPMax K ε₀ X x := by
  unfold simultaneousAPMax
  apply iSup_le
  intro q
  apply iSup_le
  intro hqpos
  apply iSup_le
  intro hqcap
  apply iSup_le
  intro a
  apply iSup_le
  intro haq
  apply iSup_le
  intro ha
  apply iSup_le
  intro Y
  apply iSup_le
  intro hYlow
  apply iSup_le
  intro hYhigh
  have hexp : 2 / 15 + ε₀ ≤ 2 / 15 + ε₁ := by linarith
  have hpow : Real.rpow X (2 / 15 + ε₀) ≤ Real.rpow X (2 / 15 + ε₁) :=
    Real.rpow_le_rpow_of_exponent_le hX hexp
  exact le_iSup_of_le q <| le_iSup_of_le hqpos <| le_iSup_of_le hqcap <|
    le_iSup_of_le a <| le_iSup_of_le haq <| le_iSup_of_le ha <|
      le_iSup_of_le Y <| le_iSup_of_le (hpow.trans hYlow) <|
        le_iSup_of_le hYhigh le_rfl

/-- The small-`ε` certification target used for exponent bookkeeping is
logically sufficient for the paper's all-positive-`ε` AP proposition. -/
theorem cappedAP_implies_paperAP
    (hAP : APFoundation.SimultaneousShortIntervalAP) :
    PaperSimultaneousShortIntervalAP := by
  intro K D ε hK hD hε
  let ε₀ : ℝ := min ε (1 / 10)
  have hε₀ : 0 < ε₀ := lt_min hε (by norm_num)
  have hε₀cap : ε₀ ≤ 13 / 30 := (min_le_right ε (1 / 10)).trans (by norm_num)
  obtain ⟨C, X₀, hC, hX₀, hbound⟩ := hAP K D ε₀ hK hD hε₀ hε₀cap
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X hXX₀
  have hX : 1 ≤ X := le_trans (by norm_num) (hX₀.trans hXX₀)
  calc
    (∫⁻ x in Set.Icc (X / 2) (4 * X), simultaneousAPMax K ε X x) ≤
        ∫⁻ x in Set.Icc (X / 2) (4 * X), simultaneousAPMax K ε₀ X x := by
      apply MeasureTheory.lintegral_mono
      intro x
      exact simultaneousAPMax_antitone_epsilon hX (min_le_left ε (1 / 10))
    _ ≤ ENNReal.ofReal (C * X * Real.rpow (Real.log X) (-D)) := hbound X hXX₀

end
end MAPAPZeroDensityCert
