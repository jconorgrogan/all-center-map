import GuthMaynardS2Source
import CGLDetectorSourceFaithfulLargeValue

/-!
# Exact Heath--Brown interface used by the Guth--Maynard `S₂` branch

Guth--Maynard Section 6 applies Heath--Brown's Theorem 1.6 to a polynomial on
a difference set.  This file records the literal finite object and the exact
spacing/interval hypotheses.  It also proves the specialization to the
zero-derived sample set produced by the MAP detector.

The coefficient `aS2` below is deliberately distinct from the detector
coefficient `bDetector`.  By the time Section 6 is reached, the original
coefficient has disappeared into the singular-value trace; `aS2` is produced
by the reflection formula and the subsequent powering step.  Conflating the
two would not be source-faithful.

`HeathBrownTheorem16` is an interface for a published analytic theorem, not a
Lean proof of that theorem.  Every theorem after that interface is proved in
Lean, but a fully self-contained certification must still formalize
Heath--Brown's proof (and Guth--Maynard Lemma 6.2) rather than merely assume the
interface.
-/

namespace GuthMaynardHeathBrownInterface

open scoped BigOperators
open CGLProofDAG GuthMaynardSource
open CGLDetectorSourceFaithfulLargeValue

noncomputable section

/-! ## Literal difference-set quadratic form -/

/-- The polynomial in Heath--Brown Theorem 1.6, with the two endpoints exactly
as printed in the source. -/
noncomputable def differencePolynomial
    (a : ℕ → ℂ) (M : ℕ) (t u : ℝ) : ℂ :=
  displayedDirichletPolynomial a M (t - u)

/-- The nonnegative quadratic form in differences of the sampling ordinates.
This is the left side of Heath--Brown Theorem 1.6 and Guth--Maynard (6.3). -/
noncomputable def differenceQuadraticForm
    (a : ℕ → ℂ) (M : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ t ∈ W, ∑ u ∈ W, ‖differencePolynomial a M t u‖ ^ 2

/-- A finite set is contained in some closed interval of length `T`.  The
left endpoint is allowed to be arbitrary, exactly as in Theorem 1.6. -/
def ContainedInIntervalOfLength (W : Finset ℝ) (T : ℝ) : Prop :=
  ∃ x : ℝ, ∀ t ∈ W, x ≤ t ∧ t ≤ x + T

theorem differenceQuadraticForm_nonneg
    (a : ℕ → ℂ) (M : ℕ) (W : Finset ℝ) :
    0 ≤ differenceQuadraticForm a M W := by
  unfold differenceQuadraticForm
  positivity

/-- The project convention `W ⊆ [0,T]` is a literal interval-of-length-`T`
hypothesis, with no loss of aperture. -/
theorem containedInIntervalOfLength_zero
    {W : Finset ℝ} {T : ℝ}
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T) :
    ContainedInIntervalOfLength W T := by
  refine ⟨0, ?_⟩
  intro t ht
  simpa using hheight t ht

/-- The difference polynomial is invariant under a common translation of its
two ordinates.  This is why the detector's sign-recentering does not alter the
Heath--Brown input. -/
theorem differencePolynomial_add_right
    (a : ℕ → ℂ) (M : ℕ) (t u c : ℝ) :
    differencePolynomial a M (t + c) (u + c) =
      differencePolynomial a M t u := by
  unfold differencePolynomial
  congr 1
  ring

/-! ## Published analytic leaf -/

/-- Epsilon-budget form of Heath--Brown, Theorem 1.6, as quoted by
Guth--Maynard.  The existential input exponent `delta` is the precise meaning
needed from the printed coefficient condition `|a_n| ≤ T^{o(1)}`; the output
loss is the requested `eta`.

This definition is intentionally uninhabited in this module.  It identifies
the published analytic leaf that remains to be proved for end-to-end Lean
certification. -/
def HeathBrownTheorem16 : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∃ delta C T₀ : ℝ,
      0 < delta ∧ 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (M : ℕ) (a : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 1 ≤ M →
        (∀ n ∈ Finset.Icc M (2 * M),
          ‖a n‖ ≤ Real.rpow T delta) →
        OneSeparated W →
        ContainedInIntervalOfLength W T →
        differenceQuadraticForm a M W ≤
          C * Real.rpow T eta *
            ((W.card : ℝ) ^ 2 * M +
              (W.card : ℝ) * (M : ℝ) ^ 2 +
              Real.rpow (W.card : ℝ) (5 / 4 : ℝ) *
                Real.rpow T (1 / 2 : ℝ) * M)

/-- Unit-bounded coefficients are a special case of the literal
`T^{o(1)}` coefficient ball. -/
theorem coefficient_le_rpow_of_le_one
    {T delta : ℝ} (hT : 1 ≤ T) (hdelta : 0 ≤ delta)
    {M : ℕ} {a : ℕ → ℂ}
    (ha : ∀ n ∈ Finset.Icc M (2 * M), ‖a n‖ ≤ 1) :
    ∀ n ∈ Finset.Icc M (2 * M), ‖a n‖ ≤ Real.rpow T delta := by
  intro n hn
  exact (ha n hn).trans (Real.one_le_rpow hT hdelta)

/-- Direct source specialization for the unit coefficient formulation quoted
inside Guth--Maynard Section 6.  No detector premise is involved here. -/
theorem unitCoefficient_differenceMeanSquare_of_heathBrown
    (hHB : HeathBrownTheorem16) {eta : ℝ} (heta : 0 < eta) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (M : ℕ) (a : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 1 ≤ M →
        (∀ n ∈ Finset.Icc M (2 * M), ‖a n‖ ≤ 1) →
        OneSeparated W →
        ContainedInIntervalOfLength W T →
        differenceQuadraticForm a M W ≤
          C * Real.rpow T eta *
            ((W.card : ℝ) ^ 2 * M +
              (W.card : ℝ) * (M : ℝ) ^ 2 +
              Real.rpow (W.card : ℝ) (5 / 4 : ℝ) *
                Real.rpow T (1 / 2 : ℝ) * M) := by
  obtain ⟨delta, C, T₀, hdelta, hC, hT₀, hbound⟩ := hHB eta heta
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T M a W hT hM ha hsep hinterval
  apply hbound T M a W hT hM
  · apply coefficient_le_rpow_of_le_one
    · linarith
    · exact hdelta.le
    · exact ha
  · exact hsep
  · exact hinterval

/-! ## Source-faithful detector specialization -/

/-- Heath--Brown's difference-set estimate on the literal recentered sample
set produced by the MAP detector.  The hypothesis `hsource` keeps the common
zero source and detector coefficient in the statement, while the proof makes
the source fact transparent: only the one-spacing and `[0,T]` consequences
enter Theorem 1.6.  The internal coefficient `aS2` remains the reflected S2
coefficient, not `bDetector`.

This theorem does not certify Heath--Brown's analytic proof: it is a proved
adapter from the exact published interface to the exact detector surface. -/
theorem projectScaleDetector_differenceMeanSquare_of_heathBrown
    (hHB : HeathBrownTheorem16) {eta : ℝ} (heta : 0 < eta) :
    ∃ delta C T₀ : ℝ,
      0 < delta ∧ 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
        (kappa h Kd e T sigma : ℝ) (Z : Finset ℂ)
        (D M : ℕ) (bDetector aS2 : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 1 ≤ M →
        (∀ n ∈ Finset.Icc M (2 * M),
          ‖aS2 n‖ ≤ Real.rpow T delta) →
        OneSeparated W →
        (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
        IsProjectScaleLiteralTypeIOutcome
          chi kappa h Kd e T sigma Z D bDetector W →
        differenceQuadraticForm aS2 M W ≤
          C * Real.rpow T eta *
            ((W.card : ℝ) ^ 2 * M +
              (W.card : ℝ) * (M : ℝ) ^ 2 +
              Real.rpow (W.card : ℝ) (5 / 4 : ℝ) *
                Real.rpow T (1 / 2 : ℝ) * M) := by
  obtain ⟨delta, C, T₀, hdelta, hC, hT₀, hbound⟩ := hHB eta heta
  refine ⟨delta, C, T₀, hdelta, hC, hT₀, ?_⟩
  intro q _inst chi kappa h Kd e T sigma Z D M bDetector aS2 W
    hT hM ha hsep hheight _hsource
  exact hbound T M aS2 W hT hM ha hsep
    (containedInIntervalOfLength_zero hheight)

end

end GuthMaynardHeathBrownInterface

#print axioms GuthMaynardHeathBrownInterface.differenceQuadraticForm_nonneg
#print axioms GuthMaynardHeathBrownInterface.containedInIntervalOfLength_zero
#print axioms GuthMaynardHeathBrownInterface.differencePolynomial_add_right
#print axioms GuthMaynardHeathBrownInterface.coefficient_le_rpow_of_le_one
#print axioms GuthMaynardHeathBrownInterface.unitCoefficient_differenceMeanSquare_of_heathBrown
#print axioms GuthMaynardHeathBrownInterface.projectScaleDetector_differenceMeanSquare_of_heathBrown
