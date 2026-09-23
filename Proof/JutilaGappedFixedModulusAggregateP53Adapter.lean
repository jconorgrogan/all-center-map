import JutilaGappedCollarSelectedP53Adapter
import JutilaP53AggregateCorrelationLeaf

/-!
# Fixed-modulus aggregate p.53 source for the MAP collar

Jutila's equation (1.7) selects rows carrying both a character modulo one
fixed modulus and one of that character's zeros.  The analytic estimate is
therefore stated for a `Finset (JutilaP53Row q)`, not separately for every
fixed character.  This module records that source-faithful surface and proves
the deterministic restriction to the fixed-character selected system used by
the existing collar aggregation.

No p.53 estimate is asserted here.
-/

namespace MAPJutilaGappedFixedModulusAggregateP53Adapter

open DirichletZeros
open MAPJutilaCollarMeshCutoff MAPJutilaCollarA5Budget
open MAPJutilaGappedCollarFiniteAggregation
open MAPJutilaGappedCollarSelectedP53Adapter
open MAPJutilaP53AggregateCorrelationLeaf

noncomputable section

local instance characterDecidableEq (q : ℕ) :
    DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _

/-- The row selection in Jutila is separated inside each character fiber.
Rows belonging to different characters may have the same or nearby
ordinates; character orthogonality is part of the aggregate estimate. -/
def FiberwiseOneSeparated {q : ℕ} (rows : Finset (JutilaP53Row q)) : Prop :=
  ∀ chi : DirichletCharacter ℂ q,
    let fiber := rows.filter (fun row => row.character = chi)
    CGLProofDAG.OneSeparated (fiber.image (fun row => row.zero.im)) ∧
      (fiber.image (fun row => row.zero.im)).card = fiber.card

/-- Exact fixed-modulus nonprincipal p.53 source.  Every row retains its
character label.  Separation and ordinate injectivity are imposed only
inside each character fiber, as in the published hybrid row selection. -/
def JutilaGappedFixedModulusAggregateP53Eventually : Prop :=
  ∃ Cp R₀ : ℝ, 0 < Cp ∧ 6 ≤ R₀ ∧
    ∀ (q : ℕ) [NeZero q] (T sigma omega : ℝ)
      (rows : Finset (JutilaP53Row q)),
      1 ≤ T →
      279 / 280 ≤ sigma → sigma ≤ 1 →
      0 ≤ omega → omega ≤ 1 - sigma →
      R₀ ≤ (q : ℝ) * T →
      Real.log ((q : ℝ) * T) ≤
        Real.rpow ((q : ℝ) * T) (a5FiberGapBudget * omega) →
      (∀ row ∈ rows,
        row.character.IsPrimitive ∧
        row.character ≠ 1 ∧
        row.zero ∈ regularCollarSupport row.character sigma T ∧
        row.zero.re ≤ 1 - omega) →
      FiberwiseOneSeparated rows →
      (rows.card : ℝ) ≤ Cp * Real.rpow ((q : ℝ) * T)
        ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
          (1 - sigma))

/-- Embed a fixed-character zero system into the aggregate row type without
discarding either coordinate. -/
def fixedCharacterRowEmbedding {q : ℕ}
    (chi : DirichletCharacter ℂ q) : ℂ ↪ JutilaP53Row q where
  toFun rho := ⟨chi, rho⟩
  inj' := by
    intro rho₁ rho₂ h
    exact congrArg JutilaP53Row.zero h

/-- The aggregate row system associated with one fixed character. -/
def fixedCharacterRows {q : ℕ} (chi : DirichletCharacter ℂ q)
    (W : Finset ℂ) : Finset (JutilaP53Row q) :=
  W.map (fixedCharacterRowEmbedding chi)

theorem card_fixedCharacterRows {q : ℕ}
    (chi : DirichletCharacter ℂ q) (W : Finset ℂ) :
    (fixedCharacterRows chi W).card = W.card := by
  simp [fixedCharacterRows]

theorem image_im_fixedCharacterRows {q : ℕ}
    (chi : DirichletCharacter ℂ q) (W : Finset ℂ) :
    (fixedCharacterRows chi W).image (fun row => row.zero.im) =
      W.image Complex.im := by
  ext y
  simp [fixedCharacterRows, fixedCharacterRowEmbedding]
  rfl

theorem filter_fixedCharacterRows {q : ℕ}
    (chi psi : DirichletCharacter ℂ q) (W : Finset ℂ) :
    (fixedCharacterRows chi W).filter (fun row => row.character = psi) =
      if chi = psi then fixedCharacterRows chi W else ∅ := by
  by_cases h : chi = psi
  · subst psi
    simp [fixedCharacterRows, fixedCharacterRowEmbedding]
    intro rho hrho
    rfl
  · rw [if_neg h, Finset.filter_eq_empty_iff]
    intro row hrow
    rcases Finset.mem_map.mp hrow with ⟨rho, hrho, heq⟩
    intro hchar
    apply h
    calc
      chi = (fixedCharacterRowEmbedding chi rho).character := rfl
      _ = row.character := congrArg JutilaP53Row.character heq
      _ = psi := hchar

/-- Deterministic domination: the published fixed-modulus aggregate estimate
applies to the subset whose character coordinate is constant.  No sum over
all characters is introduced. -/
theorem jutilaGappedSelectedSystemP53_of_fixedModulusAggregate
    (haggregate : JutilaGappedFixedModulusAggregateP53Eventually) :
    JutilaGappedSelectedSystemP53Eventually := by
  obtain ⟨Cp, R₀, hCp, hR₀, haggregate⟩ := haggregate
  refine ⟨Cp, R₀, hCp, hR₀, ?_⟩
  intro q _inst chi T sigma omega W hprimitive hnonprincipal hT
    hsigmaLow hsigmaHigh homega hgap hscale hlogGap hregularGap
    hWsub hWsep hWcard
  let rows : Finset (JutilaP53Row q) := fixedCharacterRows chi W
  have hrowsData : ∀ row ∈ rows,
      row.character.IsPrimitive ∧
      row.character ≠ 1 ∧
      row.zero ∈ regularCollarSupport row.character sigma T ∧
      row.zero.re ≤ 1 - omega := by
    intro row hrow
    rcases Finset.mem_map.mp hrow with ⟨rho, hrho, hrow⟩
    subst row
    exact ⟨hprimitive, hnonprincipal, hWsub hrho,
      hregularGap rho (hWsub hrho)⟩
  have hrowsFiberwise : FiberwiseOneSeparated rows := by
    intro psi
    dsimp only
    rw [show rows.filter (fun row => row.character = psi) =
        if chi = psi then rows else ∅ by
      simpa [rows] using filter_fixedCharacterRows chi psi W]
    by_cases hpsi : chi = psi
    · simp only [hpsi, if_pos]
      constructor
      · simpa [rows, image_im_fixedCharacterRows] using hWsep
      · rw [show rows.image (fun row => row.zero.im) = W.image Complex.im by
          simpa [rows] using image_im_fixedCharacterRows chi W]
        rw [show rows.card = W.card by
          simpa [rows] using card_fixedCharacterRows chi W]
        exact hWcard
    · simp [hpsi, CGLProofDAG.OneSeparated]
  have hbound := haggregate q T sigma omega rows hT hsigmaLow hsigmaHigh
    homega hgap hscale hlogGap hrowsData hrowsFiberwise
  simpa [rows, card_fixedCharacterRows] using hbound

end

end MAPJutilaGappedFixedModulusAggregateP53Adapter

#print axioms MAPJutilaGappedFixedModulusAggregateP53Adapter.card_fixedCharacterRows
#print axioms MAPJutilaGappedFixedModulusAggregateP53Adapter.image_im_fixedCharacterRows
#print axioms MAPJutilaGappedFixedModulusAggregateP53Adapter.filter_fixedCharacterRows
#print axioms MAPJutilaGappedFixedModulusAggregateP53Adapter.jutilaGappedSelectedSystemP53_of_fixedModulusAggregate
