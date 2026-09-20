import MAPFarCircleSourceWeld
import MAPFarRationalApproximation

/-!
# Honest source-to-padded/global weld for the MAP far branch

The deterministic rational selection and circle/source comparison are already
proved in the imported modules. This file exposes the exact remaining analytic
certificate: a literal source decomposition, componentwise padded dyadic cells,
and a bound for the fully expanded normalized expression.

A hostile normalization test is included: the abstract source contracts alone
admit error-absorption witnesses. Consequently no theorem in this file treats
mere existence of `SourceBranchDecomposition` or `SourceToPaddedDyadicCells` as
analytic progress. The expanded budget must be proved for source-faithful data.
-/

namespace MAPFarSourceWeldScaffold

open scoped BigOperators
open MeasureTheory
open MAPMRTCorollary53Source MAPMRTCorollary25Instantiation
open MAPFarAnnulusMRT MAPFarAnnulusSourceToModel
open MAPFarCircleSourceWeld MAPFarRationalApproximation
open MAPMajorArcWeld MAPAllCenterApertureTransfer MAPAllCenterNearFarTransfer
open PrimePairEndpoints

noncomputable section

/-! ## Hostile normalization / vacuity tests -/

/-- Every branch family satisfies `SourceToPaddedDyadicCells` if the complete
source mass is copied into the error and no cells are emitted. This theorem is
intentional: it proves that the abstract cell contract is only meaningful when
its errors and cell data are tied to the literal HB/Perron construction. -/
theorem sourceToPaddedDyadicCells_errorAbsorption
    (sourceMass : CutoffBranch → ℝ) :
    SourceToPaddedDyadicCells sourceMass sourceMass
      (fun _ => 0) (fun _ => 1) (fun _ => 1)
      (fun branch i => Fin.elim0 i)
      (fun _ _ _ => 0)
      (fun branch i _ _ => Fin.elim0 i)
      (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
  intro branch
  simp [SourceToPaddedDyadicCells]

/-- One literal component/factorization can be normalized into the padded-cell
interface with zero cells only by charging its entire mass to `cellError`.
This is the requested one-component death test; it creates no saving. -/
theorem oneComponentFactorization_zeroCell_normalization
    (X H beta eta : ℝ) (q₀ q₁ : ℕ) (f : ℕ → ℂ)
    (component : OuterComponent) :
    SourceToPaddedDyadicCells
      (fun branch => if branch = .typeD1 then
        componentIntegral X H q₀ q₁ f beta eta component else 0)
      (fun branch => if branch = .typeD1 then
        componentIntegral X H q₀ q₁ f beta eta component else 0)
      (fun _ => 0) (fun _ => 1) (fun _ => 1)
      (fun branch i => Fin.elim0 i)
      (fun _ _ _ => 0)
      (fun branch i _ _ => Fin.elim0 i)
      (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
  exact sourceToPaddedDyadicCells_errorAbsorption _

/-! ## Literal certificate data -/

/-- All arrays emitted by the source-faithful HB/Perron/dyadic construction for
one selected MRT input. The arrays are data, not conclusions. -/
structure LiteralPaddedSourceData (p : Corollary53Input) where
  decompositionError : OuterComponent → ℝ
  sourceMass : OuterComponent → FarSourceBranch → ℝ
  cellError : OuterComponent → CutoffBranch → ℝ
  blockCount : OuterComponent → CutoffBranch → ℕ
  q : OuterComponent → CutoffBranch → ℕ
  shortLength : OuterComponent → CutoffBranch → ℕ
  longLength : (component : OuterComponent) →
    (branch : CutoffBranch) → Fin (blockCount component branch) → ℕ
  beta : (component : OuterComponent) → (branch : CutoffBranch) →
    Fin (q component branch) → ℕ → ℂ
  g : (component : OuterComponent) → (branch : CutoffBranch) →
    Fin (blockCount component branch) → Fin (q component branch) → ℕ → ℂ
  a : OuterComponent → CutoffBranch → ℝ
  b : OuterComponent → CutoffBranch → ℝ
  U : OuterComponent → CutoffBranch → ℝ

/-- The complete expanded normalized expression after source decomposition and
padded-cell reduction, before applying the desired logarithmic budget. -/
def expandedPaddedSourceRHS
    (p : Corollary53Input) (d : LiteralPaddedSourceData p) : ℝ :=
  (divisorCount p.q : ℝ) ^ 4 /
      (p.q * stationaryWidth p.beta p.H ^ 2) *
    (nonCellSourceTotal d.decompositionError d.sourceMass +
      ∑ component : OuterComponent, ∑ branch : CutoffBranch,
        (d.cellError component branch +
          2 * blockwiseCharacterPairMixedMass
            (M := d.shortLength component branch)
            (d.longLength component branch) (d.beta component branch)
            (d.g component branch)
            ((d.a component branch + d.b component branch) / 2)
            ((d.b component branch - d.a component branch) +
              2 * d.U component branch) (d.U component branch))) +
    ordinaryError p.X p.H p.f p.beta p.eta

/-- Source-faithful local certificate. The first two fields are literal
construction identities/inequalities. The final field is the only global
analytic budget. It is deliberately stated for the expanded cells, not for
`stationaryMainTerm + ordinaryError`. -/
structure LiteralPaddedSourceCertificate
    (p : Corollary53Input) (budget : ℝ) where
  data : LiteralPaddedSourceData p
  sourceDecomposition :
    SourceBranchDecomposition p data.decompositionError data.sourceMass
  paddedCells : ∀ component,
    SourceToPaddedDyadicCells
      (fun branch => data.sourceMass component (.cutoff branch))
      (data.cellError component) (data.blockCount component) (data.q component)
      (data.shortLength component) (data.longLength component)
      (data.beta component) (data.g component)
      (data.a component) (data.b component) (data.U component)
  intervalOrder : ∀ component branch,
    data.a component branch ≤ data.b component branch
  widthNonneg : ∀ component branch, 0 ≤ data.U component branch
  expandedBudget : expandedPaddedSourceRHS p data ≤ budget

/-- A literal padded-source certificate implies the exact source RHS bound.
This is a noncircular wrapper around `sourceRHS_le_of_paddedCells`. -/
theorem sourceRHS_le_of_literalCertificate
    {p : Corollary53Input} {hq : 1 ≤ p.q} {budget : ℝ}
    (cert : LiteralPaddedSourceCertificate p budget) :
    stationaryMainTerm p.X p.H p.q p.f p.beta p.eta hq +
        ordinaryError p.X p.H p.f p.beta p.eta ≤ budget := by
  let d := cert.data
  apply sourceRHS_le_of_paddedCells
    (p := p) (decompositionError := d.decompositionError)
    (sourceMass := d.sourceMass) (cellError := d.cellError)
    (blockCount := d.blockCount) (q := d.q)
    (shortLength := d.shortLength) (longLength := d.longLength)
    (beta := d.beta) (g := d.g) (a := d.a) (b := d.b) (U := d.U)
  · exact cert.sourceDecomposition
  · exact cert.paddedCells
  · exact cert.intervalOrder
  · exact cert.widthNonneg
  · exact cert.expandedBudget

/-! ## Admissibility of the selected MAP input -/

/-- For `Q≥1`, the Dirichlet error `1/(qQ)` is at most the source parameter
`eta=1/sqrt Q`. -/
theorem inv_qQ_le_inv_sqrtQ
    {q : ℕ} {Q : ℝ} (hq : 1 ≤ q) (hQ : 1 ≤ Q) :
    1 / ((q : ℝ) * Q) ≤ 1 / Real.sqrt Q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hsqrtPos : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQpos
  have hsqrtLeQ : Real.sqrt Q ≤ Q := by
    have hs := Real.sq_sqrt hQpos.le
    nlinarith [Real.sqrt_nonneg Q]
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : Real.sqrt Q ≤ (q : ℝ) * Q := by
    calc
      Real.sqrt Q ≤ Q := hsqrtLeQ
      _ = 1 * Q := by ring
      _ ≤ (q : ℝ) * Q := mul_le_mul_of_nonneg_right hqOne hQpos.le
  exact one_div_le_one_div_of_le hsqrtPos hden

/-- The deterministic selected input is admissible with fixed hidden constants
`cBetaEta=cEta=1`. -/
theorem selectedMapInput_admissible_one
    {X H Q beta : ℝ} {q a Cc : ℕ}
    (hlog : 1 ≤ Real.log X)
    (hQ : 1 ≤ Q)
    (hH : 1 < H) (hHX : H ≤ X)
    (hq : 1 ≤ q) (ha : a.Coprime q)
    (hbeta : |beta| ≤ 1 / ((q : ℝ) * Q))
    (hfar : 2 * (Real.log X) ^ Cc < stationaryWidth beta H) :
    Corollary53Admissible 1 1
      (mapCorollary53Input X H q a beta (1 / Real.sqrt Q)) := by
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have heta : 0 < 1 / Real.sqrt Q := by positivity
  have hetaOne : 1 / Real.sqrt Q ≤ 1 := by
    have hsqrt : 1 ≤ Real.sqrt Q := by
      nlinarith [Real.sq_sqrt hQpos.le, Real.sqrt_nonneg Q]
    exact (div_le_one (by positivity : 0 < Real.sqrt Q)).2 hsqrt
  have hbetaEta : |beta| ≤ (1 : ℝ) * (1 / Real.sqrt Q) := by
    simpa using hbeta.trans (inv_qQ_le_inv_sqrtQ hq hQ)
  have hbetaNe : beta ≠ 0 := by
    intro hb
    subst beta
    simp [stationaryWidth] at hfar
    have hpow : 1 ≤ (Real.log X) ^ Cc := one_le_pow₀ hlog
    linarith
  exact mapCorollary53Input_admissible hH.le hHX hq ha heta hetaOne
    hbetaEta hetaOne hbetaNe

/-! ## Uniform analytic leaf and global constructor -/

/-- The sole remaining far-source analytic leaf after deterministic selection,
far-threshold geometry, admissibility, and circle/source comparison have been
removed. It must construct literal source data and prove the expanded budget.

The extra `D` is retained to match the public parameter package even though the
source branch itself does not use the minor-arc mask exponent. -/
def UniformLiteralPaddedFarBudget : Prop :=
  ∀ A epsilon : ℝ, 0 < A → 0 < epsilon →
    ∃ B D Cc : ℕ, ∃ Cred X₀ : ℝ,
      0 < Cred ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        1 ≤ Real.log X ∧
        1 < baseAperture epsilon X ∧
        baseAperture epsilon X ≤ X ∧
        ∀ q a : ℕ, ∀ beta : ℝ,
          let Q := (Real.log X) ^ B
          let H := baseAperture epsilon X
          let eta := 1 / Real.sqrt Q
          let p := mapCorollary53Input X H q a beta eta
          1 ≤ q → (q : ℝ) ≤ Q → a < q → a.Coprime q →
          |beta| ≤ 1 / ((q : ℝ) * Q) →
          2 * (Real.log X) ^ Cc < stationaryWidth beta H →
          Nonempty (LiteralPaddedSourceCertificate p
            (Cred * X * Real.rpow (Real.log X) (-A)))

/-- Fastest honest global weld. The only premise is the literal expanded
HB/Perron/padded-cell budget. No far-annulus conclusion or stationary RHS bound
is accepted as an assumption. -/
theorem mapFarSourceReduction_one_of_uniformLiteralPaddedFarBudget
    (hbudget : UniformLiteralPaddedFarBudget) :
    MAPFarSourceReduction 1 1 := by
  intro A epsilon hA hepsilon
  obtain ⟨B, D, Cc, Cred, X₀, hCred, hX₀, hlocal⟩ :=
    hbudget A epsilon hA hepsilon
  refine ⟨B, D, Cc, Cred, X₀, hCred, hX₀, ?_⟩
  intro X hXX₀
  obtain ⟨hlog, hHone, hHX, hcell⟩ := hlocal X hXX₀
  refine ⟨hlog, ?_⟩
  intro center houtside
  let Q := (Real.log X) ^ B
  let H := baseAperture epsilon X
  let eta := 1 / Real.sqrt Q
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact one_le_pow₀ hlog
  have hHpos : 0 < H := by dsimp [H]; linarith
  obtain ⟨q, a, beta, hq, hqQ, ha, hcop, hcenter, hbeta, hfar⟩ :=
    exists_far_reduced_rational_lift
      (Q := Q) (H := H) (B := B) (Cc := Cc)
      (epsilon := epsilon) (X := X) rfl rfl hQ hHpos center houtside
  refine ⟨q, a, beta, hq, hqQ, ha, hcop, hcenter, hbeta, hfar, ?_⟩
  let p := mapCorollary53Input X H q a beta eta
  have hp : Corollary53Admissible 1 1 p := by
    apply selectedMapInput_admissible_one hlog hQ hHone hHX hq hcop hbeta hfar
  refine ⟨hp, ?_, ?_⟩
  · have hcircle := centeredArc_primeEnergy_le_mapSourceEnergy
      (X := X) (H := H) (beta := beta) (eta := eta)
      (q := q) (a := a) hHone
    simpa [H, hcenter] using hcircle
  · have hcert : Nonempty (LiteralPaddedSourceCertificate p
        (Cred * X * Real.rpow (Real.log X) (-A))) := by
      simpa [p, Q, H, eta] using
        (hcell q a beta hq hqQ ha hcop hbeta hfar)
    obtain ⟨cert⟩ := hcert
    exact sourceRHS_le_of_literalCertificate (hq := hq) cert

end
end MAPFarSourceWeldScaffold

#print axioms MAPFarSourceWeldScaffold.sourceToPaddedDyadicCells_errorAbsorption
#print axioms MAPFarSourceWeldScaffold.oneComponentFactorization_zeroCell_normalization
#print axioms MAPFarSourceWeldScaffold.sourceRHS_le_of_literalCertificate
#print axioms MAPFarSourceWeldScaffold.mapFarSourceReduction_one_of_uniformLiteralPaddedFarBudget
