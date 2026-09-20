import MRTLemma211AllCharacterSource
import BHPAllCharacterDyadicBudget

/-!
# BHP Lemma 7 from Ramachandra's literal contour pieces

Ramachandra Lemma 3 does not produce a finite approximate functional equation.
It writes `L(1/2+it,chi)^2` as a smoothed direct series minus two continuous
Mellin integrals `I₁` and `I₂`, plus the small principal residue.  Lemmas
4--6 bound the second moments of those three literal pieces after truncating
and dyadically decomposing inside the proof.

The primary source interface below retains that continuous Mellin variable and
also keeps the exact primitive-character and missing-Euler-factor provenance.
Its source obligation consists only of the contour identity, the small
remainder, and the piecewise second-moment budgets.  It has no fourth-moment
conclusion.  The finite dyadic object at the end of the file is retained only
as a secondary adapter for any independently proved Mellin-to-finite
reduction; it is not attributed directly to Ramachandra's paper.
-/

namespace BHPRamachandraMeanValueFromDyadicAFE

open scoped BigOperators LSeries.notation
open BHPAllCharacterDyadicBudget
open MAPMRTLemma211AllCharacterSource
open CGLProofDAG
open Complex MeasureTheory

noncomputable section

/-! ## Literal source pieces from Ramachandra Lemma 3 -/

/-- The critical-line point used in the source formulas. -/
def ramachandraCriticalPoint (t : ℝ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + t * I

/-- The coefficient `chi(n) d(n)` of `L(s,chi)^2`. -/
def ramachandraDivisorCoeff {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  chi (n : ZMod q) * (orderedDivisorCount 2 n : ℂ)

/-- Ramachandra's smoothed direct series `S(s)`. -/
def ramachandraSmoothedDirect {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X t : ℝ) : ℂ :=
  ∑' n : ℕ,
    LSeries.term (ramachandraDivisorCoeff chi) (ramachandraCriticalPoint t) n *
      (Real.exp (-((n : ℝ) / X)) : ℂ)

/-- The ordinary primitive functional-equation multiplier in the orientation
`L(z,chi) = psi(z,chi) L(1-z,chi⁻¹)`. -/
def ramachandraFunctionalFactor {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  (q : ℂ) ^ (1 / 2 - z) * chi.rootNumber *
    chi⁻¹.gammaFactor (1 - z) / chi.gammaFactor z

/-- One reflected coefficient from `L(1-z,chi⁻¹)^2`. -/
def ramachandraReflectedTerm {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (z : ℂ) (n : ℕ) : ℂ :=
  LSeries.term (ramachandraDivisorCoeff chi⁻¹) (1 - z) n

/-- The `n > X` reflected series used in `I₁`. -/
def ramachandraReflectedTail {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, if X < n then ramachandraReflectedTerm chi z n else 0

/-- The `n ≤ X` reflected series used in `I₂`. -/
def ramachandraReflectedHead {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, if (n : ℝ) ≤ X then ramachandraReflectedTerm chi z n else 0

/-- The exact vertical integrand in Ramachandra's two reflected pieces. -/
def ramachandraContourIntegrand {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X u t v : ℝ) (tail : Bool) : ℂ :=
  let w : ℂ := (u : ℂ) + v * I
  let z : ℂ := ramachandraCriticalPoint t + w
  ramachandraFunctionalFactor chi z ^ 2 *
    (if tail then ramachandraReflectedTail chi X z
      else ramachandraReflectedHead chi X z) *
    Complex.Gamma w * (X : ℂ) ^ w

/-- Ramachandra's `1/(2*pi*i)` contour integral after writing `dw = i dv`. -/
def ramachandraContourPiece {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X u t : ℝ) (tail : Bool) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ v : ℝ, ramachandraContourIntegrand chi X u t v tail

/-- The source scale `X = conductor(chi) * U` after passage to the primitive
character inducing an ambient character. -/
def ramachandraPrimitiveScale {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (U : ℝ) : ℝ :=
  (chi.conductor : ℝ) * U

def ramachandraPrimitiveDirect {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (U t : ℝ) : ℂ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact ramachandraSmoothedDirect chi.primitiveCharacter
    (ramachandraPrimitiveScale chi U) t

def ramachandraPrimitiveLongContour {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (U t : ℝ) : ℂ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact ramachandraContourPiece chi.primitiveCharacter
    (ramachandraPrimitiveScale chi U) (-3 / 4) t true

def ramachandraPrimitiveShortContour {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (U t : ℝ) : ℂ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact ramachandraContourPiece chi.primitiveCharacter
    (ramachandraPrimitiveScale chi U)
    (-(Real.log (ramachandraPrimitiveScale chi U))⁻¹) t false

/-- The exact finite Euler correction relating an ambient character to its
primitive inducer. -/
def ramachandraEulerCorrection {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) : ℂ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact ∏ p ∈ q.primeFactors,
    (1 - chi.primitiveCharacter p *
      (p : ℂ) ^ (-ramachandraCriticalPoint t))

/-- The three literal source pieces after restoring the ambient character.
The Euler correction is squared because Lemma 3 is applied to `L^2`. -/
def ramachandraAmbientDirect {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (U t : ℝ) : ℂ :=
  ramachandraEulerCorrection chi t ^ 2 *
    ramachandraPrimitiveDirect chi U t

def ramachandraAmbientLongContour {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (U t : ℝ) : ℂ :=
  ramachandraEulerCorrection chi t ^ 2 *
    ramachandraPrimitiveLongContour chi U t

def ramachandraAmbientShortContour {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (U t : ℝ) : ℂ :=
  ramachandraEulerCorrection chi t ^ 2 *
    ramachandraPrimitiveShortContour chi U t

/-- Sum of the four second-moment pieces.  This is the lower quantity bounded
by Ramachandra Lemmas 4--6; it is not a fourth moment. -/
def ramachandraPieceEnergy {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (U t : ℝ)
    (remainder : DirichletCharacter ℂ q → ℝ → ℂ) : ℝ :=
  ‖ramachandraAmbientDirect chi U t‖ ^ 2 +
    ‖ramachandraAmbientLongContour chi U t‖ ^ 2 +
    ‖ramachandraAmbientShortContour chi U t‖ ^ 2 +
    ‖remainder chi t‖ ^ 2

theorem four_term_sq_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

/-- Deterministic Cauchy step from Ramachandra's literal decomposition to the
sum of the four source second moments. -/
theorem criticalLineLFourth_le_ramachandraPieceEnergy
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (U t : ℝ) (remainder : DirichletCharacter ℂ q → ℝ → ℂ)
    (hdecomp :
      DirichletCharacter.LFunction chi (ramachandraCriticalPoint t) ^ 2 =
        ramachandraAmbientDirect chi U t -
          ramachandraAmbientLongContour chi U t -
          ramachandraAmbientShortContour chi U t + remainder chi t) :
    criticalLineLFourth chi t ≤
      4 * ramachandraPieceEnergy chi U t remainder := by
  let z := DirichletCharacter.LFunction chi (ramachandraCriticalPoint t)
  let s := ramachandraAmbientDirect chi U t
  let i₁ := ramachandraAmbientLongContour chi U t
  let i₂ := ramachandraAmbientShortContour chi U t
  let e := remainder chi t
  have hnorm : ‖z ^ 2‖ ≤ ‖s‖ + ‖i₁‖ + ‖i₂‖ + ‖e‖ := by
    rw [show z ^ 2 = s - i₁ - i₂ + e by
      simpa [z, s, i₁, i₂, e] using hdecomp]
    calc
      ‖s - i₁ - i₂ + e‖ ≤ ‖s - i₁ - i₂‖ + ‖e‖ := norm_add_le _ _
      _ ≤ (‖s - i₁‖ + ‖i₂‖) + ‖e‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ ((‖s‖ + ‖i₁‖) + ‖i₂‖) + ‖e‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = ‖s‖ + ‖i₁‖ + ‖i₂‖ + ‖e‖ := by ring
  have hsq : ‖z ^ 2‖ ^ 2 ≤
      (‖s‖ + ‖i₁‖ + ‖i₂‖ + ‖e‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
  calc
    criticalLineLFourth chi t = ‖z ^ 2‖ ^ 2 := by
      unfold criticalLineLFourth criticalLineLNorm
      change ‖z‖ ^ 4 = ‖z ^ 2‖ ^ 2
      rw [norm_pow]
      ring
    _ ≤ (‖s‖ + ‖i₁‖ + ‖i₂‖ + ‖e‖) ^ 2 := hsq
    _ ≤ 4 * (‖s‖ ^ 2 + ‖i₁‖ ^ 2 + ‖i₂‖ ^ 2 + ‖e‖ ^ 2) :=
      four_term_sq_le _ _ _ _
    _ = 4 * ramachandraPieceEnergy chi U t remainder := by
      simp [ramachandraPieceEnergy, s, i₁, i₂, e]

/-- The exact lower object left by Ramachandra Lemmas 3--6.  The functions in
the budgets are the explicit `S`, `I₁`, and `I₂` above.  The only witness
function is the paper's small principal-pole/truncation remainder, whose norm
is independently constrained. -/
structure RamachandraLiteralContourData
    (q : ℕ) [NeZero q] (U x0 C : ℝ) (B : ℕ) where
  remainder : DirichletCharacter ℂ q → ℝ → ℂ
  continuous_energy : ∀ chi,
    Continuous (fun t => ramachandraPieceEnergy chi U t remainder)
  decomposition : ∀ (chi : DirichletCharacter ℂ q) (t : ℝ), |t| ≤ U →
    DirichletCharacter.LFunction chi (ramachandraCriticalPoint t) ^ 2 =
      ramachandraAmbientDirect chi U t -
        ramachandraAmbientLongContour chi U t -
        ramachandraAmbientShortContour chi U t + remainder chi t
  remainder_small : ∀ (chi : DirichletCharacter ℂ q) (t : ℝ), |t| ≤ U →
    ‖remainder chi t‖ ≤ 1 / (((q : ℝ) * U) ^ 2)
  continuous_budget :
    (∑ chi : DirichletCharacter ℂ q,
      ∫ t in (-U)..U, ramachandraPieceEnergy chi U t remainder) ≤
        C * (q : ℝ) * U * Real.log x0 ^ B
  selected_budget : ∀ (chi : DirichletCharacter ℂ q) (W : Finset ℝ),
    OneSeparated W → (∀ t ∈ W, |t| ≤ U) →
    (∑ t ∈ W, ramachandraPieceEnergy chi U t remainder) ≤
      C * (q : ℝ) * U * Real.log x0 ^ B

theorem allCharacter_integral_le_of_literalContourData
    {q : ℕ} [NeZero q] {U x0 C : ℝ} {B : ℕ}
    (hU : 0 ≤ U) (data : RamachandraLiteralContourData q U x0 C B) :
    allCharacterCriticalLineFourthIntegral q U ≤
      4 * (C * (q : ℝ) * U * Real.log x0 ^ B) := by
  classical
  have hchi (chi : DirichletCharacter ℂ q) :
      (∫ t in (-U)..U, criticalLineLFourth chi t) ≤
      ∫ t in (-U)..U,
        4 * ramachandraPieceEnergy chi U t data.remainder := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (continuous_criticalLineLFourth chi).intervalIntegrable _ _
    · exact (continuous_const.mul
        (data.continuous_energy chi)).intervalIntegrable _ _
    · intro t ht
      exact criticalLineLFourth_le_ramachandraPieceEnergy
        chi U t data.remainder
          (data.decomposition chi t ((abs_le).2 ⟨by linarith [ht.1], ht.2⟩))
  calc
    allCharacterCriticalLineFourthIntegral q U ≤
        ∑ chi : DirichletCharacter ℂ q,
          ∫ t in (-U)..U,
            4 * ramachandraPieceEnergy chi U t data.remainder := by
      unfold allCharacterCriticalLineFourthIntegral
      exact Finset.sum_le_sum fun chi _ => hchi chi
    _ = 4 * (∑ chi : DirichletCharacter ℂ q,
          ∫ t in (-U)..U,
            ramachandraPieceEnergy chi U t data.remainder) := by
      simp_rw [intervalIntegral.integral_const_mul]
      rw [Finset.mul_sum]
    _ ≤ 4 * (C * (q : ℝ) * U * Real.log x0 ^ B) :=
      mul_le_mul_of_nonneg_left data.continuous_budget (by norm_num)

theorem selected_fourth_le_of_literalContourData
    {q : ℕ} [NeZero q] {U x0 C : ℝ} {B : ℕ}
    (data : RamachandraLiteralContourData q U x0 C B)
    (chi : DirichletCharacter ℂ q) (W : Finset ℝ)
    (hsep : OneSeparated W) (hheight : ∀ t ∈ W, |t| ≤ U) :
    (∑ t ∈ W, criticalLineLFourth chi t) ≤
      4 * (C * (q : ℝ) * U * Real.log x0 ^ B) := by
  calc
    (∑ t ∈ W, criticalLineLFourth chi t) ≤
        ∑ t ∈ W,
          4 * ramachandraPieceEnergy chi U t data.remainder := by
      exact Finset.sum_le_sum fun t ht =>
        criticalLineLFourth_le_ramachandraPieceEnergy
          chi U t data.remainder (data.decomposition chi t (hheight t ht))
    _ = 4 * (∑ t ∈ W,
          ramachandraPieceEnergy chi U t data.remainder) := by
      rw [Finset.mul_sum]
    _ ≤ 4 * (C * (q : ℝ) * U * Real.log x0 ^ B) :=
      mul_le_mul_of_nonneg_left
        (data.selected_budget chi W hsep hheight) (by norm_num)

/-- Source-faithful form of Ramachandra Lemmas 3--6.  Unlike a
fourth-moment premise, it exposes the exact contour decomposition and the
second-moment budgets of its pieces. -/
def RamachandraLemmas3To6LiteralContour : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ,
    ∀ (q : ℕ) [NeZero q] (U x0 : ℝ),
      2 ≤ U → (q : ℝ) ≤ x0 → U ≤ x0 →
      Nonempty (RamachandraLiteralContourData q U x0 C B)

theorem bhpLemma7RamachandraAllCharacterMeanValue_of_literalContour
    (hsource : RamachandraLemmas3To6LiteralContour) :
    BHPLemma7RamachandraAllCharacterMeanValue := by
  obtain ⟨C, hC, B, hdata⟩ := hsource
  refine ⟨4 * C, by positivity, B, ?_⟩
  intro q _inst U x0 hU hqx hUx
  obtain ⟨data⟩ := hdata q U x0 hU hqx hUx
  calc
    allCharacterCriticalLineFourthIntegral q U ≤
        4 * (C * (q : ℝ) * U * Real.log x0 ^ B) :=
      allCharacter_integral_le_of_literalContourData (by linarith) data
    _ = (4 * C) * (q : ℝ) * U * Real.log x0 ^ B := by ring

/-! ## Secondary finite-family adapter -/

/-- A finite object which may be obtained only after an independent,
quantitative Mellin-to-finite reduction.

`dual=false` is the smoothed `chi(n)n^(-it)` sum and `dual=true` is the
functional-equation `conj(chi)(n)n^(+it)` sum.  The joint consumers only use
the source's aggregate length-energy budget, so no separate maximum-length
condition is imposed.  This retains the decay of long dual blocks instead of
replacing it by an unnecessary worst-case cutoff. -/
structure RamachandraSquaredDyadicAFEData
    (q : ℕ) [NeZero q] (U x0 C : ℝ) (B : ℕ) where
  J : ℕ
  dual : Fin J → Bool
  N : Fin J → ℕ
  b : Fin J → ℕ → ℂ
  A : ℝ
  A_nonneg : 0 ≤ A
  block_nonempty : ∀ j, 1 ≤ N j
  pointwise : ∀ (chi : DirichletCharacter ℂ q) (t : ℝ), |t| ≤ U →
    criticalLineLFourth chi t ≤
      A * ramachandraDyadicFamily dual N b chi t
  aggregate_budget :
    A * ramachandraDyadicFamilyCost q U N b ≤
      C * (q : ℝ) * U * Real.log x0 ^ B

/-- Secondary finite-family source contract.  This is useful if a separate
quadrature or finite-rank theorem is proved, but it is not the literal output
of Ramachandra Lemmas 3--6. -/
def RamachandraLemma3To6AllCharacterDyadicAFE : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ,
    ∀ (q : ℕ) [NeZero q] (U x0 : ℝ),
      2 ≤ U → (q : ℝ) ≤ x0 → U ≤ x0 →
      Nonempty (RamachandraSquaredDyadicAFEData q U x0 C B)

/-- Once the literal dyadic AFE object is constructed, BHP Lemma 7 follows
from certified character orthogonality, the finite logarithmic Hilbert
inequality, and finite sum/integral interchange. -/
theorem bhpLemma7RamachandraAllCharacterMeanValue_of_dyadicAFE
    (hAFE : RamachandraLemma3To6AllCharacterDyadicAFE) :
    BHPLemma7RamachandraAllCharacterMeanValue := by
  obtain ⟨C, hC, B, hsource⟩ := hAFE
  refine ⟨C, hC, B, ?_⟩
  intro q _inst U x0 hU hqx hUx
  obtain ⟨data⟩ := hsource q U x0 hU hqx hUx
  have hU0 : 0 ≤ U := by linarith
  have hcore := allCharacter_integral_le_ramachandraDyadicFamilyCost
    (q := q) hU0 data.A_nonneg data.dual data.N data.b
    (fun chi t => criticalLineLFourth chi t)
    continuous_criticalLineLFourth data.block_nonempty data.pointwise
  exact hcore.trans data.aggregate_budget

/-- Shared consumer for the MRT hard range and the far HB/Perron branch.  The
Perron/Rademacher premise is independent; the BHP mean-value premise has been
replaced by the lower literal dyadic AFE object. -/
theorem mrtLemma211_of_perronRademacher_and_ramachandraDyadicAFE
    (hperron : BHPEquation336PerronRademacher)
    (hAFE : RamachandraLemma3To6AllCharacterDyadicAFE) :
    MRTLemma211AllCharacterFourthMoment :=
  mrtLemma211_of_perronRademacher_and_ramachandraMeanValue hperron
    (bhpLemma7RamachandraAllCharacterMeanValue_of_dyadicAFE hAFE)

/-- Preferred source-faithful route from Ramachandra's continuous contour
pieces to the MRT hard-range fourth moment. -/
theorem mrtLemma211_of_perronRademacher_and_ramachandraLiteralContour
    (hperron : BHPEquation336PerronRademacher)
    (hsource : RamachandraLemmas3To6LiteralContour) :
    MRTLemma211AllCharacterFourthMoment :=
  mrtLemma211_of_perronRademacher_and_ramachandraMeanValue hperron
    (bhpLemma7RamachandraAllCharacterMeanValue_of_literalContour hsource)

end
end BHPRamachandraMeanValueFromDyadicAFE

#print axioms BHPRamachandraMeanValueFromDyadicAFE.bhpLemma7RamachandraAllCharacterMeanValue_of_dyadicAFE
#print axioms BHPRamachandraMeanValueFromDyadicAFE.mrtLemma211_of_perronRademacher_and_ramachandraDyadicAFE
#print axioms BHPRamachandraMeanValueFromDyadicAFE.criticalLineLFourth_le_ramachandraPieceEnergy
#print axioms BHPRamachandraMeanValueFromDyadicAFE.allCharacter_integral_le_of_literalContourData
#print axioms BHPRamachandraMeanValueFromDyadicAFE.selected_fourth_le_of_literalContourData
#print axioms BHPRamachandraMeanValueFromDyadicAFE.bhpLemma7RamachandraAllCharacterMeanValue_of_literalContour
#print axioms BHPRamachandraMeanValueFromDyadicAFE.mrtLemma211_of_perronRademacher_and_ramachandraLiteralContour
