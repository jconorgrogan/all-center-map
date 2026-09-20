import RamachandraPrimitiveShiftedMellinReduction
import BHPRamachandraMeanValueFromDyadicAFE

/-!
# Literal shifted-contour reduction for Ramachandra Theorem 6

The proof of Theorem 6 on printed p. 88 says that its primitive shifted
estimate follows "in much the same way as Theorem 3".  This file spells out
the exact shifted analogues of the `S`, `I₁`, and `I₂` pieces from Lemma 3
and proves the deterministic passage from their second moments to the
primitive shifted fourth moment.

Nothing here assumes a fourth-moment conclusion.  The remaining analytic
leaves are the literal shifted contour identity and the separate second-moment
bounds for `S`, `I₁`, `I₂`, and the residue.  Those are precisely the omitted
"same proof" steps that must be reconstructed from Lemmas 3--6.
-/

namespace RamachandraPrimitiveShiftedContourReduction

open scoped BigOperators Interval LSeries.notation
open Complex MeasureTheory
open RamachandraTheorem6ShiftedStripSource
open RamachandraTheorem6SourceProofChain
open BHPRamachandraMeanValueFromDyadicAFE

noncomputable section

/-! ## Shifted versions of the three printed source pieces -/

/-- The point `s = sigma + i t` in the narrow strip of Theorem 6. -/
def ramachandraShiftedPoint (sigma t : ℝ) : ℂ :=
  (sigma : ℂ) + t * I

/-- The shifted direct series `S(s)` from Lemma 3. -/
def ramachandraShiftedDirect {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (X sigma t : ℝ) : ℂ :=
  ∑' n : ℕ,
    LSeries.term (ramachandraDivisorCoeff psi)
        (ramachandraShiftedPoint sigma t) n *
      (Real.exp (-((n : ℝ) / X)) : ℂ)

/-- The exact vertical integrand after replacing `1/2+it` by `sigma+it`.
For the long line we later take `u = -(sigma+1/4)`, so that the reflected
Dirichlet series has real part `5/4`. -/
def ramachandraShiftedContourIntegrand {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (X sigma u t v : ℝ)
    (tail : Bool) : ℂ :=
  let w : ℂ := (u : ℂ) + v * I
  let z : ℂ := ramachandraShiftedPoint sigma t + w
  ramachandraFunctionalFactor psi z ^ 2 *
    (if tail then ramachandraReflectedTail psi X z
      else ramachandraReflectedHead psi X z) *
    Complex.Gamma w * (X : ℂ) ^ w

/-- The shifted `1/(2*pi*i)` contour integral after `dw = i dv`. -/
def ramachandraShiftedContourPiece {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (X sigma u t : ℝ)
    (tail : Bool) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ v : ℝ,
      ramachandraShiftedContourIntegrand psi X sigma u t v tail

/-- Source choice `X=dT` for a primitive family modulo `d`. -/
def primitiveShiftedScale (d : ℕ) (T : ℝ) : ℝ :=
  (d : ℝ) * T

def primitiveShiftedDirect {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (T sigma t : ℝ) : ℂ :=
  ramachandraShiftedDirect psi (primitiveShiftedScale d T) sigma t

/-- The fixed `c=1/4` long line from the shifted Lemma 3 argument. -/
def primitiveShiftedLongContour {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (T sigma t : ℝ) : ℂ :=
  ramachandraShiftedContourPiece psi (primitiveShiftedScale d T) sigma
    (-(sigma + 1 / 4)) t true

/-- The near line `u = -1/log(dT)` from the head part in Lemma 3. -/
def primitiveShiftedShortContour {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (T sigma t : ℝ) : ℂ :=
  ramachandraShiftedContourPiece psi (primitiveShiftedScale d T) sigma
    (-(Real.log (primitiveShiftedScale d T))⁻¹) t false

/-- Sum of the four literal second-moment integrands. -/
def primitiveShiftedPieceEnergy {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (T sigma t : ℝ)
    (remainder : DirichletCharacter ℂ d → ℝ → ℂ) : ℝ :=
  ‖primitiveShiftedDirect psi T sigma t‖ ^ 2 +
    ‖primitiveShiftedLongContour psi T sigma t‖ ^ 2 +
    ‖primitiveShiftedShortContour psi T sigma t‖ ^ 2 +
    ‖remainder psi t‖ ^ 2

/-! ## Deterministic Cauchy and family integration -/

/-- The Cauchy step is unchanged by the horizontal shift. -/
theorem shiftedLFourth_le_pieceEnergy
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (T sigma t : ℝ)
    (remainder : DirichletCharacter ℂ d → ℝ → ℂ)
    (hdecomp :
      DirichletCharacter.LFunction psi
          (ramachandraShiftedPoint sigma t) ^ 2 =
        primitiveShiftedDirect psi T sigma t -
          primitiveShiftedLongContour psi T sigma t -
          primitiveShiftedShortContour psi T sigma t + remainder psi t) :
    shiftedStripLFourth psi sigma t ≤
      4 * primitiveShiftedPieceEnergy psi T sigma t remainder := by
  let z := DirichletCharacter.LFunction psi
    (ramachandraShiftedPoint sigma t)
  let s := primitiveShiftedDirect psi T sigma t
  let i₁ := primitiveShiftedLongContour psi T sigma t
  let i₂ := primitiveShiftedShortContour psi T sigma t
  let e := remainder psi t
  have hnorm : ‖z ^ 2‖ ≤ ‖s‖ + ‖i₁‖ + ‖i₂‖ + ‖e‖ := by
    rw [show z ^ 2 = s - i₁ - i₂ + e by
      simpa [z, s, i₁, i₂, e, ramachandraShiftedPoint] using hdecomp]
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
    shiftedStripLFourth psi sigma t = ‖z ^ 2‖ ^ 2 := by
      unfold shiftedStripLFourth
      change ‖z‖ ^ 4 = ‖z ^ 2‖ ^ 2
      rw [norm_pow]
      ring
    _ ≤ (‖s‖ + ‖i₁‖ + ‖i₂‖ + ‖e‖) ^ 2 := hsq
    _ ≤ 4 * (‖s‖ ^ 2 + ‖i₁‖ ^ 2 + ‖i₂‖ ^ 2 + ‖e‖ ^ 2) :=
      four_term_sq_le _ _ _ _
    _ = 4 * primitiveShiftedPieceEnergy psi T sigma t remainder := by
      simp [primitiveShiftedPieceEnergy, s, i₁, i₂, e]

/-- Primitive-family integral of the literal piece energy. -/
def primitiveFamilyShiftedPieceEnergyIntegral
    (d : ℕ) [NeZero d] (T sigma : ℝ)
    (remainder : DirichletCharacter ℂ d → ℝ → ℂ) : ℝ := by
  classical
  exact ∑ psi : DirichletCharacter ℂ d,
    if psi.IsPrimitive then
      ∫ t in (-T)..T,
        primitiveShiftedPieceEnergy psi T sigma t remainder
    else 0

/-- Exact shifted Lemma 3 data, with continuity recorded only so interval
monotonicity can be applied.  The equation itself is pointwise and contains
the three literal source pieces. -/
structure PrimitiveShiftedContourIdentityData
    (d : ℕ) [NeZero d] (T sigma : ℝ) where
  remainder : DirichletCharacter ℂ d → ℝ → ℂ
  continuous_direct : ∀ psi : DirichletCharacter ℂ d,
    Continuous (fun t ↦ ‖primitiveShiftedDirect psi T sigma t‖ ^ 2)
  continuous_long : ∀ psi : DirichletCharacter ℂ d,
    Continuous (fun t ↦ ‖primitiveShiftedLongContour psi T sigma t‖ ^ 2)
  continuous_short : ∀ psi : DirichletCharacter ℂ d,
    Continuous (fun t ↦ ‖primitiveShiftedShortContour psi T sigma t‖ ^ 2)
  continuous_remainder : ∀ psi : DirichletCharacter ℂ d,
    Continuous (fun t ↦ ‖remainder psi t‖ ^ 2)
  decomposition : ∀ (psi : DirichletCharacter ℂ d), psi.IsPrimitive →
    ∀ t : ℝ, |t| ≤ T →
      DirichletCharacter.LFunction psi
          (ramachandraShiftedPoint sigma t) ^ 2 =
        primitiveShiftedDirect psi T sigma t -
          primitiveShiftedLongContour psi T sigma t -
          primitiveShiftedShortContour psi T sigma t + remainder psi t

theorem PrimitiveShiftedContourIdentityData.continuous_energy
    {d : ℕ} [NeZero d] {T sigma : ℝ}
    (data : PrimitiveShiftedContourIdentityData d T sigma)
    (psi : DirichletCharacter ℂ d) :
    Continuous (fun t ↦
      primitiveShiftedPieceEnergy psi T sigma t data.remainder) := by
  unfold primitiveShiftedPieceEnergy
  exact (((data.continuous_direct psi).add
    (data.continuous_long psi)).add
      (data.continuous_short psi)).add
        (data.continuous_remainder psi)

/-- Integrating the exact shifted Lemma 3 decomposition reduces the fourth
moment to the sum of the four literal source second moments. -/
theorem primitiveFamilyShiftedFourthIntegral_le_pieceEnergy
    {d : ℕ} [NeZero d] {T sigma : ℝ}
    (hT : 0 ≤ T) (hsigma : sigma < 1)
    (data : PrimitiveShiftedContourIdentityData d T sigma) :
    primitiveFamilyShiftedFourthIntegral d T sigma ≤
      4 * primitiveFamilyShiftedPieceEnergyIntegral d T sigma
        data.remainder := by
  classical
  unfold primitiveFamilyShiftedFourthIntegral
    primitiveFamilyShiftedPieceEnergyIntegral
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro psi hpsi
  by_cases hp : psi.IsPrimitive
  · simp only [hp, if_true]
    calc
      (∫ t in (-T)..T, shiftedStripLFourth psi sigma t) ≤
          ∫ t in (-T)..T,
            4 * primitiveShiftedPieceEnergy psi T sigma t data.remainder := by
        apply intervalIntegral.integral_mono_on (by linarith)
        · exact (continuous_shiftedStripLFourth psi hsigma).intervalIntegrable _ _
        · exact (continuous_const.mul
            (data.continuous_energy psi)).intervalIntegrable _ _
        · intro t ht
          apply shiftedLFourth_le_pieceEnergy
          exact data.decomposition psi hp t
            ((abs_le).2 ⟨by linarith [ht.1], ht.2⟩)
      _ = 4 * ∫ t in (-T)..T,
          primitiveShiftedPieceEnergy psi T sigma t data.remainder := by
        rw [intervalIntegral.integral_const_mul]
  · simp [hp]

/-! ## The four precise omitted analytic leaves -/

def primitiveFamilyDirectSecondMoment
    (d : ℕ) [NeZero d] (T sigma : ℝ) : ℝ := by
  classical
  exact ∑ psi : DirichletCharacter ℂ d,
    if psi.IsPrimitive then
      ∫ t in (-T)..T, ‖primitiveShiftedDirect psi T sigma t‖ ^ 2
    else 0

def primitiveFamilyLongContourSecondMoment
    (d : ℕ) [NeZero d] (T sigma : ℝ) : ℝ := by
  classical
  exact ∑ psi : DirichletCharacter ℂ d,
    if psi.IsPrimitive then
      ∫ t in (-T)..T, ‖primitiveShiftedLongContour psi T sigma t‖ ^ 2
    else 0

def primitiveFamilyShortContourSecondMoment
    (d : ℕ) [NeZero d] (T sigma : ℝ) : ℝ := by
  classical
  exact ∑ psi : DirichletCharacter ℂ d,
    if psi.IsPrimitive then
      ∫ t in (-T)..T, ‖primitiveShiftedShortContour psi T sigma t‖ ^ 2
    else 0

def primitiveFamilyRemainderSecondMoment
    (d : ℕ) [NeZero d] (T : ℝ)
    (remainder : DirichletCharacter ℂ d → ℝ → ℂ) : ℝ := by
  classical
  exact ∑ psi : DirichletCharacter ℂ d,
    if psi.IsPrimitive then
      ∫ t in (-T)..T, ‖remainder psi t‖ ^ 2
    else 0

/-- The energy integral is exactly the sum of the four named source leaves. -/
theorem primitiveFamilyShiftedPieceEnergyIntegral_eq
    {d : ℕ} [NeZero d] {T sigma : ℝ}
    (remainder : DirichletCharacter ℂ d → ℝ → ℂ)
    (hdir : ∀ psi : DirichletCharacter ℂ d,
      Continuous (fun t ↦ ‖primitiveShiftedDirect psi T sigma t‖ ^ 2))
    (hlong : ∀ psi : DirichletCharacter ℂ d,
      Continuous (fun t ↦ ‖primitiveShiftedLongContour psi T sigma t‖ ^ 2))
    (hshort : ∀ psi : DirichletCharacter ℂ d,
      Continuous (fun t ↦ ‖primitiveShiftedShortContour psi T sigma t‖ ^ 2))
    (hrem : ∀ psi : DirichletCharacter ℂ d,
      Continuous (fun t ↦ ‖remainder psi t‖ ^ 2)) :
    primitiveFamilyShiftedPieceEnergyIntegral d T sigma remainder =
      primitiveFamilyDirectSecondMoment d T sigma +
      primitiveFamilyLongContourSecondMoment d T sigma +
      primitiveFamilyShortContourSecondMoment d T sigma +
      primitiveFamilyRemainderSecondMoment d T remainder := by
  classical
  unfold primitiveFamilyShiftedPieceEnergyIntegral
    primitiveFamilyDirectSecondMoment
    primitiveFamilyLongContourSecondMoment
    primitiveFamilyShortContourSecondMoment
    primitiveFamilyRemainderSecondMoment
  simp_rw [primitiveShiftedPieceEnergy]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro psi hpsi
  by_cases hp : psi.IsPrimitive
  · simp only [hp, if_true]
    have hdI : IntervalIntegrable
        (fun t ↦ ‖primitiveShiftedDirect psi T sigma t‖ ^ 2)
        volume (-T) T := (hdir psi).intervalIntegrable (-T) T
    have hlI : IntervalIntegrable
        (fun t ↦ ‖primitiveShiftedLongContour psi T sigma t‖ ^ 2)
        volume (-T) T := (hlong psi).intervalIntegrable (-T) T
    have hsI : IntervalIntegrable
        (fun t ↦ ‖primitiveShiftedShortContour psi T sigma t‖ ^ 2)
        volume (-T) T := (hshort psi).intervalIntegrable (-T) T
    have hrI : IntervalIntegrable (fun t ↦ ‖remainder psi t‖ ^ 2)
        volume (-T) T := (hrem psi).intervalIntegrable (-T) T
    rw [intervalIntegral.integral_add ((hdI.add hlI).add hsI) hrI,
      intervalIntegral.integral_add (hdI.add hlI) hsI,
      intervalIntegral.integral_add hdI hlI]
  · simp [hp]

/-- Exact lower obligations left by the omitted shifted versions of Lemmas
4--6.  Each field bounds one printed source piece, never `|L|^4`. -/
structure PrimitiveShiftedContourBudgets
    (d : ℕ) [NeZero d] (T sigma C : ℝ)
    (remainder : DirichletCharacter ℂ d → ℝ → ℂ) where
  direct : primitiveFamilyDirectSecondMoment d T sigma ≤
    C * ((d : ℝ) * T) * Real.log ((d : ℝ) * T) ^ 200
  long : primitiveFamilyLongContourSecondMoment d T sigma ≤
    C * ((d : ℝ) * T) * Real.log ((d : ℝ) * T) ^ 200
  short : primitiveFamilyShortContourSecondMoment d T sigma ≤
    C * ((d : ℝ) * T) * Real.log ((d : ℝ) * T) ^ 200
  remainder_budget : primitiveFamilyRemainderSecondMoment d T remainder ≤
    C * ((d : ℝ) * T) * Real.log ((d : ℝ) * T) ^ 200

/-- The literal shifted contour identity plus the four separate Lemmas 4--6
budgets prove the primitive estimate with constant `16*C`. -/
theorem primitiveFamilyShiftedFourthIntegral_le_of_contourLemmas
    {d : ℕ} [NeZero d] {T sigma C : ℝ}
    (hT : 0 ≤ T) (hsigma : sigma < 1)
    (identity : PrimitiveShiftedContourIdentityData d T sigma)
    (budgets : PrimitiveShiftedContourBudgets d T sigma C
      identity.remainder) :
    primitiveFamilyShiftedFourthIntegral d T sigma ≤
      (16 * C) * ((d : ℝ) * T) *
        Real.log ((d : ℝ) * T) ^ 200 := by
  let M : ℝ := C * ((d : ℝ) * T) *
    Real.log ((d : ℝ) * T) ^ 200
  have henergy :
      primitiveFamilyShiftedPieceEnergyIntegral d T sigma identity.remainder
        ≤ 4 * M := by
    rw [primitiveFamilyShiftedPieceEnergyIntegral_eq identity.remainder
      identity.continuous_direct identity.continuous_long
      identity.continuous_short identity.continuous_remainder]
    dsimp [M]
    nlinarith [budgets.direct, budgets.long, budgets.short,
      budgets.remainder_budget]
  calc
    primitiveFamilyShiftedFourthIntegral d T sigma ≤
        4 * primitiveFamilyShiftedPieceEnergyIntegral d T sigma
          identity.remainder :=
      primitiveFamilyShiftedFourthIntegral_le_pieceEnergy hT hsigma identity
    _ ≤ 4 * (4 * M) := mul_le_mul_of_nonneg_left henergy (by norm_num)
    _ = (16 * C) * ((d : ℝ) * T) *
        Real.log ((d : ℝ) * T) ^ 200 := by ring

/-- A uniform construction of the shifted Lemma 3 identity and the separate
Lemmas 4--6 budgets inhabits the primitive p.88 source leaf.  This is the
exact global weld needed by the all-character conductor/Euler argument. -/
theorem ramachandraPrimitiveShiftedFourthK2_of_contourConstructions
    {C : ℝ} (hC : 0 < C)
    (hconstruct : ∀ (q d : ℕ) [NeZero q] [NeZero d]
      (T sigma : ℝ), d ∣ q → 3 ≤ T →
      |sigma - (1 / 2 : ℝ)| ≤
          (100 * Real.log ((q : ℝ) * T))⁻¹ →
      { identity : PrimitiveShiftedContourIdentityData d T sigma //
        PrimitiveShiftedContourBudgets d T sigma C identity.remainder }) :
    RamachandraPrimitiveShiftedFourthK2 := by
  refine ⟨16 * C, by positivity, ?_⟩
  intro q d _instq _instd T sigma hdq hT hstrip
  have hsigma : sigma < 1 :=
    sigma_lt_one_of_ramachandraStrip hT hstrip
  obtain ⟨identity, budgets⟩ := hconstruct q d T sigma hdq hT hstrip
  exact primitiveFamilyShiftedFourthIntegral_le_of_contourLemmas
    (by linarith : 0 ≤ T) hsigma
      identity budgets

/-! ## Regression certificate for the repaired remainder interface -/

/-- The discarded interface asking for one finite bound uniformly over every
possible remainder function was false.  Whenever the family contains a
primitive character, a sufficiently large constant remainder violates any
proposed bound.  Keeping this theorem beside `PrimitiveShiftedContourBudgets`
prevents the quantifier bug from being reintroduced. -/
theorem no_uniform_primitiveFamilyRemainderSecondMoment_bound
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hpsi : psi.IsPrimitive) (M : ℝ) :
    ¬ (∀ r : DirichletCharacter ℂ d → ℝ → ℂ,
      primitiveFamilyRemainderSecondMoment d 1 r ≤ M) := by
  classical
  intro hall
  let A : ℝ := |M| + 1
  let r : DirichletCharacter ℂ d → ℝ → ℂ := fun _ _ => (A : ℂ)
  have hbound := hall r
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hterm :
      (∫ _t in (-1 : ℝ)..1, ‖(A : ℂ)‖ ^ 2) = 2 * A ^ 2 := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_pos hApos]
    ring
  have hnonneg : ∀ chi : DirichletCharacter ℂ d,
      0 ≤ if chi.IsPrimitive then
        ∫ _t in (-1 : ℝ)..1, ‖r chi 0‖ ^ 2 else 0 := by
    intro chi
    by_cases hp : chi.IsPrimitive
    · simp only [hp, if_true]
      dsimp [r]
      rw [hterm]
      positivity
    · simp [hp]
  have hsingle :
      (if psi.IsPrimitive then
        ∫ _t in (-1 : ℝ)..1, ‖r psi 0‖ ^ 2 else 0) ≤
      primitiveFamilyRemainderSecondMoment d 1 r := by
    unfold primitiveFamilyRemainderSecondMoment
    apply Finset.single_le_sum (fun chi _ => hnonneg chi)
      (Finset.mem_univ psi)
  have hpsiTerm :
      (if psi.IsPrimitive then
        ∫ _t in (-1 : ℝ)..1, ‖r psi 0‖ ^ 2 else 0) = 2 * A ^ 2 := by
    simp only [hpsi, if_true]
    dsimp [r]
    exact hterm
  rw [hpsiTerm] at hsingle
  have hMA : M < 2 * A ^ 2 := by
    have habs : M ≤ |M| := le_abs_self M
    dsimp [A]
    nlinarith [sq_nonneg (|M| + 1)]
  linarith

end
end RamachandraPrimitiveShiftedContourReduction

#print axioms RamachandraPrimitiveShiftedContourReduction.shiftedLFourth_le_pieceEnergy
#print axioms RamachandraPrimitiveShiftedContourReduction.primitiveFamilyShiftedFourthIntegral_le_pieceEnergy
#print axioms RamachandraPrimitiveShiftedContourReduction.primitiveFamilyShiftedPieceEnergyIntegral_eq
#print axioms RamachandraPrimitiveShiftedContourReduction.primitiveFamilyShiftedFourthIntegral_le_of_contourLemmas
#print axioms RamachandraPrimitiveShiftedContourReduction.ramachandraPrimitiveShiftedFourthK2_of_contourConstructions
#print axioms RamachandraPrimitiveShiftedContourReduction.no_uniform_primitiveFamilyRemainderSecondMoment_bound
