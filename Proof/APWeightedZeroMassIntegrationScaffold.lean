import FixedScaleAPZeroRoute
import FixedCharacterReduction
import CGLMeshFormalization
import KhaleWeakVKAbsoluteBridge
import GoldfeldComparisonBridge
import MellinDetectorLeaf

/-!
# Equation (2.7) integration scaffold

This diagnostic file introduces no analytic source proposition.  It records the
literal, multiplicity-aware partition of the zero mass used in equation (2.7),
the deterministic fixed-modulus Jutila-to-primitive-inducer conversion, and the
final quantifier-preserving range weld.  The analytic range estimates remain
parameters of the last theorem.

The near-one source parameter below is deliberately the fixed-modulus family
statement of Jutila, *On Linnik's constant*, Math. Scand. 41 (1977), p. 46,
Theorem 1, equation (1.7): the sum
is over every character modulo one fixed `q`, the range is
`4/5 ≤ sigma ≤ 1`, `T ≥ 1`, and the constant is uniform in `q`, `T`, and
`sigma`.  It is not equation (1.8), which separately averages primitive
characters over all moduli up to `Q`.  No fixed-character strengthening is
silently assumed.
-/

namespace MAPAPWeightedZeroMassIntegration

open scoped BigOperators
open DirichletZeros MAPFixedScaleAPZeroRoute MAPLowBetaMeshClosure
open MAPAPZeroDensityCert ZeroDensityInterface CGLPolylogBypass

noncomputable section

/-! ## Literal three-range partition -/

/-- Strict low strip.  Equality at `1/2 + paperDelta0 epsilon` is excluded. -/
def primitiveLowRangeMass {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (epsilon X T : ℝ) : ℝ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact ∑ rho ∈ (zeroSupport chi.primitiveCharacter 0 T).filter
      (fun rho => rho.re < 1 / 2 + paperDelta0 epsilon),
    (zeroMultiplicity chi.primitiveCharacter 0 T rho : ℝ) *
      Real.rpow X (2 * (rho.re - 1))

/-- Closed-left compact strip.  It includes both the lower mesh endpoint and
`beta = 4/5`. -/
def primitiveCompactRangeMass {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (epsilon X T : ℝ) : ℝ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact ∑ rho ∈ (zeroSupport chi.primitiveCharacter 0 T).filter
      (fun rho => 1 / 2 + paperDelta0 epsilon ≤ rho.re ∧ rho.re ≤ 4 / 5),
    (zeroMultiplicity chi.primitiveCharacter 0 T rho : ℝ) *
      Real.rpow X (2 * (rho.re - 1))

/-- Strict near-one strip.  Thus `beta = 4/5` occurs only in the compact
branch. -/
def primitiveNearOneRangeMass {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X T : ℝ) : ℝ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact ∑ rho ∈ (zeroSupport chi.primitiveCharacter 0 T).filter
      (fun rho => 4 / 5 < rho.re),
    (zeroMultiplicity chi.primitiveCharacter 0 T rho : ℝ) *
      Real.rpow X (2 * (rho.re - 1))

/-- The part of the strict near-one strip not eligible to be a Siegel real
zero.  This includes every nonreal ordinate and every nonreal character. -/
def primitiveRegularNearOneRangeMass {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X T : ℝ) : ℝ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  exact ∑ rho ∈ (zeroSupport psi 0 T).filter (fun rho =>
      4 / 5 < rho.re ∧
        ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0)),
    (zeroMultiplicity psi 0 T rho : ℝ) *
      Real.rpow X (2 * (rho.re - 1))

/-- Exact exceptional-eligible atoms: strict near-one zeros on the real axis of
a real nonprincipal primitive inducer.  No simplicity is built into this
definition; analytic multiplicity is retained. -/
def primitiveExceptionalNearOneRangeMass {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X T : ℝ) : ℝ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  exact ∑ rho ∈ (zeroSupport psi 0 T).filter (fun rho =>
      4 / 5 < rho.re ∧
        psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0),
    (zeroMultiplicity psi 0 T rho : ℝ) *
      Real.rpow X (2 * (rho.re - 1))

/-- Bounded-ordinate regular near-one atoms.  The endpoint `|gamma| = 3` is
excluded and belongs to the Khale-height branch below. -/
def primitiveRegularNearOneLowHeightMass {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X T : ℝ) : ℝ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  exact ∑ rho ∈ (zeroSupport psi 0 T).filter (fun rho =>
      (4 / 5 < rho.re ∧
        ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0)) ∧ |rho.im| < 3),
    (zeroMultiplicity psi 0 T rho : ℝ) *
      Real.rpow X (2 * (rho.re - 1))

/-- High-ordinate regular near-one atoms, with the closed endpoint
`3 ≤ |gamma|`.  The sign-symmetric deterministic Khale consumer is
`MAPKhaleWeakVKApplication.khaleWeakRegionAbs_nearFactor_beats_polylog`, whose
hypotheses use this same literal absolute-ordinate convention. -/
def primitiveRegularNearOneHighHeightMass {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X T : ℝ) : ℝ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  exact ∑ rho ∈ (zeroSupport psi 0 T).filter (fun rho =>
      (4 / 5 < rho.re ∧
        ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0)) ∧ 3 ≤ |rho.im|),
    (zeroMultiplicity psi 0 T rho : ℝ) *
      Real.rpow X (2 * (rho.re - 1))

theorem primitiveRegularNearOneRangeMass_eq_lowHeight_add_highHeight
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (X T : ℝ) :
    primitiveRegularNearOneRangeMass chi X T =
      primitiveRegularNearOneLowHeightMass chi X T +
        primitiveRegularNearOneHighHeightMass chi X T := by
  classical
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  let regular : ℂ → Prop := fun rho =>
    4 / 5 < rho.re ∧ ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0)
  let S := (zeroSupport psi 0 T).filter regular
  let lowHeight : ℂ → Prop := fun rho => |rho.im| < 3
  let w : ℂ → ℝ := fun rho =>
    (zeroMultiplicity psi 0 T rho : ℝ) *
      Real.rpow X (2 * (rho.re - 1))
  have hsplit := Finset.sum_filter_add_sum_filter_not S lowHeight w
  unfold primitiveRegularNearOneRangeMass
    primitiveRegularNearOneLowHeightMass
    primitiveRegularNearOneHighHeightMass
  change (∑ rho ∈ S, w rho) =
    (∑ rho ∈ (zeroSupport psi 0 T).filter (fun rho =>
      regular rho ∧ |rho.im| < 3), w rho) +
    ∑ rho ∈ (zeroSupport psi 0 T).filter (fun rho =>
      regular rho ∧ 3 ≤ |rho.im|), w rho
  simpa only [S, lowHeight, Finset.filter_filter, not_lt] using hsplit.symm

theorem primitiveNearOneRangeMass_eq_regular_add_exceptional
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (X T : ℝ) :
    primitiveNearOneRangeMass chi X T =
      primitiveRegularNearOneRangeMass chi X T +
        primitiveExceptionalNearOneRangeMass chi X T := by
  classical
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  let S := (zeroSupport psi 0 T).filter (fun rho => 4 / 5 < rho.re)
  let eligible : ℂ → Prop := fun rho =>
    psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0
  let w : ℂ → ℝ := fun rho =>
    (zeroMultiplicity psi 0 T rho : ℝ) *
      Real.rpow X (2 * (rho.re - 1))
  have hsplit := Finset.sum_filter_add_sum_filter_not S eligible w
  have hregularFilter :
      S.filter (fun rho => ¬ eligible rho) =
        (zeroSupport psi 0 T).filter (fun rho =>
          4 / 5 < rho.re ∧ ¬ eligible rho) := by
    ext rho
    simp [S, and_assoc]
  have hexceptionalFilter :
      S.filter eligible =
        (zeroSupport psi 0 T).filter (fun rho =>
          4 / 5 < rho.re ∧ eligible rho) := by
    ext rho
    simp [S, and_assoc]
  rw [hregularFilter] at hsplit
  have hsplit' := hsplit.symm
  rw [add_comm] at hsplit'
  rw [hexceptionalFilter] at hsplit'
  unfold primitiveNearOneRangeMass primitiveRegularNearOneRangeMass
    primitiveExceptionalNearOneRangeMass
  change (∑ rho ∈ S, w rho) =
    (∑ rho ∈ (zeroSupport psi 0 T).filter (fun rho =>
        4 / 5 < rho.re ∧ ¬ eligible rho), w rho) +
      ∑ rho ∈ (zeroSupport psi 0 T).filter (fun rho =>
        4 / 5 < rho.re ∧ eligible rho), w rho
  exact hsplit'

/-- The strict/closed/strict split is exhaustive and disjoint.  The theorem
uses only the certified numerical fact that the lower cutoff is below `4/5`.
Every summand retains the analytic divisor multiplicity from the full
rectangle. -/
theorem primitiveWeightedZeroMass_eq_low_add_compact_add_near
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (epsilon X T : ℝ) :
    primitiveWeightedZeroMass chi X T =
      primitiveLowRangeMass chi epsilon X T +
        primitiveCompactRangeMass chi epsilon X T +
          primitiveNearOneRangeMass chi X T := by
  classical
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let S := zeroSupport chi.primitiveCharacter 0 T
  let w : ℂ → ℝ := fun rho =>
    (zeroMultiplicity chi.primitiveCharacter 0 T rho : ℝ) *
      Real.rpow X (2 * (rho.re - 1))
  let low : ℂ → Prop := fun rho =>
    rho.re < 1 / 2 + paperDelta0 epsilon
  let compactSide : ℂ → Prop := fun rho => rho.re ≤ 4 / 5
  have hcut : 1 / 2 + paperDelta0 epsilon ≤ (4 / 5 : ℝ) := by
    have hdelta := paperDelta0_le_one_over_120 epsilon
    linarith
  have hfirst := Finset.sum_filter_add_sum_filter_not S low w
  have hsecond := Finset.sum_filter_add_sum_filter_not
    (S.filter fun rho => ¬ low rho) compactSide w
  have hcompactFilter :
      (S.filter fun rho => ¬ low rho).filter compactSide =
        S.filter (fun rho =>
          1 / 2 + paperDelta0 epsilon ≤ rho.re ∧ rho.re ≤ 4 / 5) := by
    ext rho
    simp only [Finset.mem_filter]
    dsimp [low, compactSide]
    constructor
    · rintro ⟨⟨hrho, hnot⟩, hupper⟩
      exact ⟨hrho, le_of_not_gt hnot, hupper⟩
    · rintro ⟨hrho, hlower, hupper⟩
      exact ⟨⟨hrho, not_lt_of_ge hlower⟩, hupper⟩
  have hnearFilter :
      (S.filter fun rho => ¬ low rho).filter
          (fun rho => ¬ compactSide rho) =
        S.filter (fun rho => 4 / 5 < rho.re) := by
    ext rho
    simp only [Finset.mem_filter]
    dsimp [low, compactSide]
    constructor
    · rintro ⟨⟨hrho, _hnotLow⟩, hnotUpper⟩
      exact ⟨hrho, lt_of_not_ge hnotUpper⟩
    · rintro ⟨hrho, hnear⟩
      have hlower : 1 / 2 + paperDelta0 epsilon ≤ rho.re :=
        hcut.trans hnear.le
      exact ⟨⟨hrho, not_lt_of_ge hlower⟩, not_le_of_gt hnear⟩
  rw [hcompactFilter, hnearFilter] at hsecond
  unfold primitiveWeightedZeroMass primitiveLowRangeMass
    primitiveCompactRangeMass primitiveNearOneRangeMass
  change (∑ rho ∈ S, w rho) =
    (∑ rho ∈ S with low rho, w rho) +
      (∑ rho ∈ S.filter (fun rho =>
          1 / 2 + paperDelta0 epsilon ≤ rho.re ∧ rho.re ≤ 4 / 5), w rho) +
        ∑ rho ∈ S.filter (fun rho => 4 / 5 < rho.re), w rho
  linarith

/-- Family versions of the three disjoint ranges, with the same positive-level
and ambient-character indexing as `apWeightedZeroMass`. -/
def apLowRangeMass (Q : ℕ) (epsilon X T : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if hq : q = 0 then 0
    else
      letI : NeZero q := ⟨hq⟩
      ∑ chi : DirichletCharacter ℂ q,
        primitiveLowRangeMass chi epsilon X T

def apCompactRangeMass (Q : ℕ) (epsilon X T : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if hq : q = 0 then 0
    else
      letI : NeZero q := ⟨hq⟩
      ∑ chi : DirichletCharacter ℂ q,
        primitiveCompactRangeMass chi epsilon X T

def apNearOneRangeMass (Q : ℕ) (X T : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if hq : q = 0 then 0
    else
      letI : NeZero q := ⟨hq⟩
      ∑ chi : DirichletCharacter ℂ q,
        primitiveNearOneRangeMass chi X T

def apRegularNearOneRangeMass (Q : ℕ) (X T : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if hq : q = 0 then 0
    else
      letI : NeZero q := ⟨hq⟩
      ∑ chi : DirichletCharacter ℂ q,
        primitiveRegularNearOneRangeMass chi X T

def apExceptionalNearOneRangeMass (Q : ℕ) (X T : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if hq : q = 0 then 0
    else
      letI : NeZero q := ⟨hq⟩
      ∑ chi : DirichletCharacter ℂ q,
        primitiveExceptionalNearOneRangeMass chi X T

def apRegularNearOneLowHeightMass (Q : ℕ) (X T : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if hq : q = 0 then 0
    else
      letI : NeZero q := ⟨hq⟩
      ∑ chi : DirichletCharacter ℂ q,
        primitiveRegularNearOneLowHeightMass chi X T

def apRegularNearOneHighHeightMass (Q : ℕ) (X T : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if hq : q = 0 then 0
    else
      letI : NeZero q := ⟨hq⟩
      ∑ chi : DirichletCharacter ℂ q,
        primitiveRegularNearOneHighHeightMass chi X T

theorem apRegularNearOneRangeMass_eq_lowHeight_add_highHeight
    (Q : ℕ) (X T : ℝ) :
    apRegularNearOneRangeMass Q X T =
      apRegularNearOneLowHeightMass Q X T +
        apRegularNearOneHighHeightMass Q X T := by
  classical
  unfold apRegularNearOneRangeMass apRegularNearOneLowHeightMass
    apRegularNearOneHighHeightMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs with hq0
  · simp
  · letI : NeZero q := ⟨hq0⟩
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro chi _hchi
    exact primitiveRegularNearOneRangeMass_eq_lowHeight_add_highHeight chi X T

theorem apRegularNearOneRangeMass_le_of_lowHeight_highHeight
    {Q : ℕ} {X T Blow Bhigh : ℝ}
    (hlow : apRegularNearOneLowHeightMass Q X T ≤ Blow)
    (hhigh : apRegularNearOneHighHeightMass Q X T ≤ Bhigh) :
    apRegularNearOneRangeMass Q X T ≤ Blow + Bhigh := by
  rw [apRegularNearOneRangeMass_eq_lowHeight_add_highHeight]
  exact add_le_add hlow hhigh

theorem apNearOneRangeMass_eq_regular_add_exceptional
    (Q : ℕ) (X T : ℝ) :
    apNearOneRangeMass Q X T =
      apRegularNearOneRangeMass Q X T +
        apExceptionalNearOneRangeMass Q X T := by
  classical
  unfold apNearOneRangeMass apRegularNearOneRangeMass
    apExceptionalNearOneRangeMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs with hq0
  · simp
  · letI : NeZero q := ⟨hq0⟩
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro chi _hchi
    exact primitiveNearOneRangeMass_eq_regular_add_exceptional chi X T

theorem apWeightedZeroMass_eq_low_add_compact_add_near
    (Q : ℕ) (epsilon X T : ℝ) :
    apWeightedZeroMass Q X T =
      apLowRangeMass Q epsilon X T +
        apCompactRangeMass Q epsilon X T +
          apNearOneRangeMass Q X T := by
  classical
  unfold apWeightedZeroMass weightedZeroMassAtLevel apLowRangeMass
    apCompactRangeMass apNearOneRangeMass
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs with hq0
  · simp
  · letI : NeZero q := ⟨hq0⟩
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro chi _hchi
    exact primitiveWeightedZeroMass_eq_low_add_compact_add_near
      chi epsilon X T

/-- Four-range form used by the final analytic weld.  The exceptional branch is
separate even though it is a subset of the strict near-one strip. -/
theorem apWeightedZeroMass_eq_four_ranges
    (Q : ℕ) (epsilon X T : ℝ) :
    apWeightedZeroMass Q X T =
      apLowRangeMass Q epsilon X T +
        apCompactRangeMass Q epsilon X T +
          apRegularNearOneRangeMass Q X T +
            apExceptionalNearOneRangeMass Q X T := by
  rw [apWeightedZeroMass_eq_low_add_compact_add_near,
    apNearOneRangeMass_eq_regular_add_exceptional]
  ring

/-! ## Source-faithful Jutila conversion -/

/-- One character is a literal summand of Jutila's fixed-modulus family count.
This is the only step needed to pass from the published family statement to a
uniform fixed-character consequence. -/
theorem dirichletZeroCount_le_ambientZeroCountAtLevel
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (sigma T : ℝ) :
    dirichletZeroCount chi sigma T ≤
      ambientZeroCountAtLevel q sigma T := by
  simp only [ambientZeroCountAtLevel, NeZero.ne q, dite_false]
  exact Finset.single_le_sum
    (f := fun psi : DirichletCharacter ℂ q =>
      dirichletZeroCount psi sigma T)
    (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ chi)

/-- Deterministic consequence of Jutila (1.7) for the primitive-inducer family
used by equation (2.7).  The source premise remains a fixed-modulus sum over
all characters.  Repetition of primitive inducers among ambient characters is
paid explicitly by `Q^2`; no change of multiplicity convention occurs. -/
theorem jutila_fixedModulusFamily_to_primitiveInducerFamily
    {Q : ℕ} {T sigma eta C : ℝ}
    (hT : 1 ≤ T) (heta : 0 < eta)
    (_hsigmaLow : 4 / 5 ≤ sigma) (hsigmaHigh : sigma ≤ 1)
    (hC : 0 ≤ C)
    (hJutila : ∀ (r : ℕ) [NeZero r],
      (ambientZeroCountAtLevel r sigma T : ℝ) ≤
        C * Real.rpow ((r : ℝ) * T) ((2 + eta) * (1 - sigma))) :
    (polylogFamilyZeroCount Q sigma T : ℝ) ≤
      (Q : ℝ) ^ 2 *
        (C * Real.rpow ((Q : ℝ) * T) ((2 + eta) * (1 - sigma))) := by
  let e : ℝ := (2 + eta) * (1 - sigma)
  have he : 0 ≤ e := by
    dsimp [e]
    exact mul_nonneg (by linarith) (by linarith)
  have hB : 0 ≤ C * Real.rpow ((Q : ℝ) * T) e :=
    mul_nonneg hC (Real.rpow_nonneg
      (mul_nonneg (Nat.cast_nonneg Q) (zero_le_one.trans hT)) _)
  apply fixed_primitive_bound_to_family hB
  intro r _inst chi _hprimitive hrQ
  have hsingleNat := dirichletZeroCount_le_ambientZeroCountAtLevel chi sigma T
  have hsingle : (dirichletZeroCount chi sigma T : ℝ) ≤
      (ambientZeroCountAtLevel r sigma T : ℝ) := by
    exact_mod_cast hsingleNat
  have hsource := hsingle.trans (hJutila r)
  have hrQreal : (r : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hrQ
  have hbase : (r : ℝ) * T ≤ (Q : ℝ) * T :=
    mul_le_mul_of_nonneg_right hrQreal (zero_le_one.trans hT)
  have hrTnonneg : 0 ≤ (r : ℝ) * T :=
    mul_nonneg (Nat.cast_nonneg r) (zero_le_one.trans hT)
  have hpow : Real.rpow ((r : ℝ) * T) e ≤
      Real.rpow ((Q : ℝ) * T) e :=
    Real.rpow_le_rpow hrTnonneg hbase he
  exact hsource.trans (mul_le_mul_of_nonneg_left hpow hC)

/-- Full source-quantifier adapter for Jutila, Theorem 1, equation (1.7).
The hypothesis is intentionally a theorem parameter rather than a new named
`Prop`.  Its single constant is chosen after `eta` and before `q`, `T`, and
`sigma`, exactly expressing the published uniformity. -/
theorem jutila_source_to_primitiveInducerFamily
    (hJutila : ∀ eta : ℝ, 0 < eta →
      ∃ C : ℝ, 0 < C ∧
        ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
          1 ≤ T → 4 / 5 ≤ sigma → sigma ≤ 1 →
            (ambientZeroCountAtLevel q sigma T : ℝ) ≤
              C * Real.rpow ((q : ℝ) * T)
                ((2 + eta) * (1 - sigma))) :
    ∀ eta : ℝ, 0 < eta →
      ∃ C : ℝ, 0 < C ∧
        ∀ (Q : ℕ) (T sigma : ℝ),
          1 ≤ T → 4 / 5 ≤ sigma → sigma ≤ 1 →
            (polylogFamilyZeroCount Q sigma T : ℝ) ≤
              (Q : ℝ) ^ 2 *
                (C * Real.rpow ((Q : ℝ) * T)
                  ((2 + eta) * (1 - sigma))) := by
  intro eta heta
  obtain ⟨C, hC, hsource⟩ := hJutila eta heta
  refine ⟨C, hC, ?_⟩
  intro Q T sigma hT hsigmaLow hsigmaHigh
  exact jutila_fixedModulusFamily_to_primitiveInducerFamily
    hT heta hsigmaLow hsigmaHigh hC.le
    (fun r _inst => hsource r T sigma hT hsigmaLow hsigmaHigh)

/-! ## Primitive-inducer cell and multiplicity reindex -/

/-- One half-open cell cut directly from the full `sigma = 0` rectangle used by
`primitiveWeightedZeroMass`. -/
def primitiveInducerCellMass {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q)
    (X T sigma Delta : ℝ) : ℝ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  exact ∑ rho ∈ (zeroSupport psi 0 T).filter (fun rho =>
      sigma ≤ rho.re ∧ rho.re < sigma + Delta),
    (zeroMultiplicity psi 0 T rho : ℝ) *
      Real.rpow X (2 * (rho.re - 1))

/-- A full-rectangle cell is bounded by the primitive-inducer count at its left
edge.  The proof explicitly transports both support and analytic multiplicity
from the `0` rectangle to the `sigma` rectangle. -/
theorem primitiveInducerCellMass_le_count_weight
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X T sigma Delta : ℝ} (hX : 1 ≤ X) :
    primitiveInducerCellMass chi X T sigma Delta ≤
      (primitiveDirichletZeroCount chi sigma T : ℝ) *
        Real.rpow X (2 * (sigma + Delta - 1)) := by
  classical
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  let S := (zeroSupport psi 0 T).filter (fun rho =>
    sigma ≤ rho.re ∧ rho.re < sigma + Delta)
  let W := Real.rpow X (2 * (sigma + Delta - 1))
  have hsupport : S ⊆ zeroSupport psi sigma T := by
    intro rho hrho
    have hfull : rho ∈ zeroSupport psi 0 T := (Finset.mem_filter.mp hrho).1
    have hcell := (Finset.mem_filter.mp hrho).2
    have hfullRect :=
      (zeroDivisor psi 0 T).supportWithinDomain
        ((zeroSupport_mem_iff psi 0 T rho).mp hfull)
    have hinnerRect : rho ∈ zeroRectangle sigma T := by
      rw [zeroRectangle, Complex.mem_reProdIm] at hfullRect ⊢
      exact ⟨⟨hcell.1, hfullRect.1.2⟩, hfullRect.2⟩
    apply (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
      psi sigma T hinnerRect).mpr
    exact regularizedLFunction_eq_zero_of_mem_zeroSupport psi 0 T hfull
  have hsum :
      (∑ rho ∈ S, zeroMultiplicity psi 0 T rho) ≤
        dirichletZeroCount psi sigma T := by
    have hrewrite :
        (∑ rho ∈ S, zeroMultiplicity psi 0 T rho) =
          ∑ rho ∈ S, zeroMultiplicity psi sigma T rho := by
      apply Finset.sum_congr rfl
      intro rho hrho
      have hfull : rho ∈ zeroSupport psi 0 T := (Finset.mem_filter.mp hrho).1
      have hinner : rho ∈ zeroSupport psi sigma T := hsupport hrho
      have hfullRect :=
        (zeroDivisor psi 0 T).supportWithinDomain
          ((zeroSupport_mem_iff psi 0 T rho).mp hfull)
      have hinnerRect :=
        (zeroDivisor psi sigma T).supportWithinDomain
          ((zeroSupport_mem_iff psi sigma T rho).mp hinner)
      exact MAPMellinDetectorLeaf.zeroMultiplicity_eq_of_mem_rectangles
        psi hfullRect hinnerRect
    rw [hrewrite]
    unfold dirichletZeroCount
    exact Finset.sum_le_sum_of_subset_of_nonneg hsupport
      (fun _ _ _ => Nat.zero_le _)
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hW : 0 ≤ W := Real.rpow_nonneg hXpos.le _
  calc
    primitiveInducerCellMass chi X T sigma Delta ≤
        ∑ rho ∈ S, (zeroMultiplicity psi 0 T rho : ℝ) * W := by
      unfold primitiveInducerCellMass
      apply Finset.sum_le_sum
      intro rho hrho
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Real.rpow_le_rpow_of_exponent_le hX
      have hupper := (Finset.mem_filter.mp hrho).2.2
      linarith
    _ = ((∑ rho ∈ S, zeroMultiplicity psi 0 T rho : ℕ) : ℝ) * W := by
      push_cast
      rw [Finset.sum_mul]
    _ ≤ (dirichletZeroCount psi sigma T : ℝ) * W := by
      apply mul_le_mul_of_nonneg_right _ hW
      exact_mod_cast hsum
    _ = (primitiveDirichletZeroCount chi sigma T : ℝ) *
        Real.rpow X (2 * (sigma + Delta - 1)) := by
      rfl

/-! ## Final one-application synchronization weld -/

/-- Once the four disjoint range estimates have the exact equation-(2.7)
quantifier order, their synchronization is deterministic.  This theorem is a
staging diagnostic: its hypotheses are theorem parameters, not newly declared
source propositions. -/
theorem apWeightedZeroMassLogSaving_of_range_bounds
    (hLow : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
          apLowRangeMass ⌊Real.rpow (Real.log X) K⌋₊ epsilon X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A))
    (hCompact : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
          apCompactRangeMass ⌊Real.rpow (Real.log X) K⌋₊ epsilon X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A))
    (hRegularNear : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
          apRegularNearOneRangeMass ⌊Real.rpow (Real.log X) K⌋₊ X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A))
    (hExceptional : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
          apExceptionalNearOneRangeMass
              ⌊Real.rpow (Real.log X) K⌋₊ X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A)) :
    APWeightedZeroMassLogSaving := by
  intro K A epsilon hK hA hepsilon hepsilonCap
  obtain ⟨Clow, Xlow, hClow, hXlow, hlow⟩ :=
    hLow K A epsilon hK hA hepsilon hepsilonCap
  obtain ⟨Ccompact, Xcompact, hCcompact, hXcompact, hcompact⟩ :=
    hCompact K A epsilon hK hA hepsilon hepsilonCap
  obtain ⟨Cregular, Xregular, hCregular, hXregular, hregular⟩ :=
    hRegularNear K A epsilon hK hA hepsilon hepsilonCap
  obtain ⟨Cexceptional, Xexceptional, hCexceptional, hXexceptional,
      hexceptional⟩ :=
    hExceptional K A epsilon hK hA hepsilon hepsilonCap
  let C := Clow + Ccompact + Cregular + Cexceptional
  let X0 := max Xlow (max Xcompact (max Xregular Xexceptional))
  refine ⟨C, X0, ?_, ?_, ?_⟩
  · dsimp [C]
    positivity
  · exact hXlow.trans (le_max_left _ _)
  intro X hX
  have hXlow' : Xlow ≤ X := (le_max_left _ _).trans hX
  have hXcompact' : Xcompact ≤ X :=
    (le_max_left Xcompact (max Xregular Xexceptional)).trans
      (le_max_right Xlow _ |>.trans hX)
  have hXregular' : Xregular ≤ X :=
    (le_max_left Xregular Xexceptional).trans
      ((le_max_right Xcompact _).trans (le_max_right Xlow _ |>.trans hX))
  have hXexceptional' : Xexceptional ≤ X :=
    (le_max_right Xregular Xexceptional).trans
      ((le_max_right Xcompact _).trans (le_max_right Xlow _ |>.trans hX))
  let Q := ⌊Real.rpow (Real.log X) K⌋₊
  let T := apZeroHeight epsilon X
  have hsplit := apWeightedZeroMass_eq_four_ranges
    Q epsilon X T
  dsimp only at ⊢
  change apWeightedZeroMass Q X T ≤ C * Real.rpow (Real.log X) (-A)
  rw [hsplit]
  calc
    apLowRangeMass Q epsilon X T + apCompactRangeMass Q epsilon X T +
        apRegularNearOneRangeMass Q X T +
          apExceptionalNearOneRangeMass Q X T ≤
      Clow * Real.rpow (Real.log X) (-A) +
          Ccompact * Real.rpow (Real.log X) (-A) +
            Cregular * Real.rpow (Real.log X) (-A) +
              Cexceptional * Real.rpow (Real.log X) (-A) :=
      add_le_add
        (add_le_add (add_le_add (hlow X hXlow') (hcompact X hXcompact'))
          (hregular X hXregular'))
        (hexceptional X hXexceptional')
    _ = C * Real.rpow (Real.log X) (-A) := by
      dsimp [C]
      ring

end
end MAPAPWeightedZeroMassIntegration

#print axioms MAPAPWeightedZeroMassIntegration.primitiveWeightedZeroMass_eq_low_add_compact_add_near
#print axioms MAPAPWeightedZeroMassIntegration.apWeightedZeroMass_eq_low_add_compact_add_near
#print axioms MAPAPWeightedZeroMassIntegration.primitiveNearOneRangeMass_eq_regular_add_exceptional
#print axioms MAPAPWeightedZeroMassIntegration.apNearOneRangeMass_eq_regular_add_exceptional
#print axioms MAPAPWeightedZeroMassIntegration.apWeightedZeroMass_eq_four_ranges
#print axioms MAPAPWeightedZeroMassIntegration.primitiveRegularNearOneRangeMass_eq_lowHeight_add_highHeight
#print axioms MAPAPWeightedZeroMassIntegration.apRegularNearOneRangeMass_eq_lowHeight_add_highHeight
#print axioms MAPAPWeightedZeroMassIntegration.dirichletZeroCount_le_ambientZeroCountAtLevel
#print axioms MAPAPWeightedZeroMassIntegration.jutila_fixedModulusFamily_to_primitiveInducerFamily
#print axioms MAPAPWeightedZeroMassIntegration.jutila_source_to_primitiveInducerFamily
#print axioms MAPAPWeightedZeroMassIntegration.primitiveInducerCellMass_le_count_weight
#print axioms MAPAPWeightedZeroMassIntegration.apWeightedZeroMassLogSaving_of_range_bounds
