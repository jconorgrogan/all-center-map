import HarmonicInterfaces

/-!
# Literal support and boundary weld for the MAP prime-pair correlation

This file keeps the half-open dyadic interval `(X,2X]` literal.  It separates
the twice-supported correlation delivered by the Fourier coefficient of
`|S_X|^2` from the one-sided public correlation `R_X(h)`, and proves the exact
finite boundary decomposition between them.
-/

namespace SupportBoundaryWeld

open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The public half-open dyadic support, named once to prevent endpoint drift. -/
def dyadicSupport (X : ℝ) : Finset ℕ :=
  Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊

/-- Whether the shifted index is positive and remains in the same half-open
dyadic support. -/
def shiftStaysInSupport (X : ℝ) (n : ℕ) (h : ℤ) : Prop :=
  0 < (n : ℤ) + h ∧ ((n : ℤ) + h).toNat ∈ dyadicSupport X

instance (X : ℝ) (n : ℕ) (h : ℤ) :
    Decidable (shiftStaysInSupport X n h) := Classical.propDecidable _

/-- The one-body form of the twice-supported correlation. -/
def twiceSupportedCorrelation (X : ℝ) (h : ℤ) : ℝ :=
  ∑ n ∈ dyadicSupport X,
    if shiftStaysInSupport X n h then
      ArithmeticFunction.vonMangoldt n *
        PrimePairEndpoints.integerVonMangoldt ((n : ℤ) + h)
    else 0

/-- The exact collar discarded when one replaces the public one-sided
`R_X(h)` by the twice-supported Fourier correlation. -/
def supportBoundaryCorrection (X : ℝ) (h : ℤ) : ℝ :=
  ∑ n ∈ dyadicSupport X,
    if shiftStaysInSupport X n h then 0 else
      ArithmeticFunction.vonMangoldt n *
        PrimePairEndpoints.integerVonMangoldt ((n : ℤ) + h)

/-- Literal indices on which the boundary correction can be nonzero. -/
def boundarySupport (X : ℝ) (h : ℤ) : Finset ℕ :=
  (dyadicSupport X).filter fun n ↦
    0 < (n : ℤ) + h ∧
      ((n : ℤ) + h).toNat ∉ dyadicSupport X

/-- A sign-sensitive endpoint collar containing every boundary index.  For a
positive shift it is the last `|h|` possible base indices; for a negative
shift it is the first `|h|` possible base indices. -/
def boundaryCollar (X : ℝ) (h : ℤ) : Finset ℕ :=
  if 0 ≤ h then
    Finset.Ioc (⌊2 * X⌋₊ - h.natAbs) ⌊2 * X⌋₊
  else
    Finset.Ioc ⌊X⌋₊ (⌊X⌋₊ + h.natAbs)

theorem dyadicSupport_eq_public (X : ℝ) :
    dyadicSupport X = Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ := rfl

/-- Exact pointwise partition of the public correlation into its interior and
boundary-collar contributions. -/
theorem primePairCorrelation_eq_twiceSupported_add_boundary
    (X : ℝ) (h : ℤ) :
    PrimePairEndpoints.primePairCorrelation X h =
      twiceSupportedCorrelation X h + supportBoundaryCorrection X h := by
  classical
  unfold PrimePairEndpoints.primePairCorrelation twiceSupportedCorrelation
    supportBoundaryCorrection dyadicSupport
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hs : shiftStaysInSupport X n h <;> simp [hs]

/-- Terms for which the shifted integer is nonpositive vanish exactly, so the
boundary correction can be summed over `boundarySupport`. -/
theorem supportBoundaryCorrection_eq_sum_boundarySupport
    (X : ℝ) (h : ℤ) :
    supportBoundaryCorrection X h =
      ∑ n ∈ boundarySupport X h,
        ArithmeticFunction.vonMangoldt n *
          PrimePairEndpoints.integerVonMangoldt ((n : ℤ) + h) := by
  classical
  unfold supportBoundaryCorrection boundarySupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : 0 < (n : ℤ) + h
  · by_cases hm : ((n : ℤ) + h).toNat ∈ dyadicSupport X
    · simp [shiftStaysInSupport, hp, hm]
    · simp [shiftStaysInSupport, hp, hm]
  · have hz : PrimePairEndpoints.integerVonMangoldt ((n : ℤ) + h) = 0 := by
      simp [PrimePairEndpoints.integerVonMangoldt, hp]
    simp [shiftStaysInSupport, hp, hz]

/-- Membership in the half-open dyadic support implies strict positivity. -/
theorem pos_of_mem_dyadicSupport {X : ℝ} {n : ℕ}
    (hn : n ∈ dyadicSupport X) : 0 < n := by
  simp only [dyadicSupport, Finset.mem_Ioc] at hn
  omega

/-- If a supported pair has difference `h`, its right endpoint satisfies the
literal one-body support predicate. -/
theorem shiftStaysInSupport_of_pair
    {X : ℝ} {n m : ℕ} {h : ℤ}
    (hn : n ∈ dyadicSupport X) (heq : (n : ℤ) - (m : ℤ) = h) :
    shiftStaysInSupport X m h := by
  have hnpos : 0 < n := pos_of_mem_dyadicSupport hn
  have hshift : (m : ℤ) + h = n := by omega
  unfold shiftStaysInSupport
  constructor
  · rw [hshift]
    exact_mod_cast hnpos
  · rw [hshift, Int.toNat_natCast]
    exact hn

/-- Under the support predicate, converting the shifted integer to a natural
number loses no information. -/
theorem shifted_toNat_cast
    {X : ℝ} {m : ℕ} {h : ℤ}
    (hs : shiftStaysInSupport X m h) :
    (((m : ℤ) + h).toNat : ℤ) = (m : ℤ) + h := by
  exact Int.toNat_of_nonneg (le_of_lt hs.1)

/-- The literal boundary support lies in the appropriate endpoint collar. -/
theorem boundarySupport_subset_boundaryCollar (X : ℝ) (h : ℤ) :
    boundarySupport X h ⊆ boundaryCollar X h := by
  intro n hn
  simp only [boundarySupport, Finset.mem_filter, dyadicSupport,
    Finset.mem_Ioc] at hn
  rcases hn with ⟨⟨hnlo, hnhi⟩, hshiftpos, hshiftout⟩
  by_cases hh : 0 ≤ h
  · simp only [boundaryCollar, if_pos hh, Finset.mem_Ioc]
    have hhabs : (h.natAbs : ℤ) = h := Int.natAbs_of_nonneg hh
    have hshiftcast : ((((n : ℤ) + h).toNat : ℕ) : ℤ) =
        (n : ℤ) + h := Int.toNat_of_nonneg (le_of_lt hshiftpos)
    have hnotLower : ⌊X⌋₊ < ((n : ℤ) + h).toNat := by
      have hnloZ : (⌊X⌋₊ : ℤ) < (n : ℤ) := by exact_mod_cast hnlo
      have hnatZ : (n : ℤ) ≤ (((n : ℤ) + h).toNat : ℤ) := by
        rw [hshiftcast]
        omega
      have hz : (⌊X⌋₊ : ℤ) < (((n : ℤ) + h).toNat : ℤ) :=
        hnloZ.trans_le hnatZ
      exact_mod_cast hz
    have hover : ⌊2 * X⌋₊ < ((n : ℤ) + h).toNat := by
      by_contra hnot
      exact hshiftout ⟨hnotLower, Nat.le_of_not_gt hnot⟩
    constructor
    · omega
    · exact hnhi
  · have hhneg : h < 0 := lt_of_not_ge hh
    simp only [boundaryCollar, if_neg hh, Finset.mem_Ioc]
    have hshiftcast : ((((n : ℤ) + h).toNat : ℕ) : ℤ) =
        (n : ℤ) + h := Int.toNat_of_nonneg (le_of_lt hshiftpos)
    have hnotUpper : ((n : ℤ) + h).toNat ≤ ⌊2 * X⌋₊ := by
      have hle : (n : ℤ) + h ≤ (n : ℤ) := by omega
      exact_mod_cast (show ((((n : ℤ) + h).toNat : ℕ) : ℤ) ≤
        (⌊2 * X⌋₊ : ℤ) by omega)
    have hunder : ((n : ℤ) + h).toNat ≤ ⌊X⌋₊ := by
      by_contra hnot
      exact hshiftout ⟨Nat.lt_of_not_ge hnot, hnotUpper⟩
    constructor
    · exact hnlo
    · have hhabs : (h.natAbs : ℤ) = -h := by
        rw [← Int.natAbs_neg]
        exact Int.natAbs_of_nonneg (by omega)
      exact_mod_cast (show (n : ℤ) ≤
        (⌊X⌋₊ : ℤ) + (h.natAbs : ℤ) by omega)

/-- The number of possible nonzero boundary terms is at most `|h|`, with no
extra endpoint atom. -/
theorem boundarySupport_card_le_natAbs (X : ℝ) (h : ℤ) :
    (boundarySupport X h).card ≤ h.natAbs := by
  calc
    (boundarySupport X h).card ≤ (boundaryCollar X h).card :=
      Finset.card_le_card (boundarySupport_subset_boundaryCollar X h)
    _ ≤ h.natAbs := by
      unfold boundaryCollar
      by_cases hh : 0 ≤ h
      · rw [if_pos hh, Nat.card_Ioc]
        omega
      · rw [if_neg hh, Nat.card_Ioc]
        omega

/-- Collapse the inner supported pair sum to its unique shifted index. -/
theorem inner_supported_sum_eq
    (X : ℝ) (m : ℕ) (h : ℤ) :
    (∑ n ∈ dyadicSupport X,
      if (n : ℤ) - (m : ℤ) = h then
        ArithmeticFunction.vonMangoldt n *
          ArithmeticFunction.vonMangoldt m
      else 0) =
      if shiftStaysInSupport X m h then
        ArithmeticFunction.vonMangoldt m *
          PrimePairEndpoints.integerVonMangoldt ((m : ℤ) + h)
      else 0 := by
  classical
  by_cases hs : shiftStaysInSupport X m h
  · let k : ℕ := ((m : ℤ) + h).toNat
    have hk : k ∈ dyadicSupport X := hs.2
    have hkcast : (k : ℤ) = (m : ℤ) + h := shifted_toNat_cast hs
    rw [if_pos hs]
    rw [Finset.sum_eq_single k]
    · rw [if_pos (by omega)]
      unfold PrimePairEndpoints.integerVonMangoldt
      rw [if_pos hs.1]
      simp only [k]
      ring
    · intro b hb hbk
      rw [if_neg]
      intro heq
      have : (b : ℤ) = (k : ℤ) := by omega
      exact hbk (Int.ofNat_inj.mp this)
    · exact fun hkn ↦ (hkn hk).elim
  · rw [if_neg hs]
    apply Finset.sum_eq_zero
    intro n hn
    rw [if_neg]
    intro heq
    exact hs (shiftStaysInSupport_of_pair hn heq)

/-- The one-body twice-supported sum is exactly the Fourier correlation from
`HarmonicInterfaces`; no boundary term is hidden in this equality. -/
theorem supportedCorrelation_eq_twiceSupported
    (X : ℝ) (h : ℤ) :
    MAPHarmonicEndpoint.supportedCorrelation X h =
      twiceSupportedCorrelation X h := by
  classical
  unfold MAPHarmonicEndpoint.supportedCorrelation twiceSupportedCorrelation
    dyadicSupport
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  exact inner_supported_sum_eq X m h

/-- The exact manuscript-facing weld from the major/minor Fourier split to the
public one-sided `R_X(h)`. -/
theorem primePairCorrelation_eq_major_add_minor_add_boundary
    (X : ℝ) (B D : ℕ) (h : ℤ) :
    (PrimePairEndpoints.primePairCorrelation X h : ℂ) =
      MAPHarmonicEndpoint.majorCoefficient X B D h +
      MAPHarmonicEndpoint.minorCoefficient X B D h +
      (supportBoundaryCorrection X h : ℂ) := by
  rw [primePairCorrelation_eq_twiceSupported_add_boundary]
  rw [← supportedCorrelation_eq_twiceSupported]
  push_cast
  rw [MAPHarmonicEndpoint.supportedCorrelation_eq_major_add_minor]

/-- At zero shift the two supports coincide, so there is no collar term. -/
@[simp] theorem supportBoundaryCorrection_zero (X : ℝ) :
    supportBoundaryCorrection X 0 = 0 := by
  rw [supportBoundaryCorrection_eq_sum_boundarySupport]
  apply Finset.sum_eq_zero
  intro n hn
  simp only [boundarySupport, Finset.mem_filter] at hn
  exact (hn.2.2 hn.1).elim

/-- Exact nonzero-shift passage to the signal used in the public variance.  The
zero shift is deliberately handled separately by `primePairSignal`. -/
theorem primePairSignal_eq_major_add_minor_add_boundary
    (X : ℝ) (B D : ℕ) (h : ℤ) (hh : h ≠ 0) :
    (PrimePairEndpoints.primePairSignal X h : ℂ) =
      MAPHarmonicEndpoint.majorCoefficient X B D h +
      MAPHarmonicEndpoint.minorCoefficient X B D h +
      (supportBoundaryCorrection X h : ℂ) := by
  simp only [PrimePairEndpoints.primePairSignal, if_neg hh]
  exact primePairCorrelation_eq_major_add_minor_add_boundary X B D h

end

end SupportBoundaryWeld
