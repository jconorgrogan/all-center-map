import CGLCompactStripDensityConstructor
import AppendixA45GrowthConnector
import AppendixA4PostA5SetAdapter

/-!
# Deterministic post-A.5 crowding bookkeeping

This file records the literal multiplicity and two-branch cardinal losses
before the remaining Fourier and Type-II analytic estimates are invoked.
-/

namespace PostA5CrowdingDeterministic

open DirichletZeros MAPLocalZeroWindow MAPMellinDetectorLeaf
open MAPAPZeroDensityCert

noncomputable section

variable {q : ℕ} [NeZero q]

/-- A zero in a global rectangle belongs to the closed unit window based at
the floor of its ordinate. -/
theorem mem_closedUnitWindowSupport_floor
    (chi : DirichletCharacter ℂ q) {σ T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport chi σ T) :
    ρ ∈ closedUnitWindowSupport chi σ (Int.floor ρ.im) := by
  have hglobal : ρ ∈ zeroRectangle σ T :=
    (zeroDivisor chi σ T).supportWithinDomain
      ((zeroSupport_mem_iff chi σ T ρ).mp hρ)
  have hzero : regularizedLFunction chi ρ = 0 :=
    regularizedLFunction_eq_zero_of_mem_zeroSupport chi σ T hρ
  have hfloor : ((Int.floor ρ.im : ℤ) : ℝ) ≤ ρ.im := Int.floor_le _
  have hceil : ρ.im < ((Int.floor ρ.im : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have habs : |ρ.im| ≤ |((Int.floor ρ.im : ℤ) : ℝ)| + 1 := by
    rw [abs_le]
    constructor
    · have hnegfloor :
          -|((Int.floor ρ.im : ℤ) : ℝ)| ≤
            ((Int.floor ρ.im : ℤ) : ℝ) := neg_abs_le _
      linarith
    · have hfloorabs :
          ((Int.floor ρ.im : ℤ) : ℝ) ≤
            |((Int.floor ρ.im : ℤ) : ℝ)| := le_abs_self _
      linarith
  have hlocalRect :
      ρ ∈ zeroRectangle σ (windowHeight (Int.floor ρ.im)) := by
    rw [zeroRectangle, Complex.mem_reProdIm]
    refine ⟨(Complex.mem_reProdIm.mp hglobal).1, ?_⟩
    rw [windowHeight]
    exact abs_le.mp habs
  have hlocal :
      ρ ∈ zeroSupport chi σ (windowHeight (Int.floor ρ.im)) :=
    (mem_zeroSupport_iff_eq_zero chi σ _ hlocalRect).mpr hzero
  rw [closedUnitWindowSupport, Finset.mem_filter]
  exact ⟨hlocal, hfloor, hceil.le⟩

/-- Analytic multiplicity is independent of whether it is computed in the
global rectangle or in the floor-based unit-window rectangle. -/
theorem zeroMultiplicity_eq_floor_window
    (chi : DirichletCharacter ℂ q) {σ T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport chi σ T) :
    zeroMultiplicity chi σ T ρ =
      zeroMultiplicity chi σ (windowHeight (Int.floor ρ.im)) ρ := by
  have hglobal : ρ ∈ zeroRectangle σ T :=
    (zeroDivisor chi σ T).supportWithinDomain
      ((zeroSupport_mem_iff chi σ T ρ).mp hρ)
  have hlocalSupport := mem_closedUnitWindowSupport_floor chi hρ
  have hlocal :
      ρ ∈ zeroRectangle σ (windowHeight (Int.floor ρ.im)) :=
    closedUnitWindowSupport_mem_rectangle chi hlocalSupport
  exact zeroMultiplicity_eq_of_mem_rectangles chi hglobal hlocal

/-- Every individual global multiplicity is bounded by the certified A.5
count in its floor-based closed unit window. -/
theorem zeroMultiplicity_le_floor_closedUnitWindowCount
    (chi : DirichletCharacter ℂ q) {σ T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport chi σ T) :
    zeroMultiplicity chi σ T ρ ≤
      closedUnitWindowCount chi σ (Int.floor ρ.im) := by
  rw [zeroMultiplicity_eq_floor_window chi hρ]
  unfold closedUnitWindowCount
  exact Finset.single_le_sum
    (fun z _ => Nat.zero_le (zeroMultiplicity chi σ
      (windowHeight (Int.floor ρ.im)) z))
    (mem_closedUnitWindowSupport_floor chi hρ)

/-- Literal multiplicity death test: the certified local A.5 theorem bounds
each global analytic multiplicity by a logarithmic, rather than power-sized,
factor. -/
theorem zeroMultiplicity_le_certifiedA5Envelope
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {σ T : ℝ} (hσ : 1 / 2 ≤ σ) {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport chi σ T) :
    (zeroMultiplicity chi σ T ρ : ℝ) ≤
      (Real.log 3 + Real.log 3200 +
          2 * Real.log (arithmeticScale q (Int.floor ρ.im))) /
        Real.log (jensenOuterRadius / jensenInnerRadius) := by
  exact (Nat.cast_le.mpr
    (zeroMultiplicity_le_floor_closedUnitWindowCount chi hρ)).trans
      (MAPAppendixA45GrowthConnector.certifiedAppendixA5LocalZeroCount
        chi hchi hσ)

/-- The floor of a real number differs from it by less than one, in the
absolute-value form needed to make the A.5 cap uniform over a global
rectangle. -/
theorem abs_floor_le_abs_add_one (x : ℝ) :
    |((Int.floor x : ℤ) : ℝ)| ≤ |x| + 1 := by
  have hfloor : ((Int.floor x : ℤ) : ℝ) ≤ x := Int.floor_le _
  have hceil : x < ((Int.floor x : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  rw [abs_le]
  constructor
  · have hx : -|x| ≤ x := neg_abs_le x
    linarith
  · have hx : x ≤ |x| := le_abs_self x
    linarith

/-- A single logarithmic cap uniform over every zero with `|Im rho| <= T`. -/
def certifiedA5CrowdingEnvelope (q : ℕ) (T : ℝ) : ℝ :=
  (Real.log 3 + Real.log 3200 +
      2 * Real.log ((q : ℝ) * (T + 3))) /
    Real.log (17 / 16)

/-- The local multiplicity factor is uniformly logarithmic in `q(T+3)`.
This is the literal multiplicity/crowding death test: no factor proportional
to a positive power of `T` occurs. -/
theorem zeroMultiplicity_le_uniformA5CrowdingEnvelope
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {σ T : ℝ} (hσ : 1 / 2 ≤ σ) (hT : 0 ≤ T) {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport chi σ T) :
    (zeroMultiplicity chi σ T ρ : ℝ) ≤
      certifiedA5CrowdingEnvelope q T := by
  have hglobal : ρ ∈ zeroRectangle σ T :=
    (zeroDivisor chi σ T).supportWithinDomain
      ((zeroSupport_mem_iff chi σ T ρ).mp hρ)
  have him : |ρ.im| ≤ T :=
    abs_le.mpr (Complex.mem_reProdIm.mp hglobal).2
  have hfloor := abs_floor_le_abs_add_one ρ.im
  have hqone : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hscalePos :
      0 < arithmeticScale q (Int.floor ρ.im) := by
    unfold arithmeticScale
    positivity
  have htargetPos : 0 < (q : ℝ) * (T + 3) := by positivity
  have hscale :
      arithmeticScale q (Int.floor ρ.im) ≤ (q : ℝ) * (T + 3) := by
    unfold arithmeticScale
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have hlog := Real.log_le_log hscalePos hscale
  have hbase := zeroMultiplicity_le_certifiedA5Envelope chi hchi hσ hρ
  have hden : 0 < Real.log (17 / 16 : ℝ) := Real.log_pos (by norm_num)
  rw [show jensenOuterRadius / jensenInnerRadius = (17 / 16 : ℝ) by
    norm_num [jensenOuterRadius, jensenInnerRadius]] at hbase
  apply hbase.trans
  unfold certifiedA5CrowdingEnvelope
  apply (div_le_div_iff_of_pos_right hden).2
  linarith

/-- Summing the preceding pointwise cap retains analytic multiplicity exactly
and costs only the same logarithmic envelope times the number of distinct
zeros. -/
theorem dirichletZeroCount_le_crowdingEnvelope_mul_supportCard
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {σ T : ℝ} (hσ : 1 / 2 ≤ σ) (hT : 0 ≤ T) :
    (dirichletZeroCount chi σ T : ℝ) ≤
      certifiedA5CrowdingEnvelope q T * (zeroSupport chi σ T).card := by
  unfold dirichletZeroCount
  push_cast
  calc
    ∑ ρ ∈ zeroSupport chi σ T,
        (zeroMultiplicity chi σ T ρ : ℝ) ≤
        ∑ _ρ ∈ zeroSupport chi σ T,
          certifiedA5CrowdingEnvelope q T := by
      apply Finset.sum_le_sum
      intro ρ hρ
      exact zeroMultiplicity_le_uniformA5CrowdingEnvelope
        chi hchi hσ hT hρ
    _ = certifiedA5CrowdingEnvelope q T *
        (zeroSupport chi σ T).card := by
      simp [mul_comm]

def certifiedA5CrowdingNatCap (q : ℕ) (T : ℝ) : ℕ :=
  ⌈max 0 (certifiedA5CrowdingEnvelope q T)⌉₊

theorem floor_closedUnitWindowCount_le_uniformA5CrowdingEnvelope
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {σ T : ℝ} (hσ : 1 / 2 ≤ σ) (hT : 0 ≤ T) {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport chi σ T) :
    (closedUnitWindowCount chi σ (Int.floor ρ.im) : ℝ) ≤
      certifiedA5CrowdingEnvelope q T := by
  have hglobal : ρ ∈ zeroRectangle σ T :=
    (zeroDivisor chi σ T).supportWithinDomain
      ((zeroSupport_mem_iff chi σ T ρ).mp hρ)
  have him : |ρ.im| ≤ T :=
    abs_le.mpr (Complex.mem_reProdIm.mp hglobal).2
  have hfloor := abs_floor_le_abs_add_one ρ.im
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hscalePos :
      0 < arithmeticScale q (Int.floor ρ.im) := by
    unfold arithmeticScale
    exact mul_pos hqpos (by positivity)
  have hscale :
      arithmeticScale q (Int.floor ρ.im) ≤ (q : ℝ) * (T + 3) := by
    unfold arithmeticScale
    apply mul_le_mul_of_nonneg_left _ hqpos.le
    linarith
  have hlog := Real.log_le_log hscalePos hscale
  have hbase :=
    MAPAppendixA45GrowthConnector.certifiedAppendixA5LocalZeroCount
      chi hchi hσ (t := (Int.floor ρ.im : ℝ))
  have hden : 0 < Real.log (17 / 16 : ℝ) := Real.log_pos (by norm_num)
  rw [show jensenOuterRadius / jensenInnerRadius = (17 / 16 : ℝ) by
    norm_num [jensenOuterRadius, jensenInnerRadius]] at hbase
  apply hbase.trans
  unfold certifiedA5CrowdingEnvelope
  apply (div_le_div_iff_of_pos_right hden).2
  linarith

/-- The certified real logarithmic envelope can be used as a literal natural
fiber cap without changing its growth class. -/
theorem floor_closedUnitWindowCount_le_crowdingNatCap
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {σ T : ℝ} (hσ : 1 / 2 ≤ σ) (hT : 0 ≤ T) {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport chi σ T) :
    closedUnitWindowCount chi σ (Int.floor ρ.im) ≤
      certifiedA5CrowdingNatCap q T := by
  have hreal := floor_closedUnitWindowCount_le_uniformA5CrowdingEnvelope
    chi hchi hσ hT hρ
  have hmax :
      (closedUnitWindowCount chi σ (Int.floor ρ.im) : ℝ) ≤
        max 0 (certifiedA5CrowdingEnvelope q T) :=
    hreal.trans (le_max_right _ _)
  have hceil :
      max 0 (certifiedA5CrowdingEnvelope q T) ≤
        (certifiedA5CrowdingNatCap q T : ℝ) := by
    exact Nat.le_ceil _
  exact_mod_cast hmax.trans hceil

/-- A Type-II critical-line witness shifted by at most `B` can only move a
zero into a unit target interval from the expanded interval of length
`2B+1`.  For the certified choice `B=(log R)^2` this is polylogarithmic. -/
theorem shifted_unit_preimage_mem_expanded_interval
    {gamma u a B : ℝ} (hB : 0 ≤ B) (hu : |u| ≤ B)
    (hout : gamma + u ∈ Set.Icc a (a + 1)) :
    gamma ∈ Set.Icc (a - B) (a + 1 + B) := by
  have hub := abs_le.mp hu
  constructor <;> linarith [hout.1, hout.2]

/-- Predicate saying that the occupied floor bins of a selected zero set are
two apart.  A parity class of unit bins has exactly this property. -/
def FloorBinsTwoSeparated (S : Finset ℂ) : Prop :=
  ∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' →
    2 ≤
      |(((Int.floor ρ.im : ℤ) : ℝ) -
        ((Int.floor ρ'.im : ℤ) : ℝ))|

/-- Choosing at most one zero from each bin in one parity class produces an
actual one-separated set of ordinates.  The image has exactly the same
cardinality, so this step loses no additional factor after the two-color
choice. -/
theorem oneSeparated_im_image_of_floorBinsTwoSeparated
    {S : Finset ℂ} (hbins : FloorBinsTwoSeparated S) :
    CGLProofDAG.OneSeparated (S.image Complex.im) ∧
      (S.image Complex.im).card = S.card := by
  classical
  have himInj : Set.InjOn Complex.im (↑S : Set ℂ) := by
    intro ρ hρ ρ' hρ' him
    by_contra hne
    have hgap := hbins ρ hρ ρ' hρ' hne
    have hfloorEq : Int.floor ρ.im = Int.floor ρ'.im := by rw [him]
    rw [hfloorEq] at hgap
    norm_num at hgap
  constructor
  · intro t ht u hu htu
    rw [Finset.mem_image] at ht hu
    obtain ⟨ρ, hρ, rfl⟩ := ht
    obtain ⟨ρ', hρ', rfl⟩ := hu
    have hne : ρ ≠ ρ' := by
      intro h
      apply htu
      rw [h]
    have hgap := hbins ρ hρ ρ' hρ' hne
    let n : ℝ := (Int.floor ρ.im : ℤ)
    let m : ℝ := (Int.floor ρ'.im : ℤ)
    have hnlo : n ≤ ρ.im := by dsimp [n]; exact Int.floor_le _
    have hnhi : ρ.im < n + 1 := by dsimp [n]; exact Int.lt_floor_add_one _
    have hmlo : m ≤ ρ'.im := by dsimp [m]; exact Int.floor_le _
    have hmhi : ρ'.im < m + 1 := by dsimp [m]; exact Int.lt_floor_add_one _
    change 2 ≤ |n - m| at hgap
    rcases le_total n m with hnm | hmn
    · rw [abs_of_nonpos (sub_nonpos.mpr hnm)] at hgap
      rw [abs_of_nonpos]
      · linarith
      · linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hmn)] at hgap
      rw [abs_of_nonneg]
      · linarith
      · linarith
  · exact Finset.card_image_iff.mpr himInj

/-! ## Literal two-color extraction from floor bins -/

def occupiedFloorBins (Z : Finset ℂ) : Finset ℤ :=
  Z.image (fun ρ => Int.floor ρ.im)

noncomputable def floorBinRepresentative (Z : Finset ℂ) (n : ℤ) : ℂ :=
  if hn : n ∈ occupiedFloorBins Z then
    Classical.choose (Finset.mem_image.mp hn)
  else 0

theorem floorBinRepresentative_spec
    {Z : Finset ℂ} {n : ℤ} (hn : n ∈ occupiedFloorBins Z) :
    floorBinRepresentative Z n ∈ Z ∧
      Int.floor (floorBinRepresentative Z n).im = n := by
  rw [floorBinRepresentative, dif_pos hn]
  exact Classical.choose_spec (Finset.mem_image.mp hn)

def evenOccupiedFloorBins (Z : Finset ℂ) : Finset ℤ :=
  (occupiedFloorBins Z).filter fun n => n % 2 = 0

def oddOccupiedFloorBins (Z : Finset ℂ) : Finset ℤ :=
  (occupiedFloorBins Z).filter fun n => n % 2 ≠ 0

noncomputable def chosenParityFloorBins (Z : Finset ℂ) : Finset ℤ :=
  if (evenOccupiedFloorBins Z).card ≤ (oddOccupiedFloorBins Z).card then
    oddOccupiedFloorBins Z
  else evenOccupiedFloorBins Z

noncomputable def parityFloorRepresentatives (Z : Finset ℂ) : Finset ℂ :=
  (chosenParityFloorBins Z).image (floorBinRepresentative Z)

theorem chosenParityFloorBins_subset (Z : Finset ℂ) :
    chosenParityFloorBins Z ⊆ occupiedFloorBins Z := by
  intro n hn
  unfold chosenParityFloorBins at hn
  split at hn
  · exact (Finset.mem_filter.mp hn).1
  · exact (Finset.mem_filter.mp hn).1

theorem parityFloorRepresentatives_subset (Z : Finset ℂ) :
    parityFloorRepresentatives Z ⊆ Z := by
  classical
  intro ρ hρ
  rw [parityFloorRepresentatives, Finset.mem_image] at hρ
  obtain ⟨n, hn, rfl⟩ := hρ
  exact (floorBinRepresentative_spec (chosenParityFloorBins_subset Z hn)).1

theorem card_parityFloorRepresentatives (Z : Finset ℂ) :
    (parityFloorRepresentatives Z).card = (chosenParityFloorBins Z).card := by
  classical
  unfold parityFloorRepresentatives
  apply Finset.card_image_iff.mpr
  intro n hn m hm heq
  have hn' := floorBinRepresentative_spec (chosenParityFloorBins_subset Z hn)
  have hm' := floorBinRepresentative_spec (chosenParityFloorBins_subset Z hm)
  rw [heq] at hn'
  exact hn'.2.symm.trans hm'.2

theorem chosenParityFloorBins_large (Z : Finset ℂ) :
    (occupiedFloorBins Z).card ≤ 2 * (chosenParityFloorBins Z).card := by
  classical
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := occupiedFloorBins Z) (fun n : ℤ => n % 2 = 0)
  change (evenOccupiedFloorBins Z).card + (oddOccupiedFloorBins Z).card =
    (occupiedFloorBins Z).card at hsplit
  unfold chosenParityFloorBins
  split_ifs with hcard
  · omega
  · omega

private theorem parity_bins_gap
    {n m : ℤ} (hne : n ≠ m)
    (hparity : (n % 2 = 0 ∧ m % 2 = 0) ∨
      (n % 2 ≠ 0 ∧ m % 2 ≠ 0)) :
    2 ≤ |((n : ℝ) - (m : ℝ))| := by
  have hremn := Int.emod_two_eq_zero_or_one n
  have hremm := Int.emod_two_eq_zero_or_one m
  have hsep : n + 2 ≤ m ∨ m + 2 ≤ n := by
    rcases hparity with h | h <;> rcases hremn with hn | hn <;>
      rcases hremm with hm | hm <;> omega
  rcases hsep with hnm | hmn
  · have hcast : (n : ℝ) + 2 ≤ m := by exact_mod_cast hnm
    rw [abs_of_nonpos]
    · linarith
    · linarith
  · have hcast : (m : ℝ) + 2 ≤ n := by exact_mod_cast hmn
    rw [abs_of_nonneg]
    · linarith
    · linarith

theorem parityFloorRepresentatives_twoSeparated (Z : Finset ℂ) :
    FloorBinsTwoSeparated (parityFloorRepresentatives Z) := by
  classical
  intro ρ hρ ρ' hρ' hne
  rw [parityFloorRepresentatives, Finset.mem_image] at hρ hρ'
  obtain ⟨n, hn, rfl⟩ := hρ
  obtain ⟨m, hm, rfl⟩ := hρ'
  have hnSpec := floorBinRepresentative_spec (chosenParityFloorBins_subset Z hn)
  have hmSpec := floorBinRepresentative_spec (chosenParityFloorBins_subset Z hm)
  rw [hnSpec.2, hmSpec.2]
  apply parity_bins_gap
  · intro hnm
    apply hne
    rw [hnm]
  · by_cases hcard :
        (evenOccupiedFloorBins Z).card ≤ (oddOccupiedFloorBins Z).card
    · simp only [chosenParityFloorBins, if_pos hcard] at hn hm
      exact Or.inr ⟨(Finset.mem_filter.mp hn).2,
        (Finset.mem_filter.mp hm).2⟩
    · simp only [chosenParityFloorBins, if_neg hcard] at hn hm
      exact Or.inl ⟨(Finset.mem_filter.mp hn).2,
        (Finset.mem_filter.mp hm).2⟩

/-- Complete finite crowding extraction.  If the total weight in each unit
floor bin is at most `L`, one parity class supplies actual one-separated
ordinates controlling the full weight with the literal factor `2L`. -/
theorem exists_oneSeparated_ordinates_of_floorBin_weight_cap
    (Z : Finset ℂ) (weight : ℂ → ℕ) (L : ℕ)
    (hcap : ∀ n ∈ occupiedFloorBins Z,
      ∑ ρ ∈ Z with Int.floor ρ.im = n, weight ρ ≤ L) :
    ∃ S : Finset ℂ,
      S ⊆ Z ∧ CGLProofDAG.OneSeparated (S.image Complex.im) ∧
      (S.image Complex.im).card = S.card ∧
      ∑ ρ ∈ Z, weight ρ ≤ 2 * L * S.card := by
  classical
  let S := parityFloorRepresentatives Z
  have hsep := oneSeparated_im_image_of_floorBinsTwoSeparated
    (parityFloorRepresentatives_twoSeparated Z)
  refine ⟨S, parityFloorRepresentatives_subset Z, hsep.1, hsep.2, ?_⟩
  have hmaps : ∀ ρ ∈ Z, Int.floor ρ.im ∈ occupiedFloorBins Z := by
    intro ρ hρ
    exact Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps weight
  have hsum :
      (∑ n ∈ occupiedFloorBins Z,
          ∑ ρ ∈ Z with Int.floor ρ.im = n, weight ρ) ≤
        ∑ _n ∈ occupiedFloorBins Z, L := by
    apply Finset.sum_le_sum
    intro n hn
    exact hcap n hn
  calc
    ∑ ρ ∈ Z, weight ρ =
        ∑ n ∈ occupiedFloorBins Z,
          ∑ ρ ∈ Z with Int.floor ρ.im = n, weight ρ := hfiber.symm
    _ ≤ ∑ _n ∈ occupiedFloorBins Z, L := hsum
    _ = (occupiedFloorBins Z).card * L := by simp
    _ ≤ (2 * (chosenParityFloorBins Z).card) * L := by
      gcongr
      exact chosenParityFloorBins_large Z
    _ = 2 * L * S.card := by
      dsimp [S]
      rw [card_parityFloorRepresentatives]
      ring

/-- Pure two-branch cardinal selection.  If each detector branch is reduced
to a witness set at cost `L`, the larger witness controls their sum at cost
exactly `2L`; no power-sized loss is introduced by choosing a branch. -/
theorem two_branch_cardinal_selection
    {z a b L : ℝ} {W₁ W₂ : Finset ℝ}
    (hL : 0 ≤ L) (hz : z ≤ a + b)
    (ha : a ≤ L * (1 + (W₁.card : ℝ)))
    (hb : b ≤ L * (1 + (W₂.card : ℝ))) :
    (z ≤ 2 * L * (1 + (W₁.card : ℝ)) ∧ W₂.card ≤ W₁.card) ∨
      (z ≤ 2 * L * (1 + (W₂.card : ℝ)) ∧ W₁.card ≤ W₂.card) := by
  rcases le_total W₁.card W₂.card with hcard | hcard
  · right
    refine ⟨?_, hcard⟩
    have hcardR : (W₁.card : ℝ) ≤ W₂.card := by exact_mod_cast hcard
    calc
      z ≤ a + b := hz
      _ ≤ L * (1 + (W₁.card : ℝ)) +
          L * (1 + (W₂.card : ℝ)) := add_le_add ha hb
      _ ≤ 2 * L * (1 + (W₂.card : ℝ)) := by
        nlinarith [mul_nonneg hL
          (sub_nonneg.mpr (add_le_add_left hcardR 1))]
  · left
    refine ⟨?_, hcard⟩
    have hcardR : (W₂.card : ℝ) ≤ W₁.card := by exact_mod_cast hcard
    calc
      z ≤ a + b := hz
      _ ≤ L * (1 + (W₁.card : ℝ)) +
          L * (1 + (W₂.card : ℝ)) := add_le_add ha hb
      _ ≤ 2 * L * (1 + (W₁.card : ℝ)) := by
        nlinarith [mul_nonneg hL
          (sub_nonneg.mpr (add_le_add_left hcardR 1))]

end
end PostA5CrowdingDeterministic

#print axioms PostA5CrowdingDeterministic.zeroMultiplicity_le_certifiedA5Envelope
#print axioms PostA5CrowdingDeterministic.two_branch_cardinal_selection
