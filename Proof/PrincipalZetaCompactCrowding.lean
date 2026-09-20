import PrincipalZetaFullStrip
import PostA5CrowdingDeterministic

/-!
# Multiplicity-aware crowding for the conductor-one zeta zeros

The nonprincipal post-A.5 route cannot be specialized to modulus one because
its local Jensen estimate carries the hypothesis `chi != 1`.  The project now
has an independent, premise-free full-strip Jensen estimate for the
regularized conductor-one zeta function.  This file connects that estimate to
the generic finite floor-bin thinning machinery.

No zero-density estimate is asserted here.  The output is the exact
logarithmic multiplicity/crowding loss needed before the zeta-specific
zero-detector is fed to Guth--Maynard large values.
-/

namespace MAPPrincipalZetaCompactCrowding

open Filter
open DirichletZeros MAPLocalZeroWindow MAPMellinDetectorLeaf
open MAPAPZeroDensityCert PostA5CrowdingDeterministic

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)

/-- A zero in the global principal rectangle remains a zero in the full-strip
unit window based at the floor of its ordinate. -/
theorem mem_principal_fullStrip_floor_window
    {sigma T : ℝ} (hsigma : 0 ≤ sigma) {rho : ℂ}
    (hrho : rho ∈ zeroSupport chiOne sigma T) :
    rho ∈ closedUnitWindowSupport chiOne 0 (Int.floor rho.im) := by
  have hglobal : rho ∈ zeroRectangle sigma T :=
    (zeroDivisor chiOne sigma T).supportWithinDomain
      ((zeroSupport_mem_iff chiOne sigma T rho).mp hrho)
  have hzero : regularizedLFunction chiOne rho = 0 :=
    regularizedLFunction_eq_zero_of_mem_zeroSupport chiOne sigma T hrho
  have hfloor : ((Int.floor rho.im : ℤ) : ℝ) ≤ rho.im := Int.floor_le _
  have hceil : rho.im < ((Int.floor rho.im : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have habs : |rho.im| ≤ |((Int.floor rho.im : ℤ) : ℝ)| + 1 := by
    rw [abs_le]
    constructor
    · have hnegfloor :
          -|((Int.floor rho.im : ℤ) : ℝ)| ≤
            ((Int.floor rho.im : ℤ) : ℝ) := neg_abs_le _
      linarith
    · have hfloorabs :
          ((Int.floor rho.im : ℤ) : ℝ) ≤
            |((Int.floor rho.im : ℤ) : ℝ)| := le_abs_self _
      linarith
  have hlocalRect :
      rho ∈ zeroRectangle 0 (windowHeight (Int.floor rho.im)) := by
    rw [zeroRectangle, Complex.mem_reProdIm]
    refine ⟨⟨?_, (Complex.mem_reProdIm.mp hglobal).1.2⟩, ?_⟩
    · exact hsigma.trans (Complex.mem_reProdIm.mp hglobal).1.1
    · rw [windowHeight]
      exact abs_le.mp habs
  rw [closedUnitWindowSupport, Finset.mem_filter]
  refine ⟨(mem_zeroSupport_iff_eq_zero chiOne 0 _ hlocalRect).mpr hzero,
    hfloor, hceil.le⟩

/-- The analytic multiplicity is unchanged when the principal zero is viewed
in its full-strip floor window. -/
theorem principal_zeroMultiplicity_eq_fullStrip_floor_window
    {sigma T : ℝ} (hsigma : 0 ≤ sigma) {rho : ℂ}
    (hrho : rho ∈ zeroSupport chiOne sigma T) :
    zeroMultiplicity chiOne sigma T rho =
      zeroMultiplicity chiOne 0 (windowHeight (Int.floor rho.im)) rho := by
  have hglobal : rho ∈ zeroRectangle sigma T :=
    (zeroDivisor chiOne sigma T).supportWithinDomain
      ((zeroSupport_mem_iff chiOne sigma T rho).mp hrho)
  have hlocal := closedUnitWindowSupport_mem_rectangle chiOne
    (mem_principal_fullStrip_floor_window hsigma hrho)
  exact zeroMultiplicity_eq_of_mem_rectangles chiOne hglobal hlocal

/-- Every principal multiplicity is bounded by the premise-free full-strip
local zeta count.  The factor `1683` and the symmetric scale are literal. -/
theorem principal_zeroMultiplicity_le_floor_log
    {sigma T : ℝ} (hsigma : 0 ≤ sigma) {rho : ℂ}
    (hrho : rho ∈ zeroSupport chiOne sigma T) :
    (zeroMultiplicity chiOne sigma T rho : ℝ) ≤
      1683 * Real.log (arithmeticScale 1 (Int.floor rho.im)) := by
  rw [principal_zeroMultiplicity_eq_fullStrip_floor_window hsigma hrho]
  have hmem := mem_principal_fullStrip_floor_window hsigma hrho
  have hsingle :
      zeroMultiplicity chiOne 0 (windowHeight (Int.floor rho.im)) rho ≤
        closedUnitWindowCount chiOne 0 (Int.floor rho.im) := by
    unfold closedUnitWindowCount
    exact Finset.single_le_sum
      (fun z _ => Nat.zero_le
        (zeroMultiplicity chiOne 0 (windowHeight (Int.floor rho.im)) z))
      hmem
  exact (Nat.cast_le.mpr hsingle).trans
    (MAPPrincipalZetaFullStrip.principal_fullStrip_count_le_log
      (Int.floor rho.im))

/-- A single logarithmic envelope valid simultaneously for every principal
zero with symmetric height at most `T`. -/
theorem principal_zeroMultiplicity_le_uniform_log
    {sigma T : ℝ} (hsigma : 0 ≤ sigma) (hT : 0 ≤ T) {rho : ℂ}
    (hrho : rho ∈ zeroSupport chiOne sigma T) :
    (zeroMultiplicity chiOne sigma T rho : ℝ) ≤
      1683 * Real.log (T + 3) := by
  have hglobal : rho ∈ zeroRectangle sigma T :=
    (zeroDivisor chiOne sigma T).supportWithinDomain
      ((zeroSupport_mem_iff chiOne sigma T rho).mp hrho)
  have him : |rho.im| ≤ T :=
    abs_le.mpr (Complex.mem_reProdIm.mp hglobal).2
  have hfloor := abs_floor_le_abs_add_one rho.im
  have hscalePos : 0 < arithmeticScale 1 (Int.floor rho.im) := by
    unfold arithmeticScale
    positivity
  have htargetPos : 0 < T + 3 := by linarith
  have hscale : arithmeticScale 1 (Int.floor rho.im) ≤ T + 3 := by
    simp only [arithmeticScale, Nat.cast_one, one_mul]
    linarith
  have hlog := Real.log_le_log hscalePos hscale
  exact (principal_zeroMultiplicity_le_floor_log hsigma hrho).trans
    (mul_le_mul_of_nonneg_left hlog (by norm_num))

/-- The complete divisor-backed count is bounded by the same logarithmic
envelope times the number of distinct zeros; multiplicity is never dropped. -/
theorem principal_dirichletZeroCount_le_log_mul_supportCard
    {sigma T : ℝ} (hsigma : 0 ≤ sigma) (hT : 0 ≤ T) :
    (dirichletZeroCount chiOne sigma T : ℝ) ≤
      (1683 * Real.log (T + 3)) * (zeroSupport chiOne sigma T).card := by
  unfold dirichletZeroCount
  push_cast
  calc
    ∑ rho ∈ zeroSupport chiOne sigma T,
        (zeroMultiplicity chiOne sigma T rho : ℝ) ≤
        ∑ _rho ∈ zeroSupport chiOne sigma T,
          1683 * Real.log (T + 3) := by
      apply Finset.sum_le_sum
      intro rho hrho
      exact principal_zeroMultiplicity_le_uniform_log hsigma hT hrho
    _ = (1683 * Real.log (T + 3)) *
        (zeroSupport chiOne sigma T).card := by
      simp [mul_comm]

/-- The exact floor-bin weight cap consumed by the generic two-color
one-separated extraction. -/
theorem principal_floorBin_weight_cap
    {sigma T : ℝ} (hsigma : 0 ≤ sigma)
    (n : ℤ) (hn : n ∈ occupiedFloorBins (zeroSupport chiOne sigma T)) :
    ∑ rho ∈ zeroSupport chiOne sigma T with Int.floor rho.im = n,
        zeroMultiplicity chiOne sigma T rho ≤
      closedUnitWindowCount chiOne 0 n := by
  classical
  unfold closedUnitWindowCount
  let Z := zeroSupport chiOne sigma T
  let S := Z.filter (fun rho => Int.floor rho.im = n)
  have hsub : S ⊆ closedUnitWindowSupport chiOne 0 n := by
    intro rho hrho
    have hrhoZ := (Finset.mem_filter.mp hrho).1
    have hfloor := (Finset.mem_filter.mp hrho).2
    simpa [hfloor] using mem_principal_fullStrip_floor_window hsigma hrhoZ
  calc
    ∑ rho ∈ Z with Int.floor rho.im = n,
        zeroMultiplicity chiOne sigma T rho =
        ∑ rho ∈ S,
          zeroMultiplicity chiOne 0 (windowHeight n) rho := by
      apply Finset.sum_congr rfl
      intro rho hrho
      have hrhoZ := (Finset.mem_filter.mp hrho).1
      have hfloor := (Finset.mem_filter.mp hrho).2
      simpa [hfloor] using
        principal_zeroMultiplicity_eq_fullStrip_floor_window hsigma hrhoZ
    _ ≤ ∑ rho ∈ closedUnitWindowSupport chiOne 0 n,
        zeroMultiplicity chiOne 0 (windowHeight n) rho :=
      Finset.sum_le_sum_of_subset hsub

/-- Premise-free multiplicity-preserving one-separated thinning for the
principal zeta zeros. -/
theorem exists_principal_oneSeparated_ordinates
    {sigma T : ℝ} (hsigma : 0 ≤ sigma) :
    ∃ S : Finset ℂ,
      S ⊆ zeroSupport chiOne sigma T ∧
      CGLProofDAG.OneSeparated (S.image Complex.im) ∧
      (S.image Complex.im).card = S.card ∧
      dirichletZeroCount chiOne sigma T ≤
        2 * (⌈1683 * Real.log (T + 3)⌉₊) * S.card := by
  have hcap : ∀ n ∈ occupiedFloorBins (zeroSupport chiOne sigma T),
      ∑ rho ∈ zeroSupport chiOne sigma T with Int.floor rho.im = n,
          zeroMultiplicity chiOne sigma T rho ≤
        ⌈1683 * Real.log (T + 3)⌉₊ := by
    intro n hn
    have hlocal := principal_floorBin_weight_cap hsigma n hn
    have hlog := MAPPrincipalZetaFullStrip.principal_fullStrip_count_le_log n
    -- The global `T`-uniform comparison is only legal for occupied bins.
    have hrho := Finset.mem_image.mp hn
    obtain ⟨rho, hrhoZ, hfloor⟩ := hrho
    have hglobal : rho ∈ zeroRectangle sigma T :=
      (zeroDivisor chiOne sigma T).supportWithinDomain
        ((zeroSupport_mem_iff chiOne sigma T rho).mp hrhoZ)
    have him : |rho.im| ≤ T :=
      abs_le.mpr (Complex.mem_reProdIm.mp hglobal).2
    have hfloorAbs := abs_floor_le_abs_add_one rho.im
    have hscalePos : 0 < arithmeticScale 1 (n : ℝ) := by
      unfold arithmeticScale
      positivity
    have htargetPos : 0 < T + 3 := by
      have hTnonneg : 0 ≤ T := by
        have habsnonneg : 0 ≤ |rho.im| := abs_nonneg _
        linarith
      linarith
    have hscale : arithmeticScale 1 (n : ℝ) ≤ T + 3 := by
      rw [← hfloor]
      simp only [arithmeticScale, Nat.cast_one, one_mul]
      linarith
    have hlogScale := Real.log_le_log hscalePos hscale
    have hreal :
        (closedUnitWindowCount chiOne 0 n : ℝ) ≤
          (⌈1683 * Real.log (T + 3)⌉₊ : ℝ) := by
      exact hlog.trans <|
        (mul_le_mul_of_nonneg_left hlogScale (by norm_num)).trans
          (Nat.le_ceil _)
    exact hlocal.trans (Nat.cast_le.mp hreal)
  simpa [dirichletZeroCount] using
    exists_oneSeparated_ordinates_of_floorBin_weight_cap
      (zeroSupport chiOne sigma T)
      (zeroMultiplicity chiOne sigma T)
      ⌈1683 * Real.log (T + 3)⌉₊ hcap

end
end MAPPrincipalZetaCompactCrowding

#print axioms MAPPrincipalZetaCompactCrowding.principal_zeroMultiplicity_le_floor_log
#print axioms MAPPrincipalZetaCompactCrowding.principal_dirichletZeroCount_le_log_mul_supportCard
#print axioms MAPPrincipalZetaCompactCrowding.exists_principal_oneSeparated_ordinates
