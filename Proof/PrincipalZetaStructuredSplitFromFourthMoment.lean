import PrincipalZetaFiniteStructuredSplit
import PrincipalZetaStructuredDensity
import PostA5HighStripSplitReductionFromFourthMoment
import MAPLivePrincipalDensityAdapters

/-!
# Principal structured split from the exact zeta fourth-moment source

The residue-aware conductor-one detector already supplies the finite Type-I /
Type-II partition.  This file isolates the remaining classical source as the
discrete fourth moment of zeta on a one-separated set and proves the complete
deterministic weld from that source to
`PrincipalPostA5StructuredSplitReduction`.
-/

namespace MAPPrincipalZetaStructuredSplitFromFourthMoment

open Filter
open scoped BigOperators FourierTransform
open CGLProofDAG DirichletZeros MAPAppendixA4PostA5SetAdapter SchwartzMap
open MAPAppendixA4DetectorDichotomy MAPAppendixA4RecenteredGammaRepair
open PostA5RecenteredSourceSplit PostA5RecenteredTypeIExtractor
open PostA5TypeIIFourthMoment PostA5LongSpacingAssembly
open PostA5CrowdingDeterministic PostA5TypeIFourierAssembly
open PostA5TypeIOrdinateRecentering PostA5HighStripSplitAssembly
open PostA5TypeICoefficientProvenance
open PostA5HighStripSplitReductionFromFourthMoment
open PostA5TypeIFourierTailAbsorption MAPLocalZeroWindow
open MAPPrincipalZetaCompactCrowding MAPPrincipalZetaDetectorDichotomy
open MAPPrincipalZetaFiniteStructuredSplit MAPPrincipalZetaStructuredDensity

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

/-- The exact conductor-one Type-II source.  This is the ordinary discrete
fourth moment of zeta on an arbitrary one-separated set.  It is intentionally
stated independently of zeros and of the detector partition. -/
def PrincipalZetaDiscreteFourthMoment : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (W : Finset ℝ),
        T₀ ≤ T → OneSeparated W →
        (∀ t ∈ W, |t| ≤ T) →
        (∑ t ∈ W, ‖DirichletCharacter.LFunction chiOne
          (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤
          C * Real.rpow T (1 + epsilon)

/-- Apply the principal fourth moment to the actual shifted Type-II image.
The source zeros are `3B`-separated, so shifts of size at most `B` remain
one-separated, and the image lies in `[-2T,2T]`. -/
theorem sourceTypeII_shifted_moment_of_principalFourthMoment
    (hfourth : PrincipalZetaDiscreteFourthMoment)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Cfourth Tfourth : ℝ, 0 < Cfourth ∧ 2 ≤ Tfourth ∧
      ∀ (T B : ℝ) (S : Finset ℂ) (shift : ℂ → ℝ),
        0 ≤ T → 1 ≤ B → B ≤ T → Tfourth ≤ 2 * T →
        (∀ rho ∈ S, |rho.im| ≤ T) →
        (∀ rho ∈ S, |shift rho| ≤ B) →
        (∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' →
          3 * B ≤ |rho.im - rho'.im|) →
        (∑ t ∈ S.image (fun rho => rho.im + shift rho),
          ‖DirichletCharacter.LFunction chiOne
            (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤
          Cfourth * Real.rpow (2 * T) (1 + epsilon) := by
  obtain ⟨Cfourth, Tfourth, hCfourth, hTfourth, hsource⟩ :=
    hfourth epsilon hepsilon
  refine ⟨Cfourth, Tfourth, hCfourth, hTfourth, ?_⟩
  intro T B S shift hT hB hBT hTsource hheight hshift hsep
  have hspacing := shifted_image_oneSeparated_and_card S Complex.im shift
    hB hshift hsep
  apply hsource (2 * T) (S.image fun rho => rho.im + shift rho)
    hTsource hspacing.1
  intro t ht
  rw [Finset.mem_image] at ht
  obtain ⟨rho, hrho, rfl⟩ := ht
  calc
    |rho.im + shift rho| ≤ |rho.im| + |shift rho| := abs_add_le _ _
    _ ≤ T + B := add_le_add (hheight rho hrho) (hshift rho hrho)
    _ ≤ 2 * T := by linarith

/-- The principal one-separated thinning can be thinned once more to the
literal `3B` spacing used by the detector.  The only loss is the certified
logarithmic principal crowding cap times the residue-color count. -/
theorem exists_threeBSeparated_principal_zeroSupport
    {sigma T B : ℝ} (hsigma : 0 ≤ sigma) (hB : 0 ≤ B) :
    ∃ S : Finset ℂ,
      S ⊆ zeroSupport chiOne sigma T ∧
      (∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' →
        3 * B ≤ |rho.im - rho'.im|) ∧
      (zeroSupport chiOne sigma T).card ≤
        (2 * ⌈1683 * Real.log (T + 3)⌉₊ * longSpacingColorCount B) *
          S.card := by
  classical
  obtain ⟨S₁, hS₁, hsep₁, hcardImage, hcount₁⟩ :=
    exists_principal_oneSeparated_ordinates hsigma
  have hinj : Set.InjOn Complex.im S₁ :=
    Finset.card_image_iff.mp hcardImage
  have hfloorCap : ∀ n ∈ occupiedFloorBins S₁,
      (S₁.filter fun rho => Int.floor rho.im = n).card ≤ 1 := by
    intro n _hn
    rw [Finset.card_le_one]
    intro rho hrho rho' hrho'
    have hrhoS : rho ∈ S₁ := (Finset.mem_filter.mp hrho).1
    have hrho'S : rho' ∈ S₁ := (Finset.mem_filter.mp hrho').1
    by_contra hne
    have himne : rho.im ≠ rho'.im := fun heq => hne (hinj hrhoS hrho'S heq)
    have hgap := hsep₁ rho.im (Finset.mem_image.mpr ⟨rho, hrhoS, rfl⟩)
      rho'.im (Finset.mem_image.mpr ⟨rho', hrho'S, rfl⟩) himne
    have hfloor : Int.floor rho.im = Int.floor rho'.im :=
      (Finset.mem_filter.mp hrho).2.trans
        (Finset.mem_filter.mp hrho').2.symm
    have hlo : ((Int.floor rho.im : ℤ) : ℝ) ≤ rho.im := Int.floor_le _
    have hhi : rho.im < ((Int.floor rho.im : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have hlo' : ((Int.floor rho'.im : ℤ) : ℝ) ≤ rho'.im := Int.floor_le _
    have hhi' : rho'.im < ((Int.floor rho'.im : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    rw [hfloor] at hlo hhi
    have habs : |rho.im - rho'.im| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    linarith
  obtain ⟨S, hSsubS₁, hsep, hS₁card⟩ :=
    exists_threeBSeparated_representatives S₁ hB hfloorCap
  refine ⟨S, fun rho hrho => hS₁ (hSsubS₁ hrho), hsep, ?_⟩
  have hsupportCount : (zeroSupport chiOne sigma T).card ≤
      dirichletZeroCount chiOne sigma T := by
    unfold dirichletZeroCount
    calc
      (zeroSupport chiOne sigma T).card =
          ∑ _rho ∈ zeroSupport chiOne sigma T, 1 := by simp
      _ ≤ ∑ rho ∈ zeroSupport chiOne sigma T,
          zeroMultiplicity chiOne sigma T rho := by
        apply Finset.sum_le_sum
        intro rho hrho
        exact MAPAPZeroDensityCert.zeroMultiplicity_pos_of_mem
          chiOne sigma T hrho
  calc
    (zeroSupport chiOne sigma T).card ≤
        dirichletZeroCount chiOne sigma T := hsupportCount
    _ ≤ 2 * ⌈1683 * Real.log (T + 3)⌉₊ * S₁.card := hcount₁
    _ ≤ 2 * ⌈1683 * Real.log (T + 3)⌉₊ *
        (longSpacingColorCount B * 1 * S.card) :=
      Nat.mul_le_mul_left _ hS₁card
    _ = (2 * ⌈1683 * Real.log (T + 3)⌉₊ *
        longSpacingColorCount B) * S.card := by ring

/-- Long-spacing extraction for any selected subset of principal zeros.
This is used after removing the low-ordinate crossed-pole exception. -/
theorem exists_threeBSeparated_principal_subset
    {sigma T B : ℝ} (hsigma : 0 ≤ sigma) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (Z : Finset ℂ) (hZ : Z ⊆ zeroSupport chiOne sigma T) :
    ∃ S : Finset ℂ,
      S ⊆ Z ∧
      (∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' →
        3 * B ≤ |rho.im - rho'.im|) ∧
      Z.card ≤
        (2 * ⌈1683 * Real.log (T + 3)⌉₊ * longSpacingColorCount B) *
          S.card := by
  classical
  let L : ℕ := ⌈1683 * Real.log (T + 3)⌉₊
  have hcap : ∀ n ∈ occupiedFloorBins Z,
      (Z.filter fun rho => Int.floor rho.im = n).card ≤ L := by
    intro n hn
    have hnFull : n ∈ occupiedFloorBins (zeroSupport chiOne sigma T) := by
      rw [occupiedFloorBins, Finset.mem_image] at hn ⊢
      obtain ⟨rho, hrho, rfl⟩ := hn
      exact ⟨rho, hZ hrho, rfl⟩
    have hweight := principal_floorBin_weight_cap hsigma n hnFull
    have hlog := MAPPrincipalZetaFullStrip.principal_fullStrip_count_le_log n
    have hrho := Finset.mem_image.mp hnFull
    obtain ⟨rho, hrhoFull, hfloor⟩ := hrho
    have hglobal : rho ∈ zeroRectangle sigma T :=
      (zeroDivisor chiOne sigma T).supportWithinDomain
        ((zeroSupport_mem_iff chiOne sigma T rho).mp hrhoFull)
    have him : |rho.im| ≤ T :=
      abs_le.mpr (Complex.mem_reProdIm.mp hglobal).2
    have hfloorAbs := abs_floor_le_abs_add_one rho.im
    have hscalePos : 0 < arithmeticScale 1 (n : ℝ) := by
      unfold arithmeticScale
      positivity
    have htargetPos : 0 < T + 3 := by linarith
    have hscale : arithmeticScale 1 (n : ℝ) ≤ T + 3 := by
      rw [← hfloor]
      simp only [arithmeticScale, Nat.cast_one, one_mul]
      linarith
    have hlogScale := Real.log_le_log hscalePos hscale
    have hweightCap :
        ∑ rho ∈ zeroSupport chiOne sigma T with Int.floor rho.im = n,
            zeroMultiplicity chiOne sigma T rho ≤ L := by
      apply hweight.trans
      exact Nat.cast_le.mp <| hlog.trans <|
        (mul_le_mul_of_nonneg_left hlogScale (by norm_num)).trans
          (Nat.le_ceil _)
    calc
      (Z.filter fun rho => Int.floor rho.im = n).card =
          ∑ _rho ∈ Z.filter (fun rho => Int.floor rho.im = n), 1 := by simp
      _ ≤ ∑ rho ∈ Z.filter (fun rho => Int.floor rho.im = n),
          zeroMultiplicity chiOne sigma T rho := by
        apply Finset.sum_le_sum
        intro rho hrho
        exact MAPAPZeroDensityCert.zeroMultiplicity_pos_of_mem
          chiOne sigma T (hZ (Finset.filter_subset _ _ hrho))
      _ ≤ ∑ rho ∈ zeroSupport chiOne sigma T with Int.floor rho.im = n,
          zeroMultiplicity chiOne sigma T rho := by
        apply Finset.sum_le_sum_of_subset
        intro rho hrho
        exact Finset.mem_filter.mpr
          ⟨hZ (Finset.filter_subset _ _ hrho), (Finset.mem_filter.mp hrho).2⟩
      _ ≤ L := hweightCap
  obtain ⟨S, hS, hsep, hcard⟩ :=
    exists_threeBSeparated_representatives Z hB hcap
  refine ⟨S, hS, hsep, ?_⟩
  calc
    Z.card ≤ longSpacingColorCount B * L * S.card := hcard
    _ ≤ (2 * L * longSpacingColorCount B) * S.card := by
      nlinarith [Nat.zero_le (longSpacingColorCount B * L * S.card)]
    _ = (2 * ⌈1683 * Real.log (T + 3)⌉₊ *
        longSpacingColorCount B) * S.card := by rfl

/-- The complete natural principal thinning loss (including the factor `2`
from the first one-separated extraction) is subpower. -/
theorem eventually_two_principal_crowdingCap_le_rpow
    (a : ℝ) (ha : 0 < a) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ((2 * ⌈1683 * Real.log (T + 3)⌉₊ : ℕ) : ℝ) ≤
        Real.rpow T (2 * a) := by
  have hraw := eventually_principal_crowding_log_le_rpow a ha
  have hthreehalf : 0 < 3 * a / 2 := by positivity
  have hconst := (tendsto_rpow_atTop hthreehalf).eventually
    (eventually_ge_atTop (4 : ℝ))
  filter_upwards [hraw, hconst, eventually_ge_atTop 1] with T hrawT hconstT hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hshift : 1 < T + 3 := by linarith
  have hlog0 : 0 ≤ Real.log (T + 3) :=
    (Real.log_pos hshift).le
  have hraw0 : 0 ≤ 1683 * Real.log (T + 3) := by positivity
  have hceil := Nat.ceil_lt_add_one hraw0
  have hpOne : 1 ≤ Real.rpow T (a / 2) :=
    Real.one_le_rpow hT (by positivity)
  have hcap : (⌈1683 * Real.log (T + 3)⌉₊ : ℝ) ≤
      2 * Real.rpow T (a / 2) := by
    calc
      (⌈1683 * Real.log (T + 3)⌉₊ : ℝ) ≤
          1683 * Real.log (T + 3) + 1 := hceil.le
      _ ≤ Real.rpow T (a / 2) + 1 := by linarith
      _ ≤ 2 * Real.rpow T (a / 2) := by linarith
  push_cast
  calc
    2 * (⌈1683 * Real.log (T + 3)⌉₊ : ℝ) ≤
        4 * Real.rpow T (a / 2) := by linarith
    _ ≤ Real.rpow T (3 * a / 2) * Real.rpow T (a / 2) := by
      exact mul_le_mul_of_nonneg_right hconstT
        (Real.rpow_nonneg hTpos.le _)
    _ = Real.rpow T (2 * a) := by
      calc
        Real.rpow T (3 * a / 2) * Real.rpow T (a / 2) =
            Real.rpow T (3 * a / 2 + a / 2) :=
          (Real.rpow_add hTpos _ _).symm
        _ = Real.rpow T (2 * a) := by congr 1 <;> ring

/-- Exact Type-I project ledger for the principal thinning factor. -/
theorem eventually_principal_typeI_project_cost_le
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) :
    ∀ᶠ T : ℝ in Filter.atTop,
      let C : ℕ := ⌈2 * Real.pi * Real.rpow T h⌉₊
      let P : ℕ := 2 * ⌈1683 * Real.log (T + 3)⌉₊ *
        longSpacingColorCount (detectorVerticalCutoff T)
      ((P * detectorDyadicCount (detectorArithmeticCutoff
        (Real.rpow T (1 / 2)) T) *
        (4 * shiftedFloorWindowCount (C : ℝ) + 2 * (C + 1)) : ℕ) : ℝ) ≤
        Real.rpow T (h + 5 * a) := by
  have hprincipal := eventually_two_principal_crowdingCap_le_rpow a ha
  have hcolor := eventually_longSpacingColorCount_le_rpow a ha
  have hJ := eventually_project_detectorDyadicCount_le_rpow a ha
  have hconst := eventually_const_mul_polylog_le_rpow
    (20 * Real.pi + 20) 0 a (by nlinarith [Real.pi_pos.le]) ha
  filter_upwards [hprincipal, hcolor, hJ, hconst, eventually_ge_atTop 1]
    with T hprincipalT hcolorT hJT hconstT hT
  let C : ℕ := ⌈2 * Real.pi * Real.rpow T h⌉₊
  let P : ℕ := 2 * ⌈1683 * Real.log (T + 3)⌉₊ *
    longSpacingColorCount (detectorVerticalCutoff T)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hCceil := Nat.ceil_lt_add_one
    (show 0 ≤ 2 * Real.pi * Real.rpow T h by
      exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
        (Real.rpow_nonneg hTpos.le _))
  have hThOne : 1 ≤ Real.rpow T h := Real.one_le_rpow hT hh.le
  have hCcast : (C : ℝ) ≤ (2 * Real.pi + 1) * Real.rpow T h := by
    dsimp [C]
    calc
      (⌈2 * Real.pi * Real.rpow T h⌉₊ : ℝ) ≤
          2 * Real.pi * Real.rpow T h + 1 := hCceil.le
      _ ≤ (2 * Real.pi + 1) * Real.rpow T h := by nlinarith
  have hbase : ((4 * shiftedFloorWindowCount (C : ℝ) +
      2 * (C + 1) : ℕ) : ℝ) ≤
      (20 * Real.pi + 20) * Real.rpow T h := by
    rw [shiftedFloorWindowCount_natCast]
    push_cast
    nlinarith
  have hconstT' : 20 * Real.pi + 20 ≤ Real.rpow T a := by
    simpa [Real.rpow_zero, mul_one] using hconstT
  have hbasePow : ((4 * shiftedFloorWindowCount (C : ℝ) +
      2 * (C + 1) : ℕ) : ℝ) ≤ Real.rpow T (h + a) := by
    calc
      ((4 * shiftedFloorWindowCount (C : ℝ) +
        2 * (C + 1) : ℕ) : ℝ) ≤
          (20 * Real.pi + 20) * Real.rpow T h := hbase
      _ ≤ Real.rpow T a * Real.rpow T h := by gcongr
      _ = Real.rpow T (h + a) := by
        calc
          Real.rpow T a * Real.rpow T h = Real.rpow T (a + h) :=
            (Real.rpow_add hTpos _ _).symm
          _ = Real.rpow T (h + a) := by congr 1 <;> ring
  have hPpow : (P : ℝ) ≤ Real.rpow T (3 * a) := by
    dsimp [P]
    push_cast
    push_cast at hprincipalT
    calc
      2 * (⌈1683 * Real.log (T + 3)⌉₊ : ℝ) *
          (longSpacingColorCount (detectorVerticalCutoff T) : ℝ) ≤
          Real.rpow T (2 * a) * Real.rpow T a :=
        mul_le_mul hprincipalT hcolorT (Nat.cast_nonneg _)
          (Real.rpow_nonneg hTpos.le _)
      _ = Real.rpow T (3 * a) := by
        calc
          Real.rpow T (2 * a) * Real.rpow T a =
              Real.rpow T (2 * a + a) :=
            (Real.rpow_add hTpos _ _).symm
          _ = Real.rpow T (3 * a) := by congr 1 <;> ring
  have hPJ : (P : ℝ) * detectorDyadicCount
      (detectorArithmeticCutoff (Real.rpow T (1 / 2)) T) ≤
      Real.rpow T (3 * a) * Real.rpow T a :=
    mul_le_mul hPpow hJT (Nat.cast_nonneg _)
      (Real.rpow_nonneg hTpos.le _)
  have hmul : (P : ℝ) * detectorDyadicCount
      (detectorArithmeticCutoff (Real.rpow T (1 / 2)) T) *
      ((4 * shiftedFloorWindowCount (C : ℝ) +
        2 * (C + 1) : ℕ) : ℝ) ≤
      Real.rpow T (3 * a) * Real.rpow T a * Real.rpow T (h + a) :=
    mul_le_mul hPJ hbasePow (Nat.cast_nonneg _)
      (mul_nonneg (Real.rpow_nonneg hTpos.le _)
        (Real.rpow_nonneg hTpos.le _))
  have hpowEq : Real.rpow T (3 * a) * Real.rpow T a *
      Real.rpow T (h + a) = Real.rpow T (h + 5 * a) := by
    calc
      Real.rpow T (3 * a) * Real.rpow T a * Real.rpow T (h + a) =
          Real.rpow T (3 * a + a) * Real.rpow T (h + a) := by
        congr 1
        exact (Real.rpow_add hTpos _ _).symm
      _ = Real.rpow T ((3 * a + a) + (h + a)) :=
        (Real.rpow_add hTpos _ _).symm
      _ = Real.rpow T (h + 5 * a) := by congr 1 <;> ring
  simpa [C, P, Nat.cast_mul] using hmul.trans_eq hpowEq

/-- Elementary packing for a one-separated finite set in `[-B,B]`. -/
theorem oneSeparated_card_le_two_ceil_add_one
    (W : Finset ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hsep : OneSeparated W) (hheight : ∀ t ∈ W, |t| ≤ B) :
    W.card ≤ 2 * ⌈B⌉₊ + 1 := by
  classical
  let m : ℕ := ⌈B⌉₊
  have hBm : B ≤ (m : ℝ) := by
    dsimp [m]
    exact Nat.le_ceil B
  have hinj : Set.InjOn (fun t : ℝ => Int.floor t) W := by
    intro t ht u hu heq
    change Int.floor t = Int.floor u at heq
    by_contra htu
    have hgap := hsep t ht u hu htu
    have htlo : ((Int.floor t : ℤ) : ℝ) ≤ t := Int.floor_le _
    have hthi : t < ((Int.floor t : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hulo : ((Int.floor u : ℤ) : ℝ) ≤ u := Int.floor_le _
    have huhi : u < ((Int.floor u : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    rw [heq] at htlo hthi
    have habs : |t - u| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    linarith
  have hsub : W.image (fun t : ℝ => Int.floor t) ⊆
      Finset.Icc (-(m : ℤ)) (m : ℤ) := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨t, ht, rfl⟩ := hn
    have htB := abs_le.mp (hheight t ht)
    rw [Finset.mem_Icc]
    constructor
    · have hreal : -(m : ℝ) ≤ t := by linarith
      have hfloor := Int.floor_mono hreal
      have hfloorCast : Int.floor (-(m : ℝ)) = -(m : ℤ) := by
        convert Int.floor_intCast (R := ℝ) (-(m : ℤ)) using 1 <;> norm_num
      rw [hfloorCast] at hfloor
      exact hfloor
    · have hfloor := Int.floor_mono (show t ≤ ((m : ℤ) : ℝ) by
        simpa using (htB.2.trans hBm))
      simpa using hfloor
  calc
    W.card = (W.image (fun t : ℝ => Int.floor t)).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.Icc (-(m : ℤ)) (m : ℤ)).card := Finset.card_le_card hsub
    _ = 2 * m + 1 := by
      rw [Int.card_Icc]
      have heq : (m : ℤ) + 1 - -(m : ℤ) = ((2 * m + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [heq]
      norm_num [Int.toNat]
    _ = 2 * ⌈B⌉₊ + 1 := by rfl

/-- Zeros below a vertical cutoff form an explicit polylogarithmic exception
ledger.  This is the piece that must be removed before the crossed-pole
residue becomes uniformly negligible. -/
theorem principal_lowOrdinateSupport_card_le
    {sigma T B : ℝ} (hsigma : 0 ≤ sigma) (hB : 0 ≤ B) :
    ((zeroSupport chiOne sigma T).filter fun rho => |rho.im| < B).card ≤
      2 * ⌈1683 * Real.log (B + 3)⌉₊ * (2 * ⌈B⌉₊ + 1) := by
  classical
  let Zlow := (zeroSupport chiOne sigma T).filter fun rho => |rho.im| < B
  have hsub : Zlow ⊆ zeroSupport chiOne sigma B := by
    intro rho hrho
    have hrhoT := (Finset.mem_filter.mp hrho).1
    have him := (Finset.mem_filter.mp hrho).2.le
    have hrectT : rho ∈ zeroRectangle sigma T :=
      (zeroDivisor chiOne sigma T).supportWithinDomain
        ((zeroSupport_mem_iff chiOne sigma T rho).mp hrhoT)
    have hrectB : rho ∈ zeroRectangle sigma B := by
      rw [zeroRectangle, Complex.mem_reProdIm]
      exact ⟨(Complex.mem_reProdIm.mp hrectT).1, abs_le.mp him⟩
    apply (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
      chiOne sigma B hrectB).mpr
    exact regularizedLFunction_eq_zero_of_mem_zeroSupport
      chiOne sigma T hrhoT
  obtain ⟨S, hS, hsep, hcardImage, hcount⟩ :=
    exists_principal_oneSeparated_ordinates (T := B) hsigma
  have hSheight : ∀ rho ∈ S, |rho.im| ≤ B := by
    intro rho hrho
    have hrect : rho ∈ zeroRectangle sigma B :=
      (zeroDivisor chiOne sigma B).supportWithinDomain
        ((zeroSupport_mem_iff chiOne sigma B rho).mp (hS hrho))
    exact abs_le.mpr (Complex.mem_reProdIm.mp hrect).2
  have hpack := oneSeparated_card_le_two_ceil_add_one
    (S.image Complex.im) hB hsep (by
      intro t ht
      rw [Finset.mem_image] at ht
      obtain ⟨rho, hrho, rfl⟩ := ht
      exact hSheight rho hrho)
  have hScard : S.card ≤ 2 * ⌈B⌉₊ + 1 := by
    rw [← hcardImage]
    exact hpack
  calc
    Zlow.card ≤ (zeroSupport chiOne sigma B).card := Finset.card_le_card hsub
    _ ≤ dirichletZeroCount chiOne sigma B := by
      unfold dirichletZeroCount
      calc
        (zeroSupport chiOne sigma B).card =
            ∑ _rho ∈ zeroSupport chiOne sigma B, 1 := by simp
        _ ≤ ∑ rho ∈ zeroSupport chiOne sigma B,
            zeroMultiplicity chiOne sigma B rho := by
          apply Finset.sum_le_sum
          intro rho hrho
          exact MAPAPZeroDensityCert.zeroMultiplicity_pos_of_mem
            chiOne sigma B hrho
    _ ≤ 2 * ⌈1683 * Real.log (B + 3)⌉₊ * S.card := hcount
    _ ≤ 2 * ⌈1683 * Real.log (B + 3)⌉₊ * (2 * ⌈B⌉₊ + 1) :=
      Nat.mul_le_mul_left _ hScard

/-- The low-ordinate exception ledger at the paper cutoff is subpower,
uniformly in the horizontal edge of the rectangle. -/
theorem eventually_principal_lowOrdinateSupport_card_le_rpow
    (a : ℝ) (ha : 0 < a) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ sigma : ℝ, 0 ≤ sigma →
      (((zeroSupport chiOne sigma T).filter fun rho =>
          |rho.im| < detectorVerticalCutoff T).card : ℝ) ≤
        Real.rpow T a := by
  have hlogSq := ZeroDensityArithmetic.polylog_absorption 2 1 (by norm_num)
  have hpoly := eventually_const_mul_polylog_le_rpow 70000 3 a
    (by norm_num) ha
  filter_upwards [hlogSq, hpoly, eventually_ge_atTop (Real.exp 1),
    eventually_ge_atTop 1] with T hlogSqT hpolyT hTexp hTone
  intro sigma hsigma
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hlog : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hTexp
  let B : ℝ := detectorVerticalCutoff T
  have hB0 : 0 ≤ B := by dsimp [B, detectorVerticalCutoff]; positivity
  have hBone : 1 ≤ B := by
    dsimp [B, detectorVerticalCutoff]
    nlinarith [sq_nonneg (Real.log T - 1)]
  have hBT : B ≤ T := by
    dsimp [B, detectorVerticalCutoff]
    simpa [Real.rpow_natCast, Real.rpow_one] using hlogSqT
  have hlog4 : Real.log 4 ≤ 3 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)).trans_eq
      (by norm_num)
  have hlogB : Real.log (B + 3) ≤ 4 * Real.log T := by
    have hBpos : 0 < B + 3 := by positivity
    have hfourT : B + 3 ≤ 4 * T := by linarith
    calc
      Real.log (B + 3) ≤ Real.log (4 * T) :=
        Real.log_le_log hBpos hfourT
      _ = Real.log 4 + Real.log T := by
        rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hTpos.ne']
      _ ≤ 4 * Real.log T := by linarith
  have hcapCeil := Nat.ceil_lt_add_one
    (show 0 ≤ 1683 * Real.log (B + 3) by
      exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))
  have hcap : (⌈1683 * Real.log (B + 3)⌉₊ : ℝ) ≤
      6733 * Real.log T := by
    calc
      (⌈1683 * Real.log (B + 3)⌉₊ : ℝ) ≤
          1683 * Real.log (B + 3) + 1 := hcapCeil.le
      _ ≤ 6732 * Real.log T + 1 := by nlinarith
      _ ≤ 6733 * Real.log T := by linarith
  have hBCeil := Nat.ceil_lt_add_one hB0
  have hBcard : (2 * ⌈B⌉₊ + 1 : ℕ) ≤ ⌈(5 * B : ℝ)⌉₊ := by
    have hleft : ((2 * ⌈B⌉₊ + 1 : ℕ) : ℝ) ≤ 5 * B := by
      push_cast
      have : (⌈B⌉₊ : ℝ) ≤ B + 1 := hBCeil.le
      linarith
    exact_mod_cast hleft.trans (Nat.le_ceil (5 * B))
  have hraw := principal_lowOrdinateSupport_card_le
    (T := T) hsigma hB0
  have hrawR :
      (((zeroSupport chiOne sigma T).filter fun rho => |rho.im| < B).card : ℝ) ≤
        2 * (⌈1683 * Real.log (B + 3)⌉₊ : ℝ) *
          (2 * (⌈B⌉₊ : ℝ) + 1) := by exact_mod_cast hraw
  calc
    (((zeroSupport chiOne sigma T).filter fun rho => |rho.im| < B).card : ℝ) ≤
        2 * (⌈1683 * Real.log (B + 3)⌉₊ : ℝ) *
          (2 * (⌈B⌉₊ : ℝ) + 1) := hrawR
    _ ≤ 2 * (6733 * Real.log T) * (5 * B) := by
      have hBreal : 2 * (⌈B⌉₊ : ℝ) + 1 ≤ 5 * B := by
        have : (⌈B⌉₊ : ℝ) ≤ B + 1 := hBCeil.le
        linarith
      gcongr
    _ ≤ 70000 * Real.rpow (Real.log T) 3 := by
      dsimp [B, detectorVerticalCutoff]
      norm_num [Real.rpow_natCast]
      nlinarith [sq_nonneg (Real.log T),
        mul_nonneg (sq_nonneg (Real.log T))
          (show 0 ≤ Real.log T by linarith)]
    _ ≤ Real.rpow T a := hpolyT

/-- Exact remaining tail-absorption statement for the residue-aware
principal detector.  The ordinate lower bound is essential: without it the
crossed-pole residue grows with the detector scale.  The explicit formulas
in `PrincipalZetaDetectorDichotomy` are designed to prove this statement. -/
def PrincipalHighOrdinateDetectorBudget : Prop :=
  ∀ kappa eta : ℝ, 0 < kappa → kappa < 1 / 20 → 0 < eta →
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ rho : ℂ,
        principalF rho = 0 →
        7 / 10 ≤ rho.re → rho.re ≤ 1 →
        detectorVerticalCutoff T ≤ |rho.im| → |rho.im| ≤ T →
        principalPaperScaleTruncationError
              ⌊Real.rpow T kappa⌋₊ rho (Real.rpow T (1 / 2)) T +
            Real.rpow T (-inputLoss kappa eta) +
            Real.rpow T (-inputLoss kappa eta) ≤
          Real.exp (-(1 / Real.rpow T (1 / 2)))

set_option maxHeartbeats 1000000

theorem principalPostA5StructuredSplitReduction_of_principalFourthMoment
    (hbudget : PrincipalHighOrdinateDetectorBudget)
    (hfourth : PrincipalZetaDiscreteFourthMoment) :
    PrincipalPostA5StructuredSplitReduction := by
  intro loss hloss
  let kOut := splitOutputKappa loss
  let kDet := splitDetectorKappa loss
  let etaOut := splitOutputEta loss
  let etaDet := splitDetectorEta loss
  let dOut := inputLoss kOut etaOut
  let dDet := inputLoss kDet etaDet
  let a := splitSmallExponent loss
  let eps := splitFourthEpsilon loss
  let e := a
  let h := a
  obtain ⟨hkOut, hkDet, hetaOut, hetaDet, ha, heps⟩ :=
    split_parameters_pos hloss
  have he : 0 < e := by simpa [e] using ha
  have hh : 0 < h := by simpa [h] using ha
  obtain ⟨hkOutHalf, hkOutLoss, hkDetCap⟩ := split_output_kappa_ledger hloss
  obtain ⟨hZIexp, hNormExp, hIIexp⟩ := split_reserve_ledgers hloss
  obtain ⟨Kd, hKd, hdiv⟩ :=
    FixedCharacterPoweredBridge.orderedDivisorCount_subpolynomial
      2 (by norm_num) e he
  obtain ⟨Cfourth, Tfourth, hCfourth, hTfourth, hsourceMoment⟩ :=
    sourceTypeII_shifted_moment_of_principalFourthMoment hfourth eps heps
  have hsource := hbudget kDet etaDet hkDet hkDetCap hetaDet
  have htail :=
    eventually_exists_fourierMoment_detectorCommonCoefficient_mul_fourierTail_le_inputLoss
      kDet etaDet e h hkDet hetaDet he hh
  have hgeom := eventually_project_scale_geometry kOut kDet h hkOut
    (by simp [kDet, kOut, splitDetectorKappa])
    (by
      dsimp [kDet]
      exact hkDetCap.le.trans (by norm_num)) hh
  have hZIcost := eventually_principal_typeI_project_cost_le h a hh ha
  have hNorm := eventually_typeI_normalization_cost_le Kd e h a
    (dOut - dDet) hKd he hh ha (by
      dsimp [e, h, dOut, dDet]
      nlinarith [hNormExp])
  have hII := eventually_typeII_source_ledger Cfourth eps kDet dDet
    kOut etaOut a hCfourth heps hkDet
    (by dsimp [dDet]; exact inputLoss_pos hkDet hetaDet)
    hkOut hetaOut ha (by
      dsimp [dDet, dOut, kDet, kOut, etaOut, etaDet, a, eps]
      exact hIIexp)
  have hcolor := eventually_longSpacingColorCount_le_rpow a ha
  have hcap := eventually_two_principal_crowdingCap_le_rpow a ha
  have hJsub := eventually_project_detectorDyadicCount_le_rpow a ha
  have hqsub := ZeroDensityArithmetic.polylog_absorption 1 a ha
  have hlogSq := ZeroDensityArithmetic.polylog_absorption 2 (1 / 2)
    (by norm_num)
  have hlow := eventually_principal_lowOrdinateSupport_card_le_rpow a ha
  have hTfourthEv : ∀ᶠ T : ℝ in Filter.atTop, Tfourth ≤ 2 * T :=
    eventually_ge_atTop (Tfourth / 2) |>.mono (by
      intro T hT
      linarith)
  have hAll := hsource.and
    (htail.and
      (hgeom.and
        (hZIcost.and
          (hNorm.and
            (hII.and
              (hcolor.and
                (hcap.and
                  (hJsub.and
                    (hqsub.and
                      (hlogSq.and (hlow.and hTfourthEv)))))))))))
  obtain ⟨Tbase, hTbase⟩ := Filter.eventually_atTop.1 hAll
  let T₀ : ℝ := max (Real.exp 1) (max 4 Tbase)
  refine ⟨kOut, 2, T₀, hkOut, hkOutHalf, hkOutLoss, by norm_num,
    by
      dsimp [T₀]
      exact (by norm_num : (2 : ℝ) ≤ 4).trans
        ((le_max_left 4 Tbase).trans (le_max_right _ _)), ?_⟩
  intro T sigma hT0 hsigmaLow hsigmaHigh
  have hTb : Tbase ≤ T :=
    ((le_max_right 4 Tbase).trans (le_max_right (Real.exp 1) _)).trans hT0
  have hTexp : Real.exp 1 ≤ T := (le_max_left _ _).trans hT0
  obtain ⟨hsourceT, htailT, hgeomT, hZIcostT, hNormT, hIIT,
    hcolorT, hcapT, hJsubT, hqsubT, hlogSqT, hlowT, hTfourthT⟩ :=
    hTbase T hTb
  let U : ℕ := ⌊Real.rpow T kDet⌋₊
  let Y : ℝ := Real.rpow T (1 / 2)
  let Ncut : ℕ := detectorArithmeticCutoff Y T
  let B : ℝ := detectorVerticalCutoff T
  let C : ℕ := ⌈2 * Real.pi * Real.rpow T h⌉₊
  let V : ℝ := Real.rpow T (-dDet)
  let P : ℕ := 2 * ⌈1683 * Real.log (T + 3)⌉₊ *
    longSpacingColorCount B
  let Mfourth : ℝ := Cfourth * Real.rpow (2 * T) (1 + eps)
  dsimp only at hgeomT
  obtain ⟨hTfour, hUone, hUtwolow, hUhigh, hUN, hBone, hNtwo,
    hDtime, hNhigh, hJtime, hC⟩ := hgeomT
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hTnonneg : 0 ≤ T := hTpos.le
  have hYone : 1 ≤ Y := by dsimp [Y]; exact Real.one_le_rpow hTone (by norm_num)
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hYone
  have hVpos : 0 < V := by dsimp [V]; positivity
  have hlog : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hTexp
  have hq : (1 : ℝ) ≤ Real.rpow (Real.log T) 1 := by simpa using hlog
  have hrpow : (1 : ℝ) ≤ Real.rpow T a :=
    Real.one_le_rpow hTone ha.le
  have hsigmaHalf : 1 / 2 ≤ sigma := by
    norm_num at hsigmaLow ⊢
    linarith
  let Zhigh := (zeroSupport chiOne sigma T).filter fun rho => B ≤ |rho.im|
  let Zlow := (zeroSupport chiOne sigma T).filter fun rho => |rho.im| < B
  obtain ⟨Z0, hZ0, hsep, hcountThin⟩ :=
    exists_threeBSeparated_principal_subset (sigma := sigma) (T := T)
      (B := B) (by linarith) hTnonneg (zero_le_one.trans hBone) Zhigh
      (Finset.filter_subset _ _)
  have hZ0Full : ∀ rho ∈ Z0, rho ∈ zeroSupport chiOne sigma T := by
    intro rho hrho
    exact Finset.filter_subset _ _ (hZ0 hrho)
  have hrect : ∀ rho ∈ Z0, rho ∈ zeroRectangle sigma T := by
    intro rho hrho
    exact (zeroDivisor chiOne sigma T).supportWithinDomain
      ((zeroSupport_mem_iff chiOne sigma T rho).mp (hZ0Full rho hrho))
  have hzero : ∀ rho ∈ Z0, principalF rho = 0 := by
    intro rho hrho
    simpa [MAPPrincipalZetaFixedStrip.principalRegularized,
      DirichletZeros.regularizedLFunction] using
      (regularizedLFunction_eq_zero_of_mem_zeroSupport
        chiOne sigma T (hZ0Full rho hrho))
  have hbetaLow : ∀ rho ∈ Z0, sigma ≤ rho.re := by
    intro rho hrho
    exact (Complex.mem_reProdIm.mp (hrect rho hrho)).1.1
  have hbetaHigh : ∀ rho ∈ Z0, rho.re ≤ 1 := by
    intro rho hrho
    exact (Complex.mem_reProdIm.mp (hrect rho hrho)).1.2
  have hheight : ∀ rho ∈ Z0, |rho.im| ≤ T := by
    intro rho hrho
    exact abs_le.mpr (Complex.mem_reProdIm.mp (hrect rho hrho)).2
  have hbudget' : ∀ rho ∈ Z0,
      principalPaperScaleTruncationError U rho Y T + V + V ≤
        Real.exp (-(1 / Y)) := by
    intro rho hrho
    have hhigh : detectorVerticalCutoff T ≤ |rho.im| :=
      (Finset.mem_filter.mp (hZ0 hrho)).2
    simpa [U, Y, V, dDet] using hsourceT rho (hzero rho hrho)
      (hbetaLow rho hrho |> hsigmaLow.trans) (hbetaHigh rho hrho)
      hhigh (hheight rho hrho)
  have hVlower : Real.rpow T (-inputLoss kDet etaDet) ≤ V := by
    simp [V, dDet]
  have htail' : ∀ (j : Fin (detectorDyadicCount Ncut)) (rho : ℂ),
      sigma ≤ rho.re → rho.re ≤ 1 →
      (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
          ‖detectorCommonCoefficient chiOne U Ncut Y sigma n‖) *
        (∫ xi in (Set.Icc (-(Real.rpow T h)) (Real.rpow T h))ᶜ,
          ‖((𝓕 (detectorRealPartCutoff
            (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
        (V / (detectorDyadicCount Ncut : ℝ)) / 2 := by
    intro j rho hbLo hbHi
    exact htailT 1 chiOne U Ncut Y sigma rho j V hTfour hYpos
      hsigmaLow hsigmaHigh hbLo hbHi (by simpa [Ncut, Y] using hDtime j)
      (by simpa [Ncut, Y] using hJtime) hVlower
  have hNlow : ∀ (j : Fin (detectorDyadicCount Ncut)) (rho : ℂ),
      rho ∈ Z0 →
      V ≤ (detectorDyadicCount Ncut : ℝ) *
        ‖arithmeticDetectorDyadicBlock chiOne U Ncut rho Y j‖ →
      Real.rpow T kOut ≤ (2 ^ (j : ℕ) : ℕ) := by
    intro j rho hrho hlarge
    have hUD := mollifier_lt_two_pow_of_positive_selected_block
      chiOne hUone hVpos rho Y j hlarge
    have hUDR : (U : ℝ) < 2 * ((2 ^ (j : ℕ) : ℕ) : ℝ) := by exact_mod_cast hUD
    linarith
  have hthreshold : ∀ j : Fin (detectorDyadicCount Ncut),
      let D : ℕ := 2 ^ (j : ℕ)
      let L : ℝ := Real.rpow D (-sigma) * (Kd * Real.rpow (2 * D) e)
      Real.rpow D sigma * Real.rpow T (-inputLoss kOut etaOut) ≤
        L⁻¹ * (V / (4 * (24 * Real.rpow T h) * detectorDyadicCount Ncut)) := by
    intro j
    dsimp only
    have hcost := hNormT (2 ^ (j : ℕ) : ℝ) (detectorDyadicCount Ncut : ℝ)
      hTone (by positivity) (by simpa [Ncut, Y] using hDtime j)
      (Nat.cast_nonneg _) (by simpa [Ncut, Y] using hJsubT)
    simpa [V, dDet, dOut] using
      normalized_typeI_threshold_of_cost (sigma := sigma) hTpos
        (by positivity) (by unfold detectorDyadicCount; positivity) hKd hcost
  have hZIledger : ∀ (j : Fin (detectorDyadicCount Ncut)) (W : Finset ℝ),
      ((P * detectorDyadicCount Ncut *
        (4 * (shiftedFloorWindowCount C * 1) * W.card +
          2 * (C + 1) * 1) : ℕ) : ℝ) ≤
        Real.rpow T etaOut * (1 + (W.card : ℝ)) := by
    intro j W
    have hbase := hZIcostT
    have hpow : Real.rpow T (h + 5 * a) ≤ Real.rpow T etaOut :=
      Real.rpow_le_rpow_of_exponent_le hTone (by
        dsimp [h]
        linarith)
    have hnatural := typeI_natural_ledger_of_cost
      (P := P) (J := detectorDyadicCount Ncut) (C := C)
      (T := T) (eta := etaOut) (A := 1) (W := W)
      (by simpa [P, C, Ncut, Y] using hbase.trans hpow)
    simpa using hnatural
  have hBT : B ≤ T := by
    dsimp [B, detectorVerticalCutoff]
    have hYle : Real.rpow T (1 / 2) ≤ T := by
      have hraw := Real.rpow_le_rpow_of_exponent_le hTone
        (by norm_num : (1 / 2 : ℝ) ≤ 1)
      simpa only [Real.rpow_one] using! hraw
    have hlogSqY : (Real.log T) ^ 2 ≤ Real.rpow T (1 / 2) := by
      simpa [Real.rpow_natCast] using hlogSqT
    exact hlogSqY.trans hYle
  have hmoment : ∀ (shift : ℂ → ℝ) (SII : Finset ℂ),
      SII ⊆ postA5SourceTypeIISet chiOne U Y T V Z0 →
      (∀ rho ∈ SII, shift rho ∈ Set.Icc (-B) B) →
      (∑ t ∈ SII.image (fun rho => rho.im + shift rho),
        ‖DirichletCharacter.LFunction chiOne
          (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤ Mfourth := by
    intro shift SII hSII hshift
    apply hsourceMoment T B SII shift hTnonneg hBone hBT hTfourthT
    · intro rho hrho
      apply hheight rho
      exact (mem_postA5SourceTypeIISet_iff chiOne U Y T V Z0 rho).mp
        (hSII hrho) |>.1
    · intro rho hrho
      exact abs_le.mpr (hshift rho hrho)
    · intro rho hrho rho' hrho' hne
      apply hsep rho
      · exact (mem_postA5SourceTypeIISet_iff chiOne U Y T V Z0 rho).mp
          (hSII hrho) |>.1
      · exact (mem_postA5SourceTypeIISet_iff chiOne U Y T V Z0 rho').mp
          (hSII hrho') |>.1
      · exact hne
  have hPpow : (P : ℝ) ≤ Real.rpow T (3 * a) := by
    dsimp [P, B]
    push_cast
    push_cast at hcapT
    calc
      2 * (⌈1683 * Real.log (T + 3)⌉₊ : ℝ) *
          (longSpacingColorCount (detectorVerticalCutoff T) : ℝ) ≤
          Real.rpow T (2 * a) * Real.rpow T a :=
        mul_le_mul hcapT hcolorT (by positivity)
          (Real.rpow_nonneg hTnonneg _)
      _ = Real.rpow T (3 * a) := by
        calc
          Real.rpow T (2 * a) * Real.rpow T a =
              Real.rpow T (2 * a + a) := (Real.rpow_add hTpos _ _).symm
          _ = Real.rpow T (3 * a) := by congr 1 <;> ring
  have hUupper : (U : ℝ) ≤ Real.rpow T kDet := by
    dsimp [U]
    exact Nat.floor_le (Real.rpow_nonneg hTnonneg _)
  have hZIIledger : (P : ℝ) *
      (Mfourth / (V / (29 * Real.rpow Y (1 / 2 - sigma) *
        (2 * Real.sqrt U))) ^ 4) ≤
      Real.rpow T (2 * (1 - sigma) + 2 * kOut + etaOut) := by
    simpa [Mfourth, V, dDet, Y] using
      hIIT P 1 U sigma hTone hUone hPpow (by simpa using hrpow) hUupper
        hsigmaLow hsigmaHigh
  obtain ⟨Nout, b, W, ZI, ZII, hNoutLow, hNoutHigh, hb, hWsep,
    hWheight, hWlarge, hcount, hZI, hZII,
    Uout, NcutOut, Yout, scaleOut, hprovenance⟩ :=
    principal_finite_highStrip_structured_split_witness
      (Ztarget := Zhigh.card) (kappaDet := kDet) (etaDet := etaDet)
      (kappaOut := kOut) (etaOut := etaOut)
      (e := e) (h := h) (T := T) (sigma := sigma)
      (Y := Y) (R := T) (V := V) (Kd := Kd) (Mfourth := Mfourth)
      (AZI := 1) (AZII := 1) (U := U) (P := P) (C := C)
      Z0 hTfour hYone (by exact hTpos)
      hUone hVpos he hKd hkDet hetaDet hkOut hetaOut hh hzero hbetaLow
      hsigmaLow hsigmaHigh hbetaHigh hheight
      (by simpa [B] using hsep) (by simpa [P] using hcountThin)
      (by simpa [U, Ncut, Y] using hUN) (by simpa [B] using hBone)
      hbudget'  (by simp [V, dDet, kDet, etaDet]) hVlower
      (by simpa [Ncut, Y] using hDtime) (by simpa [Ncut, Y] using hJtime)
      (by simpa [C] using hC) htail' hdiv
      (by linarith) hUhigh hNlow (by simpa [Ncut, Y] using hNhigh)
      hthreshold hmoment
      (by simpa only [Ncut, one_mul] using hZIledger)
      (by simpa only [one_mul] using hZIIledger)
  let ZIIout : ℕ := ZII + Zlow.card
  have hsupportSplit : (zeroSupport chiOne sigma T).card ≤
      Zhigh.card + Zlow.card := by
    apply (Finset.card_le_card ?_).trans (Finset.card_union_le Zhigh Zlow)
    intro rho hrho
    by_cases hlowOrd : |rho.im| < B
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hrho, hlowOrd⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hrho, le_of_not_gt hlowOrd⟩)
  have hcountAll : (zeroSupport chiOne sigma T).card ≤ ZI + ZIIout := by
    calc
      (zeroSupport chiOne sigma T).card ≤ Zhigh.card + Zlow.card :=
        hsupportSplit
      _ ≤ (ZI + ZII) + Zlow.card := Nat.add_le_add_right hcount _
      _ = ZI + ZIIout := by simp [ZIIout, Nat.add_assoc]
  refine ⟨Nout, b, W, ZI, ZIIout, Uout, NcutOut, Yout, scaleOut,
    hNoutLow, hNoutHigh, hb, hWsep, hWheight, ?_, hcountAll, ?_, ?_,
    hprovenance⟩
  · simpa [etaOut, splitOutputEta] using hWlarge
  · have hpow : Real.rpow T etaOut ≤ Real.rpow T loss :=
      Real.rpow_le_rpow_of_exponent_le hTone (by
        dsimp [etaOut, splitOutputEta]
        linarith)
    have hZI' : (ZI : ℝ) ≤
        Real.rpow T etaOut * (1 + (W.card : ℝ)) := by
      simpa only [one_mul] using hZI
    have hout := hZI'.trans
      (mul_le_mul_of_nonneg_right hpow (by positivity))
    have hnonneg : 0 ≤ Real.rpow T loss * (1 + (W.card : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg hTnonneg _) (by positivity)
    simpa only using hout.trans (by nlinarith)
  · let targetExp : ℝ := 2 * (1 - sigma) + 2 * kOut + loss
    have hpow : Real.rpow T
        (2 * (1 - sigma) + 2 * kOut + etaOut) ≤
        Real.rpow T targetExp :=
      Real.rpow_le_rpow_of_exponent_le hTone (by
        dsimp [targetExp, etaOut, splitOutputEta]
        linarith)
    have hZII' : (ZII : ℝ) ≤ Real.rpow T
        (2 * (1 - sigma) + 2 * kOut + etaOut) := by
      simpa only [one_mul] using hZII
    have hZIIbound : (ZII : ℝ) ≤ Real.rpow T targetExp := hZII'.trans hpow
    have hlowBound : (Zlow.card : ℝ) ≤ Real.rpow T a := by
      simpa [Zlow, B] using hlowT sigma (by linarith)
    have haCap : a ≤ 1 / 1000 := by
      dsimp [a, splitSmallExponent]
      exact min_le_right _ _
    have haTarget : a ≤ targetExp := by
      dsimp [targetExp]
      have hbase : (2 : ℝ) * (1 - sigma) ≥ 2 / 5 := by linarith
      have hk0 : 0 ≤ kOut := hkOut.le
      linarith
    have hlowTarget : (Zlow.card : ℝ) ≤ Real.rpow T targetExp :=
      hlowBound.trans (Real.rpow_le_rpow_of_exponent_le hTone haTarget)
    have hcast : (ZIIout : ℝ) = (ZII : ℝ) + Zlow.card := by
      simp [ZIIout]
    rw [hcast]
    have htarget0 : 0 ≤ Real.rpow T targetExp := Real.rpow_nonneg hTnonneg _
    exact (add_le_add hZIIbound hlowTarget).trans (by nlinarith)

/-- Direct inhabitant of the exact live principal-density alias.  The only
analytic inputs are the explicit high-ordinate residue budget, the classical
principal fourth moment, and the shared provenance-sensitive large-value
theorem. -/
theorem principalClosedHighStripSource_of_principalFourthMoment
    (hbudget : PrincipalHighOrdinateDetectorBudget)
    (hfourth : PrincipalZetaDiscreteFourthMoment)
    (hStructured :
      CGLDetectorStructuredLargeValue.DetectorStructuredThirtyThirteenLargeValue) :
    MAPLiveEndpointWeld.PrincipalClosedHighStripSource :=
  MAPLivePrincipalDensityAdapters.principalClosedHighStripSource_of_structured_split
    (principalPostA5StructuredSplitReduction_of_principalFourthMoment
      hbudget hfourth)
    hStructured



end
end MAPPrincipalZetaStructuredSplitFromFourthMoment

#print axioms MAPPrincipalZetaStructuredSplitFromFourthMoment.sourceTypeII_shifted_moment_of_principalFourthMoment
#print axioms MAPPrincipalZetaStructuredSplitFromFourthMoment.exists_threeBSeparated_principal_zeroSupport
#print axioms MAPPrincipalZetaFiniteStructuredSplit.principal_finite_highStrip_structured_split_witness
#print axioms MAPPrincipalZetaStructuredSplitFromFourthMoment.principalPostA5StructuredSplitReduction_of_principalFourthMoment
#print axioms MAPPrincipalZetaStructuredSplitFromFourthMoment.principalClosedHighStripSource_of_principalFourthMoment
