import PrincipalZetaCompactCrowding

/-!
# Huxley 1972, equation (3.9): the exact exceptional set

Huxley's classification is applied only to zeros whose ordinate satisfies

`|gamma| >= 100 log T`.  The excluded zeros are said, immediately after
(3.11), to number `O(log^2 T)`.  This file proves that statement for the
actual distinct-zero support used by the MAP endpoint.  The proof uses the
premise-free conductor-one local zero count already certified in
`PrincipalZetaCompactCrowding`; no density estimate enters.
-/

namespace MAPPrincipalZetaHuxley1972Equation39Exceptions

open Filter Asymptotics DirichletZeros CGLProofDAG
open MAPPrincipalZetaCompactCrowding MAPLocalZeroWindow

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)

/-- The zeros excluded by Huxley's condition (3.9), literally
`|gamma| < 100 log T`. -/
def equation39ExceptionalSet (sigma T : ℝ) : Finset ℂ :=
  (zeroSupport chiOne sigma T).filter fun rho =>
    |rho.im| < 100 * Real.log T

/-- Elementary packing for a one-separated finite set in `[-B,B]`. -/
private theorem oneSeparated_card_le_two_ceil_add_one
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

/-- A literal finite bound for the (3.9) exceptions.  It is already stronger
than the printed `O(log^2 T)` statement and retains the exact cutoff
`100 log T`. -/
theorem equation39ExceptionalSet_card_le
    {sigma T : ℝ} (hsigma : 0 ≤ sigma) (hlog : 0 ≤ Real.log T) :
    (equation39ExceptionalSet sigma T).card ≤
      2 * ⌈1683 * Real.log (100 * Real.log T + 3)⌉₊ *
        (2 * ⌈100 * Real.log T⌉₊ + 1) := by
  classical
  let B : ℝ := 100 * Real.log T
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let Zlow := equation39ExceptionalSet sigma T
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
    _ = 2 * ⌈1683 * Real.log (100 * Real.log T + 3)⌉₊ *
        (2 * ⌈100 * Real.log T⌉₊ + 1) := by rfl

/-- The sentence following (3.11), with a completely explicit constant:
the distinct zeros excluded by (3.9) are eventually at most
`700000 (log T)^2`. -/
theorem eventually_equation39ExceptionalSet_card_le_log_sq :
    ∀ᶠ T : ℝ in atTop, ∀ sigma : ℝ, 0 ≤ sigma →
      ((equation39ExceptionalSet sigma T).card : ℝ) ≤
        700000 * Real.rpow (Real.log T) 2 := by
  have hslow :=
    (isLittleO_iff_nat_mul_le'.1 Real.isLittleO_log_id_atTop 200)
  filter_upwards [hslow, eventually_ge_atTop (Real.exp 1)]
    with T hslowT hT
  intro sigma hsigma
  have hTpos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hlogOne : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hT
  have hlogPos : 0 < Real.log T := zero_lt_one.trans_le hlogOne
  have hslow' : 200 * Real.log T ≤ T := by
    simpa [Real.norm_eq_abs, abs_of_pos hlogPos, abs_of_pos hTpos]
      using hslowT
  have hcut : 100 * Real.log T + 3 ≤ T := by
    have : 3 ≤ 100 * Real.log T := by nlinarith
    linarith
  have hcutPos : 0 < 100 * Real.log T + 3 := by positivity
  have hlogCut : Real.log (100 * Real.log T + 3) ≤ Real.log T :=
    Real.log_le_log hcutPos hcut
  have hcapCeil := Nat.ceil_lt_add_one
    (show 0 ≤ 1683 * Real.log (100 * Real.log T + 3) by
      exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))
  have hcap : (⌈1683 * Real.log (100 * Real.log T + 3)⌉₊ : ℝ) ≤
      1684 * Real.log T := by
    calc
      (⌈1683 * Real.log (100 * Real.log T + 3)⌉₊ : ℝ) ≤
          1683 * Real.log (100 * Real.log T + 3) + 1 := hcapCeil.le
      _ ≤ 1683 * Real.log T + 1 := by nlinarith
      _ ≤ 1684 * Real.log T := by linarith
  have hBCeil := Nat.ceil_lt_add_one
    (show 0 ≤ 100 * Real.log T by positivity)
  have hBcard : (2 * (⌈100 * Real.log T⌉₊ : ℝ) + 1) ≤
      203 * Real.log T := by
    have hceil : (⌈100 * Real.log T⌉₊ : ℝ) ≤
        100 * Real.log T + 1 := hBCeil.le
    nlinarith
  have hraw := equation39ExceptionalSet_card_le hsigma hlogPos.le
  have hrawR : ((equation39ExceptionalSet sigma T).card : ℝ) ≤
      2 * (⌈1683 * Real.log (100 * Real.log T + 3)⌉₊ : ℝ) *
        (2 * (⌈100 * Real.log T⌉₊ : ℝ) + 1) := by
    exact_mod_cast hraw
  calc
    ((equation39ExceptionalSet sigma T).card : ℝ) ≤
        2 * (⌈1683 * Real.log (100 * Real.log T + 3)⌉₊ : ℝ) *
          (2 * (⌈100 * Real.log T⌉₊ : ℝ) + 1) := hrawR
    _ ≤ 2 * (1684 * Real.log T) * (203 * Real.log T) := by
      gcongr
    _ ≤ 700000 * Real.rpow (Real.log T) 2 := by
      have hpow : Real.rpow (Real.log T) 2 = (Real.log T) ^ 2 := by
        simpa only [Real.rpow_def] using Real.rpow_natCast (Real.log T) 2
      rw [hpow]
      nlinarith [sq_nonneg (Real.log T)]

end
end MAPPrincipalZetaHuxley1972Equation39Exceptions

#print axioms MAPPrincipalZetaHuxley1972Equation39Exceptions.equation39ExceptionalSet_card_le
#print axioms MAPPrincipalZetaHuxley1972Equation39Exceptions.eventually_equation39ExceptionalSet_card_le_log_sq
