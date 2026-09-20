import PrincipalZetaCompactCrowding
import PostA5LongSpacingAssembly
import MontgomeryFullScaleDetectorBudgets

/-! Principal zero thinning with the full divisor multiplicity retained.
After 3B thinning, deleting |Im rho|<B costs at most one representative.
The resulting additive counting loss is explicit and remains absorbable. -/
namespace MAPMontgomeryPrincipalFullScaleThinning
open Filter Set
open DirichletZeros MAPPrincipalZetaCompactCrowding
open PostA5CrowdingDeterministic PostA5LongSpacingAssembly
noncomputable section
local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
set_option maxHeartbeats 800000

def principalThinningFactor (T B : ℝ) : ℕ :=
  2 * ⌈1683 * Real.log (T + 3)⌉₊ * longSpacingColorCount B

theorem oneSeparated_floorBin_cap_one (Z : Finset ℂ)
    (hsep : CGLProofDAG.OneSeparated (Z.image Complex.im))
    (hcard : (Z.image Complex.im).card = Z.card) (n : ℤ) :
    (Z.filter fun rho ↦ Int.floor rho.im = n).card ≤ 1 := by
  classical
  have hinj := Finset.card_image_iff.mp hcard
  apply Finset.card_le_one.mpr
  intro rho hrho rho' hrho'
  have hr := Finset.mem_filter.mp hrho
  have hr' := Finset.mem_filter.mp hrho'
  by_contra hne
  have himne : rho.im ≠ rho'.im := fun h ↦ hne (hinj hr.1 hr'.1 h)
  have hs := hsep _ (Finset.mem_image.mpr ⟨rho,hr.1,rfl⟩)
    _ (Finset.mem_image.mpr ⟨rho',hr'.1,rfl⟩) himne
  have hlo := Int.floor_le rho.im
  have hhi := Int.lt_floor_add_one rho.im
  have hlo' := Int.floor_le rho'.im
  have hhi' := Int.lt_floor_add_one rho'.im
  rw [hr.2] at hlo hhi
  rw [hr'.2] at hlo' hhi'
  have hd : |rho.im - rho'.im| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  exact (not_lt_of_ge hs) hd

/-- The entire principal multiplicity count is covered by a high-ordinate
3B-spaced subset, plus one representative charged at the same crowding loss.
The subset remains inside the exact original zero support, including beta>0.7. -/
theorem exists_principal_high_threeBSeparated
    {sigma T B : ℝ} (hsigma : 0 ≤ sigma) (hB : 1 ≤ B) :
    ∃ S : Finset ℂ,
      S ⊆ zeroSupport chiOne sigma T ∧
      (∀ rho ∈ S, B ≤ |rho.im|) ∧
      (∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' → 3 * B ≤ |rho.im - rho'.im|) ∧
      (S.image Complex.im).card = S.card ∧
      dirichletZeroCount chiOne sigma T ≤ principalThinningFactor T B * (S.card + 1) := by
  classical
  obtain ⟨Z,hZ,hZsep,hZcard,hcount⟩ := exists_principal_oneSeparated_ordinates hsigma
  obtain ⟨W,hW,hWsep,hWcard⟩ := exists_threeBSeparated_representatives Z
    (by linarith : 0 ≤ B) (L := 1)
    (fun n _ ↦ oneSeparated_floorBin_cap_one Z hZsep hZcard n)
  let S := W.filter (fun rho ↦ B ≤ |rho.im|)
  have hS : S ⊆ W := Finset.filter_subset _ _
  have hlow : (W.filter fun rho ↦ ¬B ≤ |rho.im|).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro rho hrho rho' hrho'
    have hr := Finset.mem_filter.mp hrho
    have hr' := Finset.mem_filter.mp hrho'
    by_contra hne
    have hs := hWsep rho hr.1 rho' hr'.1 hne
    have hd : |rho.im - rho'.im| ≤ |rho.im| + |rho'.im| := abs_sub _ _
    have hl := lt_of_not_ge hr.2
    have hl' := lt_of_not_ge hr'.2
    linarith
  have hcardSplit : W.card ≤ S.card + 1 := by
    have he := Finset.card_filter_add_card_filter_not (s := W) (p := fun rho ↦ B ≤ |rho.im|)
    dsimp [S]
    omega
  refine ⟨S, fun rho hrho ↦ hZ (hW (hS hrho)), ?_, ?_, ?_, ?_⟩
  · intro rho hrho
    exact (Finset.mem_filter.mp hrho).2
  · intro rho hrho rho' hrho' hne
    exact hWsep rho (hS hrho) rho' (hS hrho') hne
  · apply Finset.card_image_iff.mpr
    intro rho hrho rho' hrho' him
    by_contra hne
    have hs := hWsep rho (hS hrho) rho' (hS hrho') hne
    rw [him, sub_self, abs_zero] at hs
    linarith
  · calc
      _ ≤ 2 * ⌈1683 * Real.log (T + 3)⌉₊ * Z.card := hcount
      _ ≤ 2 * ⌈1683 * Real.log (T + 3)⌉₊ *
          (longSpacingColorCount B * 1 * W.card) := Nat.mul_le_mul_left _ hWcard
      _ ≤ principalThinningFactor T B * (S.card + 1) := by
        unfold principalThinningFactor
        simpa only [mul_one, mul_assoc] using
          Nat.mul_le_mul_left (2 * ⌈1683 * Real.log (T + 3)⌉₊ * longSpacingColorCount B) hcardSplit

/-- Uniform scalar size of the multiplicity and long-spacing loss. -/
theorem principalThinningFactor_le_log_mul
    {T B : ℝ} (hT : 3 ≤ T) (hlog : 1 ≤ Real.log T) (hB : 1 ≤ B) :
    (principalThinningFactor T B : ℝ) ≤ 33670 * Real.log T * B := by
  have hTp : 0 < T := by linarith
  have hlogShift : Real.log (T + 3) ≤ 2 * Real.log T := by
    have hmono := Real.log_le_log (by linarith : 0 < T + 3)
      (by linarith : T + 3 ≤ 2 * T)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hTp.ne'] at hmono
    have htwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ T)
    linarith
  have hL : (⌈1683 * Real.log (T + 3)⌉₊ : ℝ) ≤ 3367 * Real.log T := by
    have harg : 0 ≤ 1683 * Real.log (T + 3) := mul_nonneg (by norm_num)
      (Real.log_nonneg (by linarith))
    have hc := Nat.ceil_lt_add_one harg
    linarith
  have hm : (longSpacingColorCount B : ℝ) ≤ 5 * B := by
    have hc := Nat.ceil_lt_add_one (by linarith : 0 ≤ 3 * B + 1)
    unfold longSpacingColorCount
    linarith
  unfold principalThinningFactor
  push_cast
  calc
    _ ≤ 2 * (3367 * Real.log T) * (5 * B) := by gcongr
    _ = _ := by ring

/-- Any arbitrarily small power pays for the logarithmic multiplicity
factor, uniformly in the thinning radius. The radius itself remains explicit
for the Fourier-shift scale B=log²(T)+O(T^epsilon). -/
theorem eventually_principalThinningFactor_le_rpow_mul
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ T : ℝ in atTop, ∀ B : ℝ, 1 ≤ B →
      (principalThinningFactor T B : ℝ) ≤ Real.rpow T eta * B := by
  have hp := ZeroDensityArithmetic.polylog_absorption 1 (eta / 2) (by positivity)
  have hc := (tendsto_rpow_atTop (by positivity : 0 < eta / 2)).eventually
    (eventually_ge_atTop (33670 : ℝ))
  have hl := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hp,hc,hl,eventually_ge_atTop (3 : ℝ)] with T hpT hcT hlT hT
  intro B hB
  have hTp : 0 < T := by linarith
  have hpT' : Real.log T ≤ Real.rpow T (eta / 2) := by simpa [Real.rpow_one] using hpT
  have hcT' : 33670 ≤ Real.rpow T (eta / 2) := hcT
  calc
    _ ≤ 33670 * Real.log T * B := principalThinningFactor_le_log_mul hT hlT hB
    _ ≤ Real.rpow T (eta / 2) * Real.rpow T (eta / 2) * B := by gcongr
    _ = Real.rpow T eta * B := by
      change (T ^ (eta / 2) * T ^ (eta / 2)) * B = T ^ eta * B
      rw [← Real.rpow_add hTp]
      congr 2
      ring

/-- At the detector radius log²(T), even the additive discarded-zero cost
is an arbitrary subpower; the original divisor count is still on the left. -/
theorem eventually_principal_logSquared_high_selection
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ T : ℝ in atTop, ∀ sigma : ℝ, 0 ≤ sigma →
      ∃ S : Finset ℂ,
        S ⊆ zeroSupport chiOne sigma T ∧
        (∀ rho ∈ S, (Real.log T) ^ 2 ≤ |rho.im|) ∧
        (∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' →
          3 * (Real.log T) ^ 2 ≤ |rho.im - rho'.im|) ∧
        (S.image Complex.im).card = S.card ∧
        (dirichletZeroCount chiOne sigma T : ℝ) ≤
          Real.rpow T eta * ((S.card : ℝ) + 1) := by
  have hf := eventually_principalThinningFactor_le_rpow_mul (eta / 2) (by positivity)
  have hp := ZeroDensityArithmetic.polylog_absorption 2 (eta / 2) (by positivity)
  have hl := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hf,hp,hl,eventually_gt_atTop (0 : ℝ)] with T hfT hpT hlT hT
  intro sigma hsigma
  have hB : 1 ≤ (Real.log T) ^ 2 := by nlinarith [sq_nonneg (Real.log T - 1)]
  obtain ⟨S,hS,hhigh,hsep,hcard,hcount⟩ := exists_principal_high_threeBSeparated hsigma hB
  refine ⟨S,hS,hhigh,hsep,hcard,?_⟩
  have hcountR : (dirichletZeroCount chiOne sigma T : ℝ) ≤
      (principalThinningFactor T ((Real.log T)^2) : ℝ) * ((S.card : ℝ)+1) := by
    exact_mod_cast hcount
  have hpT' : (Real.log T)^2 ≤ Real.rpow T (eta / 2) := by simpa [Real.rpow_two] using hpT
  have hfactor : (principalThinningFactor T ((Real.log T)^2) : ℝ) ≤ Real.rpow T eta := by
    calc
      _ ≤ Real.rpow T (eta / 2) * (Real.log T)^2 := hfT _ hB
      _ ≤ Real.rpow T (eta / 2) * Real.rpow T (eta / 2) :=
        mul_le_mul_of_nonneg_left hpT' (Real.rpow_nonneg hT.le _)
      _ = _ := by
        change T ^ (eta / 2) * T ^ (eta / 2) = T ^ eta
        rw [← Real.rpow_add hT]
        congr 1
        ring
  exact hcountR.trans (mul_le_mul_of_nonneg_right hfactor (by positivity))

#print axioms eventually_principal_logSquared_high_selection

#print axioms exists_principal_high_threeBSeparated
#print axioms eventually_principalThinningFactor_le_rpow_mul
end
end MAPMontgomeryPrincipalFullScaleThinning
