import ShiuLemma1Rankin
import Mathlib

/-!
# Eventual class-III specialization of Shiu's smooth-number lemma

This module keeps the promoted Rankin/Chebyshev core stable and supplies the
literal logarithmic floor cutoff used in Shiu's class III.  Constants are
deliberately coarse: the application only needs a fourth-power saving.
-/

namespace ShiuLemma1ClassIII

open Filter Asymptotics

noncomputable section

/-- The literal natural cutoff in Shiu's class-III smooth number count. -/
def classIIICutoff (X : ℕ) : ℕ :=
  ⌊Real.log (X : ℝ) * Real.log (Real.log (X : ℝ))⌋₊

/-- All coarse scale inequalities used below hold eventually.  The last one
is precisely `log log z = o(log z)`, with a fixed natural coefficient. -/
theorem eventually_classIIIScales :
    ∀ᶠ z : ℝ in atTop,
      0 < Real.log z ∧
      0 < Real.log (Real.log z) ∧
      512 ≤ Real.log z ∧
      Real.log 90 ≤ Real.log (Real.log z) ∧
      2 * Real.log 2 ≤ Real.log (Real.log z) ∧
      368640 * Real.log 4 ≤ Real.log (Real.log z) ∧
      180 * (512 : ℝ) ^ 2 * Real.log (Real.log z) ≤ Real.log z := by
  have hloglog : Tendsto (fun z : ℝ => Real.log (Real.log z)) atTop atTop := by
    simpa only [Function.comp_def] using
      Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hlo :
      (fun z : ℝ => Real.log (Real.log z)) =o[atTop]
        (fun z : ℝ => Real.log z) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  have hslow :=
    (isLittleO_iff_nat_mul_le'.1 hlo (180 * 512 ^ 2))
  filter_upwards
    [Real.tendsto_log_atTop.eventually (eventually_gt_atTop 0),
      hloglog.eventually (eventually_gt_atTop 0),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop 512),
      hloglog.eventually (eventually_ge_atTop (Real.log 90)),
      hloglog.eventually (eventually_ge_atTop (2 * Real.log 2)),
      hloglog.eventually (eventually_ge_atTop (368640 * Real.log 4)),
      hslow]
    with z hL hLL h512 h90 h2 hbig hslow'
  refine ⟨hL, hLL, h512, h90, h2, hbig, ?_⟩
  simpa only [Real.norm_eq_abs, abs_of_pos hLL, abs_of_pos hL,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hslow'

/-- The literal floor cutoff lies in the deterministic scale window required
by `chebyshevPrimeBudget_le_log_div_64`. -/
theorem classIIICutoff_scale_bounds
    {X Z : ℕ}
    (hL : 0 < Real.log (Z : ℝ))
    (hLL : 0 < Real.log (Real.log (Z : ℝ)))
    (hLlarge : 512 ≤ Real.log (Z : ℝ))
    (hlog90 : Real.log 90 ≤ Real.log (Real.log (Z : ℝ)))
    (hLLlog2 : 2 * Real.log 2 ≤ Real.log (Real.log (Z : ℝ)))
    (hZX : Z ≤ X) (hXZ : X < Z ^ 90) :
    2 ≤ classIIICutoff X ∧
      ((classIIICutoff X : ℕ) : ℝ) ≤
        180 * Real.log (Z : ℝ) * Real.log (Real.log (Z : ℝ)) ∧
      Real.log (Z : ℝ) / 2 ≤ ((classIIICutoff X : ℕ) : ℝ) := by
  let L : ℝ := Real.log (Z : ℝ)
  let LL : ℝ := Real.log L
  let LX : ℝ := Real.log (X : ℝ)
  let LLX : ℝ := Real.log LX
  let A : ℝ := LX * LLX
  have hZ1 : (1 : ℝ) < Z :=
    (Real.log_pos_iff (Nat.cast_nonneg Z)).mp hL
  have hZpos : (0 : ℝ) < Z := lt_trans (by norm_num) hZ1
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le hZpos (by exact_mod_cast hZX)
  have hL' : 0 < L := by simpa [L] using hL
  have hLL' : 0 < LL := by simpa [L, LL] using hLL
  have hlogZX : L ≤ LX := by
    dsimp [L, LX]
    exact Real.log_le_log hZpos (by exact_mod_cast hZX)
  have hlogXZ : LX < 90 * L := by
    have hcast : (X : ℝ) < (Z : ℝ) ^ 90 := by exact_mod_cast hXZ
    have h := Real.log_lt_log hXpos hcast
    rw [Real.log_pow] at h
    simpa [L, LX] using h
  have hLXpos : 0 < LX := lt_of_lt_of_le hL' hlogZX
  have hloglogZX : LL ≤ LLX := by
    dsimp [LL, LLX]
    exact Real.log_le_log hL' hlogZX
  have hloglogXZ : LLX ≤ 2 * LL := by
    have h90L : 0 < (90 : ℝ) * L := by positivity
    have h := (Real.log_lt_log hLXpos hlogXZ).le
    have heq : Real.log ((90 : ℝ) * L) = Real.log 90 + LL := by
      rw [Real.log_mul (by norm_num : (90 : ℝ) ≠ 0) hL'.ne']
    rw [heq] at h
    have h90 : Real.log 90 ≤ LL := by simpa [L, LL] using hlog90
    linarith
  have hLLone : 1 ≤ LL := by
    have h2 : 2 * Real.log 2 ≤ LL := by simpa [L, LL] using hLLlog2
    linarith [Real.log_two_gt_d9]
  have hLLXpos : 0 < LLX := hLL'.trans_le hloglogZX
  have hLLXone : 1 ≤ LLX := hLLone.trans hloglogZX
  have hApos : 0 ≤ A := mul_nonneg hLXpos.le hLLXpos.le
  have hAupper : A ≤ 180 * L * LL := by
    dsimp [A]
    calc
      LX * LLX ≤ (90 * L) * LLX :=
        mul_le_mul_of_nonneg_right hlogXZ.le hLLXpos.le
      _ ≤ (90 * L) * (2 * LL) := by
        exact mul_le_mul_of_nonneg_left hloglogXZ (by positivity)
      _ = 180 * L * LL := by ring
  have hAlower : L ≤ A := by
    dsimp [A]
    calc
      L = L * 1 := by ring
      _ ≤ LX * 1 := mul_le_mul_of_nonneg_right hlogZX (by norm_num)
      _ ≤ LX * LLX := mul_le_mul_of_nonneg_left hLLXone hLXpos.le
  have hfloorUpper : ((classIIICutoff X : ℕ) : ℝ) ≤ 180 * L * LL := by
    calc
      ((classIIICutoff X : ℕ) : ℝ) ≤ A := by
        simpa [classIIICutoff, A, LX, LLX] using Nat.floor_le hApos
      _ ≤ 180 * L * LL := hAupper
  have hfloorLower : L / 2 ≤ ((classIIICutoff X : ℕ) : ℝ) := by
    have hfloor := Nat.sub_one_lt_floor A
    have hhalf : L / 2 ≤ A - 1 := by
      have h512 : 512 ≤ L := by simpa [L] using hLlarge
      linarith
    exact hhalf.trans hfloor.le
  have hcut2 : 2 ≤ classIIICutoff X := by
    exact_mod_cast (show (2 : ℝ) ≤ ((classIIICutoff X : ℕ) : ℝ) by
      have h512 : 512 ≤ L := by simpa [L] using hLlarge
      linarith)
  refine ⟨hcut2, ?_, ?_⟩
  · simpa [L, LL] using hfloorUpper
  · simpa [L] using hfloorLower

/-- A coarse deterministic estimate for the Chebyshev budget.  The hypotheses
are exactly the scale relations later obtained from
`Z ≤ X < Z^90` and sufficiently large `Z`. -/
theorem chebyshevPrimeBudget_le_log_div_64
    {Z Y : ℕ}
    (hLpos : 0 < Real.log (Z : ℝ))
    (hLLpos : 0 < Real.log (Real.log (Z : ℝ)))
    (hYupper : (Y : ℝ) ≤
      180 * Real.log (Z : ℝ) * Real.log (Real.log (Z : ℝ)))
    (hYlower : Real.log (Z : ℝ) / 2 ≤ (Y : ℝ))
    (hLlarge : 512 ≤ Real.log (Z : ℝ))
    (hLLlog2 : 2 * Real.log 2 ≤ Real.log (Real.log (Z : ℝ)))
    (hLLlarge : 368640 * Real.log 4 ≤ Real.log (Real.log (Z : ℝ)))
    (hslow : 180 * (512 : ℝ) ^ 2 * Real.log (Real.log (Z : ℝ)) ≤
      Real.log (Z : ℝ)) :
    ShiuLemma1Rankin.chebyshevPrimeBudget Y ≤
      Real.log (Z : ℝ) / 64 := by
  let L : ℝ := Real.log (Z : ℝ)
  let LL : ℝ := Real.log L
  let s : ℝ := Nat.sqrt Y
  have hL : 0 < L := hLpos
  have hLL : 0 < LL := by simpa [L, LL] using hLLpos
  have hYup : (Y : ℝ) ≤ 180 * L * LL := by simpa [L, LL] using hYupper
  have hYlow : L / 2 ≤ (Y : ℝ) := by simpa [L] using hYlower
  have hL512 : 512 ≤ L := by simpa [L] using hLlarge
  have hLL2 : 2 * Real.log 2 ≤ LL := by simpa [L, LL] using hLLlog2
  have hLLbig : 368640 * Real.log 4 ≤ LL := by
    simpa [L, LL] using hLLlarge
  have hslow' : 180 * (512 : ℝ) ^ 2 * LL ≤ L := by
    simpa [L, LL] using hslow
  have hs_sq : s ^ 2 ≤ (Y : ℝ) := by
    dsimp [s]
    exact_mod_cast Nat.sqrt_le' Y
  have hscaled_sq : (512 * s) ^ 2 ≤ L ^ 2 := by
    calc
      (512 * s) ^ 2 = (512 : ℝ) ^ 2 * s ^ 2 := by ring
      _ ≤ (512 : ℝ) ^ 2 * (Y : ℝ) := by gcongr
      _ ≤ (512 : ℝ) ^ 2 * (180 * L * LL) := by gcongr
      _ = (180 * (512 : ℝ) ^ 2 * LL) * L := by ring
      _ ≤ L * L := mul_le_mul_of_nonneg_right hslow' hL.le
      _ = L ^ 2 := by ring
  have hs_le : 512 * s ≤ L :=
    (sq_le_sq₀ (by positivity) hL.le).mp hscaled_sq
  have hs_add : s + 1 ≤ L / 256 := by
    have hone : (1 : ℝ) ≤ L / 512 := by nlinarith
    nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 :=
    (by linarith [Real.log_two_gt_d9])
  have hinvlog2 : (Real.log 2)⁻¹ ≤ 2 := by
    simpa using
      (inv_le_inv₀ hlog2 (by norm_num : (0 : ℝ) < 1 / 2)).2 hlog2half
  have hfirst :
      ((Nat.sqrt Y + 1 : ℕ) : ℝ) * (Real.log 2)⁻¹ ≤ L / 128 := by
    have : (s + 1) * (Real.log 2)⁻¹ ≤ L / 128 := by
      calc
      (s + 1) * (Real.log 2)⁻¹ ≤ (L / 256) * 2 := by gcongr
      _ = L / 128 := by ring
    simpa [s, Nat.cast_add, Nat.cast_one] using this
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le (by positivity) hYlow
  have hlogY : LL / 2 ≤ Real.log (Y : ℝ) := by
    have hhalfpos : 0 < L / 2 := by positivity
    have hlogmono := Real.log_le_log hhalfpos hYlow
    have hloghalf : Real.log (L / 2) = LL - Real.log 2 := by
      rw [Real.log_div hL.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    rw [hloghalf] at hlogmono
    nlinarith
  have hden : 0 < (LL / 2) ^ 2 := sq_pos_of_pos (by positivity)
  have hnum_le :
      4 * Real.log 4 * (Y : ℝ) ≤
        4 * Real.log 4 * (180 * L * LL) := by gcongr
  have hden_le : (LL / 2) ^ 2 ≤ (Real.log (Y : ℝ)) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (le_trans (by positivity) hlogY)).2 hlogY
  have hsecond_raw :
      (4 * Real.log 4 * (Y : ℝ)) / (Real.log (Y : ℝ)) ^ 2 ≤
        (4 * Real.log 4 * (180 * L * LL)) / (LL / 2) ^ 2 :=
    div_le_div₀ (by positivity) hnum_le hden hden_le
  have hsecond_simplify :
      (4 * Real.log 4 * (180 * L * LL)) / (LL / 2) ^ 2 =
        2880 * Real.log 4 * L / LL := by
    field_simp [hLL.ne']
    ring
  have hsecond_final : 2880 * Real.log 4 * L / LL ≤ L / 128 := by
    apply (div_le_iff₀ hLL).2
    have hmul := mul_le_mul_of_nonneg_right hLLbig hL.le
    nlinarith
  have hsecond :
      (4 * Real.log 4 * (Y : ℝ)) / (Real.log (Y : ℝ)) ^ 2 ≤
        L / 128 := by
    calc
      _ ≤ (4 * Real.log 4 * (180 * L * LL)) / (LL / 2) ^ 2 := hsecond_raw
      _ = 2880 * Real.log 4 * L / LL := hsecond_simplify
      _ ≤ L / 128 := hsecond_final
  unfold ShiuLemma1Rankin.chebyshevPrimeBudget
  change
    ((Nat.sqrt Y + 1 : ℕ) : ℝ) * (Real.log 2)⁻¹ +
      (4 * Real.log 4 * (Y : ℝ)) / (Real.log (Y : ℝ)) ^ 2 ≤ L / 64
  linarith

/-- The exact eventual finite/natural theorem used by Shiu's class III when
`alpha = beta = 1/3`.  The surrounding decomposition supplies `Z ≤ X` and
`X < Z^90` from `Z = y^(1/30)` and `x^(1/3) < y ≤ x` (with a robust rounded
choice of `Z`). -/
theorem exists_classIII_smoothCount_pow_four :
    ∃ Z₀ : ℕ, 2 ≤ Z₀ ∧
      ∀ X Z : ℕ,
        Z₀ ≤ Z →
        Z ≤ X →
        X < Z ^ 90 →
        ShiuLemma1Rankin.smoothCount Z (classIIICutoff X) ^ 4 ≤ Z := by
  obtain ⟨z₀, hz₀⟩ := Filter.eventually_atTop.1 eventually_classIIIScales
  obtain ⟨Z₀, hZ₀⟩ := exists_nat_ge (max z₀ 2)
  have hZ₀two : 2 ≤ Z₀ := by
    exact_mod_cast (show (2 : ℝ) ≤ (Z₀ : ℝ) from
      (le_max_right z₀ 2).trans hZ₀)
  refine ⟨Z₀, hZ₀two, ?_⟩
  intro X Z hZ₀Z hZX hXZ
  have hz₀Z : z₀ ≤ (Z : ℝ) := by
    calc
      z₀ ≤ max z₀ 2 := le_max_left _ _
      _ ≤ (Z₀ : ℝ) := hZ₀
      _ ≤ (Z : ℝ) := by exact_mod_cast hZ₀Z
  obtain ⟨hL, hLL, hLlarge, hlog90, hLLlog2, hLLlarge, hslow⟩ :=
    hz₀ (Z : ℝ) hz₀Z
  obtain ⟨hcut2, hcutUpper, hcutLower⟩ :=
    classIIICutoff_scale_bounds hL hLL hLlarge hlog90 hLLlog2 hZX hXZ
  have hprimeBudget :
      ShiuLemma1Rankin.chebyshevPrimeBudget (classIIICutoff X) ≤
        Real.log (Z : ℝ) / 64 :=
    chebyshevPrimeBudget_le_log_div_64 hL hLL hcutUpper hcutLower
      hLlarge hLLlog2 hLLlarge hslow
  have hbudget :
      4 * (((1 : ℝ) / 8) * Real.log (Z : ℝ) +
          (((1 : ℝ) / 8)⁻¹) *
            ShiuLemma1Rankin.chebyshevPrimeBudget (classIIICutoff X)) ≤
        Real.log (Z : ℝ) := by
    norm_num
    linarith
  exact ShiuLemma1Rankin.smoothCount_pow_four_le_of_chebyshevBudget
    (show (0 : ℝ) < (1 : ℝ) / 8 by norm_num)
    (show 0 < Z by omega) hcut2 hbudget

end

end ShiuLemma1ClassIII
