import RamachandraShiftedContourSharpEnvelopes
import RamachandraShortGammaPolylogMass

/-!
# Uniform fourth-power envelope on Ramachandra's short contour

The near-line exponent is not discarded.  In the source strip it is
`O(1 / log X)`, so the conductor and external ordinate powers are bounded by
an absolute constant.  Only a fixed cubic Mellin-ordinate weight remains.
-/

namespace RamachandraShortFunctionalFactorMomentEnvelope

open Complex
open RamachandraShiftedContourSharpEnvelopes
open RamachandraShortGammaPolylogMass
open BHPRamachandraMeanValueFromDyadicAFE

noncomputable section

variable {d : ℕ} [NeZero d]

/-- A convenient absolute constant for the short functional-factor fourth
power. -/
def shortFunctionalMomentConstant : ℝ :=
  (8000 * Real.exp 4) ^ 4

theorem shortFunctionalMomentConstant_nonneg :
    0 ≤ shortFunctionalMomentConstant := by
  unfold shortFunctionalMomentConstant
  positivity

private theorem exp_seven_fifths_lt_six : Real.exp (7 / 5 : ℝ) < 6 := by
  have he1 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have heTwoFifths : Real.exp (2 / 5 : ℝ) ≤ 5 / 3 := by
    have h := MAPMertensAnalyticLeaf.exp_le_inv_one_sub
      (u := (2 / 5 : ℝ)) (by norm_num)
    norm_num at h ⊢
    exact h
  rw [show (7 / 5 : ℝ) = 1 + 2 / 5 by norm_num, Real.exp_add]
  calc
    Real.exp 1 * Real.exp (2 / 5 : ℝ) < 3 * (5 / 3 : ℝ) :=
      mul_lt_mul he1 heTwoFifths (Real.exp_pos _) (by norm_num)
    _ < 6 := by norm_num

private theorem seven_fifths_le_log_of_six_le
    {X : ℝ} (hX : 6 ≤ X) :
    7 / 5 ≤ Real.log X := by
  have hlog6 : (7 / 5 : ℝ) < Real.log 6 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 exp_seven_fifths_lt_six
  have hXpos : 0 < X := by linarith
  exact hlog6.le.trans
    (Real.strictMonoOn_log.monotoneOn (by norm_num) hXpos hX)

/-- Exact smallness of the near-line exponent under the source-width strip. -/
theorem shortExponent_bounds
    {X sigma : ℝ} (hX : 6 ≤ X)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log X)⁻¹) :
    let a := (1 / 2 : ℝ) - (sigma - (Real.log X)⁻¹)
    0 ≤ a ∧ a ≤ 2 / Real.log X ∧ a ≤ 3 / 4 := by
  let L := Real.log X
  let delta := L⁻¹ * (1 / 100 : ℝ)
  let a := (1 / 2 : ℝ) - (sigma - L⁻¹)
  have hL : 7 / 5 ≤ L := by
    simpa [L] using seven_fifths_le_log_of_six_le hX
  have hLpos : 0 < L := by linarith
  have hdelta0 : 0 ≤ delta := by dsimp [delta]; positivity
  have hdelta_le_inv : delta ≤ L⁻¹ := by
    dsimp [delta]
    have hInv0 : 0 ≤ L⁻¹ := inv_nonneg.mpr hLpos.le
    nlinarith
  have habs : -(delta) ≤ sigma - (1 / 2 : ℝ) ∧
      sigma - (1 / 2 : ℝ) ≤ delta := by
    simpa [delta, L, mul_comm] using (abs_le.mp hstrip)
  have hslo : (1 / 2 : ℝ) - delta ≤ sigma := by linarith [habs.1]
  have hshi : sigma ≤ (1 / 2 : ℝ) + delta := by linarith [habs.2]
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have ha2 : a ≤ 2 / L := by
    calc
      a ≤ delta + L⁻¹ := by dsimp [a]; linarith [hslo]
      _ ≤ L⁻¹ + L⁻¹ := by linarith [hdelta_le_inv]
      _ = 2 / L := by simp only [div_eq_mul_inv]; ring
  have hainv : a ≤ (101 / 100 : ℝ) * L⁻¹ := by
    dsimp [a]
    dsimp [delta] at hslo
    linarith
  have hinvL : L⁻¹ ≤ (5 / 7 : ℝ) := by
    have := (inv_le_inv₀ hLpos (by norm_num : (0 : ℝ) < 7 / 5)).2 hL
    norm_num at this ⊢
    exact this
  have ha34 : a ≤ 3 / 4 := by
    calc
      a ≤ (101 / 100 : ℝ) * L⁻¹ := hainv
      _ ≤ (101 / 100 : ℝ) * (5 / 7 : ℝ) := by gcongr
      _ ≤ 3 / 4 := by norm_num
  exact ⟨ha0, ha2, ha34⟩

/-- Source-range fourth-power envelope.  The product identity `X=dT` is
kept explicit so no conductor/height growth is hidden in the constant. -/
theorem norm_functionalFactor_short_pow_four_le
    (psi : DirichletCharacter ℂ d) (hprim : psi.IsPrimitive)
    {X T sigma t v : ℝ}
    (hXeq : X = (d : ℝ) * T) (hT : 3 ≤ T)
    (hX : 6 ≤ X)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log X)⁻¹)
    (ht : |t| ≤ T) (hne : t + v ≠ 0) :
    ‖ramachandraFunctionalFactor psi
        (shortFunctionalPoint X sigma t v)‖ ^ 4 ≤
      shortFunctionalMomentConstant * (1 + |v|) ^ 3 := by
  let r : ℝ := sigma - (Real.log X)⁻¹
  let a : ℝ := (1 / 2 : ℝ) - r
  let V : ℝ := 1 + |v|
  let E : ℝ := (d : ℝ) * (1 + |t|)
  have hab := shortExponent_bounds hX hstrip
  change 0 ≤ a ∧ a ≤ 2 / Real.log X ∧ a ≤ 3 / 4 at hab
  have ha0 : 0 ≤ a := hab.1
  have ha2 : a ≤ 2 / Real.log X := hab.2.1
  have ha34 : a ≤ 3 / 4 := hab.2.2
  have hrlo : -(1 / 4 : ℝ) ≤ r := by dsimp [a] at ha34; linarith
  have hrhi : r ≤ 1 / 2 := by dsimp [a] at ha0; linarith
  have hraw := norm_functionalFactor_shortFunctionalPoint_sharp_le
    psi hprim (X := X) (sigma := sigma) (t := t) (v := v)
      (by simpa [r] using hrlo) (by simpa [r] using hrhi) hne
  have hB0 : 0 ≤ 1 + |t + v| := by positivity
  have hV1 : 1 ≤ V := by dsimp [V]; linarith [abs_nonneg v]
  have hV0 : 0 ≤ V := hV1.trans' (by norm_num)
  have hsplit2000 :
      Real.rpow (2000 * (1 + |t + v|)) a =
        Real.rpow 2000 a * Real.rpow (1 + |t + v|) a := by
    exact Real.mul_rpow (by norm_num) hB0
  have hmerge2000 :
      Real.rpow 2000 (1 / 2 + r) * Real.rpow 2000 a = 2000 := by
    calc
      Real.rpow 2000 (1 / 2 + r) * Real.rpow 2000 a =
          Real.rpow 2000 ((1 / 2 + r) + a) :=
        (Real.rpow_add (by norm_num : (0 : ℝ) < 2000) _ _).symm
      _ = Real.rpow 2000 1 := by
        congr 1
        dsimp [a]
        ring
      _ = 2000 := Real.rpow_one 2000
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hcombine :
      Real.rpow (d : ℝ) a * Real.rpow (1 + |t + v|) a =
        Real.rpow ((d : ℝ) * (1 + |t + v|)) a := by
    exact (Real.mul_rpow hd0 hB0).symm
  have hraw' :
      ‖ramachandraFunctionalFactor psi
          (shortFunctionalPoint X sigma t v)‖ ≤
        8000 * Real.rpow ((d : ℝ) * (1 + |t + v|)) a := by
    rw [show (1 / 2 : ℝ) - (sigma - (Real.log X)⁻¹) = a by rfl,
      show (1 / 2 : ℝ) + (sigma - (Real.log X)⁻¹) = 1 / 2 + r by rfl,
      hsplit2000] at hraw
    calc
      _ ≤ Real.rpow (d : ℝ) a *
          (4 * (Real.rpow 2000 (1 / 2 + r) *
            (Real.rpow 2000 a * Real.rpow (1 + |t + v|) a))) := hraw
      _ = 4 * (Real.rpow (d : ℝ) a *
          Real.rpow (1 + |t + v|) a) *
          (Real.rpow 2000 (1 / 2 + r) * Real.rpow 2000 a) := by ring
      _ = 8000 * (Real.rpow (d : ℝ) a *
          Real.rpow (1 + |t + v|) a) := by rw [hmerge2000]; ring
      _ = 8000 * Real.rpow ((d : ℝ) * (1 + |t + v|)) a := by rw [hcombine]
  have hsep : 1 + |t + v| ≤ (1 + |t|) * V := by
    dsimp [V]
    have htri := abs_add_le t v
    nlinarith [abs_nonneg t, abs_nonneg v]
  have hbase : (d : ℝ) * (1 + |t + v|) ≤ E * V := by
    simpa [E, mul_assoc] using mul_le_mul_of_nonneg_left hsep hd0
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hEV :
      Real.rpow ((d : ℝ) * (1 + |t + v|)) a ≤
        Real.rpow E a * Real.rpow V a := by
    calc
      Real.rpow ((d : ℝ) * (1 + |t + v|)) a ≤
          Real.rpow (E * V) a :=
        Real.rpow_le_rpow (mul_nonneg hd0 hB0) hbase ha0
      _ = Real.rpow E a * Real.rpow V a := Real.mul_rpow hE0 hV0
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hE2X : E ≤ 2 * X := by
    have htT : |t| ≤ T := ht
    have h1t : 1 + |t| ≤ 2 * T := by linarith
    dsimp [E]
    calc
      (d : ℝ) * (1 + |t|) ≤ (d : ℝ) * (2 * T) :=
        mul_le_mul_of_nonneg_left h1t hd0
      _ = 2 * X := by rw [hXeq]; ring
  have hEpos : 0 < E := by dsimp [E]; positivity
  have h2Xpos : 0 < 2 * X := by linarith
  have hlog2X : Real.log (2 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : X ≠ 0)]
    have hlog2 : Real.log 2 ≤ Real.log X :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith
  have haLog : a * Real.log (2 * X) ≤ 4 := by
    have hlog2X0 : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by linarith)
    have hstep : a * Real.log (2 * X) ≤
        (2 / Real.log X) * (2 * Real.log X) := by gcongr
    calc
      a * Real.log (2 * X) ≤
          (2 / Real.log X) * (2 * Real.log X) := hstep
      _ = 4 := by field_simp; norm_num
  have hErpow : Real.rpow E a ≤ Real.exp 4 := by
    calc
      Real.rpow E a ≤ Real.rpow (2 * X) a :=
        Real.rpow_le_rpow hEpos.le hE2X ha0
      _ = Real.exp (Real.log (2 * X) * a) := Real.rpow_def_of_pos h2Xpos _
      _ ≤ Real.exp 4 := by
        apply Real.exp_le_exp.mpr
        nlinarith [haLog]
  have hnorm :
      ‖ramachandraFunctionalFactor psi
          (shortFunctionalPoint X sigma t v)‖ ≤
        (8000 * Real.exp 4) * Real.rpow V a := by
    calc
      _ ≤ 8000 * Real.rpow ((d : ℝ) * (1 + |t + v|)) a := hraw'
      _ ≤ 8000 * (Real.rpow E a * Real.rpow V a) := by gcongr
      _ ≤ 8000 * (Real.exp 4 * Real.rpow V a) := by
        gcongr
        exact Real.rpow_nonneg hV0 a
      _ = (8000 * Real.exp 4) * Real.rpow V a := by ring
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hnorm 4
  have hrpow4 : (Real.rpow V a) ^ 4 = Real.rpow V (4 * a) := by
    calc
      (Real.rpow V a) ^ 4 = Real.rpow V (a * (4 : ℝ)) :=
        (Real.rpow_mul_natCast hV0 a 4).symm
      _ = Real.rpow V (4 * a) := by ring
  have h4a : 4 * a ≤ 3 := by linarith
  have hVpow : Real.rpow V (4 * a) ≤ V ^ 3 := by
    calc
      Real.rpow V (4 * a) ≤ Real.rpow V 3 :=
        Real.rpow_le_rpow_of_exponent_le hV1 h4a
      _ = V ^ 3 := by norm_num [Real.rpow_natCast]
  calc
    ‖ramachandraFunctionalFactor psi
        (shortFunctionalPoint X sigma t v)‖ ^ 4 ≤
      ((8000 * Real.exp 4) * Real.rpow V a) ^ 4 := hpow
    _ = shortFunctionalMomentConstant * Real.rpow V (4 * a) := by
      rw [mul_pow, hrpow4]
      rfl
    _ ≤ shortFunctionalMomentConstant * V ^ 3 :=
      mul_le_mul_of_nonneg_left hVpow shortFunctionalMomentConstant_nonneg
    _ = shortFunctionalMomentConstant * (1 + |v|) ^ 3 := rfl

end
end RamachandraShortFunctionalFactorMomentEnvelope

#print axioms RamachandraShortFunctionalFactorMomentEnvelope.norm_functionalFactor_short_pow_four_le
