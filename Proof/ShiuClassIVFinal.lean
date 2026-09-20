import ShiuClassIVBound
import ShiuClassIFinal
import ShiuClassIVEulerBridge

/-! # Final class-IV eventual-scale and natural-budget weld -/

namespace ShiuClassIVBound

open ArithmeticFunction MixedMellinCert ShiuFoundation ShiuSection5Split
  ShiuSection5Structure ShiuLemma4TauTail ShiuLemma4EndpointWeld
open ShiuBoundaryPrimeStructure ShiuClassIBound
open scoped ArithmeticFunction.zeta ArithmeticFunction.Omega BigOperators Topology

noncomputable section

/-- At the common Section-5 endpoint, the literal cutoff
`floor(log X * log log X)` is large enough for the class-IV Rankin range.
The proof uses only the very coarse consequences `log X ≥ 2` and
`log log X ≥ 2`; the enormous existing rounded-scale threshold supplies
these with ample room. -/
theorem smoothCutoff_log_dominates
    {X Z : ℕ}
    (hX : sectionFiveFinalAbsorptionThreshold ≤ X)
    (hZ : 1 ≤ Z) (hZX : Z ≤ X) :
    Real.log (Z : ℝ) <
      (ShiuEndToEnd.smoothCutoff X : ℝ) *
        Real.log (ShiuEndToEnd.smoothCutoff X : ℝ) := by
  have h9pow30T : (9 : ℕ) ^ 30 ≤ sectionFiveFinalAbsorptionThreshold := by
    unfold sectionFiveFinalAbsorptionThreshold
    exact Nat.le_pow (by positivity)
  have h9pow30X : (9 : ℕ) ^ 30 ≤ X := h9pow30T.trans hX
  have h9X : 9 ≤ X := (Nat.le_pow (by omega : 0 < (30 : ℕ))).trans h9pow30X
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hexpOne : Real.exp 1 < (3 : ℝ) :=
    Real.exp_one_lt_d9.trans (by norm_num)
  have hexpTwo : Real.exp 2 < (9 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have h := mul_self_lt_mul_self (Real.exp_pos 1).le hexpOne
    norm_num at h ⊢
    exact h
  have hlog9two : (2 : ℝ) < Real.log 9 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 9)]
    exact hexpTwo
  have hlogPow : Real.log (((9 : ℕ) ^ 30 : ℕ) : ℝ) ≤ Real.log (X : ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast h9pow30X
  have hlogXnine : (9 : ℝ) ≤ Real.log (X : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hlogPow
    norm_num at hlogPow
    nlinarith
  have hlogX2 : (2 : ℝ) ≤ Real.log (X : ℝ) := by linarith
  have hloglogX2 : (2 : ℝ) ≤ Real.log (Real.log (X : ℝ)) := by
    apply (Real.le_log_iff_exp_le (by linarith : 0 < Real.log (X : ℝ))).2
    exact hexpTwo.le.trans hlogXnine
  let t : ℝ := Real.log (X : ℝ) * Real.log (Real.log (X : ℝ))
  have ht : 2 * Real.log (X : ℝ) ≤ t := by
    dsimp [t]
    nlinarith
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hfloorAbove : t < (ShiuEndToEnd.smoothCutoff X : ℝ) + 1 := by
    simpa [ShiuEndToEnd.smoothCutoff, t] using Nat.lt_floor_add_one t
  have hlogXCut : Real.log (X : ℝ) <
      (ShiuEndToEnd.smoothCutoff X : ℝ) := by
    nlinarith
  have hcut3 : 3 ≤ ShiuEndToEnd.smoothCutoff X := by
    exact_mod_cast (show (3 : ℝ) ≤ (ShiuEndToEnd.smoothCutoff X : ℕ) by
      linarith)
  have hcutpos : (0 : ℝ) < ShiuEndToEnd.smoothCutoff X := by
    exact_mod_cast (show 0 < ShiuEndToEnd.smoothCutoff X by omega)
  have hlogcutOne : (1 : ℝ) <
      Real.log (ShiuEndToEnd.smoothCutoff X : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hcutpos]
    exact hexpOne.trans_le (by exact_mod_cast hcut3)
  have hlogZX : Real.log (Z : ℝ) ≤ Real.log (X : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < Z by omega)
    · exact_mod_cast hZX
  have hcutMul : (ShiuEndToEnd.smoothCutoff X : ℝ) <
      (ShiuEndToEnd.smoothCutoff X : ℝ) *
        Real.log (ShiuEndToEnd.smoothCutoff X : ℝ) := by
    nlinarith
  exact hlogZX.trans_lt (hlogXCut.trans hcutMul)

theorem classIVRootCutoff_le_Z
    {Z r : ℕ} (hZ : 1 ≤ Z) (hr : 1 ≤ r) :
    classIVRootCutoff Z r ≤ Z := by
  have hfloor : (classIVRootCutoff Z r : ℝ) ≤
      (Z : ℝ) ^ ((r : ℝ)⁻¹) := by
    unfold classIVRootCutoff
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg Z) _)
  have hexp : (r : ℝ)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hr)
  have hrpow : (Z : ℝ) ^ ((r : ℝ)⁻¹) ≤ (Z : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hZ) hexp
  exact_mod_cast hfloor.trans hrpow

/-- The complete arithmetic absorption for the bracket in one class-IV bin.
The main term uses the exact `modulus / phi(modulus)` Euler cancellation; the
Selberg square error uses `modulus * Z^2 <= Y` and the same Euler envelope. -/
theorem modulus_mul_classIVBracket_exp_le_logPow
    (k X Y modulus Z y : ℕ) (hk : 1 ≤ k)
    (hX : 3 ≤ X) (hmodulus : 0 < modulus) (hmodX : modulus ≤ X)
    (hyX : y ≤ X) (herror : modulus * Z ^ 2 ≤ Y) :
    (modulus : ℝ) *
        (((((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) * Real.log 2)) + (Z : ℝ) ^ 2) *
          Real.exp ((k * k : ℕ) * omittedPrimeInvSum y modulus)) ≤
      5 * (Y : ℝ) *
        (Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4)) *
          (Real.log (X : ℝ)) ^ (k * k)) := by
  let E : ℝ := Real.exp ((k * k : ℕ) * omittedPrimeInvSum y modulus)
  let Q : ℝ := Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4)) *
    (Real.log (X : ℝ)) ^ (k * k)
  have hQ := ShiuClassIVEulerBridge.modulusTotient_mul_exp_omittedPrimeInvSum_le_logPow
    k X y modulus hk hyX hX hmodulus hmodX
  have hQ' : ((modulus : ℝ) / (Nat.totient modulus : ℝ)) * E ≤ Q := by
    simpa [E, Q] using hQ
  have hphi : (0 : ℝ) < Nat.totient modulus := by
    exact_mod_cast Nat.totient_pos.mpr hmodulus
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : (1 : ℝ) ≤
      (modulus : ℝ) / (Nat.totient modulus : ℝ) := by
    apply (le_div_iff₀ hphi).2
    simpa using (show (Nat.totient modulus : ℝ) ≤ (modulus : ℝ) by
      exact_mod_cast Nat.totient_le modulus)
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hlogtwoHalf : (1 : ℝ) ≤ 2 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hcoef : ((2 * Y : ℕ) : ℝ) / Real.log 2 ≤ 4 * (Y : ℝ) := by
    apply (div_le_iff₀ hlog2).2
    push_cast
    nlinarith
  have hmain :
      (modulus : ℝ) *
          ((((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) * Real.log 2)) * E) ≤
        4 * (Y : ℝ) * Q := by
    calc
      (modulus : ℝ) *
          ((((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) * Real.log 2)) * E) =
        (((2 * Y : ℕ) : ℝ) / Real.log 2) *
          (((modulus : ℝ) / (Nat.totient modulus : ℝ)) * E) := by
            field_simp
      _ ≤ (4 * (Y : ℝ)) * Q :=
        mul_le_mul hcoef hQ'
          (mul_nonneg (by positivity) hE0) (by positivity)
  have herrorR : (modulus : ℝ) * (Z : ℝ) ^ 2 ≤ (Y : ℝ) := by
    exact_mod_cast herror
  have hEleRatio : E ≤
      ((modulus : ℝ) / (Nat.totient modulus : ℝ)) * E := by
    calc
      E = 1 * E := by ring
      _ ≤ ((modulus : ℝ) / (Nat.totient modulus : ℝ)) * E :=
        mul_le_mul_of_nonneg_right hratio hE0
  have herr : (modulus : ℝ) * ((Z : ℝ) ^ 2 * E) ≤
      (Y : ℝ) * Q := by
    calc
      (modulus : ℝ) * ((Z : ℝ) ^ 2 * E) =
          ((modulus : ℝ) * (Z : ℝ) ^ 2) * E := by ring
      _ ≤ (Y : ℝ) * E :=
        mul_le_mul_of_nonneg_right herrorR hE0
      _ ≤ (Y : ℝ) *
          (((modulus : ℝ) / (Nat.totient modulus : ℝ)) * E) :=
        mul_le_mul_of_nonneg_left hEleRatio (by positivity)
      _ ≤ (Y : ℝ) * Q :=
        mul_le_mul_of_nonneg_left hQ' (by positivity)
  dsimp [E, Q] at hmain herr ⊢
  calc
    (modulus : ℝ) *
        (((((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) * Real.log 2)) + (Z : ℝ) ^ 2) *
          Real.exp ((k * k : ℕ) * omittedPrimeInvSum y modulus)) =
      (modulus : ℝ) *
          ((((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) * Real.log 2)) *
              Real.exp ((k * k : ℕ) * omittedPrimeInvSum y modulus)) +
        (modulus : ℝ) * ((Z : ℝ) ^ 2 *
          Real.exp ((k * k : ℕ) * omittedPrimeInvSum y modulus)) := by ring
    _ ≤ 4 * (Y : ℝ) *
          (Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4)) *
            (Real.log (X : ℝ)) ^ (k * k)) +
        (Y : ℝ) *
          (Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4)) *
            (Real.log (X : ℝ)) ^ (k * k)) := add_le_add hmain herr
    _ = _ := by ring

/-- One `r`-bin, after a valid weakening of the arithmetic bracket, is bounded
by a summable term sufficient for the end of (5.8). -/
theorem modulus_mul_classIVBinMass_cast_le_series
    (k X Y modulus residue Z cutoff r : ℕ)
    (hk : 1 ≤ k) (hX3 : 3 ≤ X)
    (hZ : 3 ≤ Z) (hcutoff : 2 ≤ cutoff)
    (hlogcutoff : Real.log (Z : ℝ) <
      (cutoff : ℝ) * Real.log (cutoff : ℝ))
    (hYX : Y ≤ X) (hXZ : X < Z ^ 90) (hZY : Z ≤ Y)
    (hmodulus : 0 < modulus) (hmodX : modulus ≤ X)
    (hresidueLt : residue < modulus) (hresidue : residue.Coprime modulus)
    (herror : modulus * Z ^ 2 ≤ Y)
    (hmodLength : ∀ b ∈
      classIVActivePrefixes X Y modulus residue Z cutoff r,
      modulus < quotientLength X Y b)
    (hr : r ∈ Finset.Icc 2 Z) :
    ((modulus * classIVBinMass k X Y modulus residue Z cutoff r : ℕ) : ℝ) ≤
      (5 * ShiuClassIBound.classISelbergConstant *
          ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k *
          Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4))) *
        (Y : ℝ) * (Real.log (X : ℝ)) ^ (k * k) *
          classIVSeriesTerm (classIVSuffixBase k : ℝ) r := by
  have hrIcc := Finset.mem_Icc.mp hr
  have hrootZ : classIVRootCutoff Z r ≤ Z :=
    classIVRootCutoff_le_Z (by omega) (by omega)
  have hrootX : classIVRootCutoff Z r ≤ X := hrootZ.trans (hZY.trans hYX)
  have hbin := classIVBinMass_cast_le_oneTenth
    k X Y modulus residue Z cutoff r hk hZ hcutoff hlogcutoff
    hYX hXZ hZY hmodulus hresidueLt hresidue hmodLength
  let S : ℝ := (k : ℝ) * (k : ℝ) *
    omittedPrimeInvSum (classIVRootCutoff Z r) modulus
  let d : ℝ := (1 / 10 : ℝ) * (r : ℝ) * Real.log (r : ℝ)
  let E : ℝ := Real.exp S
  let T : ℝ := Real.exp (-d)
  let B : ℝ := (((2 * Y : ℕ) : ℝ) /
      ((Nat.totient modulus : ℝ) * Real.log 2)) + (Z : ℝ) ^ 2
  let Q : ℝ := Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4)) *
    (Real.log (X : ℝ)) ^ (k * k)
  have hbracket := modulus_mul_classIVBracket_exp_le_logPow
    k X Y modulus Z (classIVRootCutoff Z r) hk hX3 hmodulus hmodX
      hrootX herror
  have hbracket' : (modulus : ℝ) * (B * E) ≤ 5 * (Y : ℝ) * Q := by
    simpa [B, E, S, Q] using hbracket
  have hExp : Real.exp (S - d) = E * T := by
    dsimp [E, T]
    rw [sub_eq_add_neg, Real.exp_add]
  have hbin0 : (classIVBinMass k X Y modulus residue Z cutoff r : ℝ) ≤
      ((classIVSuffixBase k : ℝ) ^ r *
        ShiuClassIBound.classISelbergConstant) *
          (B * (ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k *
            Real.exp (S - d))) := by
    simpa [B, S, d, Nat.cast_mul] using hbin
  have hbin' : (classIVBinMass k X Y modulus residue Z cutoff r : ℝ) ≤
      ((classIVSuffixBase k : ℝ) ^ r *
        ShiuClassIBound.classISelbergConstant) *
          (B * (ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k *
            (E * T))) := by
    rw [← hExp]
    exact hbin0
  have hfactor0 : 0 ≤
      (classIVSuffixBase k : ℝ) ^ r *
        ShiuClassIBound.classISelbergConstant *
          ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k * T := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg (by positivity) _)
          ShiuClassIBound.classISelbergConstant_pos.le)
        (ShiuFiniteEulerDistortion.explicitEulerDistortionConstant_pos k).le)
      (by dsimp [T]; positivity)
  have hraw :
      ((modulus * classIVBinMass k X Y modulus residue Z cutoff r : ℕ) : ℝ) ≤
        ((classIVSuffixBase k : ℝ) ^ r *
          ShiuClassIBound.classISelbergConstant *
            ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k * T) *
          (5 * (Y : ℝ) * Q) := by
    calc
      ((modulus * classIVBinMass k X Y modulus residue Z cutoff r : ℕ) : ℝ) =
          (modulus : ℝ) *
            (classIVBinMass k X Y modulus residue Z cutoff r : ℝ) := by norm_num
      _ ≤ (modulus : ℝ) *
          (((classIVSuffixBase k : ℝ) ^ r *
            ShiuClassIBound.classISelbergConstant) *
              (B * (ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k *
                (E * T)))) :=
        mul_le_mul_of_nonneg_left hbin' (by positivity)
      _ = ((classIVSuffixBase k : ℝ) ^ r *
          ShiuClassIBound.classISelbergConstant *
            ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k * T) *
          ((modulus : ℝ) * (B * E)) := by ring
      _ ≤ ((classIVSuffixBase k : ℝ) ^ r *
          ShiuClassIBound.classISelbergConstant *
            ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k * T) *
          (5 * (Y : ℝ) * Q) :=
        mul_le_mul_of_nonneg_left hbracket' hfactor0
  have hterm :
      (classIVSuffixBase k : ℝ) ^ r * T ≤
        classIVSeriesTerm (classIVSuffixBase k : ℝ) r := by
    let U : ℝ := (classIVSuffixBase k : ℝ) ^ r * T
    have hU : 0 ≤ U := by dsimp [U, T]; positivity
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    calc
      (classIVSuffixBase k : ℝ) ^ r * T = U := by rfl
      _ = 1 * U := by ring
      _ ≤ (r : ℝ) * U := mul_le_mul_of_nonneg_right hrR hU
      _ = classIVSeriesTerm (classIVSuffixBase k : ℝ) r := by
        dsimp [U, T, d, classIVSeriesTerm]
        ring
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hcoef0 : 0 ≤
      5 * ShiuClassIBound.classISelbergConstant *
        ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k *
        (Y : ℝ) * Q := by
    dsimp [Q]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) ShiuClassIBound.classISelbergConstant_pos.le)
          (ShiuFiniteEulerDistortion.explicitEulerDistortionConstant_pos k).le)
        (by positivity))
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg hlogX0 _))
  calc
    ((modulus * classIVBinMass k X Y modulus residue Z cutoff r : ℕ) : ℝ) ≤
      ((classIVSuffixBase k : ℝ) ^ r *
        ShiuClassIBound.classISelbergConstant *
          ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k * T) *
        (5 * (Y : ℝ) * Q) := hraw
    _ = (5 * ShiuClassIBound.classISelbergConstant *
          ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k *
          (Y : ℝ) * Q) *
        ((classIVSuffixBase k : ℝ) ^ r * T) := by ring
    _ ≤ (5 * ShiuClassIBound.classISelbergConstant *
          ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k *
          (Y : ℝ) * Q) *
        classIVSeriesTerm (classIVSuffixBase k : ℝ) r :=
      mul_le_mul_of_nonneg_left hterm hcoef0
    _ = (5 * ShiuClassIBound.classISelbergConstant *
          ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k *
          Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4))) *
        (Y : ℝ) * (Real.log (X : ℝ)) ^ (k * k) *
          classIVSeriesTerm (classIVSuffixBase k : ℝ) r := by
      dsimp [Q]
      ring

/-- Summing the exact bins and using the already-certified convergent
`r A^r exp(-r log r/10)` series gives a bound uniform in the upper endpoint
`Z`. -/
theorem modulus_mul_classIVMass_cast_le_logPow
    (k X Y modulus residue Z cutoff : ℕ)
    (hk : 1 ≤ k) (hX3 : 3 ≤ X)
    (hZ : 3 ≤ Z) (hcutoff : 2 ≤ cutoff)
    (hlogcutoff : Real.log (Z : ℝ) <
      (cutoff : ℝ) * Real.log (cutoff : ℝ))
    (hYX : Y ≤ X) (hXZ : X < Z ^ 90) (hZY : Z ≤ Y)
    (hmodulus : 0 < modulus) (hmodX : modulus ≤ X)
    (hresidueLt : residue < modulus) (hresidue : residue.Coprime modulus)
    (herror : modulus * Z ^ 2 ≤ Y)
    (hmodLength : ∀ r, ∀ b ∈
      classIVActivePrefixes X Y modulus residue Z cutoff r,
      modulus < quotientLength X Y b) :
    ((modulus * ShiuEndToEnd.classMass k X Y modulus residue Z cutoff
        FourClass.IV : ℕ) : ℝ) ≤
      ((5 * ShiuClassIBound.classISelbergConstant *
          ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k *
          Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4))) *
        (∑' r : ℕ, classIVSeriesTerm (classIVSuffixBase k : ℝ) r)) *
          (Y : ℝ) * (Real.log (X : ℝ)) ^ (k * k) := by
  let K : ℝ := 5 * ShiuClassIBound.classISelbergConstant *
    ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k *
    Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4))
  let A : ℝ := classIVSuffixBase k
  let R : ℝ := ∑' r : ℕ, classIVSeriesTerm A r
  have hApos : 0 < A := by
    dsimp [A, classIVSuffixBase]
    have hkk : 0 < k * k := by nlinarith
    positivity
  have hR0 : 0 ≤ R := by
    dsimp [R]
    exact tsum_nonneg (fun r => classIVSeriesTerm_nonneg hApos.le r)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) ShiuClassIBound.classISelbergConstant_pos.le)
        (ShiuFiniteEulerDistortion.explicitEulerDistortionConstant_pos k).le)
      (Real.exp_pos _).le
  have hY0 : (0 : ℝ) ≤ Y := by positivity
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hsum := finite_classIVSeries_le_tsum A hApos Z
  have hmassEq := classIVMass_eq_sum_bins
    k X Y modulus residue Z cutoff hZ (by omega : 1 ≤ cutoff)
  calc
    ((modulus * ShiuEndToEnd.classMass k X Y modulus residue Z cutoff
        FourClass.IV : ℕ) : ℝ) =
      ∑ r ∈ Finset.Icc 2 Z,
        ((modulus * classIVBinMass k X Y modulus residue Z cutoff r : ℕ) : ℝ) := by
      rw [hmassEq]
      push_cast
      rw [Finset.mul_sum]
    _ ≤ ∑ r ∈ Finset.Icc 2 Z,
        K * (Y : ℝ) * (Real.log (X : ℝ)) ^ (k * k) *
          classIVSeriesTerm A r := by
      apply Finset.sum_le_sum
      intro r hr
      simpa [K, A] using modulus_mul_classIVBinMass_cast_le_series
        k X Y modulus residue Z cutoff r hk hX3 hZ hcutoff hlogcutoff
        hYX hXZ hZY hmodulus hmodX hresidueLt hresidue herror
        (hmodLength r) hr
    _ = (K * (Y : ℝ) * (Real.log (X : ℝ)) ^ (k * k)) *
        (∑ r ∈ Finset.Icc 2 Z, classIVSeriesTerm A r) := by
      rw [Finset.mul_sum]
    _ ≤ (K * (Y : ℝ) * (Real.log (X : ℝ)) ^ (k * k)) * R :=
      mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (mul_nonneg hK0 hY0) (pow_nonneg hlogX0 _))
    _ = ((5 * ShiuClassIBound.classISelbergConstant *
          ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k *
          Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4))) *
        (∑' r : ℕ, classIVSeriesTerm (classIVSuffixBase k : ℝ) r)) *
          (Y : ℝ) * (Real.log (X : ℝ)) ^ (k * k) := by
      dsimp [K, A, R]
      ring

/-- Unconditional adapter to the end-to-end consequence required from (5.8).
The proof uses a sufficient weakening of the printed intermediate bracket. -/
theorem certifiedClassIV58Estimate : ShiuEndToEnd.ClassIV58Estimate := by
  intro k hk
  let A : ℝ := classIVSuffixBase k
  let R : ℝ := ∑' r : ℕ, classIVSeriesTerm A r
  let K : ℝ :=
    (5 * ShiuClassIBound.classISelbergConstant *
      ShiuFiniteEulerDistortion.explicitEulerDistortionConstant k *
      Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4))) * R
  let C : ℕ := ⌈K⌉₊ + 1
  let X₀ : ℕ := max sectionFiveFinalAbsorptionThreshold 3
  have hCpos : 0 < C := by dsimp [C]; omega
  have hX₀ : 2 ≤ X₀ := by dsimp [X₀]; omega
  refine ⟨C, X₀, hCpos, hX₀, ?_⟩
  intro X Y modulus residue hX hmodulus hresidueLt hresidue
    hYX hXY hmodcube
  have hFinalX : sectionFiveFinalAbsorptionThreshold ≤ X :=
    (le_max_left sectionFiveFinalAbsorptionThreshold 3).trans hX
  have hScaleThreshold :
      sectionFiveScaleThreshold ≤ sectionFiveFinalAbsorptionThreshold := by
    unfold sectionFiveScaleThreshold sectionFiveFinalAbsorptionThreshold
    have hbase : (4 : ℕ) ^ 30 ≤ (9 : ℕ) ^ 30 :=
      Nat.pow_le_pow_left (by norm_num) 30
    exact Nat.pow_le_pow_left hbase 3
  have hScaleX : sectionFiveScaleThreshold ≤ X :=
    hScaleThreshold.trans hFinalX
  have hX3 : 3 ≤ X := (le_max_right sectionFiveFinalAbsorptionThreshold 3).trans hX
  obtain ⟨hZ1, hXZ, hsieve, hmodLengthI⟩ :=
    ShiuEndToEnd.certifiedClassIScalePackage
      hScaleX hYX hXY hmodulus hmodcube
  obtain ⟨hZY, hlogSieve, herror⟩ :=
    ShiuEndToEnd.certifiedClassIFinalAbsorptionPackage
      hFinalX hXY hmodcube
  let Z : ℕ := ShiuEndToEnd.sectionFiveZ Y
  let cutoff : ℕ := ShiuEndToEnd.smoothCutoff X
  have hZ1' : 1 ≤ Z := by simpa [Z] using hZ1
  have hXZ' : X < Z ^ 90 := by simpa [Z] using hXZ
  have hZY' : Z ≤ Y := by simpa [Z] using hZY
  have hZX : Z ≤ X := hZY'.trans hYX
  have hsieve' : 2 ≤ classISieveLevel Z := by simpa [Z] using hsieve
  have hZ3 : 3 ≤ Z := by
    have hsquare : classISieveLevel Z ^ 2 ≤ Z := by
      simpa [classISieveLevel, pow_two] using Nat.sqrt_le Z
    have hfour : 4 ≤ classISieveLevel Z ^ 2 := by nlinarith
    omega
  have hlogcutoff : Real.log (Z : ℝ) <
      (cutoff : ℝ) * Real.log (cutoff : ℝ) := by
    simpa [Z, cutoff] using
      smoothCutoff_log_dominates hFinalX hZ1' hZX
  have hcutoff2 : 2 ≤ cutoff := by
    by_contra hnot
    have hcutle : cutoff ≤ 1 := by omega
    have hlogcutNonpos : Real.log (cutoff : ℝ) ≤ 0 :=
      Real.log_nonpos (by positivity) (by exact_mod_cast hcutle)
    have hprodNonpos : (cutoff : ℝ) * Real.log (cutoff : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hlogcutNonpos
    have hlogZpos : 0 < Real.log (Z : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
    linarith
  have herror' : modulus * Z ^ 2 ≤ Y := by simpa [Z] using herror
  have hmodX : modulus ≤ X :=
    ShiuEndToEnd.modulus_le_ambient_of_shiuRange (by omega) hYX hmodcube
  have hmodLength : ∀ r, ∀ b ∈
      classIVActivePrefixes X Y modulus residue Z cutoff r,
      modulus < quotientLength X Y b := by
    intro r b hb
    have hbIcc := activePrefix_mem_Icc hb
    have hbCop := (activePrefix_mem_tauSquareSmoothTailSupport
      hZ3 (by omega : 1 ≤ cutoff) hresidue hb).2.2
    have hbOuter : b ∈ classIOuterPrefixes Z modulus := by
      exact Finset.mem_filter.mpr ⟨hbIcc, hbCop⟩
    simpa [Z] using hmodLengthI b hbOuter
  have hreal := modulus_mul_classIVMass_cast_le_logPow
    k X Y modulus residue Z cutoff hk hX3 hZ3 hcutoff2 hlogcutoff
      hYX hXZ' hZY' hmodulus hmodX hresidueLt hresidue herror' hmodLength
  have hreal' :
      ((modulus * ShiuEndToEnd.classMass k X Y modulus residue Z cutoff
          FourClass.IV : ℕ) : ℝ) ≤
        K * (Y : ℝ) * (Real.log (X : ℝ)) ^ (k * k) := by
    simpa [K, R, A, mul_assoc] using hreal
  have hlog0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hlogBridge := realLog_le_natLogTwoSucc
    (X := X) (show 1 ≤ X by omega)
  have hlogPow : (Real.log (X : ℝ)) ^ (k * k) ≤
      (((Nat.log 2 (X + 2) + 1 : ℕ) : ℝ)) ^ (k * k) :=
    pow_le_pow_left₀ hlog0 hlogBridge (k * k)
  have hKle : K ≤ (C : ℝ) := by
    calc
      K ≤ (⌈K⌉₊ : ℕ) := Nat.le_ceil K
      _ ≤ (C : ℕ) := by dsimp [C]; exact_mod_cast Nat.le_succ _
  have htargetR :
      ((modulus * ShiuEndToEnd.classMass k X Y modulus residue Z cutoff
          FourClass.IV : ℕ) : ℝ) ≤
        ((C * Y * (Nat.log 2 (X + 2) + 1) ^ (k * k) : ℕ) : ℝ) := by
    calc
      ((modulus * ShiuEndToEnd.classMass k X Y modulus residue Z cutoff
          FourClass.IV : ℕ) : ℝ) ≤
        K * (Y : ℝ) * (Real.log (X : ℝ)) ^ (k * k) := hreal'
      _ ≤ (C : ℝ) * (Y : ℝ) *
          (((Nat.log 2 (X + 2) + 1 : ℕ) : ℝ)) ^ (k * k) := by
        gcongr
      _ = ((C * Y * (Nat.log 2 (X + 2) + 1) ^ (k * k) : ℕ) : ℝ) := by
        norm_num
  have htargetNat :
      modulus * ShiuEndToEnd.classMass k X Y modulus residue Z cutoff
          FourClass.IV ≤
        C * Y * (Nat.log 2 (X + 2) + 1) ^ (k * k) := by
    exact_mod_cast htargetR
  simpa [Z, cutoff, ShiuEndToEnd.classBudgetBase, Nat.mul_assoc] using htargetNat

end
end ShiuClassIVBound

#print axioms ShiuClassIVBound.smoothCutoff_log_dominates
#print axioms ShiuClassIVBound.modulus_mul_classIVBracket_exp_le_logPow
#print axioms ShiuClassIVBound.modulus_mul_classIVBinMass_cast_le_series
#print axioms ShiuClassIVBound.modulus_mul_classIVMass_cast_le_logPow
#print axioms ShiuClassIVBound.certifiedClassIV58Estimate
