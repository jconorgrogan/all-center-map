import ShiuSection5ScaleRounding
import ShiuEndToEndScaffold

/-!
# Final Section-5 class-I absorption

This file joins the literal Lemma-2/Lemma-3 class-I estimate to the rounded
Section-5 scale package and the exact modulus/totient Euler-product
cancellation.  In particular, the modulus does not introduce a second
logarithmic power: the final exponent remains exactly `k*k`.
-/

namespace ShiuClassIBound

open ArithmeticFunction MixedMellinCert ShiuFoundation ShiuSection5Split
  ShiuSection5Structure
open scoped ArithmeticFunction.zeta BigOperators

noncomputable section

/-- The finite omitted Euler product, in the notation of the end-to-end
modulus/totient cancellation module. -/
def classIOmittedEulerProduct (k x modulus : ℕ) : ℝ :=
  ∏ p ∈ (x + 1).primesBelow,
    (if p ∣ modulus then 1 else
      ShiuEndToEnd.eulerInvFactor p ^ (k * k))

lemma classIOmittedEulerProduct_nonneg (k x modulus : ℕ) :
    0 ≤ classIOmittedEulerProduct k x modulus := by
  apply Finset.prod_nonneg
  intro p hp
  by_cases hpd : p ∣ modulus
  · simp [hpd]
  · have hprime := Nat.prime_of_mem_primesBelow hp
    simp only [hpd, if_false]
    exact (show (0 : ℝ) ≤ 1 by norm_num).trans
      (one_le_pow₀ (ShiuEndToEnd.one_le_eulerInvFactor hprime))

/-- Enlarging the prime cutoff only inserts Euler factors at least one. -/
theorem classIOmittedEulerProduct_mono
    (k modulus : ℕ) {z x : ℕ} (hzx : z ≤ x) :
    classIOmittedEulerProduct k z modulus ≤
      classIOmittedEulerProduct k x modulus := by
  unfold classIOmittedEulerProduct
  apply Finset.prod_le_prod_of_subset_of_one_le₀
  · intro p hp
    have hpdata := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega, hpdata.2⟩
  · intro p hp
    by_cases hpd : p ∣ modulus
    · simp [hpd]
    · have hprime := Nat.prime_of_mem_primesBelow hp
      simp only [hpd, if_false]
      exact (show (0 : ℝ) ≤ 1 by norm_num).trans
        (one_le_pow₀ (ShiuEndToEnd.one_le_eulerInvFactor hprime))
  · intro p hp hnot
    by_cases hpd : p ∣ modulus
    · simp [hpd]
    · have hprime := Nat.prime_of_mem_primesBelow hp
      simpa [hpd] using
        one_le_pow₀ (ShiuEndToEnd.one_le_eulerInvFactor hprime)

/-- The natural base-two logarithm in the public Shiu contract dominates the
real logarithm. -/
theorem realLog_le_natLogTwoSucc
    {X : ℕ} (hX : 1 ≤ X) :
    Real.log (X : ℝ) ≤ ((Nat.log 2 (X + 2) + 1 : ℕ) : ℝ) := by
  let L : ℕ := Nat.log 2 (X + 2) + 1
  have hpow : X + 2 < 2 ^ L := by
    simpa [L, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by omega : 1 < 2) (X + 2)
  have hXpowNat : X ≤ 2 ^ L := by omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXpow : (X : ℝ) ≤ (2 : ℝ) ^ L := by exact_mod_cast hXpowNat
  have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  calc
    Real.log (X : ℝ) ≤ Real.log ((2 : ℝ) ^ L) :=
      Real.log_le_log hXpos hXpow
    _ = (L : ℝ) * Real.log 2 := by rw [Real.log_pow]
    _ ≤ (L : ℝ) := by
      have hL : (0 : ℝ) ≤ L := by positivity
      nlinarith
    _ = ((Nat.log 2 (X + 2) + 1 : ℕ) : ℝ) := by rfl

/-- Real form of the final class-I estimate.  The coefficient depends only on
`k`; all interval, progression, and rounded-scale variables remain uniform. -/
theorem modulus_mul_classIMass_cast_le_logPow
    (k X Y modulus residue Z cutoff : ℕ) (hk : 1 ≤ k)
    (hZ : 1 ≤ Z) (hYX : Y ≤ X) (hXZ : X < Z ^ 90)
    (hZY : Z ≤ Y) (hZX : Z ≤ X)
    (hmodulus : 0 < modulus) (hresidueLt : residue < modulus)
    (hresidue : residue.Coprime modulus)
    (hsieve : 2 ≤ classISieveLevel Z)
    (hmodLength : ∀ b ∈ classIOuterPrefixes Z modulus,
      modulus < quotientLength X Y b)
    (hlog : (1 : ℝ) ≤ Real.log (classISieveLevel Z : ℝ))
    (herror : modulus * Z ^ 2 ≤ Y)
    (hXthree : 3 ≤ X) (hmodX : modulus ≤ X) :
    ((modulus * classIMass k X Y modulus residue Z cutoff : ℕ) : ℝ) ≤
      (3 * (((k * k) ^ 179 : ℕ) : ℝ) * classISelbergConstant *
          Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4))) *
        (Y : ℝ) * (Real.log (X : ℝ)) ^ (k * k) := by
  let PZ := classIOmittedEulerProduct k Z modulus
  let PX := classIOmittedEulerProduct k X modulus
  let A : ℝ := (((k * k) ^ 179 : ℕ) : ℝ) * classISelbergConstant
  let L : ℝ := Real.log (classISieveLevel Z : ℝ)
  let B : ℝ :=
    (((2 * Y : ℕ) : ℝ) /
      ((Nat.totient modulus : ℝ) * L) + (Z : ℝ) ^ 2) * PZ
  have hmass0 := classIMass_cast_le_localEulerProductBracket_fixed
    k X Y modulus residue Z cutoff hk hZ hYX hXZ hZY
      hmodulus hresidueLt hresidue hsieve hmodLength
  have hmass : (classIMass k X Y modulus residue Z cutoff : ℝ) ≤
      A * B := by
    simpa [A, B, L, PZ, classIOmittedEulerProduct,
      ShiuEndToEnd.eulerInvFactor] using hmass0
  have hphi : (0 : ℝ) < Nat.totient modulus := by
    exact_mod_cast Nat.totient_pos.mpr hmodulus
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hqphi : (1 : ℝ) ≤ (modulus : ℝ) / (Nat.totient modulus : ℝ) := by
    apply (le_div_iff₀ hphi).2
    have ht : (Nat.totient modulus : ℝ) ≤ (modulus : ℝ) := by
      exact_mod_cast Nat.totient_le modulus
    simpa using ht
  have hPmono : PZ ≤ PX := by
    exact classIOmittedEulerProduct_mono k modulus hZX
  have hPZ0 : 0 ≤ PZ := by
    exact classIOmittedEulerProduct_nonneg k Z modulus
  have hPX0 : 0 ≤ PX := by
    exact classIOmittedEulerProduct_nonneg k X modulus
  have hmainCoeff :
      (modulus : ℝ) *
          (((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) * L)) ≤
        ((2 * Y : ℕ) : ℝ) *
          ((modulus : ℝ) / (Nat.totient modulus : ℝ)) := by
    have hnum : 0 ≤ ((2 * Y : ℕ) : ℝ) *
        ((modulus : ℝ) / (Nat.totient modulus : ℝ)) := by positivity
    calc
      (modulus : ℝ) *
          (((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) * L)) =
        ((((2 * Y : ℕ) : ℝ) *
          ((modulus : ℝ) / (Nat.totient modulus : ℝ))) / L) := by
            field_simp
      _ ≤ ((2 * Y : ℕ) : ℝ) *
          ((modulus : ℝ) / (Nat.totient modulus : ℝ)) := by
            apply (div_le_iff₀ hLpos).2
            nlinarith
  have hmain :
      (modulus : ℝ) *
          (((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) * L)) * PZ ≤
        ((2 * Y : ℕ) : ℝ) *
          (((modulus : ℝ) / (Nat.totient modulus : ℝ)) * PX) := by
    calc
      (modulus : ℝ) *
          (((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) * L)) * PZ ≤
        (((2 * Y : ℕ) : ℝ) *
          ((modulus : ℝ) / (Nat.totient modulus : ℝ))) * PZ :=
            mul_le_mul_of_nonneg_right hmainCoeff hPZ0
      _ ≤ (((2 * Y : ℕ) : ℝ) *
          ((modulus : ℝ) / (Nat.totient modulus : ℝ))) * PX := by
            apply mul_le_mul_of_nonneg_left hPmono
            positivity
      _ = ((2 * Y : ℕ) : ℝ) *
          (((modulus : ℝ) / (Nat.totient modulus : ℝ)) * PX) := by ring
  have herrorR : (modulus : ℝ) * (Z : ℝ) ^ 2 ≤ (Y : ℝ) := by
    exact_mod_cast herror
  have hPXleQ : PX ≤
      ((modulus : ℝ) / (Nat.totient modulus : ℝ)) * PX := by
    calc
      PX = 1 * PX := by ring
      _ ≤ ((modulus : ℝ) / (Nat.totient modulus : ℝ)) * PX :=
        mul_le_mul_of_nonneg_right hqphi hPX0
  have herr :
      (modulus : ℝ) * (Z : ℝ) ^ 2 * PZ ≤
        (Y : ℝ) *
          (((modulus : ℝ) / (Nat.totient modulus : ℝ)) * PX) := by
    calc
      (modulus : ℝ) * (Z : ℝ) ^ 2 * PZ ≤ (Y : ℝ) * PZ :=
        mul_le_mul_of_nonneg_right herrorR hPZ0
      _ ≤ (Y : ℝ) * PX := by
        exact mul_le_mul_of_nonneg_left hPmono (by positivity)
      _ ≤ (Y : ℝ) *
          (((modulus : ℝ) / (Nat.totient modulus : ℝ)) * PX) :=
        mul_le_mul_of_nonneg_left hPXleQ (by positivity)
  have hbracket :
      (modulus : ℝ) * B ≤
        (3 * (Y : ℝ)) *
          (((modulus : ℝ) / (Nat.totient modulus : ℝ)) * PX) := by
    dsimp [B]
    calc
      (modulus : ℝ) *
          ((((2 * Y : ℕ) : ℝ) /
              ((Nat.totient modulus : ℝ) * L) + (Z : ℝ) ^ 2) * PZ) =
        (modulus : ℝ) *
            (((2 * Y : ℕ) : ℝ) /
              ((Nat.totient modulus : ℝ) * L)) * PZ +
          (modulus : ℝ) * (Z : ℝ) ^ 2 * PZ := by ring
      _ ≤ ((2 * Y : ℕ) : ℝ) *
            (((modulus : ℝ) / (Nat.totient modulus : ℝ)) * PX) +
          (Y : ℝ) *
            (((modulus : ℝ) / (Nat.totient modulus : ℝ)) * PX) :=
        add_le_add hmain herr
      _ = (3 * (Y : ℝ)) *
          (((modulus : ℝ) / (Nat.totient modulus : ℝ)) * PX) := by
        push_cast
        ring
  have hQ := ShiuEndToEnd.modulusTotient_omittedEulerProduct_le_logPow
    k X modulus hk hXthree hmodulus hmodX
  have hQ' :
      ((modulus : ℝ) / (Nat.totient modulus : ℝ)) * PX ≤
        Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4)) *
          (Real.log (X : ℝ)) ^ (k * k) := by
    simpa [PX, classIOmittedEulerProduct] using hQ
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (by positivity) classISelbergConstant_pos.le
  calc
    ((modulus * classIMass k X Y modulus residue Z cutoff : ℕ) : ℝ) =
        (modulus : ℝ) *
          (classIMass k X Y modulus residue Z cutoff : ℝ) := by norm_num
    _ ≤ (modulus : ℝ) * (A * B) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = A * ((modulus : ℝ) * B) := by ring
    _ ≤ A * ((3 * (Y : ℝ)) *
        (((modulus : ℝ) / (Nat.totient modulus : ℝ)) * PX)) :=
      mul_le_mul_of_nonneg_left hbracket hA0
    _ ≤ A * ((3 * (Y : ℝ)) *
        (Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4)) *
          (Real.log (X : ℝ)) ^ (k * k))) := by
      gcongr
    _ = (3 * (((k * k) ^ 179 : ℕ) : ℝ) * classISelbergConstant *
          Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4))) *
        (Y : ℝ) * (Real.log (X : ℝ)) ^ (k * k) := by
      dsimp [A]
      ring


/-- The literal natural-valued class-I contribution required by the public
Section-5 class estimates.  The only constant chosen here depends on `k`; the
endpoint and every displayed progression parameter are uniform. -/
theorem certifiedClassIContributionBound : ClassIContributionBound := by
  intro k hk
  let K : ℝ :=
    3 * (((k * k) ^ 179 : ℕ) : ℝ) * classISelbergConstant *
      Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4))
  let C : ℕ := ⌈K⌉₊ + 1
  let X₀ : ℕ := max sectionFiveFinalAbsorptionThreshold 3
  have hKpos : 0 < K := by
    dsimp [K]
    have hkk : 1 ≤ k * k := Nat.mul_le_mul hk hk
    have hpow : 0 < ((k * k) ^ 179 : ℕ) :=
      Nat.zero_lt_one.trans_le (one_le_pow₀ hkk)
    have hpowR : (0 : ℝ) < (((k * k) ^ 179 : ℕ) : ℝ) := by
      exact_mod_cast hpow
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) hpowR) classISelbergConstant_pos)
      (Real.exp_pos _)
  have hCpos : 0 < C := by dsimp [C]; omega
  have hX₀ : 2 ≤ X₀ := by dsimp [X₀]; omega
  refine ⟨C, X₀, hCpos, hX₀, ?_⟩
  intro X Y modulus residue hX hmodulus hresidueLt hresidue
    hYX hXY hmodcube
  dsimp only
  have hFinalX : sectionFiveFinalAbsorptionThreshold ≤ X := by
    exact (le_max_left sectionFiveFinalAbsorptionThreshold 3).trans hX
  have hScaleThreshold :
      sectionFiveScaleThreshold ≤ sectionFiveFinalAbsorptionThreshold := by
    unfold sectionFiveScaleThreshold sectionFiveFinalAbsorptionThreshold
    have hbase : (4 : ℕ) ^ 30 ≤ (9 : ℕ) ^ 30 :=
      Nat.pow_le_pow_left (by norm_num) 30
    exact Nat.pow_le_pow_left hbase 3
  have hScaleX : sectionFiveScaleThreshold ≤ X :=
    hScaleThreshold.trans hFinalX
  have hXthree : 3 ≤ X := (le_max_right sectionFiveFinalAbsorptionThreshold 3).trans hX
  obtain ⟨hZ, hXZ, hsieve, hmodLength⟩ :=
    sectionFive_classI_scale_package hScaleX hYX hXY hmodulus hmodcube
  obtain ⟨hZY, hlog, herror⟩ :=
    sectionFive_classI_final_absorption_package hFinalX hXY hmodcube
  have hZX : sectionFiveZ Y ≤ X := hZY.trans hYX
  have hmodX : modulus ≤ X :=
    ShiuEndToEnd.modulus_le_ambient_of_shiuRange
      (by omega : 2 ≤ X) hYX hmodcube
  have hreal := modulus_mul_classIMass_cast_le_logPow
    k X Y modulus residue (sectionFiveZ Y) (smoothCutoff X) hk
    hZ hYX hXZ hZY hZX hmodulus hresidueLt hresidue hsieve
    hmodLength hlog herror hXthree hmodX
  have hlog0 : 0 ≤ Real.log (X : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hlogBridge := realLog_le_natLogTwoSucc (X := X) (show 1 ≤ X by omega)
  have hlogPow : (Real.log (X : ℝ)) ^ (k * k) ≤
      (((Nat.log 2 (X + 2) + 1 : ℕ) : ℝ)) ^ (k * k) :=
    pow_le_pow_left₀ hlog0 hlogBridge (k * k)
  have hKle : K ≤ (C : ℝ) := by
    calc
      K ≤ (⌈K⌉₊ : ℕ) := Nat.le_ceil K
      _ ≤ (C : ℕ) := by dsimp [C]; exact_mod_cast Nat.le_succ _
  have htargetR :
      ((modulus * classIMass k X Y modulus residue
          (sectionFiveZ Y) (smoothCutoff X) : ℕ) : ℝ) ≤
        ((C * Y * (Nat.log 2 (X + 2) + 1) ^ (k * k) : ℕ) : ℝ) := by
    calc
      ((modulus * classIMass k X Y modulus residue
          (sectionFiveZ Y) (smoothCutoff X) : ℕ) : ℝ) ≤
        K * (Y : ℝ) * (Real.log (X : ℝ)) ^ (k * k) := by
          simpa [K, mul_assoc] using hreal
      _ ≤ (C : ℝ) * (Y : ℝ) *
          (((Nat.log 2 (X + 2) + 1 : ℕ) : ℝ)) ^ (k * k) := by
        gcongr
      _ = ((C * Y * (Nat.log 2 (X + 2) + 1) ^ (k * k) : ℕ) : ℝ) := by
        norm_num
  exact_mod_cast htargetR

/-- The floor-square-root sieve level loses at most a factor four in the
logarithm.  This is the precise elementary bridge from the certified natural
Lemma-2 interface back to the manuscript's `log Z` denominator. -/
theorem realLog_le_four_log_classISieveLevel
    {Z : ℕ} (hsieve : 2 ≤ classISieveLevel Z) :
    Real.log (Z : ℝ) ≤
      4 * Real.log (classISieveLevel Z : ℝ) := by
  let s := classISieveLevel Z
  have hs : 2 ≤ s := by simpa [s] using hsieve
  have hsq : s ^ 2 ≤ Z := by
    simpa [s, classISieveLevel, pow_two] using Nat.sqrt_le Z
  have hZpos : (0 : ℝ) < Z := by
    exact_mod_cast (show 0 < Z by nlinarith)
  have hsplus : s + 1 ≤ s ^ 2 := by nlinarith
  have hsuccPow : (s + 1) ^ 2 ≤ s ^ 4 := by
    calc
      (s + 1) ^ 2 ≤ (s ^ 2) ^ 2 := Nat.pow_le_pow_left hsplus 2
      _ = s ^ 4 := by ring
  have hZpowNat : Z ≤ s ^ 4 :=
    (Nat.lt_succ_sqrt Z).le.trans (by
      simpa only [s, classISieveLevel, pow_two] using! hsuccPow)
  have hZpow : (Z : ℝ) ≤ (s : ℝ) ^ 4 := by exact_mod_cast hZpowNat
  calc
    Real.log (Z : ℝ) ≤ Real.log ((s : ℝ) ^ 4) :=
      Real.log_le_log hZpos hZpow
    _ = 4 * Real.log (s : ℝ) := by rw [Real.log_pow]; norm_num
    _ = 4 * Real.log (classISieveLevel Z : ℝ) := by rfl

/-- Literal equation-(5.3) estimate with the manuscript's `log Z`, `Z²`,
and omitted-prime exponential, including its eventual quantifiers. -/
theorem certifiedClassIFiveThreeBound : ClassIFiveThreeBound := by
  intro k hk
  let C : ℝ :=
    8 * (((k * k) ^ 179 : ℕ) : ℝ) * classISelbergConstant *
      Real.exp (4 * (k * k : ℕ))
  have hC : 0 < C := by
    dsimp [C]
    have hkk : 1 ≤ k * k := Nat.mul_le_mul hk hk
    have hpow : 0 < ((k * k) ^ 179 : ℕ) :=
      Nat.zero_lt_one.trans_le (one_le_pow₀ hkk)
    have hpowR : (0 : ℝ) < (((k * k) ^ 179 : ℕ) : ℝ) := by
      exact_mod_cast hpow
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) hpowR) classISelbergConstant_pos)
      (Real.exp_pos _)
  let X₀ : ℕ := max sectionFiveFinalAbsorptionThreshold 3
  refine ⟨C, hC, X₀, by dsimp [X₀]; omega, ?_⟩
  intro X Y modulus residue hX hmodulus hresidueLt hresidue
    hYX hXY hmodcube
  dsimp only
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
  obtain ⟨hZ, hXZ, hsieve, hmodLength⟩ :=
    sectionFive_classI_scale_package hScaleX hYX hXY hmodulus hmodcube
  obtain ⟨hZY, hlogS, herror⟩ :=
    sectionFive_classI_final_absorption_package hFinalX hXY hmodcube
  let Z := sectionFiveZ Y
  let S := classISieveLevel Z
  let P := classIOmittedEulerProduct k Z modulus
  let E := Real.exp
    (ShiuUniformContract.omittedPrimeSum
      ((tauAF k).pmul (tauAF k)) Z modulus)
  have hraw0 := classIMass_cast_le_localEulerProductBracket_fixed
    k X Y modulus residue Z (smoothCutoff X) hk hZ hYX hXZ hZY
      hmodulus hresidueLt hresidue hsieve hmodLength
  have hraw : (classIMass k X Y modulus residue Z (smoothCutoff X) : ℝ) ≤
      (((k * k) ^ 179 : ℕ) : ℝ) * classISelbergConstant *
        (((((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) * Real.log (S : ℝ))) +
          (Z : ℝ) ^ 2) * P) := by
    simpa [Z, S, P, classIOmittedEulerProduct,
      ShiuEndToEnd.eulerInvFactor] using hraw0
  have hphi : (0 : ℝ) < Nat.totient modulus := by
    exact_mod_cast Nat.totient_pos.mpr hmodulus
  have hLS : (0 : ℝ) < Real.log (S : ℝ) := by
    dsimp [S, Z]
    linarith
  have hZfour : Real.log (Z : ℝ) ≤ 4 * Real.log (S : ℝ) := by
    simpa [Z, S] using realLog_le_four_log_classISieveLevel hsieve
  have hZfourNat : 4 ≤ Z := by
    have hsSq : S ^ 2 ≤ Z := by
      simpa [Z, S, classISieveLevel, pow_two] using Nat.sqrt_le Z
    have hfourS : 4 ≤ S ^ 2 := by
      have hs2 : 2 ≤ S := by simpa [S, Z] using hsieve
      nlinarith
    exact hfourS.trans hsSq
  have hLZ : (0 : ℝ) < Real.log (Z : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < Z by omega)
  have hinv : (1 : ℝ) / Real.log (S : ℝ) ≤
      4 / Real.log (Z : ℝ) := by
    apply (div_le_div_iff₀ hLS hLZ).2
    nlinarith
  have hmain :
      ((2 * Y : ℕ) : ℝ) /
          ((Nat.totient modulus : ℝ) * Real.log (S : ℝ)) ≤
        8 * ((Y : ℝ) /
          ((Nat.totient modulus : ℝ) * Real.log (Z : ℝ))) := by
    have hcoef : 0 ≤ ((2 * Y : ℕ) : ℝ) /
        (Nat.totient modulus : ℝ) := by positivity
    calc
      ((2 * Y : ℕ) : ℝ) /
          ((Nat.totient modulus : ℝ) * Real.log (S : ℝ)) =
        (((2 * Y : ℕ) : ℝ) / (Nat.totient modulus : ℝ)) *
          (1 / Real.log (S : ℝ)) := by field_simp
      _ ≤ (((2 * Y : ℕ) : ℝ) / (Nat.totient modulus : ℝ)) *
          (4 / Real.log (Z : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv hcoef
      _ = 8 * ((Y : ℝ) /
          ((Nat.totient modulus : ℝ) * Real.log (Z : ℝ))) := by
        push_cast
        field_simp
        ring
  have hbracket :
      (((2 * Y : ℕ) : ℝ) /
          ((Nat.totient modulus : ℝ) * Real.log (S : ℝ)) + (Z : ℝ) ^ 2) ≤
        8 * ((Y : ℝ) /
            ((Nat.totient modulus : ℝ) * Real.log (Z : ℝ)) +
          (Z : ℝ) ^ 2) := by
    calc
      _ ≤ 8 * ((Y : ℝ) /
            ((Nat.totient modulus : ℝ) * Real.log (Z : ℝ))) +
          8 * (Z : ℝ) ^ 2 := by
        exact add_le_add hmain (by nlinarith [sq_nonneg (Z : ℝ)])
      _ = _ := by ring
  have hEuler0 := ShiuLemma3TauMean.localEulerProduct_le_exp_omittedPrimeSum
    k Z modulus hk
  have hEuler : P ≤ Real.exp (4 * (k * k : ℕ)) * E := by
    simpa [P, E, classIOmittedEulerProduct,
      ShiuEndToEnd.eulerInvFactor] using hEuler0
  have hP0 : 0 ≤ P := classIOmittedEulerProduct_nonneg k Z modulus
  have htargetBracket :
      0 ≤ (Y : ℝ) /
          ((Nat.totient modulus : ℝ) * Real.log (Z : ℝ)) +
        (Z : ℝ) ^ 2 := by positivity
  have hA0 : 0 ≤ (((k * k) ^ 179 : ℕ) : ℝ) * classISelbergConstant :=
    mul_nonneg (by positivity) classISelbergConstant_pos.le
  calc
    (classIMass k X Y modulus residue Z (smoothCutoff X) : ℝ) ≤
      (((k * k) ^ 179 : ℕ) : ℝ) * classISelbergConstant *
        (((((2 * Y : ℕ) : ℝ) /
            ((Nat.totient modulus : ℝ) * Real.log (S : ℝ))) +
          (Z : ℝ) ^ 2) * P) := hraw
    _ ≤ (((k * k) ^ 179 : ℕ) : ℝ) * classISelbergConstant *
        ((8 * ((Y : ℝ) /
            ((Nat.totient modulus : ℝ) * Real.log (Z : ℝ)) +
          (Z : ℝ) ^ 2)) * (Real.exp (4 * (k * k : ℕ)) * E)) := by
      apply mul_le_mul_of_nonneg_left _ hA0
      exact mul_le_mul hbracket hEuler hP0
        (mul_nonneg (by positivity) htargetBracket)
    _ = classIFiveThreeRHS k Y modulus Z C := by
      dsimp [classIFiveThreeRHS, C, E]
      ring

/-- Adapter to the exact end-to-end class-I contract. -/
theorem certifiedClassI53Estimate : ShiuEndToEnd.ClassI53Estimate := by
  intro k hk
  obtain ⟨C, X₀, hC, hX₀, hbound⟩ :=
    certifiedClassIContributionBound k hk
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X Y modulus residue hX hmodulus hresidueLt hresidue
    hYX hXY hmodcube
  have h := hbound X Y modulus residue hX hmodulus hresidueLt
    hresidue hYX hXY hmodcube
  simpa [ShiuEndToEnd.classMass, classIMass,
    ShiuEndToEnd.sectionFiveZ, sectionFiveZ,
    ShiuEndToEnd.smoothCutoff, smoothCutoff,
    ShiuEndToEnd.classBudgetBase, mul_assoc] using h

end

end ShiuClassIBound

#print axioms ShiuClassIBound.certifiedClassIFiveThreeBound
#print axioms ShiuClassIBound.certifiedClassIContributionBound
#print axioms ShiuClassIBound.certifiedClassI53Estimate
