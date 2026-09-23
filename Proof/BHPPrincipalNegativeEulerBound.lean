import RamachandraEulerExpEnvelope
import PrimeFactorSquareRootBound

/-!
# Ambient principal Euler factors just left of the critical strip

On `Re s = -delta` the missing Euler factors are not bounded by two.  The
source-faithful loss is instead

`2 ^ omega(q) * q ^ delta`.

This is still `O(sqrt q)` at the canonical BHP offset
`delta = 1 / (400 log x0)` and `q <= x0`.  Keeping this lemma separate avoids
silently applying the nonnegative-half-plane convention at a negative real
part.
-/

namespace MAPBHPPrincipalNegativeEulerBound

open scoped BigOperators
open Complex
open PrimitiveEulerZeroTransport
open MAPPrimeFactorSquareRootBound

noncomputable section

def trivialEulerCorrection (q : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))

theorem norm_eulerFactor_negative_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p ∈ q.primeFactors) {delta v : ℝ}
    (hdelta : 0 ≤ delta) :
    ‖1 - chi.primitiveCharacter p *
        (p : ℂ) ^ (-(((-delta : ℝ) : ℂ) + v * I))‖ ≤
      2 * (p : ℝ) ^ delta := by
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_le
  have hpow :
      ‖(p : ℂ) ^ (-(((-delta : ℝ) : ℂ) + v * I))‖ =
        (p : ℝ) ^ delta := by
    change ‖((p : ℝ) : ℂ) ^ (-(((-delta : ℝ) : ℂ) + v * I))‖ =
      (p : ℝ) ^ delta
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpPos]
    congr 1
    norm_num
  have hpowOne : 1 ≤ (p : ℝ) ^ delta :=
    Real.one_le_rpow hpOne hdelta
  calc
    ‖1 - chi.primitiveCharacter p *
        (p : ℂ) ^ (-(((-delta : ℝ) : ℂ) + v * I))‖ ≤
        ‖(1 : ℂ)‖ +
          ‖chi.primitiveCharacter p *
            (p : ℂ) ^ (-(((-delta : ℝ) : ℂ) + v * I))‖ :=
      norm_sub_le _ _
    _ = 1 + ‖chi.primitiveCharacter p‖ * (p : ℝ) ^ delta := by
      rw [norm_one, norm_mul, hpow]
    _ ≤ 1 + 1 * (p : ℝ) ^ delta := by
      gcongr
      exact chi.primitiveCharacter.norm_le_one p
    _ ≤ 2 * (p : ℝ) ^ delta := by nlinarith

theorem norm_eulerCorrection_negative_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {delta v : ℝ} (hdelta : 0 ≤ delta) :
    ‖eulerCorrection chi (((-delta : ℝ) : ℂ) + v * I)‖ ≤
      (2 : ℝ) ^ q.primeFactors.card * (q : ℝ) ^ delta := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hprodle : (∏ p ∈ q.primeFactors, p) ≤ q :=
    Nat.le_of_dvd hqpos (Nat.prod_primeFactors_dvd q)
  have hprodleR :
      (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ (q : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast hprodle
  have hprod0 : 0 ≤ ∏ p ∈ q.primeFactors, (p : ℝ) := by positivity
  have hprodRpow :
      (∏ p ∈ q.primeFactors, (p : ℝ) ^ delta) =
        (∏ p ∈ q.primeFactors, (p : ℝ)) ^ delta := by
    simpa only using Real.finsetProd_rpow q.primeFactors
      (fun p => (p : ℝ))
      (fun p hp => Nat.cast_nonneg p) delta
  unfold eulerCorrection
  rw [norm_prod]
  calc
    (∏ p ∈ q.primeFactors,
        ‖1 - chi.primitiveCharacter p *
          (p : ℂ) ^ (-(((-delta : ℝ) : ℂ) + v * I))‖) ≤
      ∏ p ∈ q.primeFactors, (2 * (p : ℝ) ^ delta) := by
        exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun p hp => norm_eulerFactor_negative_le chi hp hdelta)
    _ = (2 : ℝ) ^ q.primeFactors.card *
          (∏ p ∈ q.primeFactors, (p : ℝ)) ^ delta := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, hprodRpow]
    _ ≤ (2 : ℝ) ^ q.primeFactors.card * (q : ℝ) ^ delta := by
      gcongr

theorem norm_eulerCorrection_canonical_le_four_exp_sqrt
    {q : ℕ} [NeZero q] {x0 v : ℝ}
    (hx0 : 1 < x0) (hqx : (q : ℝ) ≤ x0) :
    ‖eulerCorrection (1 : DirichletCharacter ℂ q)
        (((-RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset x0 : ℝ) : ℂ) +
          v * I)‖ ≤
      4 * Real.exp (1 / 400 : ℝ) * Real.sqrt (q : ℝ) := by
  let delta := RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset x0
  have hlog : 0 < Real.log x0 := Real.log_pos hx0
  have hdelta : 0 ≤ delta := by
    dsimp [delta, RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset]
    positivity
  have hbaseq : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hlogq : Real.log (q : ℝ) ≤ Real.log x0 :=
    Real.log_le_log hbaseq hqx
  have hpow : (q : ℝ) ^ delta ≤ Real.exp (1 / 400 : ℝ) := by
    rw [Real.rpow_def_of_pos hbaseq]
    apply Real.exp_le_exp.mpr
    dsimp [delta, RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset]
    have hden : 0 < 400 * Real.log x0 := by positivity
    rw [div_eq_mul_inv]
    calc
      Real.log (q : ℝ) * (400 * Real.log x0)⁻¹ ≤
          Real.log x0 * (400 * Real.log x0)⁻¹ := by
        exact mul_le_mul_of_nonneg_right hlogq (inv_nonneg.mpr hden.le)
      _ = 1 / 400 := by field_simp
  have hbase := norm_eulerCorrection_negative_le
    (1 : DirichletCharacter ℂ q) (v := v) hdelta
  have htwo := two_pow_card_primeFactors_le_four_sqrt q (NeZero.ne q)
  calc
    ‖eulerCorrection (1 : DirichletCharacter ℂ q)
        (((-delta : ℝ) : ℂ) + v * I)‖ ≤
      (2 : ℝ) ^ q.primeFactors.card * (q : ℝ) ^ delta := hbase
    _ ≤ (4 * Real.sqrt (q : ℝ)) * Real.exp (1 / 400 : ℝ) :=
      mul_le_mul htwo hpow (Real.rpow_nonneg hbaseq.le _)
        (by positivity)
    _ = 4 * Real.exp (1 / 400 : ℝ) * Real.sqrt (q : ℝ) := by ring

theorem norm_trivialEulerCorrection_negative_le
    {q : ℕ} [NeZero q] {delta v : ℝ} (hdelta : 0 ≤ delta) :
    ‖trivialEulerCorrection q (((-delta : ℝ) : ℂ) + v * I)‖ ≤
      (2 : ℝ) ^ q.primeFactors.card * (q : ℝ) ^ delta := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hprodle : (∏ p ∈ q.primeFactors, p) ≤ q :=
    Nat.le_of_dvd hqpos (Nat.prod_primeFactors_dvd q)
  have hprodleR :
      (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ (q : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast hprodle
  have hprod0 : 0 ≤ ∏ p ∈ q.primeFactors, (p : ℝ) := by positivity
  have hprodRpow :
      (∏ p ∈ q.primeFactors, (p : ℝ) ^ delta) =
        (∏ p ∈ q.primeFactors, (p : ℝ)) ^ delta := by
    simpa only using Real.finsetProd_rpow q.primeFactors
      (fun p => (p : ℝ)) (fun p hp => Nat.cast_nonneg p) delta
  unfold trivialEulerCorrection
  rw [norm_prod]
  calc
    (∏ p ∈ q.primeFactors,
        ‖1 - (p : ℂ) ^ (-(((-delta : ℝ) : ℂ) + v * I))‖) ≤
      ∏ p ∈ q.primeFactors, (2 * (p : ℝ) ^ delta) := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro p hp
        have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
        have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_le
        have hpow :
            ‖(p : ℂ) ^ (-(((-delta : ℝ) : ℂ) + v * I))‖ =
              (p : ℝ) ^ delta := by
          change ‖((p : ℝ) : ℂ) ^ (-(((-delta : ℝ) : ℂ) + v * I))‖ =
            (p : ℝ) ^ delta
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hpPos]
          congr 1
          norm_num
        have hone : 1 ≤ (p : ℝ) ^ delta := Real.one_le_rpow hpOne hdelta
        calc
          ‖1 - (p : ℂ) ^ (-(((-delta : ℝ) : ℂ) + v * I))‖ ≤
              ‖(1 : ℂ)‖ +
                ‖(p : ℂ) ^ (-(((-delta : ℝ) : ℂ) + v * I))‖ :=
            norm_sub_le (1 : ℂ)
              ((p : ℂ) ^ (-(((-delta : ℝ) : ℂ) + v * I)))
          _ = 1 + (p : ℝ) ^ delta := by rw [norm_one, hpow]
          _ ≤ 2 * (p : ℝ) ^ delta := by nlinarith
    _ = (2 : ℝ) ^ q.primeFactors.card *
          (∏ p ∈ q.primeFactors, (p : ℝ)) ^ delta := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, hprodRpow]
    _ ≤ (2 : ℝ) ^ q.primeFactors.card * (q : ℝ) ^ delta := by
      gcongr

theorem norm_trivialEulerCorrection_canonical_le_four_exp_sqrt
    {q : ℕ} [NeZero q] {x0 v : ℝ}
    (hx0 : 1 < x0) (hqx : (q : ℝ) ≤ x0) :
    ‖trivialEulerCorrection q
        (((-RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset x0 : ℝ) : ℂ) +
          v * I)‖ ≤
      4 * Real.exp (1 / 400 : ℝ) * Real.sqrt (q : ℝ) := by
  let delta := RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset x0
  have hlog : 0 < Real.log x0 := Real.log_pos hx0
  have hdelta : 0 ≤ delta := by
    dsimp [delta, RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset]
    positivity
  have hbaseq : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hlogq : Real.log (q : ℝ) ≤ Real.log x0 :=
    Real.log_le_log hbaseq hqx
  have hpow : (q : ℝ) ^ delta ≤ Real.exp (1 / 400 : ℝ) := by
    rw [Real.rpow_def_of_pos hbaseq]
    apply Real.exp_le_exp.mpr
    dsimp [delta, RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset]
    have hden : 0 < 400 * Real.log x0 := by positivity
    rw [div_eq_mul_inv]
    calc
      Real.log (q : ℝ) * (400 * Real.log x0)⁻¹ ≤
          Real.log x0 * (400 * Real.log x0)⁻¹ := by
        exact mul_le_mul_of_nonneg_right hlogq (inv_nonneg.mpr hden.le)
      _ = 1 / 400 := by field_simp
  have hbase := norm_trivialEulerCorrection_negative_le
    (q := q) (v := v) hdelta
  have htwo := two_pow_card_primeFactors_le_four_sqrt q (NeZero.ne q)
  calc
    ‖trivialEulerCorrection q (((-delta : ℝ) : ℂ) + v * I)‖ ≤
      (2 : ℝ) ^ q.primeFactors.card * (q : ℝ) ^ delta := hbase
    _ ≤ (4 * Real.sqrt (q : ℝ)) * Real.exp (1 / 400 : ℝ) :=
      mul_le_mul htwo hpow (Real.rpow_nonneg hbaseq.le _) (by positivity)
    _ = 4 * Real.exp (1 / 400 : ℝ) * Real.sqrt (q : ℝ) := by ring

end
end MAPBHPPrincipalNegativeEulerBound

#print axioms MAPBHPPrincipalNegativeEulerBound.norm_eulerCorrection_negative_le
#print axioms MAPBHPPrincipalNegativeEulerBound.norm_eulerCorrection_canonical_le_four_exp_sqrt
#print axioms MAPBHPPrincipalNegativeEulerBound.norm_trivialEulerCorrection_negative_le
#print axioms MAPBHPPrincipalNegativeEulerBound.norm_trivialEulerCorrection_canonical_le_four_exp_sqrt
