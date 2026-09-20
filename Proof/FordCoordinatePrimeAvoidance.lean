import FordVandermondeSize
import Mathlib.Data.ZMod.Basic
import FordFiniteBadPrimeAvoidance

open scoped BigOperators
noncomputable section
namespace MAPFordCoordinatePrimeAvoidance
open MAPFordVandermondeSize MAPFordFiniteBadPrimeAvoidance

/-- One common finite prime family avoids the scalar and both coordinate
Vandermonde factors simultaneously.  The size input is the literal
`T*Vandermonde(z)*Vandermonde(w)` bound; no point-dependent prime pool is
introduced. -/
theorem exists_common_coordinate_prime
    {S : Finset ℕ}
    (hprime : ∀ p ∈ S, p.Prime)
    {n P d : ℕ} {T : ℤ}
    (hT : T ≠ 0) (hTsize : T.natAbs ≤ P ^ d)
    (z w : Fin n → Fin (P + 1))
    (hz : Function.Injective z) (hw : Function.Injective w)
    (hprod : P ^ (d + n * (n - 1)) < ∏ p ∈ S, p) :
    ∃ p ∈ S,
      (T : ZMod p) ≠ 0 ∧
      Function.Injective (fun i : Fin n => ((z i).val : ZMod p)) ∧
      Function.Injective (fun i : Fin n => ((w i).val : ZMod p)) := by
  let Vz : ℤ := (Matrix.vandermonde (fun i => ((z i).val : ℤ))).det
  let Vw : ℤ := (Matrix.vandermonde (fun i => ((w i).val : ℤ))).det
  let N : ℤ := T * Vz * Vw
  have hzi : Function.Injective (fun i : Fin n => ((z i).val : ℤ)) := by
    intro i j hij
    apply hz
    apply Fin.ext
    change ((z i).val : ℤ) = ((z j).val : ℤ) at hij
    exact_mod_cast hij
  have hwi : Function.Injective (fun i : Fin n => ((w i).val : ℤ)) := by
    intro i j hij
    apply hw
    apply Fin.ext
    change ((w i).val : ℤ) = ((w j).val : ℤ) at hij
    exact_mod_cast hij
  have hVz : Vz ≠ 0 := by
    dsimp [Vz]
    exact (Matrix.det_vandermonde_ne_zero_iff).mpr hzi
  have hVw : Vw ≠ 0 := by
    dsimp [Vw]
    exact (Matrix.det_vandermonde_ne_zero_iff).mpr hwi
  have hN : N ≠ 0 := by
    dsimp [N]
    exact mul_ne_zero (mul_ne_zero hT hVz) hVw
  have hNsize : N.natAbs ≤ P ^ (d + n * (n - 1)) := by
    dsimp [N, Vz, Vw]
    exact bad_product_natAbs_le T hTsize z w
  have hNprod : N.natAbs < ∏ p ∈ S, p := hNsize.trans_lt hprod
  obtain ⟨p, hpS, hpfull⟩ :=
    exists_prime_not_dvd_natAbs_of_prod_gt hN S hprime hNprod
  have hexpand : N.natAbs = T.natAbs * Vz.natAbs * Vw.natAbs := by
    dsimp [N]
    rw [Int.natAbs_mul, Int.natAbs_mul]
  have hTfactor : T.natAbs ∣ N.natAbs := by
    rw [hexpand]
    exact ⟨Vz.natAbs * Vw.natAbs, by ring⟩
  have hVzfactor : Vz.natAbs ∣ N.natAbs := by
    rw [hexpand]
    exact ⟨T.natAbs * Vw.natAbs, by ring⟩
  have hVwfactor : Vw.natAbs ∣ N.natAbs := by
    rw [hexpand]
    exact ⟨T.natAbs * Vz.natAbs, by ring⟩
  have hpT : ¬ p ∣ T.natAbs := by
    intro hd
    exact hpfull (hd.trans hTfactor)
  have hpVz : ¬ p ∣ Vz.natAbs := by
    intro hd
    exact hpfull (hd.trans hVzfactor)
  have hpVw : ¬ p ∣ Vw.natAbs := by
    intro hd
    exact hpfull (hd.trans hVwfactor)
  letI : Fact p.Prime := ⟨hprime p hpS⟩
  have hTz : (T : ZMod p) ≠ 0 := by
    intro hzero
    have hd : (p : ℤ) ∣ T :=
      (CharP.intCast_eq_zero_iff (ZMod p) p T).mp hzero
    exact hpT ((Int.natCast_dvd).mp hd)
  have hVzcast : (Vz : ZMod p) ≠ 0 := by
    intro hzero
    have hd : (p : ℤ) ∣ Vz :=
      (CharP.intCast_eq_zero_iff (ZMod p) p Vz).mp hzero
    exact hpVz ((Int.natCast_dvd).mp hd)
  have hVwcast : (Vw : ZMod p) ≠ 0 := by
    intro hzero
    have hd : (p : ℤ) ∣ Vw :=
      (CharP.intCast_eq_zero_iff (ZMod p) p Vw).mp hzero
    exact hpVw ((Int.natCast_dvd).mp hd)
  have hdetz : (Matrix.vandermonde
      (fun i : Fin n => ((z i).val : ZMod p))).det ≠ 0 := by
    simpa [Vz, Matrix.det_vandermonde] using hVzcast
  have hdetw : (Matrix.vandermonde
      (fun i : Fin n => ((w i).val : ZMod p))).det ≠ 0 := by
    simpa [Vw, Matrix.det_vandermonde] using hVwcast
  refine ⟨p, hpS, hTz, ?_, ?_⟩
  · exact (Matrix.det_vandermonde_ne_zero_iff).mp hdetz
  · exact (Matrix.det_vandermonde_ne_zero_iff).mp hdetw

end MAPFordCoordinatePrimeAvoidance

#print axioms MAPFordCoordinatePrimeAvoidance.exists_common_coordinate_prime
