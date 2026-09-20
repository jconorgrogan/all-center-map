import FordMixedLogEndpointMargins
import FordMixedShiftProducts
import FordRiseCoefficient
import FordCompactIncrementScales
import FordScaleFloor
import FordGoodShiftError

noncomputable section
namespace FordCompactGoodShiftMargins

open FordMixedLogEndpointMargins FordMixedKernelBounds FordMixedShiftProducts
open FordRiseCoefficient FordCompactIncrementScales FordScaleFloor FordGoodShiftError
open FordDiscretePairCount

/-- Literal numerical endpoint margins for a good compact shift list. -/
theorem endpoint_margins
    {N H : ℕ} {lam q eps u : ℝ} (hs : List ℕ)
    (hN : 2 ≤ N) (hr : 2 ≤ hs.length)
    (heps : 0 ≤ eps) (heq : eps ≤ q) (hq : q ≤ (3 : ℝ) / 4)
    (hlam : 0 ≤ lam)
    (hexpU : lam + (hs.length : ℝ) * q - (hs.length + 1) = -(1 / 2))
    (hexpL : lam + (hs.length : ℝ) * (q - eps) -
      (hs.length + 1) = -(3 / 4))
    (hgood : ∀ g ∈ hs,
      g ∈ goodShifts (FordScaleFloor.scale N q) ((N : ℝ) ^ (-eps)))
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hH : H ≤ N)
    (hcollar : (hs.length : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4) ≤ (N : ℝ)) :
    1 / ((2 : ℝ) ^ hs.length * 4 ^ (hs.length + 1)) *
        (N : ℝ) ^ (-(3 / 4 : ℝ)) ≤
      (N : ℝ) ^ lam * endpointCoeff
        (hs.map (fun h : ℕ => (h : ℝ))) /
        ((N : ℝ) + u + H + 1 +
          shiftSum (hs.map (fun h : ℕ => (h : ℝ)))) ^ (hs.length + 1) ∧
    (N : ℝ) ^ lam * endpointCoeff
        (hs.map (fun h : ℕ => (h : ℝ))) /
        (N : ℝ) ^ (hs.length + 1) ≤
      (hs.length.factorial : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  let Q : ℕ := FordScaleFloor.scale N q
  let A : ℝ := (N : ℝ) ^ (-eps)
  let L : List ℝ := hs.map (fun h : ℕ => (h : ℝ))
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hq0 : 0 ≤ q := heps.trans heq
  have hNnat : 1 ≤ N := by omega
  have hscale := scale_comparable hNnat hq0
  have hQ1 : 1 ≤ Q := by dsimp [Q]; exact hscale.1
  have hQlo : (N : ℝ) ^ q / 2 ≤ (Q : ℝ) := by dsimp [Q]; exact hscale.2.2
  have hQup : (Q : ℝ) ≤ (N : ℝ) ^ q := by dsimp [Q]; exact hscale.2.1
  have hA0 : 0 ≤ A := by dsimp [A]; exact Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hprod := good_shift_sum_prod_bounds hQ1 hA0 hs (by
    intro g hg
    exact hgood g hg)
  have hsumL : shiftSum L ≤ (hs.length : ℝ) * (Q : ℝ) := by simpa [L] using hprod.1
  have hprodlo : ((Q : ℝ) * A) ^ hs.length ≤ shiftProd L := by simpa [L] using hprod.2.1
  have hprodup : shiftProd L ≤ (Q : ℝ) ^ hs.length := by simpa [L] using hprod.2.2
  have hqpow : (N : ℝ) ^ q ≤ (N : ℝ) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hq
  have hsumN : shiftSum L ≤ (N : ℝ) := by
    have h1 := hsumL
    have h2 : (hs.length : ℝ) * (Q : ℝ) ≤
        (hs.length : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left (hQup.trans hqpow) (by positivity)
    linarith
  have hDlo : (N : ℝ) ≤ (N : ℝ) + u + H + 1 + shiftSum L := by
    have hHr : (0 : ℝ) ≤ H := by positivity
    have hsum0 : 0 ≤ shiftSum L := shiftSum_nonneg (by
      intro z hz
      rcases List.mem_map.mp hz with ⟨g, hg, rfl⟩
      positivity)
    linarith
  have hDhi : (N : ℝ) + u + H + 1 + shiftSum L ≤ 4 * (N : ℝ) := by
    have hHr : (H : ℝ) ≤ (N : ℝ) := by exact_mod_cast hH
    have hN2r : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith [hsumN]
  have hpowlo : (N : ℝ) ^ (hs.length + 1) ≤
      ((N : ℝ) + u + H + 1 + shiftSum L) ^ (hs.length + 1) := by
    exact pow_le_pow_left₀ (by linarith [hDlo]) hDlo _
  have hpowhi : ((N : ℝ) + u + H + 1 + shiftSum L) ^ (hs.length + 1) ≤
      (4 * (N : ℝ)) ^ (hs.length + 1) := by
    exact pow_le_pow_left₀ (by linarith [hDlo]) hDhi _
  have hfac : (1 : ℝ) ≤ (hs.length.factorial : ℝ) := by
    have hfacnat : 1 ≤ hs.length.factorial := by
      have hp : 0 < hs.length.factorial := Nat.factorial_pos _
      omega
    exact_mod_cast hfacnat
  have hprod0 : 0 ≤ shiftProd L := (pow_nonneg (mul_nonneg (by positivity) hA0) _).trans hprodlo
  have hcoefflo : ((Q : ℝ) * A) ^ hs.length ≤ endpointCoeff L := by
    have hm := mul_le_mul hfac hprodlo (pow_nonneg (mul_nonneg (by positivity) hA0) _) (by positivity)
    simpa [endpointCoeff, riseCoeff_one_eq_factorial, L] using hm
  have hcoeffup : endpointCoeff L ≤ (hs.length.factorial : ℝ) * (Q : ℝ) ^ hs.length := by
    have hm := mul_le_mul_of_nonneg_left hprodup (by positivity : (0 : ℝ) ≤ (hs.length.factorial : ℝ))
    simpa [endpointCoeff, riseCoeff_one_eq_factorial, L] using hm
  have hnumlo : (N : ℝ) ^ lam * ((N : ℝ) ^ q / 2 * A) ^ hs.length ≤
      (N : ℝ) ^ lam * endpointCoeff L := by
    have hbase : (N : ℝ) ^ q / 2 * A ≤ (Q : ℝ) * A :=
      mul_le_mul_of_nonneg_right hQlo hA0
    have hp := pow_le_pow_left₀ (by positivity) hbase hs.length
    exact mul_le_mul_of_nonneg_left (hp.trans hcoefflo) (by positivity)
  have hnumup : (N : ℝ) ^ lam * endpointCoeff L ≤
      (hs.length.factorial : ℝ) * ((N : ℝ) ^ lam * ((N : ℝ) ^ q) ^ hs.length) := by
    have hfac0 : 0 ≤ (hs.length.factorial : ℝ) := by positivity
    have hNlam0 : 0 ≤ (N : ℝ) ^ lam := by positivity
    have hp := pow_le_pow_left₀ (by positivity) hQup hs.length
    have hm := mul_le_mul_of_nonneg_left hp hfac0
    have hm' := mul_le_mul_of_nonneg_left hm hNlam0
    calc
      (N : ℝ) ^ lam * endpointCoeff L ≤
          (N : ℝ) ^ lam * ((hs.length.factorial : ℝ) * (Q : ℝ)^hs.length) :=
        mul_le_mul_of_nonneg_left hcoeffup hNlam0
      _ ≤ (hs.length.factorial : ℝ) *
          ((N : ℝ)^lam * ((N : ℝ)^q)^hs.length) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hm'
  have hDpos : 0 < (N : ℝ) + u + H + 1 + shiftSum L := by linarith [hDlo]
  have hDpowpos : 0 < ((N : ℝ) + u + H + 1 + shiftSum L) ^ (hs.length + 1) := by positivity
  have hNpowpos : 0 < (N : ℝ) ^ (hs.length + 1) := by positivity
  have hbigpos : 0 < (4 * (N : ℝ)) ^ (hs.length + 1) := by positivity
  have hlowfrac :
      (N : ℝ) ^ lam * ((N : ℝ) ^ q / 2 * A) ^ hs.length /
        (4 * (N : ℝ)) ^ (hs.length + 1) ≤
      (N : ℝ) ^ lam * endpointCoeff L /
        ((N : ℝ) + u + H + 1 + shiftSum L) ^ (hs.length + 1) := by
    apply (div_le_div_iff₀ hbigpos hDpowpos).2
    have hnumlo0 : 0 ≤ (N : ℝ) ^ lam *
        ((N : ℝ) ^ q / 2 * A) ^ hs.length := by positivity
    have hnum0 : 0 ≤ (N : ℝ) ^ lam * endpointCoeff L :=
      hnumlo0.trans hnumlo
    exact mul_le_mul hnumlo hpowhi (le_of_lt hDpowpos) hnum0
  have hidlo := lower_scale_identity (N := (N : ℝ)) (lam := lam) (q := q)
    (eps := eps) (r := hs.length) hNr hexpL
  have hupperfrac :
      (N : ℝ) ^ lam * endpointCoeff L /
        (N : ℝ) ^ (hs.length + 1) ≤
      (hs.length.factorial : ℝ) *
        ((N : ℝ) ^ lam * ((N : ℝ) ^ q) ^ hs.length) /
          (N : ℝ) ^ (hs.length + 1) := by
    exact div_le_div_of_nonneg_right hnumup hNpowpos.le
  constructor
  · calc
      _ = (N : ℝ) ^ lam * ((N : ℝ) ^ q / 2 * A) ^ hs.length /
          (4 * (N : ℝ)) ^ (hs.length + 1) := by
            rw [hidlo]
      _ ≤ _ := by simpa [L] using hlowfrac
  · calc
      _ ≤ (hs.length.factorial : ℝ) *
          ((N : ℝ) ^ lam * ((N : ℝ) ^ q) ^ hs.length) /
            (N : ℝ) ^ (hs.length + 1) := by simpa [L] using hupperfrac
      _ = _ := by
        calc
          _ = (hs.length.factorial : ℝ) *
              ((N : ℝ) ^ lam * ((N : ℝ) ^ q) ^ hs.length /
                (N : ℝ) ^ (hs.length + 1)) := by ring
          _ = _ := by rw [upper_scale_identity hNr hexpU]

end FordCompactGoodShiftMargins

#print axioms FordCompactGoodShiftMargins.endpoint_margins
