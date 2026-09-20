import KhaleAppendixBFirstPartExactHeightRepair

/-!
# Applicability of Khale Lemma 4.1 at the Appendix-B parameters

This module certifies the numerical collar which precedes the four literal
applications of Lemma 4.1.  It is deterministic exponent bookkeeping, not an
analytic zero estimate.
-/

namespace MAPKhaleAppendixBLemma41Applicability

open MAPKhaleAppendixBSource MAPKhaleAppendixBEtaAlgebra
open MAPKhaleAppendixBNumericalCore
open MAPKhaleAppendixB1FirstPartReduction

noncomputable section

/-- A convenient explicit lower bound for the source mollification width.
The constant has ample room relative to the final `1.92` collar. -/
theorem khaleEta_lower_196
    {B gamma : ℝ} (hB : 0 < B) (hBtop : B ≤ 4.45)
    (hL : 0 < Real.log gamma)
    (hell : 0 < Real.log (Real.log gamma))
    (hell924 : (9.24 : ℝ) ≤ Real.log (Real.log gamma)) :
    1.96 * Real.rpow (Real.log gamma) (-2 / 3 : ℝ) ≤
      khaleEta B gamma := by
  let L : ℝ := Real.log gamma
  let ell : ℝ := Real.log (Real.log gamma)
  let base : ℝ := ((4 / 3 : ℝ) / B) * (ell / L)
  have hL' : 0 < L := by simpa only [L] using hL
  have hell' : 0 < ell := by simpa only [ell] using hell
  have hbase : 0 < base := by
    dsimp only [base]
    positivity
  have heta0 : 0 ≤ khaleEta B gamma := by
    exact (khaleEta_pos hB hL hell).le
  have hlhs0 : 0 ≤ 1.96 * Real.rpow L (-2 / 3 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hL'.le _)
  apply (pow_le_pow_iff_left₀ hlhs0 heta0
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  have hetaCube : (khaleEta B gamma) ^ (3 : ℕ) = base ^ (2 : ℕ) := by
    have hpow := Real.rpow_mul_natCast hbase.le (2 / 3 : ℝ) 3
    norm_num at hpow
    simpa only [khaleEta, base, L, ell] using hpow.symm
  have hLCube :
      (Real.rpow L (-2 / 3 : ℝ)) ^ (3 : ℕ) =
        Real.rpow L (-2 : ℝ) := by
    have hpow := Real.rpow_mul_natCast hL'.le (-2 / 3 : ℝ) 3
    calc
      (Real.rpow L (-2 / 3 : ℝ)) ^ (3 : ℕ) =
          Real.rpow L ((-2 / 3 : ℝ) * (3 : ℝ)) := hpow.symm
      _ = Real.rpow L (-2 : ℝ) := by congr 1 <;> norm_num
  rw [hetaCube]
  rw [mul_pow, hLCube]
  have hLpow : Real.rpow L (-2 : ℝ) = 1 / L ^ (2 : ℕ) := by
    calc
      Real.rpow L (-2 : ℝ) = (Real.rpow L (2 : ℝ))⁻¹ := by
        simpa only using Real.rpow_neg hL'.le 2
      _ = (L ^ (2 : ℕ))⁻¹ := by
        congr 1
        exact Real.rpow_natCast L 2
      _ = 1 / L ^ (2 : ℕ) := by rw [one_div]
  rw [hLpow]
  have hBsq : B ^ (2 : ℕ) ≤ (4.45 : ℝ) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg B, sq_nonneg (4.45 - B)]
  have hellsq : (9.24 : ℝ) ^ (2 : ℕ) ≤ ell ^ (2 : ℕ) := by
    have h : (9.24 : ℝ) ≤ ell := by simpa only [ell] using hell924
    nlinarith [sq_nonneg (ell - 9.24)]
  have hbaseSq : base ^ (2 : ℕ) =
      (((4 / 3 : ℝ) ^ (2 : ℕ) * ell ^ (2 : ℕ)) /
        (B ^ (2 : ℕ) * L ^ (2 : ℕ))) := by
    dsimp only [base]
    field_simp [hB.ne', hL'.ne']
  rw [hbaseSq]
  have hlhsDiv :
      (1.96 : ℝ) ^ (3 : ℕ) * (1 / L ^ (2 : ℕ)) =
        (1.96 : ℝ) ^ (3 : ℕ) / L ^ (2 : ℕ) := by ring
  rw [hlhsDiv]
  have hrhsDiv :
      ((4 / 3 : ℝ) ^ (2 : ℕ) * ell ^ (2 : ℕ)) /
          (B ^ (2 : ℕ) * L ^ (2 : ℕ)) =
        (((4 / 3 : ℝ) ^ (2 : ℕ) * ell ^ (2 : ℕ)) /
          B ^ (2 : ℕ)) / L ^ (2 : ℕ) := by
    field_simp [hB.ne', hL'.ne']
  rw [hrhsDiv]
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < L ^ (2 : ℕ))).2
  apply (le_div_iff₀ (by positivity : 0 < B ^ (2 : ℕ))).2
  nlinarith

/-- The zero-gap hypothesis makes the distance from the zero to the auxiliary
line less than three thousandths of the source width. -/
theorem appendixB_delta_div_eta_le_0029
    {A B T₀ gamma beta : ℝ} {q : ℕ}
    (hB : 0 < B) (hL : 0 < Real.log gamma)
    (hell : 0 < Real.log (Real.log gamma))
    (hell924 : (9.24 : ℝ) ≤ Real.log (Real.log gamma))
    (hq : 3 ≤ q)
    (hgap : 1 - beta ≤ 1 /
      (18 * Real.log q + appendixBHeightCoefficient A T₀ *
        Real.rpow B (2 / 3 : ℝ) *
        Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
        Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ))) :
    (1 - beta) / khaleEta B gamma ≤ 0.0029 := by
  let L : ℝ := Real.log gamma
  let ell : ℝ := Real.log (Real.log gamma)
  let BP : ℝ := Real.rpow B (2 / 3 : ℝ)
  let R : ℝ := Real.rpow (L / ell) (2 / 3 : ℝ)
  let M : ℝ := BP * R
  let P : ℝ := BP * Real.rpow L (2 / 3 : ℝ) *
    Real.rpow ell (1 / 3 : ℝ)
  have hL' : 0 < L := by simpa only [L] using hL
  have hell' : 0 < ell := by simpa only [ell] using hell
  have hM : 0 < M := by dsimp [M, BP, R]; positivity
  have hP : 0 < P := by dsimp [P, BP]; positivity
  have hMell : M * ell = P := by
    have hr := ratio_two_thirds_mul_loglog hL hell
    have hr' : R * ell = Real.rpow L (2 / 3 : ℝ) *
        Real.rpow ell (1 / 3 : ℝ) := by
      simpa only [R, L, ell] using hr
    dsimp only [M, P]
    rw [mul_assoc, hr']
    ring
  have hinvEta : 1 / khaleEta B gamma = sourceScale * M := by
    simpa only [khaleInvEtaScale, M, BP, R, L, ell, mul_assoc] using
      one_div_khaleEta hB hL hell
  have hcoeff : (31.76 : ℝ) ≤ appendixBHeightCoefficient A T₀ := by
    unfold appendixBHeightCoefficient
    linarith [le_max_right (sSup (appendixBCorrection A '' Set.Ici T₀)) 0]
  have hqReal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 3).trans hqReal)
  have hden : 31.76 * P ≤
      18 * Real.log q + appendixBHeightCoefficient A T₀ * P := by
    have hc := mul_le_mul_of_nonneg_right hcoeff hP.le
    nlinarith
  have hgapP : 1 - beta ≤ 1 / (31.76 * P) := by
    have hbase : 0 < 31.76 * P := mul_pos (by norm_num) hP
    have hinv := one_div_le_one_div_of_le hbase hden
    have hg : 1 - beta ≤
        1 / (18 * Real.log q + appendixBHeightCoefficient A T₀ * P) := by
      simpa only [P, BP, L, ell, mul_assoc] using hgap
    exact hg.trans hinv
  have hk0 : 0 ≤ sourceScale := Real.rpow_nonneg (by norm_num) _
  have hscaled := mul_le_mul_of_nonneg_right hgapP
    (mul_nonneg hk0 hM.le)
  have hdeltaEta :
      (1 - beta) / khaleEta B gamma ≤ sourceScale / (31.76 * ell) := by
    have hinvEta' : (khaleEta B gamma)⁻¹ = sourceScale * M := by
      simpa only [one_div] using hinvEta
    rw [div_eq_mul_inv, hinvEta']
    calc
      (1 - beta) * (sourceScale * M) ≤
          (1 / (31.76 * P)) * (sourceScale * M) := hscaled
      _ = sourceScale / (31.76 * ell) := by
        rw [← hMell]
        field_simp [hM.ne', hell'.ne']
  have hk := sourceScale_upper
  have hell924' : (9.24 : ℝ) ≤ ell := by
    simpa only [ell] using hell924
  have hnum : sourceScale / (31.76 * ell) ≤ 0.0029 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hell')).2
    nlinarith
  exact hdeltaEta.trans hnum

/-- At height at least `exp 10650`, replacing `log gamma` by
`log (gamma/100)` costs less than the `1.96 - 1.92` reserve. -/
theorem collar_rpow_192_le_194
    {gamma : ℝ} (hgamma : Real.exp 10650 ≤ gamma) :
    1.92 * Real.rpow (Real.log (gamma / 100)) (-2 / 3 : ℝ) ≤
      1.94 * Real.rpow (Real.log gamma) (-2 / 3 : ℝ) := by
  let L : ℝ := Real.log gamma
  let d : ℝ := Real.log (gamma / 100)
  have hgamma0 : 0 < gamma := (Real.exp_pos _).trans_le hgamma
  have hLlower : (10650 : ℝ) ≤ L := by
    dsimp only [L]
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos _) hgamma
  have hL : 0 < L := by linarith
  have hlog100 : Real.log (100 : ℝ) < 99 := by
    have := Real.log_lt_sub_one_of_pos (x := (100 : ℝ)) (by norm_num) (by norm_num)
    norm_num at this ⊢
    exact this
  have hdEq : d = L - Real.log 100 := by
    dsimp only [d, L]
    rw [Real.log_div hgamma0.ne' (by norm_num : (100 : ℝ) ≠ 0)]
  have hdLower : 0.99 * L ≤ d := by
    rw [hdEq]
    nlinarith
  have hd : 0 < d := (mul_pos (by norm_num) hL).trans_le hdLower
  have hlhs0 : 0 ≤ 1.92 * Real.rpow d (-2 / 3 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hd.le _)
  have hrhs0 : 0 ≤ 1.94 * Real.rpow L (-2 / 3 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hL.le _)
  apply (pow_le_pow_iff_left₀ hlhs0 hrhs0
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  have hdCube : (Real.rpow d (-2 / 3 : ℝ)) ^ (3 : ℕ) =
      1 / d ^ (2 : ℕ) := by
    calc
      (Real.rpow d (-2 / 3 : ℝ)) ^ (3 : ℕ) =
          Real.rpow d ((-2 / 3 : ℝ) * (3 : ℝ)) :=
            (Real.rpow_mul_natCast hd.le (-2 / 3 : ℝ) 3).symm
      _ = Real.rpow d (-2 : ℝ) := by congr 1 <;> norm_num
      _ = (Real.rpow d (2 : ℝ))⁻¹ := by
        simpa only using Real.rpow_neg hd.le 2
      _ = (d ^ (2 : ℕ))⁻¹ := by congr 1; exact Real.rpow_natCast d 2
      _ = 1 / d ^ (2 : ℕ) := by rw [one_div]
  have hLCube : (Real.rpow L (-2 / 3 : ℝ)) ^ (3 : ℕ) =
      1 / L ^ (2 : ℕ) := by
    calc
      (Real.rpow L (-2 / 3 : ℝ)) ^ (3 : ℕ) =
          Real.rpow L ((-2 / 3 : ℝ) * (3 : ℝ)) :=
            (Real.rpow_mul_natCast hL.le (-2 / 3 : ℝ) 3).symm
      _ = Real.rpow L (-2 : ℝ) := by congr 1 <;> norm_num
      _ = (Real.rpow L (2 : ℝ))⁻¹ := by
        simpa only using Real.rpow_neg hL.le 2
      _ = (L ^ (2 : ℕ))⁻¹ := by congr 1; exact Real.rpow_natCast L 2
      _ = 1 / L ^ (2 : ℕ) := by rw [one_div]
  rw [mul_pow, mul_pow, hdCube, hLCube]
  have hdSq : (0.99 : ℝ) ^ (2 : ℕ) * L ^ (2 : ℕ) ≤
      d ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (d - 0.99 * L)]
  rw [show (1.92 : ℝ) ^ (3 : ℕ) * (1 / d ^ (2 : ℕ)) =
      (1.92 : ℝ) ^ (3 : ℕ) / d ^ (2 : ℕ) by ring,
    show (1.94 : ℝ) ^ (3 : ℕ) * (1 / L ^ (2 : ℕ)) =
      (1.94 : ℝ) ^ (3 : ℕ) / L ^ (2 : ℕ) by ring]
  rw [div_le_div_iff₀ (by positivity : 0 < d ^ (2 : ℕ))
    (by positivity : 0 < L ^ (2 : ℕ))]
  nlinarith

/-- Increasing the ordinate from `gamma` to `j*gamma`, for `j ≥ 1`, only
shrinks the negative-power collar in Lemma 4.1. -/
theorem collar_rpow_mul_le_base
    {gamma j : ℝ} (hgamma : Real.exp 10650 ≤ gamma) (hj : 1 ≤ j) :
    Real.rpow (Real.log ((j * gamma) / 100)) (-2 / 3 : ℝ) ≤
      Real.rpow (Real.log (gamma / 100)) (-2 / 3 : ℝ) := by
  have hgamma0 : 0 < gamma := (Real.exp_pos _).trans_le hgamma
  have hj0 : 0 < j := zero_lt_one.trans_le hj
  have hL : (10650 : ℝ) ≤ Real.log gamma := by
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos _) hgamma
  have hlog100 : Real.log (100 : ℝ) < 99 := by
    have := Real.log_lt_sub_one_of_pos (x := (100 : ℝ)) (by norm_num) (by norm_num)
    norm_num at this ⊢
    exact this
  have hbase : 0 < Real.log (gamma / 100) := by
    rw [Real.log_div hgamma0.ne' (by norm_num : (100 : ℝ) ≠ 0)]
    linarith
  have hratio : gamma / 100 ≤ (j * gamma) / 100 := by
    apply div_le_div_of_nonneg_right
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right hj hgamma0.le
    · norm_num
  have hlog : Real.log (gamma / 100) ≤
      Real.log ((j * gamma) / 100) :=
    Real.log_le_log (div_pos hgamma0 (by norm_num)) hratio
  exact Real.rpow_le_rpow_of_exponent_nonpos hbase hlog (by norm_num)

/-- The exact Appendix-B auxiliary line satisfies the full `1.92` collar
required by Khale Lemma 4.1. -/
theorem appendixB_sigmaAux_collar
    {A B T₀ gamma beta : ℝ} {q : ℕ}
    (hB : 0 < B) (hBtop : B ≤ 4.45)
    (hgamma : Real.exp 10650 ≤ gamma)
    (hell924 : (9.24 : ℝ) ≤ Real.log (Real.log gamma))
    (hq : 3 ≤ q)
    (hgap : 1 - beta ≤ 1 /
      (18 * Real.log q + appendixBHeightCoefficient A T₀ *
        Real.rpow B (2 / 3 : ℝ) *
        Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
        Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ))) :
    1 + 3.238 * (1 - beta) ≤
      1 + khaleEta B gamma -
        1.92 * Real.rpow (Real.log (gamma / 100)) (-2 / 3 : ℝ) := by
  have hLlower : (10650 : ℝ) ≤ Real.log gamma := by
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos _) hgamma
  have hL : 0 < Real.log gamma := by linarith
  have hell : 0 < Real.log (Real.log gamma) := by linarith
  have heta := khaleEta_pos hB hL hell
  have hetaLower := khaleEta_lower_196 hB hBtop hL hell hell924
  have hratio := appendixB_delta_div_eta_le_0029
    hB hL hell hell924 hq hgap
  have hdelta : 1 - beta ≤ 0.0029 * khaleEta B gamma := by
    have := (div_le_iff₀ heta).mp hratio
    simpa [div_eq_mul_inv] using this
  have hcollarScale :
      1.94 * Real.rpow (Real.log gamma) (-2 / 3 : ℝ) ≤
        0.99 * khaleEta B gamma := by
    have hmul := mul_le_mul_of_nonneg_left hetaLower
      (by norm_num : (0 : ℝ) ≤ 0.99)
    nlinarith
  have hheight := collar_rpow_192_le_194 hgamma
  nlinarith

end
end MAPKhaleAppendixBLemma41Applicability

#print axioms MAPKhaleAppendixBLemma41Applicability.khaleEta_lower_196
#print axioms MAPKhaleAppendixBLemma41Applicability.appendixB_delta_div_eta_le_0029
#print axioms MAPKhaleAppendixBLemma41Applicability.collar_rpow_192_le_194
#print axioms MAPKhaleAppendixBLemma41Applicability.collar_rpow_mul_le_base
#print axioms MAPKhaleAppendixBLemma41Applicability.appendixB_sigmaAux_collar
