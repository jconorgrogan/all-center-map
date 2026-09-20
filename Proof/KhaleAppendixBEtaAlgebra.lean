import KhaleAppendixBNumericalCore
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Exact algebra of Khale's Appendix-B scale eta
-/

namespace MAPKhaleAppendixBEtaAlgebra

open MAPKhaleAppendixBNumericalCore

noncomputable section

def khaleEta (B gamma : ℝ) : ℝ :=
  Real.rpow (((4 / 3 : ℝ) / B) *
    (Real.log (Real.log gamma) / Real.log gamma)) (2 / 3 : ℝ)

def khaleInvEtaScale (B gamma : ℝ) : ℝ :=
  sourceScale * Real.rpow B (2 / 3 : ℝ) *
    Real.rpow (Real.log gamma / Real.log (Real.log gamma)) (2 / 3 : ℝ)

private theorem etaBase_pos
    {B gamma : ℝ} (hB : 0 < B) (hL : 0 < Real.log gamma)
    (hell : 0 < Real.log (Real.log gamma)) :
    0 < ((4 / 3 : ℝ) / B) *
      (Real.log (Real.log gamma) / Real.log gamma) := by
  positivity

theorem khaleEta_pos
    {B gamma : ℝ} (hB : 0 < B) (hL : 0 < Real.log gamma)
    (hell : 0 < Real.log (Real.log gamma)) :
    0 < khaleEta B gamma := by
  exact Real.rpow_pos_of_pos (etaBase_pos hB hL hell) _

private theorem invScale_pos
    {B gamma : ℝ} (hB : 0 < B) (hL : 0 < Real.log gamma)
    (hell : 0 < Real.log (Real.log gamma)) :
    0 < khaleInvEtaScale B gamma := by
  unfold khaleInvEtaScale sourceScale
  exact mul_pos
    (mul_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4 / 3) _)
      (Real.rpow_pos_of_pos hB _))
    (Real.rpow_pos_of_pos (div_pos hL hell) _)

/-- Exact reciprocal form used in the numerical decomposition. -/
theorem one_div_khaleEta
    {B gamma : ℝ} (hB : 0 < B) (hL : 0 < Real.log gamma)
    (hell : 0 < Real.log (Real.log gamma)) :
    1 / khaleEta B gamma = khaleInvEtaScale B gamma := by
  have hbase := etaBase_pos hB hL hell
  have heta := khaleEta_pos hB hL hell
  have hinv := invScale_pos hB hL hell
  apply Real.log_injOn_pos (by exact div_pos (by norm_num) heta) hinv
  let base : ℝ := ((4 / 3 : ℝ) / B) *
    (Real.log (Real.log gamma) / Real.log gamma)
  let k : ℝ := Real.rpow (4 / 3 : ℝ) (-2 / 3 : ℝ)
  let bp : ℝ := Real.rpow B (2 / 3 : ℝ)
  let rp : ℝ := Real.rpow
    (Real.log gamma / Real.log (Real.log gamma)) (2 / 3 : ℝ)
  have hbase' : 0 < base := hbase
  have hk : 0 < k := Real.rpow_pos_of_pos (by norm_num) _
  have hbp : 0 < bp := Real.rpow_pos_of_pos hB _
  have hrp : 0 < rp := Real.rpow_pos_of_pos (div_pos hL hell) _
  have hlhs : Real.log (1 / Real.rpow base (2 / 3 : ℝ)) =
      -(2 / 3 : ℝ) * Real.log base := by
    have hldiv : Real.log (1 / Real.rpow base (2 / 3 : ℝ)) =
        Real.log 1 - Real.log (Real.rpow base (2 / 3 : ℝ)) :=
      Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
        (Real.rpow_pos_of_pos hbase' _).ne'
    rw [hldiv, Real.log_one,
      show Real.log (Real.rpow base (2 / 3 : ℝ)) =
        (2 / 3 : ℝ) * Real.log base from Real.log_rpow hbase' _]
    ring
  have hrhs : Real.log (k * bp * rp) =
      (-2 / 3 : ℝ) * Real.log (4 / 3 : ℝ) +
        (2 / 3 : ℝ) * Real.log B +
        (2 / 3 : ℝ) * Real.log
          (Real.log gamma / Real.log (Real.log gamma)) := by
    rw [Real.log_mul (mul_pos hk hbp).ne' hrp.ne',
      Real.log_mul hk.ne' hbp.ne',
      show Real.log k = (-2 / 3 : ℝ) * Real.log (4 / 3 : ℝ) from
        Real.log_rpow (by norm_num) _,
      show Real.log bp = (2 / 3 : ℝ) * Real.log B from
        Real.log_rpow hB _,
      show Real.log rp = (2 / 3 : ℝ) *
          Real.log (Real.log gamma / Real.log (Real.log gamma)) from
        Real.log_rpow (div_pos hL hell) _]
  change Real.log (1 / Real.rpow base (2 / 3 : ℝ)) =
    Real.log (k * bp * rp)
  rw [hlhs, hrhs]
  dsimp [base]
  rw [Real.log_mul (div_pos (by norm_num) hB).ne' (div_pos hell hL).ne',
    Real.log_div (by norm_num : (4 / 3 : ℝ) ≠ 0) hB.ne',
    Real.log_div hell.ne' hL.ne',
    Real.log_div hL.ne' hell.ne']
  ring

/-- The source choice makes `B eta^(3/2) log gamma = (4/3) loglog gamma`. -/
theorem B_mul_eta_three_halves_mul_log
    {B gamma : ℝ} (hB : 0 < B) (hL : 0 < Real.log gamma)
    (hell : 0 < Real.log (Real.log gamma)) :
    B * Real.rpow (khaleEta B gamma) (3 / 2 : ℝ) * Real.log gamma =
      (4 / 3 : ℝ) * Real.log (Real.log gamma) := by
  let x : ℝ := ((4 / 3 : ℝ) / B) *
    (Real.log (Real.log gamma) / Real.log gamma)
  have hx : 0 < x := etaBase_pos hB hL hell
  have hpow : Real.rpow (khaleEta B gamma) (3 / 2 : ℝ) = x := by
    have h := Real.rpow_mul hx.le (2 / 3 : ℝ) (3 / 2 : ℝ)
    have h' : Real.rpow x ((2 / 3 : ℝ) * (3 / 2 : ℝ)) =
        Real.rpow (Real.rpow x (2 / 3 : ℝ)) (3 / 2 : ℝ) := h
    rw [show (2 / 3 : ℝ) * (3 / 2 : ℝ) = 1 by norm_num] at h'
    have hone : Real.rpow x (1 : ℝ) = x := Real.rpow_one x
    rw [hone] at h'
    simpa only [khaleEta, x] using h'.symm
  rw [hpow]
  dsimp [x]
  field_simp

/-- Exact logarithm of the reciprocal eta. -/
theorem log_one_div_khaleEta
    {B gamma : ℝ} (hB : 0 < B) (hL : 0 < Real.log gamma)
    (hell : 0 < Real.log (Real.log gamma)) :
    Real.log (1 / khaleEta B gamma) =
      (2 / 3 : ℝ) *
        (Real.log (Real.log gamma) -
          Real.log (Real.log (Real.log gamma)) +
          Real.log (B / (4 / 3 : ℝ))) := by
  rw [one_div_khaleEta hB hL hell]
  let k : ℝ := Real.rpow (4 / 3 : ℝ) (-2 / 3 : ℝ)
  let bp : ℝ := Real.rpow B (2 / 3 : ℝ)
  let rp : ℝ := Real.rpow
    (Real.log gamma / Real.log (Real.log gamma)) (2 / 3 : ℝ)
  have hk : 0 < k := Real.rpow_pos_of_pos (by norm_num) _
  have hbp : 0 < bp := Real.rpow_pos_of_pos hB _
  have hrp : 0 < rp := Real.rpow_pos_of_pos (div_pos hL hell) _
  have hout : Real.log (k * bp * rp) = Real.log (k * bp) + Real.log rp :=
    Real.log_mul (mul_pos hk hbp).ne' hrp.ne'
  have hinner : Real.log (k * bp) = Real.log k + Real.log bp :=
    Real.log_mul hk.ne' hbp.ne'
  change Real.log (k * bp * rp) = _
  rw [hout, hinner,
    show Real.log (Real.rpow (4 / 3 : ℝ) (-2 / 3 : ℝ)) =
        (-2 / 3 : ℝ) * Real.log (4 / 3 : ℝ) from
      Real.log_rpow (by norm_num) _,
    show Real.log (Real.rpow B (2 / 3 : ℝ)) =
        (2 / 3 : ℝ) * Real.log B from Real.log_rpow hB _,
    show Real.log (Real.rpow
        (Real.log gamma / Real.log (Real.log gamma)) (2 / 3 : ℝ)) =
        (2 / 3 : ℝ) * Real.log
          (Real.log gamma / Real.log (Real.log gamma)) from
      Real.log_rpow (div_pos hL hell) _,
    Real.log_div hL.ne' hell.ne',
    Real.log_div hB.ne' (by norm_num : (4 / 3 : ℝ) ≠ 0)]
  ring

/-- The reciprocal-scale factor times `loglog gamma` is the VK monomial
appearing in the penultimate display. -/
theorem ratio_two_thirds_mul_loglog
    {gamma : ℝ} (hL : 0 < Real.log gamma)
    (hell : 0 < Real.log (Real.log gamma)) :
    Real.rpow (Real.log gamma / Real.log (Real.log gamma)) (2 / 3 : ℝ) *
        Real.log (Real.log gamma) =
      Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
        Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ) := by
  have hdiv : Real.rpow
      (Real.log gamma / Real.log (Real.log gamma)) (2 / 3 : ℝ) =
      Real.rpow (Real.log gamma) (2 / 3 : ℝ) /
        Real.rpow (Real.log (Real.log gamma)) (2 / 3 : ℝ) :=
    Real.div_rpow hL.le hell.le _
  have hsub : Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ) =
      Real.log (Real.log gamma) /
        Real.rpow (Real.log (Real.log gamma)) (2 / 3 : ℝ) := by
    have h := Real.rpow_sub hell (1 : ℝ) (2 / 3 : ℝ)
    have h' : Real.rpow (Real.log (Real.log gamma))
        ((1 : ℝ) - 2 / 3) =
        Real.rpow (Real.log (Real.log gamma)) 1 /
          Real.rpow (Real.log (Real.log gamma)) (2 / 3 : ℝ) := h
    rw [show (1 : ℝ) - 2 / 3 = 1 / 3 by norm_num,
      show Real.rpow (Real.log (Real.log gamma)) (1 : ℝ) =
        Real.log (Real.log gamma) from Real.rpow_one _] at h'
    exact h'
  rw [hdiv, hsub]
  ring

theorem khaleEta_le_point_zero_six_of_ratio
    {B gamma : ℝ} (hB : 0 < B) (hL : 0 < Real.log gamma)
    (hell : 0 < Real.log (Real.log gamma))
    (hRatio : 5110.6 / B ≤
      Real.log gamma / Real.log (Real.log gamma)) :
    khaleEta B gamma ≤ 0.06 := by
  have hcross : (5110.6 : ℝ) * Real.log (Real.log gamma) ≤
      Real.log gamma * B :=
    (div_le_div_iff₀ hB hell).mp hRatio
  have hbase : ((4 / 3 : ℝ) / B) *
      (Real.log (Real.log gamma) / Real.log gamma) ≤
      (4 / 3 : ℝ) / 5110.6 := by
    field_simp
    nlinarith
  have hrpow := Real.rpow_le_rpow
    (etaBase_pos hB hL hell).le hbase (by norm_num : (0 : ℝ) ≤ 2 / 3)
  exact hrpow.trans MAPKhaleAppendixBNumericalCore.startup_eta_upper

theorem log_ratio_mono_from_exp10650
    {T₀ gamma : ℝ} (hT₀ : Real.exp 10650 ≤ T₀) (hgamma : T₀ ≤ gamma) :
    Real.log T₀ / Real.log (Real.log T₀) ≤
      Real.log gamma / Real.log (Real.log gamma) := by
  have hTpos : 0 < T₀ := (Real.exp_pos 10650).trans_le hT₀
  have hgpos : 0 < gamma := hTpos.trans_le hgamma
  have hlogmono : Real.log T₀ ≤ Real.log gamma :=
    Real.log_le_log hTpos hgamma
  have hlogTlower : (10650 : ℝ) ≤ Real.log T₀ := by
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos 10650) hT₀
  have hlogTpos : 0 < Real.log T₀ := by linarith
  have hlogGpos : 0 < Real.log gamma := hlogTpos.trans_le hlogmono
  have hllTpos : 0 < Real.log (Real.log T₀) :=
    Real.log_pos (by linarith)
  have hllGpos : 0 < Real.log (Real.log gamma) :=
    Real.log_pos (by linarith)
  have hlargeT : Real.exp 1 ≤ Real.log T₀ :=
    Real.exp_one_lt_three.le.trans (by linarith)
  have hlargeG : Real.exp 1 ≤ Real.log gamma := hlargeT.trans hlogmono
  have hanti : Real.log (Real.log gamma) / Real.log gamma ≤
      Real.log (Real.log T₀) / Real.log T₀ :=
    Real.log_div_self_antitoneOn hlargeT hlargeG hlogmono
  have hcross : Real.log (Real.log gamma) * Real.log T₀ ≤
      Real.log (Real.log T₀) * Real.log gamma :=
    (div_le_div_iff₀ hlogGpos hlogTpos).mp hanti
  apply (div_le_div_iff₀ hllTpos hllGpos).2
  nlinarith

end
end MAPKhaleAppendixBEtaAlgebra

#print axioms MAPKhaleAppendixBEtaAlgebra.one_div_khaleEta
#print axioms MAPKhaleAppendixBEtaAlgebra.B_mul_eta_three_halves_mul_log
#print axioms MAPKhaleAppendixBEtaAlgebra.log_one_div_khaleEta
#print axioms MAPKhaleAppendixBEtaAlgebra.ratio_two_thirds_mul_loglog
#print axioms MAPKhaleAppendixBEtaAlgebra.khaleEta_le_point_zero_six_of_ratio
#print axioms MAPKhaleAppendixBEtaAlgebra.log_ratio_mono_from_exp10650
