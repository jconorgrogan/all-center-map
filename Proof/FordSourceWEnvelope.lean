import FordSourceKernelFactor
import FordWEnvelopeScalar
open FordSourceKernelFactor FordWEnvelopeScalar
noncomputable section
namespace FordSourceWEnvelope

def coeff (R j : ℕ) : ℝ := 2 * R + 2 ^ (j+1) + R / (Real.pi * j) +
  4 * Real.pi * j * 4 ^ j / R + 2

def exponent (j : ℕ) (lam : ℝ) : ℝ :=
  min (mu2 * j) (max 0 (max (lam - (1-mu2)*j) ((1-mu1)*j-lam)))

theorem sourceW_le_power {R M1 M2 N j : ℕ} {lam : ℝ}
    (hN : 1 ≤ N) (hj : 1 ≤ j) (hR : 1 ≤ R) (hM1 : 1 ≤ M1)
    (hlo : (N : ℝ)^mu1 / 2 ≤ M1) (hhi : (M2 : ℝ) ≤ (N : ℝ)^mu2) :
    sourceW R R M1 M2 j N ((N : ℝ)^lam) ≤ coeff R j * (N : ℝ)^(exponent j lam) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by positivity
  have hr0 : (0 : ℝ) < R := by positivity
  have hj0 : (0 : ℝ) < j := by positivity
  have hm0 : (0 : ℝ) < M1 := by positivity
  let A : ℝ := mu2 * j
  let B : ℝ := lam - (1-mu2)*j
  let D : ℝ := (1-mu1)*j-lam
  let T : ℝ := max 0 (max B D)
  have hp2 : (M2 : ℝ)^j ≤ (N : ℝ)^A := by
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ M2) hhi j
    simpa [A, Real.rpow_mul, Real.rpow_natCast, hn0.le] using hp
  have hp1 : (N : ℝ)^(mu1*(j : ℝ)) ≤ (2 : ℝ)^j * (M1 : ℝ)^j := by
    have hb : (N : ℝ)^mu1 ≤ 2*(M1 : ℝ) := by
      have h := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hlo
      simpa [mul_comm] using h
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg hn0.le _) hb j
    simpa [Real.rpow_mul, Real.rpow_natCast, hn0.le, mul_pow] using hp
  have hratio : (M2 : ℝ)^j ≤ (2 : ℝ)^j*(M1 : ℝ)^j := by
    apply hp2.trans
    apply le_trans _ hp1
    apply Real.rpow_le_rpow_of_exponent_le hn
    dsimp [A]; have hmu : mu2 ≤ mu1 := by norm_num
    exact mul_le_mul_of_nonneg_right hmu (by positivity)
  have hpowB : (N : ℝ)^B * (N : ℝ)^j = (N : ℝ)^lam*(N : ℝ)^A := by
    rw [← Real.rpow_natCast (N : ℝ) j, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
    congr 1; dsimp [A,B]; ring
  have hpowD : (N : ℝ)^D * (N : ℝ)^lam * (N : ℝ)^(mu1*(j : ℝ)) = (N : ℝ)^j := by
    rw [← Real.rpow_add hn0, ← Real.rpow_add hn0, ← Real.rpow_natCast (N : ℝ) j]
    congr 1; dsimp [D]; ring
  have hpowT : (1 : ℝ) ≤ (N : ℝ)^T := Real.one_le_rpow hn (le_max_left _ _)
  have hBT : (N : ℝ)^B ≤ (N : ℝ)^T := Real.rpow_le_rpow_of_exponent_le hn
    ((le_max_left _ _).trans (le_max_right _ _))
  have hDT : (N : ℝ)^D ≤ (N : ℝ)^T := Real.rpow_le_rpow_of_exponent_le hn
    ((le_max_right _ _).trans (le_max_right _ _))
  have hfirst : 2*((R : ℝ)*(M2 : ℝ)^j)/((R : ℝ)*(M1 : ℝ)^j) ≤ (2 : ℝ)^(j+1) := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 2*(R : ℝ))
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hm
  have hsecond : (R : ℝ)*(M2 : ℝ)^j*(N : ℝ)^lam /
      (Real.pi*(j : ℝ)*(N : ℝ)^j) ≤ (R : ℝ)/(Real.pi*j)*(N : ℝ)^B := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_left hp2
      (by positivity : 0 ≤ (R : ℝ)*(N : ℝ)^lam)
    have heq : (R : ℝ)/(Real.pi*j)*(N : ℝ)^B*(Real.pi*j*(N : ℝ)^j) =
        (R : ℝ)*((N : ℝ)^lam*(N : ℝ)^A) := by
      calc
        _ = (R : ℝ)*((N : ℝ)^B*(N : ℝ)^j) := by field_simp <;> ring
        _ = _ := by rw [hpowB]
    rw [heq]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hm
  have hthird : 4*Real.pi*(j : ℝ)*(2*(N : ℝ))^j /
      ((R : ℝ)*(M1 : ℝ)^j*(N : ℝ)^lam) ≤
      4*Real.pi*(j : ℝ)*(4 : ℝ)^j/(R : ℝ)*(N : ℝ)^D := by
    have hm := mul_le_mul_of_nonneg_left hp1
      (by positivity : 0 ≤ (N : ℝ)^D*(N : ℝ)^lam)
    rw [hpowD] at hm
    have hm2 := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (2 : ℝ)^j)
    have h4 : (2 : ℝ)^j*(2 : ℝ)^j = (4 : ℝ)^j := by rw [← mul_pow]; norm_num
    have hbase : (2*(N : ℝ))^j ≤ (4 : ℝ)^j*(M1 : ℝ)^j*(N : ℝ)^lam*(N : ℝ)^D := by
      calc
        _ = (2 : ℝ)^j*(N : ℝ)^j := mul_pow _ _ _
        _ ≤ _ := hm2
        _ = _ := by rw [← h4]; ring
    apply (div_le_iff₀ (by positivity)).mpr
    have hm3 := mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ 4*Real.pi*(j : ℝ))
    convert hm3 using 1 <;> field_simp <;> ring
  have hc : 0 ≤ coeff R j := by unfold coeff; positivity
  have hcA : 2*(R : ℝ) ≤ coeff R j := by
    have hh : 0 ≤ (2 : ℝ)^(j+1) + R/(Real.pi*j) + 4*Real.pi*j*(4 : ℝ)^j/R + 2 := by positivity
    unfold coeff
    linarith only [hh]
  have hcap : 2*((R : ℝ)*(M2 : ℝ)^j) ≤ coeff R j*(N : ℝ)^A := by
    calc
      _ ≤ (2*(R : ℝ))*(N : ℝ)^A := by nlinarith [mul_le_mul_of_nonneg_left hp2 (by positivity : 0 ≤ 2*(R : ℝ))]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcA (by positivity)
  have hC : sourceC R R M1 M2 j N ((N : ℝ)^lam) ≤ coeff R j*(N : ℝ)^T := by
    have h1 : 2*((R : ℝ)*(M2 : ℝ)^j)/((R : ℝ)*(M1 : ℝ)^j) ≤ (2 : ℝ)^(j+1)*(N : ℝ)^T := by
      apply hfirst.trans
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpowT (by positivity : 0 ≤ (2 : ℝ)^(j+1))
    have h2 := hsecond.trans (mul_le_mul_of_nonneg_left hBT (by positivity : 0 ≤ (R : ℝ)/(Real.pi*j)))
    have h3 := hthird.trans (mul_le_mul_of_nonneg_left hDT (by positivity : 0 ≤ 4*Real.pi*(j : ℝ)*(4 : ℝ)^j/(R : ℝ)))
    unfold sourceC coeff
    push_cast
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2*R by positivity) (show 0 ≤ (N : ℝ)^T by positivity)]
  unfold sourceW exponent
  change min _ _ ≤ coeff R j*(N : ℝ)^(min A T)
  by_cases hAT : A ≤ T
  · rw [min_eq_left hAT]
    exact (min_le_left _ _).trans (by simpa using hcap)
  · rw [min_eq_right (le_of_not_ge hAT)]
    exact (min_le_right _ _).trans hC
end FordSourceWEnvelope
#print axioms FordSourceWEnvelope.sourceW_le_power
