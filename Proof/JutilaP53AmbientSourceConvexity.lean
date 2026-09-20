import JutilaEulerEpsilonBound
import BHPRademacherGaussianThreeLines
import JutilaHybridConvexityEulerReduction

/-! # Ambient nonprincipal convexity on the positive source strip -/
namespace MAPJutilaP53AmbientSourceConvexity
open Complex
open MAPJutilaEulerEpsilonBound MAPBHPRademacherGaussianThreeLines
open MAPJutilaHybridConvexityEulerReduction
noncomputable section

/-- Allocate one quarter of the fixed left-edge margin to primitive
convexity and one quarter to the ambient Euler correction. -/
theorem exists_ambient_source_convexity
    {epsilon : ℝ} (heps : 0 < epsilon) (hepsHalf : epsilon ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q), chi ≠ 1 →
      ∀ sigma t : ℝ, epsilon ≤ sigma → sigma ≤ 1 →
        ‖DirichletCharacter.LFunction chi ((sigma : ℂ) + (t : ℂ) * I)‖ ≤
          C * Real.rpow ((q : ℝ) * (1 + |t|)) (1 / 2) := by
  let eta : ℝ := epsilon / 4
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hetaHalf : eta ≤ 1 / 2 := by dsimp [eta]; linarith
  obtain ⟨Ce, hCe, heulerBound⟩ := exists_two_pow_primeFactors_card_le_rpow heta
  let Cp : ℝ := 36 * (1 + eta⁻¹) * Real.rpow 6 (eta + 1 / 2)
  have hCp : 0 < Cp := by dsimp [Cp]; positivity
  refine ⟨Cp * Ce, mul_pos hCp hCe, ?_⟩
  intro q _inst chi hchi sigma t hsigma hsigma1
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hprimNe : chi.primitiveCharacter ≠ 1 := by
    intro hp
    exact hchi ((PrimitiveTruncatedExplicitFormulaBridge.primitiveCharacter_eq_one_iff chi).mp hp)
  have hsigma0 : 0 ≤ sigma := heps.le.trans hsigma
  have hp := norm_LFunction_le_jutila_convexity heta hetaHalf
    chi.primitiveCharacter chi.primitiveCharacter_isPrimitive hprimNe hsigma0 hsigma1
    (u := t)
  have he := norm_LFunction_le_primitive_mul_two_pow_card chi hchi
    (s := (sigma : ℂ) + (t : ℂ) * I) (by simpa using hsigma0)
  let Q : ℝ := (q : ℝ) * (1 + |t|)
  let E : ℝ := (1 / 2) * (1 - sigma) + eta
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hQ : 1 ≤ Q := by dsimp [Q]; nlinarith [abs_nonneg t]
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hE : 0 ≤ E := by dsimp [E]; linarith
  have hcond : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast ZeroDensityInterface.conductor_le_level chi
  have hcondScale : (chi.conductor : ℝ) * (1 + |t|) ≤ Q :=
    mul_le_mul_of_nonneg_right hcond (by positivity)
  have hprimBound : ‖DirichletCharacter.LFunction chi.primitiveCharacter
      ((sigma : ℂ) + (t : ℂ) * I)‖ ≤ Cp * Real.rpow Q E := by
    exact hp.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hcondScale hE) hCp.le)
  have hqQ : (q : ℝ) ≤ Q := by dsimp [Q]; nlinarith [abs_nonneg t]
  have hEulerBound : (2 : ℝ)^q.primeFactors.card ≤ Ce * Real.rpow Q eta :=
    (heulerBound q (Nat.pos_of_ne_zero (NeZero.ne q))).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg q) hqQ heta.le) hCe.le)
  have hEx : E + eta ≤ 1 / 2 := by dsimp [E, eta]; linarith
  calc
    _ ≤ ‖DirichletCharacter.LFunction chi.primitiveCharacter
        ((sigma : ℂ) + (t : ℂ) * I)‖ * (2 : ℝ)^q.primeFactors.card := he
    _ ≤ (Cp * Real.rpow Q E) * (Ce * Real.rpow Q eta) :=
      mul_le_mul hprimBound hEulerBound (by positivity)
        (mul_nonneg hCp.le (Real.rpow_nonneg hQpos.le _))
    _ = (Cp * Ce) * Real.rpow Q (E + eta) := by
      change (Cp * Q ^ E) * (Ce * Q ^ eta) = (Cp * Ce) * Q ^ (E + eta)
      rw [Real.rpow_add hQpos E eta]
      ring
    _ ≤ (Cp * Ce) * Real.rpow Q (1 / 2) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ hEx)
        (mul_pos hCp hCe).le
end
end MAPJutilaP53AmbientSourceConvexity
#print axioms MAPJutilaP53AmbientSourceConvexity.exists_ambient_source_convexity
