import FordDifferenceFamily
import FordDifferencePairs

open FordDifferencePairs MAPFordDifferenceFamily MAPFordType
open MAPFordP16Source35Triangular

noncomputable section
namespace FordPositiveHeightFamily

def shift {P modulus : ℕ} (h : PositiveHeight P modulus) : ℤ :=
  (modulus * h.1.val : ℕ)

theorem shift_bounds {P modulus : ℕ} (hm : 0 < modulus)
    (h : PositiveHeight P modulus) : 1 ≤ shift h ∧ shift h ≤ (P : ℤ) := by
  have hh : 0 < h.1.val := h.2
  have hheight : h.1.val ≤ P / modulus := by have := h.1.isLt; omega
  have hpos : 0 < modulus * h.1.val := Nat.mul_pos hm hh
  have hle : modulus * h.1.val ≤ P := by
    calc
      modulus * h.1.val ≤ modulus * (P / modulus) := Nat.mul_le_mul_left _ hheight
      _ = P / modulus * modulus := Nat.mul_comm _ _
      _ ≤ P := Nat.div_mul_le_self _ _
  constructor <;> dsimp [shift] <;> exact_mod_cast (by omega : _)

/-- Every actual positive height gives a legal next Ford family, not merely
an arbitrary family satisfying a coefficient bound. -/
theorem difference_family_of_height
    {k d m P modulus : ℕ} {T : ℤ}
    (psi : Fin k → Polynomial ℤ)
    (htype : FordType k d T m (psiNatSucc psi))
    (hT : T ≠ 0) (hsize : T.natAbs ≤ P ^ d)
    (hm : 0 < modulus) (h : PositiveHeight P modulus) :
    FordType k (d + 1) (shift h * T) m
      (psiNatSucc (differencePsi psi (shift h))) ∧
      shift h * T ≠ 0 ∧ (shift h * T).natAbs ≤ P ^ (d + 1) := by
  obtain ⟨hlo, hhi⟩ := shift_bounds hm h
  have hpos : 0 < shift h := by omega
  exact ⟨ford_type_differencePsi psi htype (shift h) hpos,
    scaled_step_ne_zero hT hpos, natAbs_scaled_step_le hsize hlo hhi⟩

theorem positive_scale_bounds {P modulus : ℕ} {T : ℤ}
    (hm : 0 < modulus) (hT : 0 ≤ T) (h : PositiveHeight P modulus) :
    T ≤ shift h * T ∧ shift h * T ≤ (P : ℤ) * T := by
  obtain ⟨hlo, hhi⟩ := shift_bounds hm h
  constructor <;> nlinarith

end FordPositiveHeightFamily

#print axioms FordPositiveHeightFamily.shift_bounds
#print axioms FordPositiveHeightFamily.difference_family_of_height
#print axioms FordPositiveHeightFamily.positive_scale_bounds
