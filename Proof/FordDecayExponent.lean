import FordWeakBilinear
import FordWEnvelopeScalar
noncomputable section
namespace FordDecayExponent
open FordWEnvelopeScalar

def decay (k : ℕ) : ℝ := 1 / (400 * (1003 : ℝ)^2 * (k : ℝ)^2)

theorem root_exponent {k : ℕ} (hk : 1 ≤ k) :
    ((k : ℝ)^2/200) / ((FordWeakBilinear.order k *
      (2*FordWeakBilinear.order k) : ℕ) : ℝ) = decay k := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  unfold decay FordWeakBilinear.order
  push_cast
  field_simp
  <;> ring

theorem decay_pos {k : ℕ} (hk : 1 ≤ k) : 0 < decay k := by
  unfold decay
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  positivity

theorem decay_le_b {k : ℕ} (hk : 1 ≤ k) : decay k ≤ b := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (1 : ℝ) ≤ (k : ℝ)^2 := by nlinarith
  unfold decay
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 400*(1003 : ℝ)^2*(k : ℝ)^2)).mpr
  norm_num [b]
  nlinarith

end FordDecayExponent
#print axioms FordDecayExponent.root_exponent
#print axioms FordDecayExponent.decay_pos
#print axioms FordDecayExponent.decay_le_b
