import GuthMaynardEnergy119RoundedRange
import GuthMaynardHeathBrownMajorant

noncomputable section
namespace GuthMaynardEnergy119ScaleAlgebra
open GuthMaynardEnergy119RoundedRange GuthMaynardHeathBrownMajorant

theorem quadratic_shape_scale {a b M N d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hd : 0 < d) (hscale : M ≤ 2*N/d) :
    a*M^2+b*M ≤ 4*(a*N^2/d^2+b*N/d) := by
  have hq : 0 ≤ 2*N/d := by positivity
  have hsq := (sq_le_sq₀ hM hq).mpr hscale
  have hquad := mul_le_mul_of_nonneg_left hsq ha
  have hlin := mul_le_mul_of_nonneg_left hscale hb
  have hnon : 0 ≤ b*N/d := by positivity
  have hid : a*(2*N/d)^2+b*(2*N/d) =
      4*(a*N^2/d^2)+2*(b*N/d) := by ring
  calc
    _ ≤ a*(2*N/d)^2+b*(2*N/d) := add_le_add hquad hlin
    _ = 4*(a*N^2/d^2)+2*(b*N/d) := hid
    _ ≤ _ := by nlinarith

/-- Rounding the gcd quotient increases the literal Heath--Brown polynomial
by at most four. The time and cardinality powers are unchanged. -/
theorem rounded_heathBrownShape_le {N d : ℕ} (T : ℝ) (W : Finset ℝ)
    (hN : 1 ≤ N) (hd : 1 ≤ d) (hd2 : d ≤ 2*N) (hT : 0 ≤ T) :
    heathBrownShape T (Nat.ceil ((N : ℝ)/(d : ℝ))) W ≤
      4*((W.card : ℝ)*(N : ℝ)^2/(d : ℝ)^2+
        ((W.card : ℝ)^2+Real.rpow (W.card : ℝ) (5/4 : ℝ)*
          Real.rpow T (1/2 : ℝ))*(N : ℝ)/(d : ℝ)) := by
  obtain ⟨hM,hscale,hcover⟩ := ceil_dyadic_range_cover hN hd hd2
  have hh := quadratic_shape_scale
    (a := (W.card : ℝ))
    (b := (W.card : ℝ)^2+Real.rpow (W.card : ℝ) (5/4 : ℝ)*Real.rpow T (1/2 : ℝ))
    (by positivity)
    (add_nonneg (sq_nonneg _) (mul_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hT _)))
    (by positivity) (by positivity)
    (by exact_mod_cast (show 0 < d by omega)) hscale
  calc
    _ = (W.card : ℝ)*(Nat.ceil ((N : ℝ)/(d : ℝ)) : ℝ)^2+
      ((W.card : ℝ)^2+Real.rpow (W.card : ℝ) (5/4 : ℝ)*Real.rpow T (1/2 : ℝ))*
        (Nat.ceil ((N : ℝ)/(d : ℝ)) : ℝ) := by
      unfold heathBrownShape
      ring
    _ ≤ _ := hh

end GuthMaynardEnergy119ScaleAlgebra
#print axioms GuthMaynardEnergy119ScaleAlgebra.quadratic_shape_scale
#print axioms GuthMaynardEnergy119ScaleAlgebra.rounded_heathBrownShape_le
