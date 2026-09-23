import GuthMaynardEnergy119FactorBound

noncomputable section
namespace GuthMaynardEnergy119FactorThree
open GuthMaynardEnergy119FactorBound

/-- The literal one-separated energy geometry has E ≤ 3R³. Clipping E to
R³ permits use of the sharp scalar core at a fixed additional factor two. -/
theorem lemma11_9_scalar_factor_bound_three
    {T N R E : ℝ}
    (hT : 1 ≤ T) (hN : Real.rpow T (3/4 : ℝ) ≤ N)
    (hR : 1 ≤ R) (hElo : Real.rpow R (2 : ℝ) ≤ E)
    (hEhi : E ≤ 3*Real.rpow R (3 : ℝ)) :
    Real.sqrt (Real.rpow R 1*T+Real.rpow R 2*N+
      Real.rpow R (5/4 : ℝ)*Real.rpow T (1/2 : ℝ)*N)*
      Real.sqrt (N*Real.rpow R 4+E*T+
        Real.rpow E (3/4 : ℝ)*R*Real.rpow T (1/2 : ℝ)*N) ≤
      20*(N*Real.rpow R 3+N*Real.rpow T (1/4 : ℝ)*
        Real.rpow R (21/8 : ℝ)+N^2*Real.rpow R (1/2 : ℝ)*
          Real.rpow E (1/2 : ℝ)) := by
  have hT0 : 0 ≤ T := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hN0 : 0 ≤ N := (Real.rpow_nonneg hT0 _).trans hN
  have hE0 : 0 ≤ E := (Real.rpow_nonneg hR0 _).trans hElo
  let E0 := min E (Real.rpow R (3 : ℝ))
  have hlow : Real.rpow R (2 : ℝ) ≤ E0 := by
    apply le_min hElo
    exact Real.rpow_le_rpow_of_exponent_le hR (by norm_num)
  have hE00 : 0 ≤ E0 := (Real.rpow_nonneg hR0 _).trans hlow
  have hupper : E0 ≤ Real.rpow R (3 : ℝ) := min_le_right _ _
  have hsmall : E0 ≤ E := min_le_left _ _
  have hscale : E ≤ 3*E0 := by
    by_cases hh : E ≤ Real.rpow R (3 : ℝ)
    · have heq : E0 = E := min_eq_left hh
      rw [heq]
      linarith
    · have heq : E0 = Real.rpow R (3 : ℝ) := min_eq_right (le_of_not_ge hh)
      rw [heq]
      exact hEhi
  have hpow : Real.rpow E (3/4 : ℝ) ≤ 3*Real.rpow E0 (3/4 : ℝ) := by
    have hthree : Real.rpow 3 (3/4 : ℝ) ≤ 3 := by
      have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (by norm_num : (3/4 : ℝ) ≤ 1)
      simpa only [Real.rpow_one] using! hh
    calc
      _ ≤ Real.rpow (3*E0) (3/4 : ℝ) :=
        Real.rpow_le_rpow hE0 hscale (by norm_num)
      _ = Real.rpow 3 (3/4 : ℝ)*Real.rpow E0 (3/4 : ℝ) :=
        Real.mul_rpow (by norm_num) hE00
      _ ≤ _ := mul_le_mul_of_nonneg_right hthree (Real.rpow_nonneg hE00 _)
  let A := Real.rpow R 1*T+Real.rpow R 2*N+
    Real.rpow R (5/4 : ℝ)*Real.rpow T (1/2 : ℝ)*N
  let B := N*Real.rpow R 4+E*T+
    Real.rpow E (3/4 : ℝ)*R*Real.rpow T (1/2 : ℝ)*N
  let B0 := N*Real.rpow R 4+E0*T+
    Real.rpow E0 (3/4 : ℝ)*R*Real.rpow T (1/2 : ℝ)*N
  have hB0 : 0 ≤ B0 := by
    dsimp [B0]
    exact add_nonneg (add_nonneg (mul_nonneg hN0 (Real.rpow_nonneg hR0 _))
      (mul_nonneg hE00 hT0)) (mul_nonneg
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg hE00 _) hR0)
        (Real.rpow_nonneg hT0 _)) hN0)
  have hB : B ≤ 4*B0 := by
    have hh := mul_le_mul_of_nonneg_right hscale hT0
    have hp := mul_le_mul_of_nonneg_right hpow
      (mul_nonneg (mul_nonneg hR0 (Real.rpow_nonneg hT0 (1/2 : ℝ))) hN0)
    have hn := mul_nonneg hN0 (Real.rpow_nonneg hR0 (4 : ℝ))
    dsimp [B,B0] at *
    nlinarith
  have hroot : Real.sqrt B ≤ 2*Real.sqrt B0 := by
    calc
      _ ≤ Real.sqrt (4*B0) := Real.sqrt_le_sqrt hB
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  have hcore := lemma11_9_scalar_factor_bound hT hN hR hlow hupper
  have htarget : N*Real.rpow R 3+N*Real.rpow T (1/4 : ℝ)*Real.rpow R (21/8 : ℝ)+
      N^2*Real.rpow R (1/2 : ℝ)*Real.rpow E0 (1/2 : ℝ) ≤
      N*Real.rpow R 3+N*Real.rpow T (1/4 : ℝ)*Real.rpow R (21/8 : ℝ)+
      N^2*Real.rpow R (1/2 : ℝ)*Real.rpow E (1/2 : ℝ) := by
    apply add_le_add (le_refl _)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hE00 hsmall (by norm_num))
      (mul_nonneg (sq_nonneg N) (Real.rpow_nonneg hR0 _))
  calc
    Real.sqrt A*Real.sqrt B ≤ Real.sqrt A*(2*Real.sqrt B0) :=
      mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg A)
    _ = 2*(Real.sqrt A*Real.sqrt B0) := by ring
    _ ≤ 2*(10*(N*Real.rpow R 3+N*Real.rpow T (1/4 : ℝ)*Real.rpow R (21/8 : ℝ)+
        N^2*Real.rpow R (1/2 : ℝ)*Real.rpow E0 (1/2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hcore (by norm_num)
    _ ≤ _ := by nlinarith [htarget]

end GuthMaynardEnergy119FactorThree
#print axioms GuthMaynardEnergy119FactorThree.lemma11_9_scalar_factor_bound_three
