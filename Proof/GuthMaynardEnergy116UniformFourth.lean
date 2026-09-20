import GuthMaynardEnergy116ActualFourth
import GuthMaynardEnergy116LogAbsorption

noncomputable section
namespace GuthMaynardEnergy116UniformFourth
open CGLProofDAG GuthMaynardHeathBrownInterface GuthMaynardLemma118
open GuthMaynardS3LiteralLemma83Energy

def fourthMomentShape (T : ℝ) (M : ℕ) (W : Finset ℝ) : ℝ :=
  (M : ℝ)*(W.card : ℝ)^4+
    (M : ℝ)^2*(sourceApproximateAdditiveEnergy W : ℝ)+
    Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ)*
      (W.card : ℝ)*Real.rpow T (1/2 : ℝ)*M

theorem fourthMomentShape_nonneg {T : ℝ} (hT : 0 ≤ T) (M : ℕ) (W : Finset ℝ) :
    0 ≤ fourthMomentShape T M W := by
  unfold fourthMomentShape
  exact add_nonneg (add_nonneg (by positivity) (by positivity))
    (mul_nonneg (mul_nonneg (mul_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))
      (Real.rpow_nonneg hT _)) (Nat.cast_nonneg _))

theorem fourthMomentShape_enlarged_time {T : ℝ} (hT : 1 ≤ T)
    (M : ℕ) (W : Finset ℝ) :
    fourthMomentShape (2*T+1) M W ≤ 2*fourthMomentShape T M W := by
  have hT0 : 0 ≤ T := by linarith
  have htime : Real.rpow (2*T+1) (1/2 : ℝ) ≤ 2*Real.rpow T (1/2 : ℝ) := by
    calc
      _ ≤ Real.rpow (4*T) (1/2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = Real.rpow 4 (1/2 : ℝ)*Real.rpow T (1/2 : ℝ) :=
        Real.mul_rpow (by norm_num) hT0
      _ = _ := by norm_num [← Real.sqrt_eq_rpow]
  have hcoef : 0 ≤ Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ)*
      (W.card : ℝ)*(M : ℝ) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hh := mul_le_mul_of_nonneg_left htime hcoef
  have hfirst : 0 ≤ (M : ℝ)*(W.card : ℝ)^4 := by positivity
  have hsecond : 0 ≤ (M : ℝ)^2*(sourceApproximateAdditiveEnergy W : ℝ) := by positivity
  unfold fourthMomentShape
  nlinarith

/-- Actual discrete fourth moment with arbitrary subpower loss in the
original time variable. Class logarithms and enlarged time are supplied
and absorbed internally, including the closed-block endpoint correction. -/
theorem discrete_fourth_moment {eps : ℝ} (heps : 0 < eps) :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧
      ∀ (T : ℝ) (M : ℕ) (W : Finset ℝ),
        T0 ≤ T → 1 ≤ M → OneSeparated W →
        ContainedInIntervalOfLength W T →
        ratioKernelMoment 4 M W ≤
          C*Real.rpow T eps*fourthMomentShape T M W := by
  obtain ⟨C4,T4,hC4,hT4,hfour⟩ :=
    GuthMaynardEnergy116ActualFourth.discrete_fourth_moment
      (show 0 < eps/2 by positivity)
  obtain ⟨CL,hCL,hlog⟩ :=
    GuthMaynardEnergy116LogAbsorption.exists_log_square_absorption eps heps
  refine ⟨2*C4*CL,max 2 T4,by positivity,le_max_left _ _,?_⟩
  intro T M W hT hM hsep hcontained
  have hTone : 1 ≤ T := by have := (le_max_left (2 : ℝ) T4).trans hT; linarith
  have hT0 : 0 ≤ T := by linarith
  have hT4' : T4 ≤ 2*T+1 := by
    have := (le_max_right (2 : ℝ) T4).trans hT
    linarith
  have hf := hfour M W T hM hTone hT4' hsep hcontained
  have hl := hlog T W hTone hsep hcontained
  have hshape := fourthMomentShape_enlarged_time hTone M W
  have hcoeff : C4*Real.rpow (2*T+1) (eps/2)*
      ((Nat.log2 W.card+1 : ℕ) : ℝ)^2 ≤ C4*(CL*Real.rpow T eps) := by
    have hh := mul_le_mul_of_nonneg_left hl hC4.le
    simpa only [Nat.cast_add,Nat.cast_one,mul_assoc] using hh
  calc
    _ ≤ C4*Real.rpow (2*T+1) (eps/2)*
        ((Nat.log2 W.card+1 : ℕ) : ℝ)^2*fourthMomentShape (2*T+1) M W := hf
    _ ≤ (C4*(CL*Real.rpow T eps))*(2*fourthMomentShape T M W) :=
      mul_le_mul hcoeff hshape
        (fourthMomentShape_nonneg (by positivity) M W)
        (mul_nonneg hC4.le (mul_nonneg hCL.le (Real.rpow_nonneg hT0 _)))
    _ = _ := by ring

end GuthMaynardEnergy116UniformFourth
#print axioms GuthMaynardEnergy116UniformFourth.discrete_fourth_moment
