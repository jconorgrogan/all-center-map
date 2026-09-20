import GuthMaynardEnergyCubicActual
import GuthMaynardEnergy114Actual
import GuthMaynardS3Assembly

open scoped BigOperators
noncomputable section
namespace GuthMaynardEnergy111Actual
open CGLProofDAG GuthMaynardHeathBrownInterface GuthMaynardS3LiteralLemma83Energy
open GuthMaynardEnergyCubicActual GuthMaynardEnergy119Actual
open GuthMaynardEnergy114Actual GuthMaynardS3Source

def largeValueEnergyShape (sigma T : ℝ) (N : ℕ) (W : Finset ℝ) : ℝ :=
  (W.card : ℝ)*Real.rpow (N : ℝ) (4-4*sigma)+
    Real.rpow (W.card : ℝ) (21/8 : ℝ)*Real.rpow T (1/4 : ℝ)*
      Real.rpow (N : ℝ) (1-2*sigma)+
    Real.rpow (W.card : ℝ) (3 : ℝ)*Real.rpow (N : ℝ) (1-2*sigma)

theorem largeValueEnergyShape_nonneg {T : ℝ} (hT : 0 ≤ T)
    (sigma : ℝ) (N : ℕ) (W : Finset ℝ) :
    0 ≤ largeValueEnergyShape sigma T N W := by
  unfold largeValueEnergyShape
  exact add_nonneg (add_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg hT _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- Actual Proposition 11.1 energy estimate. The local-L2/cubic estimate,
both gcd ranges, and square-root energy absorption are supplied internally.
Constants are uniform in sigma, the coefficients, and all source variables. -/
theorem exists_actual_large_value_energy_bound {eps : ℝ} (heps : 0 < eps) :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧
      ∀ (N : ℕ) (W : Finset ℝ) (T sigma : ℝ) (b : ℕ → ℂ),
        1 ≤ N → T0 ≤ T → Real.rpow T (3/4 : ℝ) ≤ N →
        OneSeparated W → ContainedInIntervalOfLength W T →
        (∀ n ∈ Finset.Ioc N (2*N), ‖b n‖ ≤ 1) →
        (∀ t ∈ W, Real.rpow (N : ℝ) sigma ≤ ‖dirichletPolynomial b N t‖) →
        (sourceApproximateAdditiveEnergy W : ℝ) ≤
          C*Real.rpow T eps*largeValueEnergyShape sigma T N W := by
  obtain ⟨Ce,hCe,henergy⟩ := energy_le_cubic_moment_uniform
  obtain ⟨Cc,T0,hCc,hT0,hcubic⟩ := exists_actual_cubic_moment_bound (show 0 < eps/2 by positivity)
  let K := Ce*Cc
  have hK : 0 < K := mul_pos hCe hCc
  refine ⟨2*K+K^2+1,T0,by positivity,hT0,?_⟩
  intro N W T sigma b hN hT hscale hsep hcontained hb hlarge
  have hTone : 1 ≤ T := by have := hT0.trans hT; linarith
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hS : 0 ≤ largeValueEnergyShape sigma T N W :=
    largeValueEnergyShape_nonneg hTpos.le sigma N W
  by_cases hW : W.Nonempty
  swap
  · have hW0 : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst W
    have hh := mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2*K+K^2+1)
      (Real.rpow_nonneg hTpos.le eps)) hS
    simpa [sourceApproximateAdditiveEnergy] using hh
  have hRpos : 0 < (W.card : ℝ) := by exact_mod_cast hW.card_pos
  have he := henergy N b W (Real.rpow (N : ℝ) sigma) hN
    (Real.rpow_nonneg hNpos.le _) hb hsep hlarge
  have hc := hcubic N W T hN hT hscale hsep hcontained
  have hpre : (sourceApproximateAdditiveEnergy W : ℝ)*(Real.rpow (N : ℝ) sigma)^2 ≤
      K*Real.rpow T (eps/2)*cubicMomentShape T N W := by
    have hh := he.trans (mul_le_mul_of_nonneg_left hc hCe.le)
    simpa only [K,mul_assoc] using hh
  have hinv : Real.rpow (N : ℝ) (-2*sigma)*(Real.rpow (N : ℝ) sigma)^2 = 1 := by
    calc
      _ = Real.rpow (N : ℝ) (-2*sigma)*Real.rpow (N : ℝ) (sigma*(2 : ℕ)) :=
        congrArg (fun z : ℝ => Real.rpow (N : ℝ) (-2*sigma)*z)
          (Real.rpow_mul_natCast hNpos.le sigma 2).symm
      _ = Real.rpow (N : ℝ) ((-2*sigma)+sigma*(2 : ℕ)) :=
        (Real.rpow_add hNpos _ _).symm
      _ = 1 := by convert Real.rpow_zero (N : ℝ) using 1 <;> congr 1 <;> ring
  have hraw : (sourceApproximateAdditiveEnergy W : ℝ) ≤
      (K*Real.rpow T (eps/2))*(Real.rpow (N : ℝ) (-2*sigma)*
        ((N : ℝ)*Real.rpow (W.card : ℝ) (3 : ℝ)+
          (N : ℝ)*Real.rpow T (1/4 : ℝ)*Real.rpow (W.card : ℝ) (21/8 : ℝ)+
          Real.sqrt (sourceApproximateAdditiveEnergy W : ℝ)*Real.sqrt (W.card : ℝ)*(N : ℝ)^2)) := by
    have hh := mul_le_mul_of_nonneg_left hpre (Real.rpow_nonneg hNpos.le (-2*sigma))
    change Real.rpow (N : ℝ) (-2*sigma)*
      ((sourceApproximateAdditiveEnergy W : ℝ)*(Real.rpow (N : ℝ) sigma)^2) ≤
      Real.rpow (N : ℝ) (-2*sigma)*(K*Real.rpow T (eps/2)*cubicMomentShape T N W) at hh
    have hleft : Real.rpow (N : ℝ) (-2*sigma)*
        ((sourceApproximateAdditiveEnergy W : ℝ)*(Real.rpow (N : ℝ) sigma)^2) =
        (sourceApproximateAdditiveEnergy W : ℝ) := by
      calc
        _ = (sourceApproximateAdditiveEnergy W : ℝ)*
            (Real.rpow (N : ℝ) (-2*sigma)*(Real.rpow (N : ℝ) sigma)^2) := by ring
        _ = _ := by rw [hinv,mul_one]
    rw [hleft] at hh
    have hR3 : Real.rpow (W.card : ℝ) (3 : ℝ) = (W.card : ℝ)^3 := Real.rpow_natCast _ 3
    rw [hR3]
    convert hh using 1 <;> unfold cubicMomentShape <;> ring
  have ha := proposition11_1_of_literal_postLemma11_9
    (by positivity : 0 ≤ (sourceApproximateAdditiveEnergy W : ℝ)) hRpos hTpos.le hNpos
    (mul_nonneg hK.le (Real.rpow_nonneg hTpos.le _)) hraw
  have hpowle : Real.rpow T (eps/2) ≤ Real.rpow T eps :=
    Real.rpow_le_rpow_of_exponent_le hTone (by linarith)
  have hpowsq : (Real.rpow T (eps/2))^2 = Real.rpow T eps := by
    calc
      _ = Real.rpow T ((eps/2)*(2 : ℕ)) :=
        (Real.rpow_mul_natCast hTpos.le (eps/2) 2).symm
      _ = _ := by congr 1; norm_num
  have hcoeff : 2*(K*Real.rpow T (eps/2))+(K*Real.rpow T (eps/2))^2 ≤
      (2*K+K^2+1)*Real.rpow T eps := by
    rw [mul_pow,hpowsq]
    have hh := mul_le_mul_of_nonneg_left hpowle (by positivity : 0 ≤ 2*K)
    have hnon := Real.rpow_nonneg hTpos.le eps
    nlinarith
  calc
    _ ≤ (2*(K*Real.rpow T (eps/2))+(K*Real.rpow T (eps/2))^2)*
        largeValueEnergyShape sigma T N W := ha
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff hS

end GuthMaynardEnergy111Actual
#print axioms GuthMaynardEnergy111Actual.exists_actual_large_value_energy_bound
