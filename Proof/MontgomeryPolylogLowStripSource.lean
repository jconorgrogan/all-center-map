import MontgomeryFullScalePrincipalDensity
import MontgomeryPolylogLowStripConsumer
namespace MAPMontgomeryPolylogLowStripSource
open DirichletZeros ZeroDensityArithmetic
open MAPMontgomeryPolylogLowStripConsumer MAPMontgomeryFullScaleNonprincipalDensity
open MAPMontgomeryFullScalePrincipalDensity MAPMontgomeryTheorem12SourceDAG
noncomputable section

/-- The actual compact low-strip source consumed by MAP. Both primitive
character cases are proved, including conductor-one zeta and all zeros with
real part at least sigma. Fixed logarithmic losses are absorbed by eta. -/
theorem polylogLowStripDensity_proved : PolylogLowStripDensity := by
  classical
  intro K delta eta hK hdelta heta
  obtain ⟨Cn,Tn,hCn,hTn,hn⟩ := nonprincipal_fullScale_low_strip_density K delta eta hK hdelta heta
  obtain ⟨Cp,Tp,hCp,hTp,hp⟩ := principal_fullScale_low_strip_density delta eta hdelta heta
  refine ⟨max Cn Cp,max Tn Tp,hCn.trans_le (le_max_left _ _),hTn.trans (le_max_left _ _),?_⟩
  intro T Q sigma hT hQ hslo hshi r _ chi hprim hrQ
  have hTn' : Tn ≤ T := (le_max_left _ _).trans hT
  have hTp' : Tp ≤ T := (le_max_right _ _).trans hT
  have hpow : 0 ≤ Real.rpow T (uniformCoeff*(1-sigma)+eta) :=
    Real.rpow_nonneg (by linarith) _
  by_cases hchi : chi=1
  · have hrone : r=1 := by
      have hc := (DirichletCharacter.isPrimitive_def chi).mp hprim
      rw [hchi,DirichletCharacter.conductor_one] at hc
      exact hc.symm
    subst r
    subst chi
    exact (hp T sigma hTp' hslo hshi).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)
  · have hq : (r : ℝ) ≤ Real.rpow (Real.log T) K :=
      (show (r : ℝ) ≤ Q by exact_mod_cast hrQ).trans hQ
    have hsingle : dirichletZeroCount chi sigma T ≤ nonprincipalAmbientZeroCountAtLevel r sigma T := by
      unfold nonprincipalAmbientZeroCountAtLevel
      exact Finset.single_le_sum (f := fun psi : DirichletCharacter ℂ r => dirichletZeroCount psi sigma T)
        (fun psi hpsi => Nat.zero_le _)
        (Finset.mem_erase.mpr ⟨hchi,Finset.mem_univ _⟩)
    exact (show (dirichletZeroCount chi sigma T : ℝ) ≤
      (nonprincipalAmbientZeroCountAtLevel r sigma T : ℝ) by exact_mod_cast hsingle).trans
      ((hn T r sigma hTn' hq hslo hshi).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow))
end
end MAPMontgomeryPolylogLowStripSource
#print axioms MAPMontgomeryPolylogLowStripSource.polylogLowStripDensity_proved
