import PsiEndpointImprimitiveAdapters

/-!
# Exact principal/nonprincipal split of the primitive source binder

This file makes the only exceptional quantifier in the source-facing
Siegel--Walfisz input explicit.  For a primitive principal character the
level is forced to be one; every other primitive character belongs to the
nonprincipal branch.
 -/

namespace MAPPrimitiveTwistedMangoldtSourceSplit

noncomputable section

def PrimitiveNonprincipalTwistedMangoldtPsi : Prop :=
  ∀ A B : ℕ, ∃ C X0 : ℝ,
    0 < C ∧ 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 1 ≤ q →
        (q : ℝ) ≤ (Real.log X) ^ B →
      ∀ chi : DirichletCharacter ℂ q, chi.IsPrimitive → chi ≠ 1 →
      ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
        ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) -
            MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤
          C * X / (Real.log X) ^ A

def PrimitivePrincipalOneTwistedMangoldtPsi : Prop :=
  ∀ A : ℕ, ∃ C X0 : ℝ,
    0 < C ∧ 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
      ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
        ‖APFoundation.twistedMangoldtSum
              (1 : DirichletCharacter ℂ 1) (Finset.Icc 1 ⌊t⌋₊) -
            MAPSiegelWalfiszCharacterReduction.characterMain
              (1 : DirichletCharacter ℂ 1) t‖ ≤
          C * X / (Real.log X) ^ A

theorem primitive_level_eq_one_of_eq_one
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi = 1) : q = 1 := by
  have hcond : chi.conductor = q := hprim
  rw [hchi, DirichletCharacter.conductor_one] at hcond
  exact hcond.symm

theorem primitiveTwistedMangoldtPsi_of_split
    (hnonprincipal : PrimitiveNonprincipalTwistedMangoldtPsi)
    (hprincipal : PrimitivePrincipalOneTwistedMangoldtPsi) :
    ∀ A B : ℕ, ∃ C X0 : ℝ,
      0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
        ∀ q : ℕ, 1 ≤ q →
          (q : ℝ) ≤ (Real.log X) ^ B →
        ∀ chi : DirichletCharacter ℂ q, chi.IsPrimitive →
        ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
          ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) -
              MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤
            C * X / (Real.log X) ^ A := by
  intro A B
  obtain ⟨Cn, Xn, hCn, hXn, hn⟩ := hnonprincipal A B
  obtain ⟨Cp, Xp, hCp, hXp, hp⟩ := hprincipal A
  let C := max Cn Cp
  let X0 := max Xn Xp
  refine ⟨C, X0, ?_, ?_, ?_⟩
  · exact hCn.trans_le (le_max_left _ _)
  · exact hXn.trans (le_max_left _ _)
  intro X hX q hq hqcap chi hprim t ht
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hX2 : 2 ≤ X := hXn.trans ((le_max_left Xn Xp).trans hX)
  have hden0 : 0 ≤ (Real.log X) ^ A :=
    pow_nonneg (Real.log_nonneg (by linarith)) A
  by_cases hchi : chi = 1
  · have hqone := primitive_level_eq_one_of_eq_one chi hprim hchi
    subst q
    subst chi
    exact (hp X ((le_max_right Xn Xp).trans hX) t ht).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right Cn Cp) (by linarith [hX2])) hden0)
  · exact (hn X ((le_max_left Xn Xp).trans hX) q hq hqcap chi hprim hchi t ht).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left Cn Cp) (by linarith [hX2])) hden0)

theorem uniformTwistedMangoldtPsi_of_split
    (hnonprincipal : PrimitiveNonprincipalTwistedMangoldtPsi)
    (hprincipal : PrimitivePrincipalOneTwistedMangoldtPsi) :
    MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
  MAPPsiEndpointImprimitiveAdapters.uniformTwistedMangoldtPsi_of_primitive
    (primitiveTwistedMangoldtPsi_of_split hnonprincipal hprincipal)

end
end MAPPrimitiveTwistedMangoldtSourceSplit

#print axioms MAPPrimitiveTwistedMangoldtSourceSplit.primitive_level_eq_one_of_eq_one
#print axioms MAPPrimitiveTwistedMangoldtSourceSplit.primitiveTwistedMangoldtPsi_of_split
#print axioms MAPPrimitiveTwistedMangoldtSourceSplit.uniformTwistedMangoldtPsi_of_split
