import GoldfeldScaleSelectionImprimitive
import GoldfeldComparisonBridge

/-!
# Structural lemmas for the varying-level Goldfeld lift
-/

namespace MAPGoldfeldSiegel

open Complex

noncomputable section

/-- Changing the level of a primitive character does not change its
conductor. -/
theorem conductor_changeLevel_of_primitive
    {M N : ℕ} [NeZero M] [NeZero N]
    (h : M ∣ N) (chi : DirichletCharacter ℂ M)
    (hprim : chi.IsPrimitive) :
    (DirichletCharacter.changeLevel h chi).conductor = M := by
  let lambda := DirichletCharacter.changeLevel h chi
  have hcondM : lambda.conductor ∣ M :=
    DirichletCharacter.conductor_dvd_of_mem_conductorSet lambda
      (DirichletCharacter.changeLevel_factorsThrough chi h)
  haveI : NeZero lambda.conductor := ⟨lambda.conductor_ne_zero⟩
  have hfactor : DirichletCharacter.FactorsThrough chi lambda.conductor := by
    refine ⟨hcondM, lambda.primitiveCharacter, ?_⟩
    apply DirichletCharacter.changeLevel_injective h
    rw [← DirichletCharacter.changeLevel_trans]
    change lambda = DirichletCharacter.changeLevel (dvd_trans hcondM h)
      lambda.primitiveCharacter
    simpa [lambda] using lambda.changeLevel_primitiveCharacter.symm
  have hMcond : M ∣ lambda.conductor := by
    rw [← hprim]
    exact DirichletCharacter.conductor_dvd_of_mem_conductorSet chi hfactor
  exact Nat.dvd_antisymm hcondM hMcond

namespace PrimitiveRealCharacter

theorem two_le_level (a : PrimitiveRealCharacter) : 2 ≤ a.level := by
  rcases a with ⟨q, hq, chi, hprim, hchi, hreal⟩
  dsimp
  have hneOne : q ≠ 1 := by
    intro hqOne
    subst q
    exact hchi (Subsingleton.elim _ _)
  omega

/-- Two primitive characters which have the same lift to their product level
are the same packaged character. -/
theorem eq_of_changeLevel_mul_eq
    (a b : PrimitiveRealCharacter)
    (hEq : DirichletCharacter.changeLevel
          (Nat.dvd_mul_right a.level b.level) a.chi =
      DirichletCharacter.changeLevel
          (Nat.dvd_mul_left b.level a.level) b.chi) :
    a = b := by
  letI : NeZero (a.level * b.level) :=
    ⟨Nat.mul_ne_zero a.level_ne_zero b.level_ne_zero⟩
  have hlevel : a.level = b.level := by
    have hc := congrArg DirichletCharacter.conductor hEq
    rw [conductor_changeLevel_of_primitive
          (Nat.dvd_mul_right a.level b.level) a.chi a.primitive,
      conductor_changeLevel_of_primitive
          (Nat.dvd_mul_left b.level a.level) b.chi b.primitive] at hc
    exact hc
  cases a with
  | mk qa hqa chia hpa hna hra =>
    cases b with
    | mk qb hqb chib hpb hnb hrb =>
      dsimp at hlevel hEq ⊢
      subst qb
      have hchi : chia = chib :=
        DirichletCharacter.changeLevel_injective
          (Nat.dvd_mul_right qa qa) hEq
      subst chib
      rfl

end PrimitiveRealCharacter

def productLevel (a b : PrimitiveRealCharacter) : ℕ := a.level * b.level

instance (a b : PrimitiveRealCharacter) : NeZero (productLevel a b) :=
  ⟨Nat.mul_ne_zero a.level_ne_zero b.level_ne_zero⟩

def leftLift (a b : PrimitiveRealCharacter) :
    DirichletCharacter ℂ (productLevel a b) :=
  DirichletCharacter.changeLevel (Nat.dvd_mul_right a.level b.level) a.chi

def rightLift (a b : PrimitiveRealCharacter) :
    DirichletCharacter ℂ (productLevel a b) :=
  DirichletCharacter.changeLevel (Nat.dvd_mul_left b.level a.level) b.chi

theorem leftLift_ne_one (a b : PrimitiveRealCharacter) : leftLift a b ≠ 1 := by
  intro h
  apply a.nonprincipal
  unfold leftLift productLevel at h
  exact (DirichletCharacter.changeLevel_eq_one_iff
    (R := ℂ) (Nat.dvd_mul_right a.level b.level)).mp h

theorem rightLift_ne_one (a b : PrimitiveRealCharacter) : rightLift a b ≠ 1 := by
  intro h
  apply b.nonprincipal
  unfold rightLift productLevel at h
  exact (DirichletCharacter.changeLevel_eq_one_iff
    (R := ℂ) (Nat.dvd_mul_left b.level a.level)).mp h

theorem leftLift_sq (a b : PrimitiveRealCharacter) : leftLift a b ^ 2 = 1 := by
  unfold leftLift productLevel
  calc
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right a.level b.level)
        a.chi) ^ 2 =
      DirichletCharacter.changeLevel (Nat.dvd_mul_right a.level b.level)
        (a.chi ^ 2) :=
      ((DirichletCharacter.changeLevel
        (Nat.dvd_mul_right a.level b.level)).map_pow a.chi 2).symm
    _ = 1 := by rw [a.real, DirichletCharacter.changeLevel_one]

theorem rightLift_sq (a b : PrimitiveRealCharacter) : rightLift a b ^ 2 = 1 := by
  unfold rightLift productLevel
  calc
    (DirichletCharacter.changeLevel (Nat.dvd_mul_left b.level a.level)
        b.chi) ^ 2 =
      DirichletCharacter.changeLevel (Nat.dvd_mul_left b.level a.level)
        (b.chi ^ 2) :=
      ((DirichletCharacter.changeLevel
        (Nat.dvd_mul_left b.level a.level)).map_pow b.chi 2).symm
    _ = 1 := by rw [b.real, DirichletCharacter.changeLevel_one]

theorem leftLift_mul_rightLift_ne_one
    (a b : PrimitiveRealCharacter) (hne : a ≠ b) :
    leftLift a b * rightLift a b ≠ 1 := by
  intro hmul
  have heq : leftLift a b = rightLift a b := by
    calc
      leftLift a b = leftLift a b * 1 := by simp
      _ = leftLift a b * (leftLift a b * rightLift a b) := by rw [hmul]
      _ = (leftLift a b * leftLift a b) * rightLift a b := by rw [mul_assoc]
      _ = (leftLift a b ^ 2) * rightLift a b := by rw [pow_two]
      _ = rightLift a b := by rw [leftLift_sq]; simp
  exact hne (PrimitiveRealCharacter.eq_of_changeLevel_mul_eq a b heq)

/-- A zero of the primitive left character remains a zero after lifting. -/
theorem leftLift_LFunction_eq_zero
    (a b : PrimitiveRealCharacter) {beta : ℝ}
    (hzero : a.LFunction beta = 0) :
    DirichletCharacter.LFunction (leftLift a b) beta = 0 := by
  unfold leftLift productLevel
  rw [DirichletCharacter.LFunction_changeLevel
    (Nat.dvd_mul_right a.level b.level) a.chi (.inl a.nonprincipal)]
  rw [show DirichletCharacter.LFunction a.chi (beta : ℂ) = 0 by
    simpa [PrimitiveRealCharacter.LFunction] using hzero]
  simp

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.conductor_changeLevel_of_primitive
#print axioms MAPGoldfeldSiegel.PrimitiveRealCharacter.eq_of_changeLevel_mul_eq
#print axioms MAPGoldfeldSiegel.leftLift_mul_rightLift_ne_one
#print axioms MAPGoldfeldSiegel.leftLift_LFunction_eq_zero
