import SiegelWalfiszContract

/-!
# Exact character reduction for the Siegel--Walfisz contract

This file contains only the finite, deterministic bridge.  It does not claim
to prove the analytic character-sum estimate stated below as a hypothesis.
-/

namespace MAPSiegelWalfiszCharacterReduction

open Set
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The project definition of `psi(t; q, a)` is exactly the finite sum of
Mathlib's residue-class von Mangoldt arithmetic function. -/
theorem progressionPsi_eq_sum_residueClass
    {q a : ℕ} (t : ℝ) :
    APFoundation.progressionPsi t q a =
      ∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) n := by
  unfold APFoundation.progressionPsi
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmod : n % q = a % q
  · have hz : (n : ZMod q) = (a : ZMod q) :=
      (ZMod.natCast_eq_natCast_iff' n a q).2 hmod
    simp [ArithmeticFunction.vonMangoldt.residueClass, hz, hmod]
  · have hz : (n : ZMod q) ≠ (a : ZMod q) := by
      intro hz
      exact hmod ((ZMod.natCast_eq_natCast_iff' n a q).1 hz)
    simp [ArithmeticFunction.vonMangoldt.residueClass, hz, hmod]

/-- The pole main term for one character, with the classical equality decision
made explicit so downstream statements need no local `DecidableEq` instance. -/
noncomputable def characterMain {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  @ite ℂ (χ = 1) (Classical.propDecidable _) (t : ℂ) 0

/-- Exact finite reduction: a uniform bound for every character-twisted
Mangoldt prefix implies the same bound for each reduced progression.  The
`1 / phi(q)` projector loses no factor because there are exactly `phi(q)`
characters and every character has norm at most one. -/
theorem progressionPsi_error_le_of_character_errors
    {W t : ℝ} {q a : ℕ}
    (hq : 1 ≤ q) (ha : a.Coprime q)
    (hchar : ∀ χ : DirichletCharacter ℂ q,
      ‖(∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
          χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) -
          characterMain χ t‖ ≤ W) :
    |APFoundation.progressionPsi t q a -
        t / (q.totient : ℝ)| ≤ W := by
  classical
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let az : ZMod q := (a : ZMod q)
  have haz : IsUnit az := by
    simpa only [az, ZMod.isUnit_iff_coprime] using ha
  let T : DirichletCharacter ℂ q → ℂ := fun χ ↦
    ∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
      χ n * (ArithmeticFunction.vonMangoldt n : ℂ)
  let M : DirichletCharacter ℂ q → ℂ := fun χ ↦
    characterMain χ t
  have hmain :
      ∑ χ : DirichletCharacter ℂ q, χ az⁻¹ * M χ = (t : ℂ) := by
    simp [M, characterMain]
    have hazinv : IsUnit az⁻¹ := by
      rw [isUnit_iff_exists]
      exact ⟨az, ZMod.inv_mul_of_unit az haz, ZMod.mul_inv_of_unit az haz⟩
    rw [MulChar.one_apply hazinv, one_mul]
  have hprojector :
      (APFoundation.progressionPsi t q a : ℂ) =
        (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q, χ az⁻¹ * T χ := by
    rw [progressionPsi_eq_sum_residueClass t]
    push_cast
    simpa only [az, T] using
      (APFoundation.sum_residueClass_eq_sum_characters haz
        (Finset.Icc 1 ⌊t⌋₊))
  have hphi : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hq)).ne'
  have hcomplex :
      ‖(APFoundation.progressionPsi t q a : ℂ) -
          (t / (q.totient : ℝ) : ℝ)‖ ≤ W := by
    rw [hprojector]
    have hid :
        (t / (q.totient : ℝ) : ℝ) =
          ((q.totient : ℂ)⁻¹ * (t : ℂ)) := by
      push_cast
      rw [div_eq_mul_inv, mul_comm]
    rw [show ((t / (q.totient : ℝ) : ℝ) : ℂ) =
        (q.totient : ℂ)⁻¹ * (t : ℂ) by exact_mod_cast hid,
      ← hmain, ← mul_sub, ← Finset.sum_sub_distrib]
    calc
      ‖(q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            (χ az⁻¹ * T χ - χ az⁻¹ * M χ)‖ =
          (q.totient : ℝ)⁻¹ *
            ‖∑ χ : DirichletCharacter ℂ q,
              χ az⁻¹ * (T χ - M χ)‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
        congr 2
        apply Finset.sum_congr rfl
        intro χ _
        ring
      _ ≤ (q.totient : ℝ)⁻¹ *
          ∑ _χ : DirichletCharacter ℂ q, W := by
        gcongr
        calc
          ‖∑ χ : DirichletCharacter ℂ q,
              χ az⁻¹ * (T χ - M χ)‖ ≤
              ∑ χ : DirichletCharacter ℂ q,
                ‖χ az⁻¹ * (T χ - M χ)‖ := norm_sum_le _ _
          _ ≤ ∑ _χ : DirichletCharacter ℂ q, W := by
            apply Finset.sum_le_sum
            intro χ _
            rw [norm_mul]
            exact (mul_le_of_le_one_left (norm_nonneg _)
              (χ.norm_le_one az⁻¹)).trans (by simpa [T, M] using hchar χ)
      _ = W := by
        have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
          rw [← Nat.card_eq_fintype_card,
            DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
        field_simp
  have hre :
      |((APFoundation.progressionPsi t q a : ℂ) -
          (t / (q.totient : ℝ) : ℝ)).re| ≤ W :=
    (Complex.abs_re_le_norm _).trans hcomplex
  simpa using hre

/-- A source-faithful individual-character form of uniform Siegel--Walfisz.
This remains the analytic theorem to prove; the next theorem only shows that
it is sufficient for the public progression contract. -/
def UniformTwistedMangoldtPsi : Prop :=
  ∀ A B : ℕ, ∃ C X0 : ℝ,
    0 < C ∧ 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ,
        1 ≤ q →
        (q : ℝ) ≤ (Real.log X) ^ B →
      ∀ χ : DirichletCharacter ℂ q,
      ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
        ‖(∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
            χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) -
            characterMain χ t‖ ≤
          C * X / (Real.log X) ^ A

/-- The exact deterministic implication from individual twisted sums to the
public progression form.  No contour shift, zero-free region, or Siegel lower
bound is hidden in this proof. -/
theorem uniformSiegelWalfiszPsi_of_uniformTwistedMangoldtPsi
    (h : UniformTwistedMangoldtPsi) :
    MAPPointwiseMajorArc.UniformSiegelWalfiszPsi := by
  intro A B
  obtain ⟨C, X0, hC, hX0, hchar⟩ := h A B
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X hX q a hq hqcap haq ha t ht
  apply progressionPsi_error_le_of_character_errors hq ha
  intro χ
  exact hchar X hX q hq hqcap χ t ht

end

end MAPSiegelWalfiszCharacterReduction

#print axioms MAPSiegelWalfiszCharacterReduction.progressionPsi_error_le_of_character_errors
#print axioms MAPSiegelWalfiszCharacterReduction.uniformSiegelWalfiszPsi_of_uniformTwistedMangoldtPsi
