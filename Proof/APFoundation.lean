import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Foundations for the simultaneous short-interval AP input

This file separates the unconditional algebra already available in mathlib
from the quantitative analytic theorem still to be proved.  In particular,
`SimultaneousShortIntervalAP` is only a proposition: it is not an axiom and no
theorem below claims to prove it.
-/

namespace APFoundation

open MeasureTheory
open scoped ArithmeticFunction BigOperators ENNReal

noncomputable section

/-- `psi(x; q, a)`, represented by reduced natural residues. -/
def progressionPsi (x : ℝ) (q a : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    if n % q = a % q then ArithmeticFunction.vonMangoldt n else 0

/-- The normalized short-interval error in a reduced progression. -/
def normalizedAPError (x Y : ℝ) (q a : ℕ) : ℝ :=
  (progressionPsi (x + Y) q a - progressionPsi x q a -
      Y / (q.totient : ℝ)) / Y

/-- The pointwise maximum over every legal modulus, reduced residue, and real aperture. -/
def simultaneousAPMax (K ε X x : ℝ) : ℝ≥0∞ :=
  ⨆ (q : ℕ) (_hqpos : 1 ≤ q)
      (_hqcap : (q : ℝ) ≤ Real.rpow (Real.log X) K)
      (a : ℕ) (_haq : a < q) (_ha : a.Coprime q)
      (Y : ℝ) (_hYlow : Real.rpow X (2 / 15 + ε) ≤ Y)
      (_hYhigh : Y ≤ X),
    ENNReal.ofReal |normalizedAPError x Y q a| ^ 2

/--
The exact maximal-in-`x`, simultaneous short-interval AP target used by the
MAP collars.  `K`, the requested logarithmic saving `A`, and the aperture
reserve `ε` are fixed before `C`, `X₀`, `X`, every modulus/residue, and every
real aperture.  The maximum is inside the `x`-integral.
-/
def SimultaneousShortIntervalAP : Prop :=
  ∀ K A ε : ℝ, 0 < K → 0 < A → 0 < ε → ε ≤ 13 / 30 →
    ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        (∫⁻ x in Set.Icc (X / 2) (4 * X), simultaneousAPMax K ε X x) ≤
          ENNReal.ofReal (C * X * Real.rpow (Real.log X) (-A))

section CharacterExpansion

variable {q : ℕ} [NeZero q]

/-- The literal finite von Mangoldt window in one invertible residue class. -/
def residueClassWindow (a : ZMod q) (m n : ℕ) : ℂ :=
  ∑ k ∈ Finset.Ioc m n,
    (ArithmeticFunction.vonMangoldt.residueClass a k : ℂ)

/-- Exact finite character projector on an arbitrary finite set of integers. -/
theorem sum_residueClass_eq_sum_characters
    {a : ZMod q} (ha : IsUnit a) (S : Finset ℕ) :
    (∑ n ∈ S,
        (ArithmeticFunction.vonMangoldt.residueClass a n : ℂ)) =
      (q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          χ a⁻¹ * ∑ n ∈ S,
            χ n * (ArithmeticFunction.vonMangoldt n : ℂ) := by
  simp_rw [ArithmeticFunction.vonMangoldt.residueClass_apply ha]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [mul_assoc]

/-- Short-interval specialization of the exact finite character projector. -/
theorem residueClassWindow_eq_sum_characters
    {a : ZMod q} (ha : IsUnit a) (m n : ℕ) :
    residueClassWindow a m n =
      (q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          χ a⁻¹ * ∑ k ∈ Finset.Ioc m n,
            χ k * (ArithmeticFunction.vonMangoldt k : ℂ) := by
  exact sum_residueClass_eq_sum_characters ha (Finset.Ioc m n)

open Classical in
/--
The same projector with the principal character separated from every
nonprincipal ambient character.  The latter finite sum still includes all
imprimitive characters modulo `q`.
-/
theorem sum_residueClass_eq_principal_add_nonprincipal
    {a : ZMod q} (ha : IsUnit a) (S : Finset ℕ) :
    (∑ n ∈ S,
        (ArithmeticFunction.vonMangoldt.residueClass a n : ℂ)) =
      (q.totient : ℂ)⁻¹ *
        (((1 : DirichletCharacter ℂ q) a⁻¹) *
            ∑ n ∈ S, (1 : DirichletCharacter ℂ q) n *
              (ArithmeticFunction.vonMangoldt n : ℂ) +
          ∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)),
            χ a⁻¹ * ∑ n ∈ S,
              χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) := by
  rw [sum_residueClass_eq_sum_characters ha S]
  congr 1
  simpa [add_comm] using
    (Finset.sum_erase_add Finset.univ
      (fun χ : DirichletCharacter ℂ q =>
        χ a⁻¹ * ∑ n ∈ S, χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
      (Finset.mem_univ (1 : DirichletCharacter ℂ q))).symm

/--
Every ambient character in the finite AP projector is exactly the change of
level of its primitive character.  This identity deliberately does not replace
the ambient values by primitive values at integers sharing factors with `q`.
-/
theorem ambient_sum_eq_sum_changed_primitive
    {a : ZMod q} (S : Finset ℕ) :
    (∑ χ : DirichletCharacter ℂ q,
        χ a⁻¹ * ∑ n ∈ S,
          χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) =
      ∑ χ : DirichletCharacter ℂ q,
        χ a⁻¹ * ∑ n ∈ S,
          (DirichletCharacter.changeLevel χ.conductor_dvd_level
              χ.primitiveCharacter) n *
            (ArithmeticFunction.vonMangoldt n : ℂ) := by
  apply Finset.sum_congr rfl
  intro χ _
  rw [χ.changeLevel_primitiveCharacter]

/-! ### Exact primitive/imprimitive transport on finite Mangoldt sums -/

/-- An ambient character and its primitive inducer have identical values on
integers coprime to the ambient level.  The coprimality hypothesis is essential:
the ambient character vanishes at the additional bad Euler factors. -/
theorem ambient_eq_primitive_of_coprime
    (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : n.Coprime q) :
    χ n = χ.primitiveCharacter n := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hχ : χ = DirichletCharacter.changeLevel χ.conductor_dvd_level
      χ.primitiveCharacter := χ.changeLevel_primitiveCharacter.symm
  calc
    χ n = (DirichletCharacter.changeLevel χ.conductor_dvd_level
        χ.primitiveCharacter) n :=
      DFunLike.congr_fun hχ (n : ZMod q)
    _ = (DirichletCharacter.changeLevel χ.conductor_dvd_level
        χ.primitiveCharacter)
          (ZMod.unitOfCoprime n hn : ZMod q) := by
      rw [ZMod.coe_unitOfCoprime]
    _ = χ.primitiveCharacter
        (ZMod.cast (ZMod.unitOfCoprime n hn : ZMod q)) :=
      DirichletCharacter.changeLevel_eq_cast_of_dvd χ.primitiveCharacter
        χ.conductor_dvd_level (ZMod.unitOfCoprime n hn)
    _ = χ.primitiveCharacter n := by
      rw [ZMod.coe_unitOfCoprime,
        ZMod.cast_natCast χ.conductor_dvd_level n]

omit [NeZero q] in
/-- An ambient character vanishes on every integer not coprime to its level. -/
theorem ambient_eq_zero_of_not_coprime
    (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : ¬ n.Coprime q) :
    χ n = 0 := by
  apply χ.map_nonunit
  simpa only [ZMod.isUnit_iff_coprime] using hn

/-- A finite character-twisted von Mangoldt sum. -/
def twistedMangoldtSum (χ : DirichletCharacter ℂ q) (S : Finset ℕ) : ℂ :=
  ∑ n ∈ S, χ n * (ArithmeticFunction.vonMangoldt n : ℂ)

/-- The exact finite correction introduced when an ambient character is
replaced by its primitive inducer.  It is supported precisely on integers in
the chosen set that are not coprime to the ambient level; no asymptotic estimate
is built into the definition. -/
def imprimitiveMangoldtCorrection
    (χ : DirichletCharacter ℂ q) (S : Finset ℕ) : ℂ := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact ∑ n ∈ S.filter (fun n => ¬ n.Coprime q),
    χ.primitiveCharacter n * (ArithmeticFunction.vonMangoldt n : ℂ)

/-- Exact primitive/imprimitive transport for a finite twisted Mangoldt sum.
This is the algebra behind the paper's statement that changing to the inducing
character costs only the missing Euler factors. -/
theorem twistedMangoldtSum_eq_primitive_sub_correction
    (χ : DirichletCharacter ℂ q) (S : Finset ℕ) :
    twistedMangoldtSum χ S =
      twistedMangoldtSum χ.primitiveCharacter S -
        imprimitiveMangoldtCorrection χ S := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  classical
  simp only [twistedMangoldtSum, imprimitiveMangoldtCorrection]
  let f : ℕ → ℂ := fun n =>
    χ n * (ArithmeticFunction.vonMangoldt n : ℂ)
  let g : ℕ → ℂ := fun n =>
    χ.primitiveCharacter n * (ArithmeticFunction.vonMangoldt n : ℂ)
  have hgood :
      ∑ n ∈ S.filter (fun n => n.Coprime q), f n =
        ∑ n ∈ S.filter (fun n => n.Coprime q), g n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_filter] at hn
    simp only [f, g, ambient_eq_primitive_of_coprime χ hn.2]
  have hbad :
      ∑ n ∈ S.filter (fun n => ¬ n.Coprime q), f n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_filter] at hn
    simp only [f, ambient_eq_zero_of_not_coprime χ hn.2, zero_mul]
  change (∑ n ∈ S, f n) = (∑ n ∈ S, g n) -
    ∑ n ∈ S.filter (fun n => ¬ n.Coprime q), g n
  rw [← Finset.sum_filter_add_sum_filter_not S (fun n => n.Coprime q) f,
    ← Finset.sum_filter_add_sum_filter_not S (fun n => n.Coprime q) g,
    hgood, hbad]
  ring

/-- The primitive/imprimitive correction is bounded by its literal bad-factor
von Mangoldt mass.  This cleanly separates the finite correction from the
still-unformalized `O(log q * log X)` estimate used in the paper. -/
theorem norm_imprimitiveMangoldtCorrection_le
    (χ : DirichletCharacter ℂ q) (S : Finset ℕ) :
    ‖imprimitiveMangoldtCorrection χ S‖ ≤
      ∑ n ∈ S.filter (fun n => ¬ n.Coprime q),
        ArithmeticFunction.vonMangoldt n := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  classical
  unfold imprimitiveMangoldtCorrection
  calc
    ‖∑ n ∈ S.filter (fun n => ¬ n.Coprime q),
        χ.primitiveCharacter n *
          (ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤
        ∑ n ∈ S.filter (fun n => ¬ n.Coprime q),
          ‖χ.primitiveCharacter n *
            (ArithmeticFunction.vonMangoldt n : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ S.filter (fun n => ¬ n.Coprime q),
        ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
        (χ.primitiveCharacter.norm_le_one n)

/-- Summing the missing-Euler-factor corrections over all characters costs at
most the same bad-factor Mangoldt mass for each character. -/
theorem norm_sum_imprimitiveMangoldtCorrections_le
    (a : ZMod q) (S : Finset ℕ) :
    ‖∑ χ : DirichletCharacter ℂ q,
        χ a * imprimitiveMangoldtCorrection χ S‖ ≤
      ∑ _χ : DirichletCharacter ℂ q,
        ∑ n ∈ S.filter (fun n => ¬ n.Coprime q),
          ArithmeticFunction.vonMangoldt n := by
  classical
  calc
    ‖∑ χ : DirichletCharacter ℂ q,
        χ a * imprimitiveMangoldtCorrection χ S‖ ≤
        ∑ χ : DirichletCharacter ℂ q,
          ‖χ a * imprimitiveMangoldtCorrection χ S‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _χ : DirichletCharacter ℂ q,
        ∑ n ∈ S.filter (fun n => ¬ n.Coprime q),
          ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum
      intro χ hχ
      rw [norm_mul]
      calc
        ‖χ a‖ * ‖imprimitiveMangoldtCorrection χ S‖ ≤
            1 * ‖imprimitiveMangoldtCorrection χ S‖ :=
          mul_le_mul_of_nonneg_right (χ.norm_le_one a) (norm_nonneg _)
        _ ≤ 1 * ∑ n ∈ S.filter (fun n => ¬ n.Coprime q),
            ArithmeticFunction.vonMangoldt n :=
          mul_le_mul_of_nonneg_left
            (norm_imprimitiveMangoldtCorrection_le χ S) zero_le_one
        _ = ∑ n ∈ S.filter (fun n => ¬ n.Coprime q),
            ArithmeticFunction.vonMangoldt n := one_mul _

/-- After the character projector's `1 / φ(q)` normalization, summing the
primitive/imprimitive corrections causes no character-family loss at all: it
is bounded by one copy of the literal bad-factor Mangoldt mass. -/
theorem norm_normalized_imprimitiveMangoldtCorrections_le
    (a : ZMod q) (S : Finset ℕ) :
    ‖(q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          χ a * imprimitiveMangoldtCorrection χ S‖ ≤
      ∑ n ∈ S.filter (fun n => ¬ n.Coprime q),
        ArithmeticFunction.vonMangoldt n := by
  classical
  let B : ℝ := ∑ n ∈ S.filter (fun n => ¬ n.Coprime q),
    ArithmeticFunction.vonMangoldt n
  have hsum :
      ‖∑ χ : DirichletCharacter ℂ q,
          χ a * imprimitiveMangoldtCorrection χ S‖ ≤
        (q.totient : ℝ) * B := by
    calc
      ‖∑ χ : DirichletCharacter ℂ q,
          χ a * imprimitiveMangoldtCorrection χ S‖ ≤
          ∑ _χ : DirichletCharacter ℂ q, B := by
        simpa only [B] using norm_sum_imprimitiveMangoldtCorrections_le a S
      _ = (Fintype.card (DirichletCharacter ℂ q) : ℝ) * B := by simp
      _ = (q.totient : ℝ) * B := by
        rw [← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne'
  calc
    ‖(q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          χ a * imprimitiveMangoldtCorrection χ S‖ =
        (q.totient : ℝ)⁻¹ *
          ‖∑ χ : DirichletCharacter ℂ q,
            χ a * imprimitiveMangoldtCorrection χ S‖ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (q.totient : ℝ)⁻¹ * ((q.totient : ℝ) * B) := by
      exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = B := by field_simp

/-- The exact short-interval residue-class projector after replacing every
ambient twisted Mangoldt sum by its primitive inducer and subtracting the
missing-Euler-factor correction. -/
theorem residueClassWindow_eq_sum_primitive_sub_corrections
    {a : ZMod q} (ha : IsUnit a) (m n : ℕ) :
    residueClassWindow a m n =
      (q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          χ a⁻¹ *
            (twistedMangoldtSum χ.primitiveCharacter (Finset.Ioc m n) -
              imprimitiveMangoldtCorrection χ (Finset.Ioc m n)) := by
  rw [residueClassWindow_eq_sum_characters ha]
  congr 1
  apply Finset.sum_congr rfl
  intro χ hχ
  congr 1
  exact twistedMangoldtSum_eq_primitive_sub_correction χ (Finset.Ioc m n)

/-- Exact missing-Euler-factor formula for each imprimitive ambient character. -/
theorem LSeries_eq_primitive_mul_eulerFactors
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => χ n) s =
      LSeries (fun n => χ.primitiveCharacter n) s *
        ∏ p ∈ q.primeFactors,
          (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  simpa only [χ.changeLevel_primitiveCharacter] using
    (DirichletCharacter.LSeries_changeLevel
      χ.conductor_dvd_level χ.primitiveCharacter hs)

end CharacterExpansion

section FiniteExplicitFormulaAlgebra

/-- The regularized contribution `(t^rho - 1) / rho` used in explicit formulas. -/
def regularizedZeroTerm (t : ℝ) (ρ : ℂ) : ℂ :=
  (Complex.cpow (t : ℂ) ρ - 1) / ρ

/-- A finite truncated explicit-formula model, with an arbitrary remainder. -/
def truncatedExplicitModel
    (δ : ℂ) (zeros : Finset ℂ) (remainder : ℝ → ℂ) (t : ℝ) : ℂ :=
  δ * t - ∑ ρ ∈ zeros, regularizedZeroTerm t ρ + remainder t

/--
Subtracting the same finite truncation at both endpoints cancels the
regularizing constants exactly.  This is algebra only; it does not assert an
explicit formula or the existence, location, or multiplicity of L-function
zeros.
-/
theorem truncatedExplicitModel_interval
    (δ : ℂ) (zeros : Finset ℂ) (remainder : ℝ → ℂ) (x Y : ℝ) :
    truncatedExplicitModel δ zeros remainder (x + Y) -
        truncatedExplicitModel δ zeros remainder x =
      δ * Y -
        ∑ ρ ∈ zeros,
          (Complex.cpow ((x + Y : ℝ) : ℂ) ρ -
              Complex.cpow (x : ℂ) ρ) / ρ +
        (remainder (x + Y) - remainder x) := by
  classical
  have hterm (ρ : ℂ) :
      regularizedZeroTerm (x + Y) ρ - regularizedZeroTerm x ρ =
        (Complex.cpow ((x + Y : ℝ) : ℂ) ρ -
          Complex.cpow (x : ℂ) ρ) / ρ := by
    simp only [regularizedZeroTerm, div_eq_mul_inv]
    ring
  calc
    truncatedExplicitModel δ zeros remainder (x + Y) -
        truncatedExplicitModel δ zeros remainder x =
      δ * Y -
          ((∑ ρ ∈ zeros, regularizedZeroTerm (x + Y) ρ) -
            ∑ ρ ∈ zeros, regularizedZeroTerm x ρ) +
        (remainder (x + Y) - remainder x) := by
          simp only [truncatedExplicitModel]
          push_cast
          ring
    _ = δ * Y -
          ∑ ρ ∈ zeros,
            (Complex.cpow ((x + Y : ℝ) : ℂ) ρ -
                Complex.cpow (x : ℂ) ρ) / ρ +
          (remainder (x + Y) - remainder x) := by
            congr 2
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro ρ _
            exact hterm ρ

end FiniteExplicitFormulaAlgebra

end
end APFoundation
