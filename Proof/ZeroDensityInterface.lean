import ZeroDensityArithmetic
import DirichletZeros
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# The certified interface around the missing analytic zero-density input

The zero count below is the literal compact divisor of mathlib's regularized
Dirichlet `L`-function, with analytic multiplicity. The theorems prove what
follows once a genuine fixed-character density theorem supplies the only
analytic estimate premise.
-/

namespace ZeroDensityInterface

open scoped BigOperators
open ZeroDensityArithmetic
open DirichletZeros

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The number of ambient characters is at most the ambient modulus. -/
theorem card_dirichletCharacters_le_level :
    Fintype.card (DirichletCharacter ℂ q) ≤ q := by
  rw [← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  exact Nat.totient_le q

/-- The primitive conductor inducing an ambient character divides, hence is at
most, the ambient level. -/
theorem conductor_le_level (χ : DirichletCharacter ℂ q) :
    χ.conductor ≤ q := by
  exact Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level

/-- Consequently a polylog bound for the ambient modulus is also a polylog
bound for every inducing conductor. -/
theorem conductor_le_polylog (χ : DirichletCharacter ℂ q)
    {X K : ℝ} (hq : (q : ℝ) ≤ Real.rpow (Real.log X) K) :
    (χ.conductor : ℝ) ≤ Real.rpow (Real.log X) K := by
  calc
    (χ.conductor : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast conductor_le_level χ
    _ ≤ Real.rpow (Real.log X) K := hq

/-- Mathlib already proves analytic continuation of change-of-level: away from
the possible principal pole, an ambient `L`-function is the primitive inducing
`L`-function times its finite Euler correction. -/
theorem LFunction_eq_primitive_mul_eulerFactors
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] {s : ℂ}
    (hs : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1) :
    DirichletCharacter.LFunction χ s =
      DirichletCharacter.LFunction χ.primitiveCharacter s *
        ∏ p ∈ q.primeFactors,
          (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) := by
  simpa only [χ.changeLevel_primitiveCharacter] using
    (DirichletCharacter.LFunction_changeLevel
      χ.conductor_dvd_level χ.primitiveCharacter hs)

/-- The total number of characters in all levels `q ≤ Q` is bounded by the
elementary `Q(Q+1)` envelope. -/
theorem sum_totients_upto_le (Q : ℕ) :
    (∑ q ∈ Finset.range (Q + 1), q.totient) ≤ (Q + 1) * Q := by
  calc
    (∑ q ∈ Finset.range (Q + 1), q.totient) ≤
        ∑ _q ∈ Finset.range (Q + 1), Q := by
      apply Finset.sum_le_sum
      intro n hn
      exact (Nat.totient_le n).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
    _ = (Q + 1) * Q := by simp

/-- Left endpoint of mesh cell `j`. -/
def meshPoint (δ : ℝ) (j : ℕ) : ℝ :=
  1 / 2 + δ + j * δ

/-- Enough cells to cover `[1/2+δ, 4/5]`. -/
def meshCellCount (δ : ℝ) : ℕ :=
  ⌊((3 / 10) - δ) / δ⌋₊ + 1

/-- Every point in the compact density range lies in an explicit half-open
mesh cell. -/
theorem exists_mesh_cell {δ σ : ℝ} (hδ : 0 < δ)
    (hσlow : 1 / 2 + δ ≤ σ) (hσhigh : σ ≤ 4 / 5) :
    ∃ j ∈ Finset.range (meshCellCount δ),
      meshPoint δ j ≤ σ ∧ σ < meshPoint δ j + δ := by
  let y : ℝ := (σ - (1 / 2 + δ)) / δ
  let R : ℝ := ((3 / 10) - δ) / δ
  have hy0 : 0 ≤ y := div_nonneg (sub_nonneg.mpr hσlow) hδ.le
  have hyR : y ≤ R := by
    dsimp [y, R]
    apply (div_le_div_iff_of_pos_right hδ).2
    linarith
  let j : ℕ := ⌊y⌋₊
  have hjR : j ≤ ⌊R⌋₊ := Nat.floor_mono hyR
  have hjmem : j ∈ Finset.range (meshCellCount δ) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le hjR
  refine ⟨j, hjmem, ?_, ?_⟩
  · have hjy : (j : ℝ) ≤ y := Nat.floor_le hy0
    have hmul : (j : ℝ) * δ ≤ σ - (1 / 2 + δ) := by
      exact (le_div_iff₀ hδ).mp hjy
    dsimp [meshPoint]
    linarith
  · have hyj : y < (j : ℝ) + 1 := by
      simpa [j] using (Nat.lt_floor_add_one y)
    have hmul : σ - (1 / 2 + δ) < ((j : ℝ) + 1) * δ := by
      exact (div_lt_iff₀ hδ).mp hyj
    dsimp [meshPoint]
    linarith

/-- Every left endpoint in the explicit mesh stays inside the compact strip. -/
theorem meshPoint_le_four_fifths {δ : ℝ} (hδ : 0 < δ)
    (hδcap : δ ≤ 3 / 10) {j : ℕ} (hj : j < meshCellCount δ) :
    meshPoint δ j ≤ 4 / 5 := by
  have hR0 : 0 ≤ ((3 / 10 : ℝ) - δ) / δ :=
    div_nonneg (sub_nonneg.mpr hδcap) hδ.le
  have hjfloor : j ≤ ⌊((3 / 10 : ℝ) - δ) / δ⌋₊ := by
    simpa [meshCellCount] using Nat.le_of_lt_succ hj
  have hfloor :
      (⌊((3 / 10 : ℝ) - δ) / δ⌋₊ : ℝ) ≤
        ((3 / 10 : ℝ) - δ) / δ := Nat.floor_le hR0
  have hjdiv : (j : ℝ) ≤ ((3 / 10 : ℝ) - δ) / δ := by
    exact (Nat.cast_le.mpr hjfloor).trans hfloor
  have hjmul : (j : ℝ) * δ ≤ (3 / 10 : ℝ) - δ :=
    (le_div_iff₀ hδ).mp hjdiv
  dsimp [meshPoint]
  linarith

/-! ## The actual divisor-backed zero mass -/

/-- Zeros of `χ` in one half-open mesh cell, taken from the actual compact
divisor support at the cell's left endpoint. -/
def analyticCellSupport (χ : DirichletCharacter ℂ q) (T δ : ℝ) (j : ℕ) :
    Finset ℂ :=
  (zeroSupport χ (meshPoint δ j) T).filter fun ρ =>
    ρ.re < meshPoint δ j + δ

/-- The literal `X^{2(β-1)}` mass, with analytic multiplicity. -/
def analyticCellMass (χ : DirichletCharacter ℂ q)
    (X T δ : ℝ) (j : ℕ) : ℝ :=
  ∑ ρ ∈ analyticCellSupport χ T δ j,
    (zeroMultiplicity χ (meshPoint δ j) T ρ : ℝ) *
      Real.rpow X (2 * (ρ.re - 1))

/-- The actual divisor-backed mass in one cell is controlled by the actual
multiplicity-aware zero count at the cell's left endpoint. -/
theorem analyticCellMass_le_count_rpow (χ : DirichletCharacter ℂ q)
    {X T δ : ℝ} (j : ℕ) (hX : 1 ≤ X) :
    analyticCellMass χ X T δ j ≤
      (dirichletZeroCount χ (meshPoint δ j) T : ℝ) *
        Real.rpow X (2 * (meshPoint δ j + δ - 1)) := by
  let R : ℝ := Real.rpow X (2 * (meshPoint δ j + δ - 1))
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hsum :
      (∑ ρ ∈ analyticCellSupport χ T δ j,
          zeroMultiplicity χ (meshPoint δ j) T ρ) ≤
        dirichletZeroCount χ (meshPoint δ j) T := by
    unfold analyticCellSupport dirichletZeroCount
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro ρ _hρ _hnmem
      exact Nat.zero_le _
  calc
    analyticCellMass χ X T δ j ≤
        ∑ ρ ∈ analyticCellSupport χ T δ j,
          (zeroMultiplicity χ (meshPoint δ j) T ρ : ℝ) * R := by
      unfold analyticCellMass
      apply Finset.sum_le_sum
      intro ρ hρ
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Real.rpow_le_rpow_of_exponent_le hX
      have hρre := (Finset.mem_filter.mp hρ).2
      linarith
    _ = ((∑ ρ ∈ analyticCellSupport χ T δ j,
          zeroMultiplicity χ (meshPoint δ j) T ρ : ℕ) : ℝ) * R := by
      push_cast
      rw [Finset.sum_mul]
    _ ≤ (dirichletZeroCount χ (meshPoint δ j) T : ℝ) * R := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hsum
      · dsimp [R]
        exact Real.rpow_nonneg hXpos.le _

/-- The core fixed-character implication, now stated for the divisor-backed
Dirichlet zero count rather than arbitrary finite data. -/
theorem analytic_gm_count_implies_power_saving
    (χ : DirichletCharacter ℂ q) {ε δ X T C : ℝ} (j : ℕ)
    (hε : 0 < ε) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ densityReserve ε / 100)
    (hσ : meshPoint δ j ≤ 4 / 5)
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hdensity :
      (dirichletZeroCount χ (meshPoint δ j) T : ℝ) ≤
        C * Real.rpow X
          (uniformCoeff * heightExponent ε *
              (1 - meshPoint δ j) + densityReserve ε / 100)) :
    analyticCellMass χ X T δ j ≤
      C * Real.rpow X (-(17 / 100) * densityReserve ε) := by
  let a := uniformCoeff * heightExponent ε *
    (1 - meshPoint δ j) + densityReserve ε / 100
  let b := 2 * (meshPoint δ j + δ - 1)
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hmass := analyticCellMass_le_count_rpow χ (T := T) (δ := δ) j hX
  have hbnonneg : 0 ≤ Real.rpow X b := Real.rpow_nonneg hXpos.le b
  calc
    analyticCellMass χ X T δ j ≤
        (dirichletZeroCount χ (meshPoint δ j) T : ℝ) *
          Real.rpow X b := hmass
    _ ≤ (C * Real.rpow X a) * Real.rpow X b :=
      mul_le_mul_of_nonneg_right hdensity hbnonneg
    _ = C * Real.rpow X (a + b) := by
      rw [mul_assoc]
      congr 1
      exact (Real.rpow_add hXpos a b).symm
    _ ≤ C * Real.rpow X (-(17 / 100) * densityReserve ε) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow_of_exponent_le hX
      dsimp [a, b]
      simpa [add_comm, add_left_comm, add_assoc] using
        compactMeshExponent_bound hε hδ0 hδ hσ

/-- Divisor-backed cell mass for the primitive inducer of an ambient
character. The `NeZero` conductor instance is installed internally. -/
def primitiveAnalyticCellMass (χ : DirichletCharacter ℂ q)
    (X T δ : ℝ) (j : ℕ) : ℝ := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact analyticCellMass χ.primitiveCharacter X T δ j

/-- Finite aggregation over all ambient characters and mesh cells. This is
where applying a fixed-character theorem separately costs exactly one
totient and one finite mesh cardinality. -/
theorem sum_cells_over_characters_le
    (J : ℕ) (F : DirichletCharacter ℂ q → ℕ → ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ χ j, j < J → 0 ≤ F χ j ∧ F χ j ≤ M) :
    (∑ χ : DirichletCharacter ℂ q, ∑ j ∈ Finset.range J, F χ j) ≤
      (q : ℝ) * J * M := by
  have hinner (χ : DirichletCharacter ℂ q) :
      (∑ j ∈ Finset.range J, F χ j) ≤ J * M := by
    calc
      (∑ j ∈ Finset.range J, F χ j) ≤
          ∑ _j ∈ Finset.range J, M := by
        apply Finset.sum_le_sum
        intro j hj
        exact (hF χ j (Finset.mem_range.mp hj)).2
      _ = J * M := by simp
  calc
    (∑ χ : DirichletCharacter ℂ q, ∑ j ∈ Finset.range J, F χ j) ≤
        ∑ _χ : DirichletCharacter ℂ q, J * M := by
      apply Finset.sum_le_sum
      intro χ _hχ
      exact hinner χ
    _ = (Fintype.card (DirichletCharacter ℂ q) : ℝ) * (J * M) := by simp
    _ ≤ (q : ℝ) * (J * M) := by
      gcongr
      exact_mod_cast card_dirichletCharacters_le_level (q := q)
    _ = (q : ℝ) * J * M := by ring

/-- Applying the fixed-character analytic input separately to each ambient
character and mesh cell. The premise is the only unformalized analytic input;
the zero count and mass in the conclusion are actual L-function divisors. -/
theorem fixedModulus_actualZeros_imply_weighted_bound
    {ε δ X T C : ℝ}
    (hε : 0 < ε) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ densityReserve ε / 100)
    (hδpos : 0 < δ) (hδcap : δ ≤ 3 / 10)
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hdensity : ∀ (χ : DirichletCharacter ℂ q) j,
      j < meshCellCount δ →
      (primitiveDirichletZeroCount χ (meshPoint δ j) T : ℝ) ≤
        C * Real.rpow X
          (uniformCoeff * heightExponent ε *
              (1 - meshPoint δ j) + densityReserve ε / 100)) :
    (∑ χ : DirichletCharacter ℂ q,
        ∑ j ∈ Finset.range (meshCellCount δ),
          primitiveAnalyticCellMass χ X T δ j) ≤
      (q : ℝ) * meshCellCount δ *
        (C * Real.rpow X (-(17 / 100) * densityReserve ε)) := by
  apply sum_cells_over_characters_le
  · exact mul_nonneg hC
      (Real.rpow_nonneg (zero_le_one.trans hX)
        (-(17 / 100) * densityReserve ε))
  · intro χ j hj
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    constructor
    · unfold primitiveAnalyticCellMass analyticCellMass
      apply Finset.sum_nonneg
      intro ρ hρ
      exact mul_nonneg (Nat.cast_nonneg _)
        (Real.rpow_nonneg (zero_le_one.trans hX) _)
    · simpa only [primitiveAnalyticCellMass,
          primitiveDirichletZeroCount] using
        (analytic_gm_count_implies_power_saving
          (χ := χ.primitiveCharacter) j hε hδ0 hδ
          (meshPoint_le_four_fifths hδpos hδcap hj) hX hC
          (hdensity χ j hj))

/-- The MAP threshold itself is the exact positive reserve proved above. -/
theorem map_threshold_reserve {ε : ℝ} (hε : 0 < ε) :
    0 < (17 / 100) * densityReserve ε ∧
      (17 / 100) * densityReserve ε = (51 / 260) * ε := by
  constructor
  · positivity [densityReserve_pos hε]
  · rw [densityReserve_eq]
    ring

end
end ZeroDensityInterface
