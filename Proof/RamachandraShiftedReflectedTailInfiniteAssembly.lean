import RamachandraShiftedReflectedTailAssembly
import RamachandraShiftedFunctionalEquationBridge

/-!
# Infinite dyadic assembly of the reflected tail

The finite tail truncation is already decomposed into source shells in
`RamachandraShiftedReflectedTailAssembly`.  Here we close the corresponding
infinite identity.  The exact standard cells `(2^j,2^(j+1)]` partition every
natural number at least two, and absolute convergence on the long line
justifies regrouping the reflected Dirichlet series by those cells.
-/

namespace RamachandraShiftedReflectedTailInfiniteAssembly

open scoped BigOperators LSeries.notation
open Complex
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedFunctionalEquationBridge
open MRTLemma215DyadicPartition
open MAPHBPerronSourceData
open MAPMRTLemma210OrthogonalityReduction
open BHPRamachandraMeanValueFromDyadicAFE
open MontgomeryVaughanFiniteReduction
open RamachandraShiftedReflectedSeries
open BHPAllCharacterDyadicBudget

set_option maxHeartbeats 800000

noncomputable section

/-- The sigma type of all standard positive dyadic cells. -/
abbrev ReflectedDyadicIndex :=
  Σ j : ℕ, {n : ℕ // n ∈ dyadicSupport (2 ^ j)}

/-- Forgetting the shell label maps the dyadic sigma type to the naturals
outside `{0,1}`. -/
def reflectedDyadicIndexToNatCompl :
    ReflectedDyadicIndex → {
      n : ℕ // n ∉ ({0, 1} : Finset ℕ) } := fun a =>
  ⟨a.2.1, by
    have hn : 2 ^ a.1 < a.2.1 := (Finset.mem_Ioc.mp a.2.2).1
    have hpow : 1 ≤ 2 ^ a.1 := one_le_pow₀ (by norm_num)
    have hn2 : 2 ≤ a.2.1 := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega⟩

theorem reflectedDyadicIndexToNatCompl_injective :
    Function.Injective reflectedDyadicIndexToNatCompl := by
  rintro ⟨j, n, hn⟩ ⟨k, m, hm⟩ h
  have hnm : n = m := congrArg Subtype.val h
  subst m
  have hn2 : 2 ≤ n := by
    have hlo : 2 ^ j < n := (Finset.mem_Ioc.mp hn).1
    have hp : 1 ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    omega
  have hj : (n - 1).log2 = j :=
    (log2_sub_one_eq_iff_mem_Ioc hn2).2 hn
  have hk : (n - 1).log2 = k :=
    (log2_sub_one_eq_iff_mem_Ioc hn2).2 hm
  have hjk : j = k := hj.symm.trans hk
  cases hjk
  rfl

theorem reflectedDyadicIndexToNatCompl_surjective :
    Function.Surjective reflectedDyadicIndexToNatCompl := by
  rintro ⟨n, hn⟩
  have hn01 : n ≠ 0 ∧ n ≠ 1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hn
  have hn2 : 2 ≤ n := by omega
  let j : ℕ := (n - 1).log2
  have hmem : n ∈ dyadicSupport (2 ^ j) :=
    (log2_sub_one_eq_iff_mem_Ioc hn2).1 rfl
  refine ⟨⟨j, ⟨n, hmem⟩⟩, ?_⟩
  rfl

/-- Exact equivalence between all dyadic cells and the naturals at least two. -/
def reflectedDyadicIndexEquivNatCompl :
    ReflectedDyadicIndex ≃ {n : ℕ // n ∉ ({0, 1} : Finset ℕ)} :=
  Equiv.ofBijective reflectedDyadicIndexToNatCompl
    ⟨reflectedDyadicIndexToNatCompl_injective,
      reflectedDyadicIndexToNatCompl_surjective⟩

/-- Literal infinite reflected-tail shell on the standard dyadic cell. -/
def ramachandraReflectedTailDyadicShell
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (X : ℝ) (z : ℂ) (j : ℕ) : ℂ :=
  ∑ n ∈ dyadicSupport (2 ^ j),
    if X < n then ramachandraReflectedTerm psi z n else 0

/-- Character-independent coefficient of one infinite tail shell after the
inverse character and the `t` phase have been extracted. -/
def reflectedTailInfiniteShellCoeff
    (X sigma u v : ℝ) (n : ℕ) : ℂ :=
  if X < n then shiftedReflectedBlockCoeff sigma u v n else 0

/-- Each literal infinite tail shell is exactly the standard dual block used
by the all-character Hilbert/orthogonality engine. -/
theorem ramachandraReflectedTailDyadicShell_eq_ramachandraDyadicBlock
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (X sigma u v t : ℝ) (j : ℕ) :
    ramachandraReflectedTailDyadicShell psi X
        (ramachandraShiftedPoint sigma t + ((u : ℂ) + v * I)) j =
      ramachandraDyadicBlock d (2 ^ j)
        (reflectedTailInfiniteShellCoeff X sigma u v) true psi t := by
  unfold ramachandraReflectedTailDyadicShell ramachandraDyadicBlock
    twistedFinitePolynomial
  simp only [if_true]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n :=
    Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
  by_cases hXn : X < n
  · rw [if_pos hXn]
    rw [reflectedTerm_eq_blockTerm psi hnpos sigma u t v]
    simp [reflectedTailInfiniteShellCoeff, hXn]
  · rw [if_neg hXn]
    simp [reflectedTailInfiniteShellCoeff, hXn]

theorem continuous_reflectedTailInfiniteShellCoeff
    (X sigma u : ℝ) (n : ℕ) :
    Continuous (fun v => reflectedTailInfiniteShellCoeff X sigma u v n) := by
  unfold reflectedTailInfiniteShellCoeff
  split_ifs
  · exact continuous_shiftedReflectedBlockCoeff sigma u n
  · fun_prop

/-- Masking by `X<n` can only decrease the exact dyadic coefficient energy. -/
theorem coefficientEnergy_reflectedTailInfiniteShellCoeff_le
    (X sigma u v : ℝ) (N : ℕ) :
    coefficientEnergy (reflectedTailInfiniteShellCoeff X sigma u v) N ≤
      coefficientEnergy (shiftedReflectedBlockCoeff sigma u v) N := by
  unfold coefficientEnergy
  apply Finset.sum_le_sum
  intro n hn
  by_cases hXn : X < n
  · simp [reflectedTailInfiniteShellCoeff, hXn]
  · simp [reflectedTailInfiniteShellCoeff, hXn]

/-- Regrouping the absolutely convergent reflected tail into its exact
infinite dyadic cells.  `X ≥ 1` removes precisely the two indices outside
the cells. -/
theorem hasSum_ramachandraReflectedTailDyadicShell
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    {X : ℝ} (hX : 1 ≤ X) {z : ℂ} (hz : 1 < (1 - z).re) :
    HasSum (ramachandraReflectedTailDyadicShell psi X z)
      (ramachandraReflectedTail psi X z) := by
  let f : ℕ → ℂ := fun n =>
    if X < n then ramachandraReflectedTerm psi z n else 0
  have hfull := summable_ramachandraReflectedTerm psi hz
  have hf : Summable f := by
    simpa [f, Set.indicator] using!
      hfull.indicator ({n : ℕ | X < (n : ℝ)} : Set ℕ)
  have hsplit := hf.sum_add_tsum_subtype_compl ({0, 1} : Finset ℕ)
  have hfzero : ∑ n ∈ ({0, 1} : Finset ℕ), f n = 0 := by
    simp [f, show ¬ X < (0 : ℝ) by linarith,
      show ¬ X < (1 : ℝ) by linarith]
  have hcomplTsum :
      (∑' n : {n : ℕ // n ∉ ({0, 1} : Finset ℕ)}, f n) =
        ramachandraReflectedTail psi X z := by
    rw [hfzero, zero_add] at hsplit
    simpa [ramachandraReflectedTail, f] using hsplit
  have hcompl : HasSum
      (fun n : {n : ℕ // n ∉ ({0, 1} : Finset ℕ)} => f n)
      (ramachandraReflectedTail psi X z) := by
    have hs : Summable
        (fun n : {n : ℕ // n ∉ ({0, 1} : Finset ℕ)} => f n) :=
      hf.comp_injective Subtype.val_injective
    rw [← hcomplTsum]
    exact hs.hasSum
  have hsigma : HasSum
      (fun a : ReflectedDyadicIndex => f a.2.1)
      (ramachandraReflectedTail psi X z) := by
    exact (reflectedDyadicIndexEquivNatCompl.hasSum_iff).2 hcompl
  have hgroup := hsigma.sigma (fun j =>
    hasSum_fintype (fun n : {n : ℕ // n ∈ dyadicSupport (2 ^ j)} => f n))
  convert hgroup using 1
  funext j
  unfold ramachandraReflectedTailDyadicShell
  rw [← Finset.sum_attach]
  rfl

theorem summable_ramachandraReflectedTailDyadicShell
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    {X : ℝ} (hX : 1 ≤ X) {z : ℂ} (hz : 1 < (1 - z).re) :
    Summable (ramachandraReflectedTailDyadicShell psi X z) :=
  (hasSum_ramachandraReflectedTailDyadicShell psi hX hz).summable

theorem tsum_ramachandraReflectedTailDyadicShell_eq
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    {X : ℝ} (hX : 1 ≤ X) {z : ℂ} (hz : 1 < (1 - z).re) :
    (∑' j : ℕ, ramachandraReflectedTailDyadicShell psi X z j) =
      ramachandraReflectedTail psi X z :=
  (hasSum_ramachandraReflectedTailDyadicShell psi hX hz).tsum_eq

end
end RamachandraShiftedReflectedTailInfiniteAssembly

#print axioms RamachandraShiftedReflectedTailInfiniteAssembly.hasSum_ramachandraReflectedTailDyadicShell
#print axioms RamachandraShiftedReflectedTailInfiniteAssembly.tsum_ramachandraReflectedTailDyadicShell_eq
