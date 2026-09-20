import FordCollisionThreeHolder
import FordBoundaryEnergyMoments
import FordBoundaryAlias

open scoped BigOperators ZMod ComplexConjugate

namespace FordCollisionThreeMoments

open FordBoundaryCountGeometry
open FordBoundaryPinnedCross
open FordBoundaryEnergyMoments
open FordBoundaryWeightedHolder
open MAPFordBoundaryCrossFourier
open FordCollisionThreeHolder

noncomputable section

private theorem modulus_diff_bound
    {R : Type*} [Fintype R] {k : ℕ}
    (freq : R → Fin k → ℤ) (x y : R) (j : Fin k) :
    |freq x j - freq y j| < (FordBoundaryAlias.modulus freq : ℤ) := by
  classical
  let row : R → ℕ := fun r => ∑ j', (freq r j').natAbs
  let total : ℕ := ∑ r', row r'
  have hx1 : (freq x j).natAbs ≤ row x := by
    dsimp [row]
    exact Finset.single_le_sum (f := fun j' => (freq x j').natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hy1 : (freq y j).natAbs ≤ row y := by
    dsimp [row]
    exact Finset.single_le_sum (f := fun j' => (freq y j').natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hxy : (freq x j - freq y j).natAbs ≤ total := by
    by_cases hxy : x = y
    · subst y
      simp [total]
    · have hpair : (freq x j).natAbs + (freq y j).natAbs ≤ row x + row y :=
        add_le_add hx1 hy1
      have hsum : row x + row y =
          ∑ r' ∈ (insert x ({y} : Finset R)), row r' := by
        rw [Finset.sum_insert]
        · simp [hxy, row]
        · simp [hxy]
      have hsubset : (∑ r' ∈ (insert x ({y} : Finset R)), row r') ≤
          ∑ r' ∈ (Finset.univ : Finset R), row r' := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.subset_univ _
        · intro r' hr' hnot
          exact Nat.zero_le _
      exact (Int.natAbs_sub_le _ _).trans (hpair.trans (by simpa [total, hsum] using hsubset))
  have hnat : (freq x j - freq y j).natAbs < FordBoundaryAlias.modulus freq := by
    unfold FordBoundaryAlias.modulus
    simpa [row, total] using (show (freq x j - freq y j).natAbs < 1 + total by omega)
  rw [← Int.natCast_natAbs]
  exact_mod_cast hnat

theorem exists_common_modulus_three
    {R S T : Type*} [Fintype R] [Fintype S] [Fintype T] {k : ℕ}
    (f : R → Fin k → ℤ) (g : S → Fin k → ℤ) (h : T → Fin k → ℤ) :
    ∃ L : ℕ, 0 < L ∧
      (∀ r r' j, |f r j - f r' j| < (L : ℤ)) ∧
      (∀ s s' j, |g s j - g s' j| < (L : ℤ)) ∧
      (∀ t t' j, |h t j - h t' j| < (L : ℤ)) := by
  let all : R ⊕ S ⊕ T → Fin k → ℤ := fun x =>
    match x with
    | Sum.inl r => f r
    | Sum.inr (Sum.inl s) => g s
    | Sum.inr (Sum.inr t) => h t
  refine ⟨FordBoundaryAlias.modulus all, FordBoundaryAlias.modulus_pos all, ?_, ?_, ?_⟩
  · intro r r' j
    exact modulus_diff_bound all (Sum.inl r) (Sum.inl r') j
  · intro s s' j
    exact modulus_diff_bound all (Sum.inr (Sum.inl s)) (Sum.inr (Sum.inl s')) j
  · intro t t' j
    exact modulus_diff_bound all (Sum.inr (Sum.inr t)) (Sum.inr (Sum.inr t')) j

def doubled {U : Type*} {k : ℕ} (g : U → Fin k → ℤ) : U → Fin k → ℤ :=
  fun u j => 2 * g u j

private theorem block_nonneg (L k : ℕ) [NeZero L] {A : Type*} [Fintype A]
    (f : A → Fin k → ℤ) (alpha : Fin k → ZMod L) :
    0 ≤ ‖fordBoundaryBlock f alpha‖ := norm_nonneg _

private theorem block_sq_nonneg (L k : ℕ) [NeZero L] {A : Type*} [Fintype A]
    (f : A → Fin k → ℤ) (alpha : Fin k → ZMod L) :
    0 ≤ ‖fordBoundaryBlock f alpha‖ ^ 2 := sq_nonneg _

theorem finite_energy_three_factor
    {A U Pin : Type*} [Fintype A] [Fintype U] [Fintype Pin]
    {L k : ℕ} [NeZero L]
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (hk : 2 ≤ k)
    (hbase : ∀ a a' j, |f a j - f a' j| < (L : ℤ))
    (henergy : ∀ r r' j,
      |wordFreq f g k r j - wordFreq f g k r' j| < (L : ℤ))
    (henergy2 : ∀ r r' j,
      |wordFreq f (doubled g) k r j - wordFreq f (doubled g) k r' j| < (L : ℤ))
    (hpin : (Fintype.card Pin : ℝ) ≤
      fordThreeMoment
        (fun alpha : Fin k → ZMod L => ‖fordBoundaryBlock f alpha‖ ^ 2)
        (fun alpha : Fin k → ZMod L => ‖fordBoundaryBlock (doubled g) alpha‖)
        (fun alpha : Fin k → ZMod L => ‖fordBoundaryBlock g alpha‖) k) :
    (Fintype.card Pin : ℝ) ^ (2 * k) ≤
      Fintype.card (EnergyZero f (doubled g) k) *
        (Fintype.card (EnergyZero f g k) : ℝ) ^ (2 * k - 2) *
          Fintype.card (BaseZero f) := by
  let w : (Fin k → ZMod L) → ℝ :=
    fun alpha => ‖fordBoundaryBlock f alpha‖ ^ 2
  let a : (Fin k → ZMod L) → ℝ :=
    fun alpha => ‖fordBoundaryBlock (doubled g) alpha‖
  let b : (Fin k → ZMod L) → ℝ :=
    fun alpha => ‖fordBoundaryBlock g alpha‖
  have hholder := fordThreeMoment_le_geometric_of_nonneg w a b k hk
    (fun alpha => sq_nonneg _) (fun alpha => norm_nonneg _) (fun alpha => norm_nonneg _)
  have hP : (Fintype.card Pin : ℝ) ≤
      fordThreeA w a k ^ (1 / (2 * k : ℝ)) *
        fordThreeE w b k ^ ((k - 1 : ℝ) / k) *
          fordThreeB w ^ (1 / (2 * k : ℝ)) := by
    exact hpin.trans hholder
  have hbaseCard := base_card_eq_fordB f hbase
  have henergyCard := energy_card_eq_fordA f g henergy
  have henergy2Card := energy_card_eq_fordA f (doubled g) henergy2
  have hA : fordThreeA w a k = (Fintype.card (EnergyZero f (doubled g) k) : ℝ) := by
    simpa [w, a, fordThreeA, fordThreeAvg, fordA, fordAvg] using henergy2Card.symm
  have hE : fordThreeE w b k = (Fintype.card (EnergyZero f g k) : ℝ) := by
    simpa [w, b, fordThreeE, fordThreeAvg, fordA, fordAvg] using henergyCard.symm
  have hB : fordThreeB w = (Fintype.card (BaseZero f) : ℝ) := by
    simpa [w, fordThreeB, fordThreeAvg, fordAvg] using hbaseCard.symm
  have hscalar := scalar_three_factor_power hk
    (P := (Fintype.card Pin : ℝ))
    (A := fordThreeA w a k) (E := fordThreeE w b k) (B := fordThreeB w)
    (by positivity) (by rw [hA]; positivity) (by rw [hE]; positivity)
    (by rw [hB]; positivity) hP
  simpa [hA, hE, hB] using hscalar

end
end FordCollisionThreeMoments

#print axioms FordCollisionThreeMoments.finite_energy_three_factor
#print axioms FordCollisionThreeMoments.exists_common_modulus_three
