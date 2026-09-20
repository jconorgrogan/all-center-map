import JutilaP53PrincipalResidueEnvelope
import CGLProofDAG

/-!
# Exponential packing for one-separated ordinates

This is the deterministic fiber estimate needed to sum the off-diagonal
principal residues on Jutila p.53.
-/

namespace MAPJutilaOneSeparatedExponentialPacking

open scoped BigOperators
open CGLProofDAG

noncomputable section

def integerExponentialMass : ℝ :=
  ∑' k : ℤ, Real.exp (-|(k : ℝ)|)

theorem summable_integer_exp_neg_abs :
    Summable (fun k : ℤ => Real.exp (-|(k : ℝ)|)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · have hgeo : Summable (fun n : ℕ => (Real.exp (-1)) ^ n) := by
      apply summable_geometric_of_norm_lt_one
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      simpa only [Real.exp_zero] using
        Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num)
    convert hgeo using 1
    funext n
    rw [← Real.exp_nat_mul]
    congr 1
    simp
  · have hgeo : Summable (fun n : ℕ => (Real.exp (-1)) ^ n) := by
      apply summable_geometric_of_norm_lt_one
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      simpa only [Real.exp_zero] using
        Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num)
    convert hgeo using 1
    funext n
    rw [← Real.exp_nat_mul]
    congr 1
    simp

private theorem floor_bin_injective
    (W : Finset ℝ) (t : ℝ) (hsep : OneSeparated W) :
    Set.InjOn (fun u : ℝ => ⌊u - t⌋) (↑W : Set ℝ) := by
  intro x hx y hy heq
  have hxW : x ∈ W := by simpa using hx
  have hyW : y ∈ W := by simpa using hy
  by_contra hxy
  have hxlo : (⌊x - t⌋ : ℝ) ≤ x - t := Int.floor_le _
  have hxhi : x - t < (⌊x - t⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hylo : (⌊y - t⌋ : ℝ) ≤ y - t := Int.floor_le _
  have hyhi : y - t < (⌊y - t⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hdiff : |x - y| < 1 := by
    change ⌊x - t⌋ = ⌊y - t⌋ at heq
    rw [← heq] at hylo hyhi
    rw [abs_lt]
    constructor <;> linarith
  exact (not_lt_of_ge (hsep x hxW y hyW hxy)) hdiff

private theorem exp_neg_abs_le_floor_mass (x : ℝ) :
    Real.exp (-|x|) ≤
      Real.exp 1 * Real.exp (-|((⌊x⌋ : ℤ) : ℝ)|) := by
  have hlo : (⌊x⌋ : ℝ) ≤ x := Int.floor_le _
  have hhi : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have habs : |((⌊x⌋ : ℤ) : ℝ)| ≤ |x| + 1 := by
    rw [abs_le]
    constructor
    · have hxLower : -|x| ≤ x := neg_abs_le x
      linarith
    · have hxUpper : x ≤ |x| := le_abs_self x
      linarith
  calc
    Real.exp (-|x|) ≤ Real.exp (1 - |((⌊x⌋ : ℤ) : ℝ)|) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = Real.exp 1 * Real.exp (-|((⌊x⌋ : ℤ) : ℝ)|) := by
      rw [← Real.exp_add]
      congr 1

/-- A one-separated finite set has uniformly bounded exponential mass around
every center.  The explicit universal constant is left as its convergent
integer theta mass, avoiding any numerical approximation. -/
theorem sum_exp_neg_abs_sub_le
    (W : Finset ℝ) (t : ℝ) (hsep : OneSeparated W) :
    ∑ u ∈ W, Real.exp (-|u - t|) ≤
      Real.exp 1 * integerExponentialMass := by
  let bin : ℝ → ℤ := fun u => ⌊u - t⌋
  let f : ℤ → ℝ := fun k => Real.exp (-|(k : ℝ)|)
  have hinj : Set.InjOn bin (↑W : Set ℝ) := floor_bin_injective W t hsep
  calc
    _ ≤ ∑ u ∈ W, Real.exp 1 * f (bin u) := by
      apply Finset.sum_le_sum
      intro u hu
      simpa [bin, f] using exp_neg_abs_le_floor_mass (u - t)
    _ = ∑ k ∈ W.image bin, Real.exp 1 * f k := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑' k : ℤ, Real.exp 1 * f k := by
      apply (summable_integer_exp_neg_abs.mul_left (Real.exp 1)).sum_le_tsum
      intro k hk
      positivity
    _ = Real.exp 1 * integerExponentialMass := by
      rw [tsum_mul_left]
      rfl

end

end MAPJutilaOneSeparatedExponentialPacking

#print axioms MAPJutilaOneSeparatedExponentialPacking.summable_integer_exp_neg_abs
#print axioms MAPJutilaOneSeparatedExponentialPacking.sum_exp_neg_abs_sub_le
