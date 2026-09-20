import GuthMaynardHeathBrownIccIocEndpointAdapter
import GuthMaynardLemma118EnergyPacking

open scoped BigOperators
noncomputable section
namespace GuthMaynardEnergy116Endpoint
open GuthMaynardRatioKernelIdentity GuthMaynardHeathBrownIccIocEndpointAdapter
open GuthMaynardLemma118

def openRatioMoment (p M : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc M (2*M), ∑ m ∈ Finset.Ioc M (2*M),
    ‖ratioDirichletKernel W ((n : ℝ)/(m : ℝ))‖^p

/-- The exact endpoint correction is bounded without comparing oscillatory
polynomials pointwise: all ratio-moment summands are nonnegative. -/
theorem closed_moment_le_open_add_endpoint (p M : ℕ) (W : Finset ℝ) :
    ratioKernelMoment p M W ≤ openRatioMoment p M W +
      (2*(M : ℝ)+1)*(W.card : ℝ)^p := by
  let f : ℕ → ℕ → ℝ := fun n m =>
    ‖ratioDirichletKernel W ((n : ℝ)/(m : ℝ))‖^p
  have heq : ratioKernelMoment p M W = openRatioMoment p M W +
      (∑ n ∈ Finset.Ioc M (2*M), f n M) +
      (∑ m ∈ Finset.Ioc M (2*M), f M m) + f M M := by
    unfold ratioKernelMoment openRatioMoment
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simp only [Icc_eq_insert_Ioc,leftEndpoint_not_mem_Ioc,not_false_eq_true,
      Finset.sum_insert,Finset.sum_add_distrib]
    dsimp [f]
    ring
  have hf (n m : ℕ) : f n m ≤ (W.card : ℝ)^p :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_ratioDirichletKernel_le_card W _) p
  have hc : (Finset.Ioc M (2*M)).card = M := by
    simp only [Nat.card_Ioc]
    omega
  have hrow : (∑ n ∈ Finset.Ioc M (2*M), f n M) ≤ (M : ℝ)*(W.card : ℝ)^p := by
    have hh := Finset.sum_le_sum (s:=Finset.Ioc M (2*M)) (fun n _ => hf n M)
    simpa only [Finset.sum_const,nsmul_eq_mul,hc] using hh
  have hcol : (∑ m ∈ Finset.Ioc M (2*M), f M m) ≤ (M : ℝ)*(W.card : ℝ)^p := by
    have hh := Finset.sum_le_sum (s:=Finset.Ioc M (2*M)) (fun m _ => hf M m)
    simpa only [Finset.sum_const,nsmul_eq_mul,hc] using hh
  rw [heq]
  nlinarith [hf M M]

/-- The closed fourth moment used by the GCD argument follows from the
open-left fourth moment with a cost already present in its first main term. -/
theorem closed_fourth_le_open_add_three (M : ℕ) (W : Finset ℝ) (hM : 1 ≤ M) :
    ratioKernelMoment 4 M W ≤ openRatioMoment 4 M W +
      3*(M : ℝ)*(W.card : ℝ)^4 := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hh := closed_moment_le_open_add_endpoint 4 M W
  apply hh.trans
  gcongr
  nlinarith

end GuthMaynardEnergy116Endpoint
#print axioms GuthMaynardEnergy116Endpoint.closed_moment_le_open_add_endpoint
#print axioms GuthMaynardEnergy116Endpoint.closed_fourth_le_open_add_three
