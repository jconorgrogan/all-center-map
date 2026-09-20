import GuthMaynardEnergy118GCDReindex
import GuthMaynardEnergy119RoundedRange
import GuthMaynardLemma118EnergyPacking

open scoped BigOperators
noncomputable section
namespace GuthMaynardEnergy119ReducedHolder
open GuthMaynardEnergy118GCD GuthMaynardEnergy119RoundedRange
open GuthMaynardRatioKernelIdentity GuthMaynardLemma118

/-- Literal reduced coordinates embed in a rounded closed dyadic block.
No equality of the two carriers is asserted. -/
theorem reducedPairs_subset_rounded_block {N d : ℕ}
    (hN : 1 ≤ N) (hd : 1 ≤ d) (hd2 : d ≤ 2*N) :
    reducedPairs N d ⊆
      (Finset.Icc (Nat.ceil ((N : ℝ)/(d : ℝ)))
        (2*Nat.ceil ((N : ℝ)/(d : ℝ)))).product
      (Finset.Icc (Nat.ceil ((N : ℝ)/(d : ℝ)))
        (2*Nat.ceil ((N : ℝ)/(d : ℝ)))) := by
  obtain ⟨hM,hscale,hcover⟩ := ceil_dyadic_range_cover hN hd hd2
  intro p hp
  obtain ⟨hpblock,hplow,hphi,hqlow,hqhi,hcop⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpI,hqI⟩ := Finset.mem_product.mp hpblock
  exact Finset.mem_product.mpr
    ⟨hcover p.1 (Finset.mem_Icc.mp hpI).1 hplow hphi,
      hcover p.2 (Finset.mem_Icc.mp hqI).1 hqlow hqhi⟩

theorem reduced_moment_le_rounded_moment (e : ℕ) (W : Finset ℝ)
    {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) (hd2 : d ≤ 2*N) :
    (∑ p ∈ reducedPairs N d,
      ‖ratioDirichletKernel W ((p.1 : ℝ)/(p.2 : ℝ))‖^e) ≤
      ratioKernelMoment e (Nat.ceil ((N : ℝ)/(d : ℝ))) W := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (reducedPairs_subset_rounded_block hN hd hd2)
  intro p hp hnot
  positivity

/-- Cauchy--Schwarz applies after a proved inclusion into the rounded block,
so the original strict lower cutoffs and exact coprimality mask are retained. -/
theorem reduced_cubic_le_rounded_geometricMean (W : Finset ℝ)
    {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) (hd2 : d ≤ 2*N) :
    (∑ p ∈ reducedPairs N d,
      ‖ratioDirichletKernel W ((p.1 : ℝ)/(p.2 : ℝ))‖^3) ≤
      Real.sqrt (ratioKernelMoment 2 (Nat.ceil ((N : ℝ)/(d : ℝ))) W)*
        Real.sqrt (ratioKernelMoment 4 (Nat.ceil ((N : ℝ)/(d : ℝ))) W) :=
  (reduced_moment_le_rounded_moment 3 W hN hd hd2).trans
    (ratioKernelMoment_three_le_geometricMean _ W)

end GuthMaynardEnergy119ReducedHolder
#print axioms GuthMaynardEnergy119ReducedHolder.reducedPairs_subset_rounded_block
#print axioms GuthMaynardEnergy119ReducedHolder.reduced_cubic_le_rounded_geometricMean
