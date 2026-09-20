import JutilaP53InfiniteHalaszWeld
import JutilaP53PseudocharacterExactBridge

/-!
# Exact pair-kernel expansion for Jutila p.53

This file turns the literal infinite positive correlation energy into the
finite double sum of source pair kernels.  It keeps character labels in every
row and uses the already proved summability of the source weight.  The
remaining p.53 work can therefore be stated as diagonal/residue and
off-diagonal/contour estimates for these explicit kernels.
-/

namespace MAPJutilaP53KernelExpansion

open scoped BigOperators ComplexConjugate
open Complex
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53InfiniteHalaszWeld
open MAPMontgomeryInfiniteHalasz

noncomputable section

/-- One literal `(chi_i,rho_i),(chi_j,rho_j)` entry of Jutila's smooth
correlation matrix. -/
def jutilaP53Kernel {q : ℕ} (S : Finset ℕ) (alpha M N : ℝ)
    (i j : JutilaP53Row q) : ℂ :=
  ∑' n : ℕ, (jutilaP53CorrelationWeight S M N n : ℂ) *
    conj (jutilaP53Phase alpha i n) * jutilaP53Phase alpha j n

theorem summable_jutilaP53Kernel
    {q R : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 R)
    {alpha M N : ℝ} (hM : 0 < M) (hMN : M < N)
    {i j : JutilaP53Row q}
    (hi : alpha ≤ i.zero.re) (hj : alpha ≤ j.zero.re) :
    Summable (fun n : ℕ =>
      (jutilaP53CorrelationWeight S M N n : ℂ) *
        conj (jutilaP53Phase alpha i n) * jutilaP53Phase alpha j n) := by
  apply Summable.of_norm_bounded
    (summable_jutilaP53CorrelationWeight hS hM hMN)
  intro n
  have hw0 := jutilaP53CorrelationWeight_nonneg S hM hMN n
  have hi1 := norm_jutilaP53Phase_le_one hi n
  have hj1 := norm_jutilaP53Phase_le_one hj n
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hw0, Complex.norm_conj]
  have hprod : ‖jutilaP53Phase alpha i n‖ *
      ‖jutilaP53Phase alpha j n‖ ≤ 1 := by
    nlinarith [norm_nonneg (jutilaP53Phase alpha i n),
      norm_nonneg (jutilaP53Phase alpha j n)]
  calc
    jutilaP53CorrelationWeight S M N n *
          ‖jutilaP53Phase alpha i n‖ *
          ‖jutilaP53Phase alpha j n‖ =
        jutilaP53CorrelationWeight S M N n *
          (‖jutilaP53Phase alpha i n‖ *
            ‖jutilaP53Phase alpha j n‖) := by ring
    _ ≤ jutilaP53CorrelationWeight S M N n * 1 :=
      mul_le_mul_of_nonneg_left hprod hw0
    _ = jutilaP53CorrelationWeight S M N n := by ring

private def selectedP53Phase {q : ℕ}
    (rows : Finset (JutilaP53Row q)) (alpha : ℝ)
    (row : JutilaP53Row q) (n : ℕ) : ℂ :=
  if row ∈ rows then jutilaP53Phase alpha row n else 0

/-- Exact double-sum expansion.  No pairwise estimate or absolute-value
loss is used. -/
theorem jutilaP53CorrelationEnergy_eq_doubleSum
    {q R : ℕ} (rows : Finset (JutilaP53Row q))
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 R)
    {alpha M N : ℝ} (hM : 0 < M) (hMN : M < N)
    (eta : JutilaP53Row q → ℂ)
    (hrow : ∀ row ∈ rows, alpha ≤ row.zero.re)
    (heta : ∀ row ∈ rows, ‖eta row‖ = 1) :
    (jutilaP53CorrelationEnergy rows S alpha M N eta : ℂ) =
      ∑ i ∈ rows, ∑ j ∈ rows,
        conj (eta i) * eta j * jutilaP53Kernel S alpha M N i j := by
  let v : JutilaP53Row q → ℕ → ℂ := selectedP53Phase rows alpha
  have hv : ∀ row n, ‖v row n‖ ≤ 1 := by
    intro row n
    by_cases hr : row ∈ rows
    · simpa [v, selectedP53Phase, hr] using
        norm_jutilaP53Phase_le_one (hrow row hr) n
    · simp [v, selectedP53Phase, hr]
  have hexpand := infiniteCorrelationEnergy_eq_doubleSum rows
    (jutilaP53CorrelationWeight S M N) eta v
    (jutilaP53CorrelationWeight_nonneg S hM hMN)
    (summable_jutilaP53CorrelationWeight hS hM hMN)
    heta hv
  have henergy :
      infiniteCorrelationEnergy rows
          (jutilaP53CorrelationWeight S M N) eta v =
        jutilaP53CorrelationEnergy rows S alpha M N eta := by
    unfold infiniteCorrelationEnergy jutilaP53CorrelationEnergy
    apply tsum_congr
    intro n
    congr 2
    apply congrArg (fun z : ℂ => ‖z‖)
    apply Finset.sum_congr rfl
    intro row hr
    simp [v, selectedP53Phase, hr]
  have hkernel : ∀ i ∈ rows, ∀ j ∈ rows,
      infiniteKernel (jutilaP53CorrelationWeight S M N) v i j =
        jutilaP53Kernel S alpha M N i j := by
    intro i hi j hj
    unfold infiniteKernel jutilaP53Kernel
    apply tsum_congr
    intro n
    simp [v, selectedP53Phase, hi, hj]
  rw [henergy] at hexpand
  calc
    (jutilaP53CorrelationEnergy rows S alpha M N eta : ℂ) =
        ∑ i ∈ rows, ∑ j ∈ rows,
          conj (eta i) * eta j *
            infiniteKernel (jutilaP53CorrelationWeight S M N) v i j :=
      hexpand
    _ = ∑ i ∈ rows, ∑ j ∈ rows,
        conj (eta i) * eta j * jutilaP53Kernel S alpha M N i j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hkernel i hi j hj]

end

end MAPJutilaP53KernelExpansion

#print axioms MAPJutilaP53KernelExpansion.summable_jutilaP53Kernel
#print axioms MAPJutilaP53KernelExpansion.jutilaP53CorrelationEnergy_eq_doubleSum
