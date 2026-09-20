import MAPHBPerronSourceData

/-!
# Arbitrary-order Heath--Brown source for the live MRT decomposition

MRT Lemma 2.15 has two independent parameters.  Its `m` controls the final
Type-`d_j` alternatives, while the Heath--Brown identity order must be at
least the reciprocal of the small-scale exponent.  Consequently the live MAP
source cannot identify the eight final Type labels with eight raw HB terms.

This module supplies the exact raw source with a dynamic order.  For the MAP
choice we use `2 * ceil (1 / delta)`: the factor two is the manuscript's
otherwise-unused `kappa`, and is what turns the source's
`(2X)^(1/K) \ll X^delta` into the literal inequality
`(2X)^(1/K) \le X^delta` for `X >= 2`.
-/

namespace MAPDynamicHBSourceV3

open scoped BigOperators ArithmeticFunction
open ArithmeticFunction
open MAPHeathBrownFiniteIdentity
open MAPMRTCorollary53Source
open MAPMRTCorollary25Instantiation
open MAPHBPerronSourceData

noncomputable section

private theorem arithmeticFunction_finsetSum_apply_real
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (F : ι → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ S, F i) n = ∑ i ∈ S, F i n := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      simp [ha, ih, ArithmeticFunction.add_apply]

/-- The source order before the safety doubling. -/
def hbBaseOrder (delta : ℝ) : ℕ := ⌈1 / delta⌉₊

/-- The literal live HB order.  This is the manuscript's `kappa=2*K_0`. -/
def hbOrder (delta : ℝ) : ℕ := 2 * hbBaseOrder delta

theorem hbBaseOrder_pos {delta : ℝ} (hdelta : 0 < delta) :
    0 < hbBaseOrder delta := by
  unfold hbBaseOrder
  rw [Nat.ceil_pos]
  positivity

theorem hbOrder_pos {delta : ℝ} (hdelta : 0 < delta) :
    0 < hbOrder delta := by
  unfold hbOrder
  exact Nat.mul_pos (by norm_num) (hbBaseOrder_pos hdelta)

theorem hbOrder_one {delta : ℝ} (hdelta : 0 < delta) :
    1 ≤ hbOrder delta := Nat.one_le_iff_ne_zero.mpr (hbOrder_pos hdelta).ne'

/-- The dynamic real cutoff `(2X)^(1/K)`. -/
def dynamicHBCutoff (X : ℝ) (K : ℕ) : ℝ :=
  Real.rpow (2 * X) ((K : ℝ)⁻¹)

theorem dynamicHBCutoff_pow
    {X : ℝ} {K : ℕ} (hX : 0 ≤ X) (hK : K ≠ 0) :
    dynamicHBCutoff X K ^ K = 2 * X := by
  unfold dynamicHBCutoff
  have hbase : 0 ≤ 2 * X := by positivity
  simpa using Real.rpow_inv_natCast_pow hbase hK

/-- `ceil(1/delta)` alone is not enough for a literal `X^delta` cutoff at
the saturated endpoint.  Doubling it yields the required exponent reserve. -/
theorem inv_hbOrder_le_half_delta
    {delta : ℝ} (hdelta : 0 < delta) :
    ((hbOrder delta : ℝ)⁻¹) ≤ delta / 2 := by
  have hceil : 1 / delta ≤ (hbBaseOrder delta : ℝ) := by
    exact Nat.le_ceil (1 / delta)
  have hKposNat : 0 < hbOrder delta := hbOrder_pos hdelta
  have hKpos : (0 : ℝ) < hbOrder delta := by exact_mod_cast hKposNat
  have hKlarge : 2 / delta ≤ (hbOrder delta : ℝ) := by
    calc
      2 / delta = 2 * (1 / delta) := by ring
      _ ≤ 2 * (hbBaseOrder delta : ℝ) :=
        mul_le_mul_of_nonneg_left hceil (by norm_num)
      _ = (hbOrder delta : ℝ) := by
        simp [hbOrder]
  rw [show ((hbOrder delta : ℝ)⁻¹) = 1 / (hbOrder delta : ℝ) by
    simp [one_div]]
  rw [div_le_iff₀ hKpos]
  calc
    1 = (delta / 2) * (2 / delta) := by field_simp
    _ ≤ (delta / 2) * (hbOrder delta : ℝ) :=
      mul_le_mul_of_nonneg_left hKlarge (by positivity)

/-- Exact small-scale inequality needed to mark every Möbius shell as a
small factor in MRT Lemma 2.15. -/
theorem dynamicHBCutoff_hbOrder_le_rpow
    {X delta : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta) :
    dynamicHBCutoff X (hbOrder delta) ≤ Real.rpow X delta := by
  have hXpos : 0 < X := by linarith
  have hbaseOne : 1 ≤ 2 * X := by linarith
  have hexp := inv_hbOrder_le_half_delta hdelta
  have hfirst :
      Real.rpow (2 * X) ((hbOrder delta : ℝ)⁻¹) ≤
        Real.rpow (2 * X) (delta / 2) :=
    Real.rpow_le_rpow_of_exponent_le hbaseOne hexp
  have hpowTwo : Real.rpow 2 (delta / 2) ≤
      Real.rpow X (delta / 2) := by
    exact Real.rpow_le_rpow (by norm_num) hX (by positivity)
  have hXpow : 0 ≤ Real.rpow X (delta / 2) :=
    Real.rpow_nonneg hXpos.le _
  calc
    dynamicHBCutoff X (hbOrder delta) ≤
        Real.rpow (2 * X) (delta / 2) := hfirst
    _ = Real.rpow 2 (delta / 2) * Real.rpow X (delta / 2) := by
      change (2 * X) ^ (delta / 2) =
        2 ^ (delta / 2) * X ^ (delta / 2)
      exact Real.mul_rpow (by norm_num) hXpos.le
    _ ≤ Real.rpow X (delta / 2) * Real.rpow X (delta / 2) :=
      mul_le_mul_of_nonneg_right hpowTwo hXpow
    _ = Real.rpow X delta := by
      change X ^ (delta / 2) * X ^ (delta / 2) = X ^ delta
      rw [← Real.rpow_add hXpos]
      congr 1 <;> ring

/-- The `k`-th raw term of the dynamic published HB identity. -/
def dynamicHBSignedTerm (X : ℝ) (K k n : ℕ) : ℂ :=
  ((((-1 : ArithmeticFunction ℝ) ^ k *
      (K.choose (k + 1) : ArithmeticFunction ℝ)) *
    (ArithmeticFunction.log *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k *
      realTruncatedMoebius (dynamicHBCutoff X K) ^ (k + 1))) n : ℂ)

/-- The source mask is applied after the full convolution coefficient. -/
def dynamicHBBranchCoeff (X : ℝ) (K : ℕ) (k : Fin K) (n : ℕ) : ℂ :=
  if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then dynamicHBSignedTerm X K k n else 0

/-- Exact dynamic-order HB identity on `(X,2X]`. -/
theorem sum_dynamicHBSignedTerm_eq_vonMangoldt
    {X : ℝ} {K : ℕ} (hX : 0 ≤ X) (hK : 1 ≤ K) {n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊) :
    (∑ k : Fin K, dynamicHBSignedTerm X K k n) =
      (ArithmeticFunction.vonMangoldt n : ℂ) := by
  have hnFloor : n ≤ ⌊2 * X⌋₊ := (Finset.mem_Ioc.mp hn).2
  have htwoX : 0 ≤ 2 * X := by positivity
  have hnReal : (n : ℝ) ≤ 2 * X := by
    have hfloorCast : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by
      exact_mod_cast hnFloor
    exact hfloorCast.trans (Nat.floor_le htwoX)
  have hcutoffNonneg : 0 ≤ dynamicHBCutoff X K :=
    Real.rpow_nonneg (by positivity) _
  have hpow : (n : ℝ) ≤ dynamicHBCutoff X K ^ K := by
    rw [dynamicHBCutoff_pow hX (Nat.ne_of_gt (Nat.zero_lt_of_lt hK))]
    exact hnReal
  have hid := heathBrownPublishedRealSum_apply
    (Y := dynamicHBCutoff X K) (K := K) (n := n)
    hK hcutoffNonneg hpow
  rw [← hid]
  rw [show (∑ k : Fin K, dynamicHBSignedTerm X K k n) =
      ∑ k ∈ Finset.range K, dynamicHBSignedTerm X K k n by
    exact Fin.sum_univ_eq_sum_range
      (fun k ↦ dynamicHBSignedTerm X K k n) K]
  unfold heathBrownPublishedRealSum dynamicHBSignedTerm
  rw [← Complex.ofReal_sum]
  congr 1
  exact (arithmeticFunction_finsetSum_apply_real
    (Finset.range K)
    (fun k =>
      ((-1 : ArithmeticFunction ℝ) ^ k *
        (K.choose (k + 1) : ArithmeticFunction ℝ)) *
        (ArithmeticFunction.log *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k *
          realTruncatedMoebius (dynamicHBCutoff X K) ^ (k + 1))) n).symm

/-- The MAP Mangoldt coefficient is the sum over the dynamic raw branches.
No Type-`d` label has yet been assigned. -/
theorem mapMangoldtCoeff_eq_sum_dynamicHBBranchCoeff
    {X : ℝ} {K : ℕ} (hX : 0 ≤ X) (hK : 1 ≤ K) (n : ℕ) :
    mapMangoldtCoeff X n = ∑ k : Fin K, dynamicHBBranchCoeff X K k n := by
  by_cases hn : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊
  · rw [mapMangoldtCoeff, if_pos hn]
    simpa [dynamicHBBranchCoeff, hn] using
      (sum_dynamicHBSignedTerm_eq_vonMangoldt hX hK hn).symm
  · simp [mapMangoldtCoeff, dynamicHBBranchCoeff, hn]

/-- Exact polynomial identity before the preliminary dyadic expansion. -/
theorem criticalDirichletPolynomial_map_eq_sum_dynamicHB
    {X : ℝ} {K : ℕ} (hX : 0 ≤ X) (hK : 1 ≤ K)
    (q₁ : ℕ) (chi : DirichletCharacter ℂ q₁) (t : ℝ) :
    criticalDirichletPolynomial X 1 q₁ (mapMangoldtCoeff X) chi t =
      ∑ k : Fin K,
        criticalDirichletPolynomial X 1 q₁
          (dynamicHBBranchCoeff X K k) chi t := by
  rw [show mapMangoldtCoeff X =
      fun n ↦ ∑ k : Fin K, dynamicHBBranchCoeff X K k n by
    funext n
    exact mapMangoldtCoeff_eq_sum_dynamicHBBranchCoeff hX hK n]
  simpa using criticalDirichletPolynomial_finset_sum
    (Finset.univ : Finset (Fin K)) X 1 q₁
    (fun k ↦ dynamicHBBranchCoeff X K k) chi t

end
end MAPDynamicHBSourceV3

#print axioms MAPDynamicHBSourceV3.dynamicHBCutoff_hbOrder_le_rpow
#print axioms MAPDynamicHBSourceV3.sum_dynamicHBSignedTerm_eq_vonMangoldt
#print axioms MAPDynamicHBSourceV3.mapMangoldtCoeff_eq_sum_dynamicHBBranchCoeff
#print axioms MAPDynamicHBSourceV3.criticalDirichletPolynomial_map_eq_sum_dynamicHB
