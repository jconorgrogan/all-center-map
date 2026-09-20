import JutilaPseudocharacterMExact
import RamachandraShiftedDirectSeries

/-!
# Explicit direct-series tail in Jutila Lemma 6

This module formalizes the source sentence after (2.11): cutting the
exponentially smoothed arithmetic series at `x` leaves a small tail.  The
bound is uniform in the character and uses only `|lambda_d|≤1`,
`phi(gcd(r,n))≤r`, and the geometric first-moment sum.
-/

namespace MAPJutilaLemma6DirectTail

open scoped BigOperators
open Complex
open MAPJutilaGappedGrahamBypass
open MAPJutilaPseudocharacterMExact
open RamachandraShiftedDirectSeries
open RamachandraShiftedCoefficientEnergy
open CGLProofDAG

noncomputable section

def jutilaWeightedPseudocharacter
    (S : Finset ℕ) (n : ℕ) : ℂ :=
  ∑ r ∈ S, (r : ℂ)⁻¹ * selbergPseudoAt r n

def jutilaLemmaSixDirectTerm {q : ℕ}
    (chi : DirichletCharacter ℂ q) (z1 z2 : ℝ)
    (S : Finset ℕ) (rho : ℂ) (X : ℝ) (n : ℕ) : ℂ :=
  (jutilaDivisorCoefficient z1 z2 n : ℂ) * chi n *
    (Real.exp (-((n : ℝ) / X)) : ℂ) * (n : ℂ) ^ (-rho) *
    jutilaWeightedPseudocharacter S n

theorem norm_jutilaWeightedPseudocharacter_le
    {S : Finset ℕ} {R n : ℕ}
    (hS : S ⊆ Finset.Icc 1 R) :
    ‖jutilaWeightedPseudocharacter S n‖ ≤ (R : ℝ) := by
  have hterm : ∀ r ∈ S,
      ‖(r : ℂ)⁻¹ * selbergPseudoAt r n‖ ≤ 1 := by
    intro r hr
    have hrI := Finset.mem_Icc.mp (hS hr)
    have hrpos : 0 < r := by omega
    have hf := norm_selbergPseudoAt_le r n
    have hphi : (Nat.totient (r.gcd n) : ℝ) ≤ r := by
      have hphiNat : Nat.totient (r.gcd n) ≤ r :=
        (Nat.totient_le _).trans (Nat.gcd_le_left n hrpos)
      exact_mod_cast hphiNat
    have hfr : ‖selbergPseudoAt r n‖ ≤ (r : ℝ) := hf.trans hphi
    rw [norm_mul, norm_inv]
    simp only [Complex.norm_natCast]
    have hrR : (0 : ℝ) < r := by exact_mod_cast hrpos
    calc
      (r : ℝ)⁻¹ * ‖selbergPseudoAt r n‖ ≤
          (r : ℝ)⁻¹ * (r : ℝ) :=
        mul_le_mul_of_nonneg_left hfr (by positivity)
      _ = 1 := inv_mul_cancel₀ hrR.ne'
  calc
    ‖jutilaWeightedPseudocharacter S n‖ ≤
        ∑ r ∈ S, ‖(r : ℂ)⁻¹ * selbergPseudoAt r n‖ := by
      unfold jutilaWeightedPseudocharacter
      exact norm_sum_le _ _
    _ ≤ ∑ _r ∈ S, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) := by simp
    _ ≤ (R : ℝ) := by
      exact_mod_cast (Finset.card_le_card hS).trans (by
        rw [Nat.card_Icc]
        omega)

theorem abs_jutilaDivisorCoefficient_le_self
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    {n : ℕ} (hn : 0 < n) :
    |jutilaDivisorCoefficient z1 z2 n| ≤ (n : ℝ) := by
  have habs := abs_divisorWeight_le_card
    (jutilaLambda z1 z2) (abs_jutilaLambda_le_one hz1 hz12) (n := n)
  have hcard : n.divisors.card ≤ n := Nat.card_divisors_le_self n
  exact habs.trans (by exact_mod_cast hcard)

theorem norm_jutilaLemmaSixDirectTerm_le
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    {S : Finset ℕ} {R n : ℕ} (hS : S ⊆ Finset.Icc 1 R)
    {rho : ℂ} (hrho : 0 ≤ rho.re) {X : ℝ} (hn : 0 < n) :
    ‖jutilaLemmaSixDirectTerm chi z1 z2 S rho X n‖ ≤
      (R : ℝ) * (n : ℝ) * Real.exp (-((n : ℝ) / X)) := by
  have ha := abs_jutilaDivisorCoefficient_le_self hz1 hz12 hn
  have hchi : ‖chi n‖ ≤ 1 := DirichletCharacter.norm_le_one chi n
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpowNorm : ‖(n : ℂ) ^ (-rho)‖ = Real.rpow (n : ℝ) (-rho.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    congr 1
  have hpow : Real.rpow (n : ℝ) (-rho.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hnOne (neg_nonpos.mpr hrho)
  have hSbound := norm_jutilaWeightedPseudocharacter_le hS (n := n)
  unfold jutilaLemmaSixDirectTerm
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), hpowNorm]
  have ha0 : 0 ≤ |jutilaDivisorCoefficient z1 z2 n| := abs_nonneg _
  have hexp0 : 0 ≤ Real.exp (-((n : ℝ) / X)) := Real.exp_nonneg _
  have hpow0 : 0 ≤ Real.rpow (n : ℝ) (-rho.re) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  calc
    |jutilaDivisorCoefficient z1 z2 n| * ‖chi n‖ *
          Real.exp (-((n : ℝ) / X)) * Real.rpow (n : ℝ) (-rho.re) *
          ‖jutilaWeightedPseudocharacter S n‖ ≤
        (n : ℝ) * 1 * Real.exp (-((n : ℝ) / X)) * 1 * (R : ℝ) := by
      gcongr
    _ = (R : ℝ) * (n : ℝ) * Real.exp (-((n : ℝ) / X)) := by ring

/-- Exact geometric envelope for the tail `n > M`. -/
theorem norm_jutilaLemmaSixDirectTail_le
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    {S : Finset ℕ} {R : ℕ} (hS : S ⊆ Finset.Icc 1 R)
    (M : ℕ) {rho : ℂ} (hrho : 0 ≤ rho.re)
    {X : ℝ} (hX : 0 < X) :
    ‖∑' k : ℕ,
        jutilaLemmaSixDirectTerm chi z1 z2 S rho X (k + (M + 1))‖ ≤
      (R : ℝ) * (M + 1 : ℝ) *
        (Real.exp (-(1 / X))) ^ (M + 1) *
        (Real.exp (-(1 / X)) /
            (1 - Real.exp (-(1 / X))) ^ 2 +
          (1 - Real.exp (-(1 / X)))⁻¹) := by
  let r : ℝ := Real.exp (-(1 / X))
  have hneg : -(1 / X) < 0 := by
    have hinv : 0 < 1 / X := one_div_pos.mpr hX
    linarith
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrlt : r < 1 := by
    dsimp [r]
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hneg
  have hrnorm : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_pos hrpos] using hrlt
  let g : ℕ → ℝ := fun k =>
    (R : ℝ) * (M + 1 : ℝ) * r ^ (M + 1) *
      ((k + 1 : ℝ) * r ^ k)
  have hsuccSummable : Summable (fun k : ℕ =>
      (k + 1 : ℝ) * r ^ k) := by
    have hk := (hasSum_coe_mul_geometric_of_norm_lt_one hrnorm).summable
    have hg := (hasSum_geometric_of_norm_lt_one hrnorm).summable
    exact (hk.add hg).congr (fun k => by ring)
  have hgSummable : Summable g :=
    hsuccSummable.mul_left
      ((R : ℝ) * (M + 1 : ℝ) * r ^ (M + 1))
  have hterm : ∀ k : ℕ,
      ‖jutilaLemmaSixDirectTerm chi z1 z2 S rho X (k + (M + 1))‖ ≤ g k := by
    intro k
    have hn : 0 < k + (M + 1) := by omega
    have hraw := norm_jutilaLemmaSixDirectTerm_le chi hz1 hz12 hS hrho
      (X := X) hn
    rw [exp_neg_nat_div_eq_pow (X := X) (k + (M + 1))] at hraw
    have hnat : (k + (M + 1) : ℝ) ≤
        (M + 1 : ℝ) * (k + 1 : ℝ) := by
      nlinarith [Nat.zero_le (k * M)]
    have hpow : r ^ (k + (M + 1)) = r ^ (M + 1) * r ^ k := by
      rw [show k + (M + 1) = (M + 1) + k by omega, pow_add]
    rw [show Real.exp (-(1 / X)) = r by rfl, hpow] at hraw
    calc
      ‖jutilaLemmaSixDirectTerm chi z1 z2 S rho X (k + (M + 1))‖ ≤
          (R : ℝ) * (k + (M + 1) : ℝ) *
            (r ^ (M + 1) * r ^ k) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hraw
      _ ≤ (R : ℝ) * ((M + 1 : ℝ) * (k + 1 : ℝ)) *
          (r ^ (M + 1) * r ^ k) := by gcongr
      _ = g k := by dsimp [g]; ring
  have hnormSummable : Summable (fun k : ℕ =>
      ‖jutilaLemmaSixDirectTerm chi z1 z2 S rho X (k + (M + 1))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hgSummable
  calc
    ‖∑' k : ℕ,
        jutilaLemmaSixDirectTerm chi z1 z2 S rho X (k + (M + 1))‖ ≤
        ∑' k : ℕ,
          ‖jutilaLemmaSixDirectTerm chi z1 z2 S rho X (k + (M + 1))‖ :=
      norm_tsum_le_tsum_norm hnormSummable
    _ ≤ ∑' k : ℕ, g k := hnormSummable.tsum_le_tsum hterm hgSummable
    _ = (R : ℝ) * (M + 1 : ℝ) * r ^ (M + 1) *
        (r / (1 - r) ^ 2 + (1 - r)⁻¹) := by
      unfold g
      rw [tsum_mul_left, tsum_succ_mul_geometric hrpos.le hrlt]
    _ = _ := by rfl

theorem summable_jutilaLemmaSixDirectTerm
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    {S : Finset ℕ} {R : ℕ} (hS : S ⊆ Finset.Icc 1 R)
    {rho : ℂ} (hrho : 0 ≤ rho.re)
    {X : ℝ} (hX : 0 < X) :
    Summable (jutilaLemmaSixDirectTerm chi z1 z2 S rho X) := by
  let r : ℝ := Real.exp (-(1 / X))
  have hneg : -(1 / X) < 0 := by
    have hinv : 0 < 1 / X := one_div_pos.mpr hX
    linarith
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrlt : r < 1 := by
    dsimp [r]
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hneg
  have hrnorm : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_pos hrpos] using hrlt
  have hmajor : Summable (fun n : ℕ =>
      (R : ℝ) * ((n : ℝ) * r ^ n)) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hrnorm).summable.mul_left (R : ℝ)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hmajor
  intro n
  by_cases hn : n = 0
  · subst n
    simp [jutilaLemmaSixDirectTerm, jutilaDivisorCoefficient]
  · have hraw := norm_jutilaLemmaSixDirectTerm_le chi hz1 hz12 hS hrho
      (X := X) (Nat.pos_of_ne_zero hn)
    rw [exp_neg_nat_div_eq_pow (X := X) n] at hraw
    simpa [r, mul_assoc] using hraw

/-- Exact finite-prefix plus shifted-tail decomposition of the literal
selected Jutila direct series. -/
theorem jutilaLemmaSixDirectSeries_eq_prefix_add_tail
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    {S : Finset ℕ} {R : ℕ} (hS : S ⊆ Finset.Icc 1 R)
    (M : ℕ) {rho : ℂ} (hrho : 0 ≤ rho.re)
    {X : ℝ} (hX : 0 < X) :
    (∑' n : ℕ, jutilaLemmaSixDirectTerm chi z1 z2 S rho X n) =
      (∑ n ∈ Finset.range (M + 1),
        jutilaLemmaSixDirectTerm chi z1 z2 S rho X n) +
      ∑' k : ℕ,
        jutilaLemmaSixDirectTerm chi z1 z2 S rho X (k + (M + 1)) := by
  have hs := summable_jutilaLemmaSixDirectTerm
    chi hz1 hz12 hS hrho hX
  exact (hs.sum_add_tsum_nat_add (M + 1)).symm

end

end MAPJutilaLemma6DirectTail

#print axioms MAPJutilaLemma6DirectTail.norm_jutilaLemmaSixDirectTerm_le
#print axioms MAPJutilaLemma6DirectTail.norm_jutilaLemmaSixDirectTail_le
#print axioms MAPJutilaLemma6DirectTail.jutilaLemmaSixDirectSeries_eq_prefix_add_tail
