import JutilaHalaszLargeValueFront

/-!
# Source-faithful p.53 correlation-energy leaf

Jutila's equation (1.7) and pages 52--53 use a selected system of rows that
carry both a character modulo the fixed modulus and one of its zeros.  The
correlation series in Lemma 7 is infinite even though the detected
polynomial is finite.  This module records that exact geometry and exposes
the remaining analytic estimate at the correlation-energy level.

No density conclusion is assumed here.  In particular, the character label
is not erased and the infinite correlation series is not replaced by a
finite hard block.
-/

namespace MAPJutilaP53AggregateCorrelationLeaf

open scoped BigOperators
open Complex Real MeasureTheory
open MAPJutilaHalaszLargeValueFront

noncomputable section

structure JutilaP53Row (q : ℕ) where
  character : DirichletCharacter ℂ q
  zero : ℂ

instance {q : ℕ} : DecidableEq (JutilaP53Row q) := Classical.decEq _

/-- The row phase in Lemma 7 after writing `rho = alpha + s_j`.  The value
at zero is set to zero because Dirichlet series start at one. -/
def jutilaP53Phase {q : ℕ} (alpha : ℝ)
    (row : JutilaP53Row q) (n : ℕ) : ℂ :=
  if n = 0 then 0 else
    row.character n * (n : ℂ) ^ (-(row.zero - (alpha : ℂ)))

theorem norm_jutilaP53Phase_le_one
    {q : ℕ} {alpha : ℝ} {row : JutilaP53Row q}
    (hrow : alpha ≤ row.zero.re) (n : ℕ) :
    ‖jutilaP53Phase alpha row n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [jutilaP53Phase, hn]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hchi := DirichletCharacter.norm_le_one row.character n
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hexp : alpha - row.zero.re ≤ 0 := sub_nonpos.mpr hrow
  have hpow : ‖(n : ℂ) ^ (-(row.zero - (alpha : ℂ)))‖ =
      Real.rpow (n : ℝ) (alpha - row.zero.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hnpos]
    congr 1
    simp
  rw [jutilaP53Phase, if_neg hn, norm_mul, hpow]
  have hp0 : 0 ≤ Real.rpow (n : ℝ) (alpha - row.zero.re) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hp1 : Real.rpow (n : ℝ) (alpha - row.zero.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hnOne hexp
  calc
    ‖row.character n‖ * Real.rpow (n : ℝ) (alpha - row.zero.re) ≤
        1 * Real.rpow (n : ℝ) (alpha - row.zero.re) :=
      mul_le_mul_of_nonneg_right hchi hp0
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hp1 zero_le_one
    _ = 1 := by ring

/-- Real pseudocharacter factor in the source weight (3.3). -/
def jutilaP53SelbergPseudoAt (r n : ℕ) : ℂ :=
  (ArithmeticFunction.moebius (r.gcd n) : ℂ) *
    (Nat.totient (r.gcd n) : ℂ)

theorem norm_jutilaP53SelbergPseudoAt_le (r n : ℕ) :
    ‖jutilaP53SelbergPseudoAt r n‖ ≤
      (Nat.totient (r.gcd n) : ℝ) := by
  have hmu : ‖(ArithmeticFunction.moebius (r.gcd n) : ℂ)‖ ≤ 1 := by
    norm_num
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := r.gcd n)
  unfold jutilaP53SelbergPseudoAt
  rw [norm_mul]
  have hphiNorm : ‖((Nat.totient (r.gcd n) : ℕ) : ℂ)‖ =
      (Nat.totient (r.gcd n) : ℝ) := by simp
  rw [hphiNorm]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg _)

def jutilaP53WeightedPseudocharacter
    (S : Finset ℕ) (n : ℕ) : ℂ :=
  ∑ r ∈ S, (r : ℂ)⁻¹ * jutilaP53SelbergPseudoAt r n

theorem norm_jutilaP53WeightedPseudocharacter_le
    {S : Finset ℕ} {R n : ℕ}
    (hS : S ⊆ Finset.Icc 1 R) :
    ‖jutilaP53WeightedPseudocharacter S n‖ ≤ (R : ℝ) := by
  have hterm : ∀ r ∈ S,
      ‖(r : ℂ)⁻¹ * jutilaP53SelbergPseudoAt r n‖ ≤ 1 := by
    intro r hr
    have hrI := Finset.mem_Icc.mp (hS hr)
    have hrpos : 0 < r := by omega
    have hf := norm_jutilaP53SelbergPseudoAt_le r n
    have hphi : (Nat.totient (r.gcd n) : ℝ) ≤ r := by
      have hphiNat : Nat.totient (r.gcd n) ≤ r :=
        (Nat.totient_le _).trans (Nat.gcd_le_left n hrpos)
      exact_mod_cast hphiNat
    have hfr : ‖jutilaP53SelbergPseudoAt r n‖ ≤ (r : ℝ) := hf.trans hphi
    rw [norm_mul, norm_inv]
    simp only [Complex.norm_natCast]
    have hrR : (0 : ℝ) < r := by exact_mod_cast hrpos
    calc
      (r : ℝ)⁻¹ * ‖jutilaP53SelbergPseudoAt r n‖ ≤
          (r : ℝ)⁻¹ * (r : ℝ) :=
        mul_le_mul_of_nonneg_left hfr (by positivity)
      _ = 1 := inv_mul_cancel₀ hrR.ne'
  calc
    ‖jutilaP53WeightedPseudocharacter S n‖ ≤
        ∑ r ∈ S, ‖(r : ℂ)⁻¹ * jutilaP53SelbergPseudoAt r n‖ := by
      unfold jutilaP53WeightedPseudocharacter
      exact norm_sum_le _ _
    _ ≤ ∑ _r ∈ S, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) := by simp
    _ ≤ (R : ℝ) := by
      exact_mod_cast (Finset.card_le_card hS).trans (by
        rw [Nat.card_Icc]
        omega)

def jutilaP53PseudoReal (S : Finset ℕ) (n : ℕ) : ℝ :=
  (jutilaP53WeightedPseudocharacter S n).re

/-- Literal source weight (3.3) for one pair of smoothing scales. -/
def jutilaP53CorrelationWeight
    (S : Finset ℕ) (M N : ℝ) (n : ℕ) : ℝ :=
  jutilaCorrelationWeight M N (jutilaP53PseudoReal S) n

theorem jutilaP53CorrelationWeight_nonneg
    (S : Finset ℕ) {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    (n : ℕ) :
    0 ≤ jutilaP53CorrelationWeight S M N n := by
  by_cases hn : n = 0
  · subst n
    simp [jutilaP53CorrelationWeight, jutilaCorrelationWeight]
  by_cases hP : jutilaP53PseudoReal S n = 0
  · simp [jutilaP53CorrelationWeight, jutilaCorrelationWeight, hP]
  exact (jutilaCorrelationWeight_pos hM hMN
    (Nat.pos_of_ne_zero hn) hP).le

theorem abs_jutilaP53PseudoReal_le
    {S : Finset ℕ} {R n : ℕ} (hS : S ⊆ Finset.Icc 1 R) :
    |jutilaP53PseudoReal S n| ≤ (R : ℝ) := by
  exact (Complex.abs_re_le_norm _).trans
    (norm_jutilaP53WeightedPseudocharacter_le hS)

theorem jutilaP53CorrelationWeight_le_geometric
    {S : Finset ℕ} {R n : ℕ} (hS : S ⊆ Finset.Icc 1 R)
    {M N : ℝ} (hM : 0 < M) (hMN : M < N) :
    jutilaP53CorrelationWeight S M N n ≤
      (R : ℝ) ^ 2 * (Real.exp (-(1 / N))) ^ n := by
  by_cases hn : n = 0
  · subst n
    simp [jutilaP53CorrelationWeight, jutilaCorrelationWeight]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hinv : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hnOne
  have hR0 : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
  have hPabs := abs_jutilaP53PseudoReal_le (n := n) hS
  have hPsq : (jutilaP53PseudoReal S n) ^ 2 ≤ (R : ℝ) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hR0] using hPabs
  have hN : 0 < N := hM.trans hMN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hquot : (n : ℝ) / N < (n : ℝ) / M :=
    (div_lt_div_iff_of_pos_left hnR hN hM).2 hMN
  have hsub0 : 0 ≤
      Real.exp (-((n : ℝ) / N)) - Real.exp (-((n : ℝ) / M)) := by
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have hsuble :
      Real.exp (-((n : ℝ) / N)) - Real.exp (-((n : ℝ) / M)) ≤
        Real.exp (-((n : ℝ) / N)) := by
    linarith [Real.exp_nonneg (-((n : ℝ) / M))]
  unfold jutilaP53CorrelationWeight jutilaCorrelationWeight
  calc
    (n : ℝ)⁻¹ * (jutilaP53PseudoReal S n) ^ 2 *
          (Real.exp (-((n : ℝ) / N)) - Real.exp (-((n : ℝ) / M))) ≤
        1 * (R : ℝ) ^ 2 * Real.exp (-((n : ℝ) / N)) := by
      gcongr
    _ = (R : ℝ) ^ 2 * (Real.exp (-(1 / N))) ^ n := by
      have hexp :
          Real.exp (-((n : ℝ) / N)) =
            (Real.exp (-(1 / N))) ^ n := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [hexp]
      ring

theorem summable_jutilaP53CorrelationWeight
    {S : Finset ℕ} {R : ℕ} (hS : S ⊆ Finset.Icc 1 R)
    {M N : ℝ} (hM : 0 < M) (hMN : M < N) :
    Summable (jutilaP53CorrelationWeight S M N) := by
  let r : ℝ := Real.exp (-(1 / N))
  have hN : 0 < N := hM.trans hMN
  have hneg : -(1 / N) < 0 := by
    have hinv : 0 < 1 / N := one_div_pos.mpr hN
    linarith
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrlt : r < 1 := by
    dsimp [r]
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hneg
  have hrsum : Summable (fun n : ℕ => (R : ℝ) ^ 2 * r ^ n) :=
    (summable_geometric_of_norm_lt_one
      (show ‖r‖ < 1 by simpa [Real.norm_eq_abs, abs_of_pos hrpos] using hrlt)).mul_left
        ((R : ℝ) ^ 2)
  exact Summable.of_nonneg_of_le
    (jutilaP53CorrelationWeight_nonneg S hM hMN)
    (fun n => by simpa [r] using
      (jutilaP53CorrelationWeight_le_geometric (n := n) hS hM hMN))
    hrsum

/-- Infinite positive correlation energy for one `(M,N)` pair. -/
def jutilaP53CorrelationEnergy {q : ℕ}
    (rows : Finset (JutilaP53Row q)) (S : Finset ℕ)
    (alpha M N : ℝ) (eta : JutilaP53Row q → ℂ) : ℝ :=
  ∑' n : ℕ, jutilaP53CorrelationWeight S M N n *
    ‖∑ row ∈ rows, eta row * jutilaP53Phase alpha row n‖ ^ 2

/-- The exact double smoothing average from (3.4)--(3.6). -/
def jutilaP53IntegratedCorrelationEnergy {q : ℕ}
    (rows : Finset (JutilaP53Row q)) (S : Finset ℕ)
    (alpha epsilon z1 x : ℝ) (eta : JutilaP53Row q → ℂ) : ℝ :=
  ∫ xi in (1 - epsilon) * Real.log z1..Real.log z1,
    ∫ upsilon in Real.log x..(1 + epsilon) * Real.log x,
      jutilaP53CorrelationEnergy rows S alpha
        (Real.exp xi) (Real.exp upsilon) eta

/-- Narrow remaining analytic statement on p.53.  `F` is the residue/diagonal
budget and `E` is the shifted-contour budget.  The theorem downstream needs
this bound for the literal infinite correlation energy and unit row phases;
it does not need a density theorem as an input.

The row set retains character labels.  A fixed-character selected system is
obtained by taking a subset with constant `row.character`; it is not baked
into the source statement. -/
def JutilaP53IntegratedCorrelationEstimateAt
    {q : ℕ} (rows : Finset (JutilaP53Row q)) (S : Finset ℕ)
    (alpha epsilon z1 x F E : ℝ) : Prop :=
  ∀ eta : JutilaP53Row q → ℂ,
    (∀ row ∈ rows, ‖eta row‖ = 1) →
    jutilaP53IntegratedCorrelationEnergy
        rows S alpha epsilon z1 x eta ≤
      F * (rows.card : ℝ) + E * (rows.card : ℝ) ^ 2

end

end MAPJutilaP53AggregateCorrelationLeaf

#print axioms MAPJutilaP53AggregateCorrelationLeaf.norm_jutilaP53Phase_le_one
#print axioms MAPJutilaP53AggregateCorrelationLeaf.jutilaP53CorrelationWeight_nonneg
#print axioms MAPJutilaP53AggregateCorrelationLeaf.summable_jutilaP53CorrelationWeight
