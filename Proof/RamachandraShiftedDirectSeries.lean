import RamachandraPrimitiveShiftedContourReduction
import RamachandraShiftedCoefficientEnergy

/-!
# Literal shifted direct-series blocks

This module connects the exact terms in Ramachandra's shifted `S(s)` to the
finite dyadic mean-square engine.  It closes the algebraic provenance and the
coefficient energy of every finite block.  The remaining direct-series input
is the uniform infinite-tail truncation stated only informally in the source.
-/

namespace RamachandraShiftedDirectSeries

open scoped BigOperators Interval LSeries.notation
open Complex MeasureTheory
open CGLProofDAG
open BHPRamachandraMeanValueFromDyadicAFE
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedCoefficientEnergy
open MAPMRTLemma210OrthogonalityReduction
open MontgomeryVaughanFiniteReduction
open BHPAllCharacterDyadicBudget

noncomputable section

/-- One literal term of the shifted exponentially smoothed direct series. -/
def shiftedDirectTerm {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (sigma X t : ℝ) (n : ℕ) : ℂ :=
  LSeries.term (ramachandraDivisorCoeff psi)
      (ramachandraShiftedPoint sigma t) n *
    (Real.exp (-((n : ℝ) / X)) : ℂ)

/-- Exact separation into character, shifted real coefficient, and
`n^(-it)` phase. -/
theorem shiftedDirectTerm_eq_blockTerm
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    {n : ℕ} (hn : 0 < n) (sigma X t : ℝ) :
    shiftedDirectTerm psi sigma X t n =
      (shiftedSmoothedDivisorBlockCoeff sigma X n * psi n) *
        twistedPhase n t := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold shiftedDirectTerm
  rw [LSeries.term_of_ne_zero hn0]
  unfold ramachandraDivisorCoeff ramachandraShiftedPoint
    shiftedSmoothedDivisorBlockCoeff shiftedDivisorBlockCoeff twistedPhase
  rw [Complex.cpow_def_of_ne_zero hnC]
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) :=
    (Complex.ofReal_log hnR.le).symm
  rw [hlog, Real.rpow_def_of_pos hnR]
  rw [div_eq_mul_inv, ← Complex.exp_neg]
  have hrpowExp :
      ((Real.exp (Real.log (n : ℝ) * -sigma) : ℝ) : ℂ) =
        Complex.exp ((Real.log (n : ℝ) * -sigma : ℝ) : ℂ) :=
    Complex.ofReal_exp _
  rw [hrpowExp]
  have hsplit :
      Complex.exp
          (-((Real.log (n : ℝ) : ℂ) * ((sigma : ℂ) + (t : ℂ) * I))) =
        Complex.exp ((Real.log (n : ℝ) * -sigma : ℝ) : ℂ) *
          Complex.exp ((-(t * Real.log (n : ℝ)) : ℝ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hsplit]
  ring

/-- One exact dyadic portion of the literal direct series. -/
def shiftedDirectDyadicBlock {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (N : ℕ)
    (sigma X t : ℝ) : ℂ :=
  ∑ n ∈ dyadicSupport N, shiftedDirectTerm psi sigma X t n

/-- The literal source block is exactly the generic orthogonality block with
our certified shifted coefficient array. -/
theorem shiftedDirectDyadicBlock_eq_ramachandraDyadicBlock
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (N : ℕ) (sigma X t : ℝ) :
    shiftedDirectDyadicBlock psi N sigma X t =
      ramachandraDyadicBlock d N
        (shiftedSmoothedDivisorBlockCoeff sigma X) false psi t := by
  unfold shiftedDirectDyadicBlock ramachandraDyadicBlock
    twistedFinitePolynomial
  simp only [Bool.false_eq_true, if_false]
  apply Finset.sum_congr rfl
  intro n hn
  exact shiftedDirectTerm_eq_blockTerm psi
    (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1) sigma X t

/-- The complete-character continuous mean square of one literal shifted
`S(s)` block, with no analytic premise. -/
theorem integral_sum_norm_shiftedDirectDyadicBlock_sq_le
    (d N : ℕ) [NeZero d] (hN : 1 ≤ N)
    {T X Y sigma delta : ℝ}
    (hT : 0 ≤ T) (hX : 0 < X) (hNY : (2 * N : ℕ) ≤ Y)
    (hdelta : 0 ≤ delta)
    (hsigma : |sigma - 1 / 2| ≤ delta) :
    (∫ t in (-T)..T,
      ∑ psi : DirichletCharacter ℂ d,
        ‖shiftedDirectDyadicBlock psi N sigma X t‖ ^ 2) ≤
      (((d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)) *
        Real.exp (2 * delta * Real.log Y) *
          (harmonic (2 * N) : ℝ) ^ 4) := by
  have hmean := integral_sum_norm_ramachandraDyadicBlock_sq_le
    d N hN (shiftedSmoothedDivisorBlockCoeff sigma X) false hT
  simp_rw [shiftedDirectDyadicBlock_eq_ramachandraDyadicBlock]
  apply hmean.trans
  unfold ramachandraDyadicCost
  have hfactor : 0 ≤ (d : ℝ) * (2 * T) +
      8 * Real.pi * (N : ℝ) := by positivity
  have henergy := coefficientEnergy_shiftedSmoothedDivisorBlockCoeff_le
    N hX hNY hdelta hsigma
  calc
    ((d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)) *
        coefficientEnergy (shiftedSmoothedDivisorBlockCoeff sigma X) N ≤
      ((d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)) *
        (Real.exp (2 * delta * Real.log Y) *
          (harmonic (2 * N) : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left henergy hfactor
    _ = _ := by ring

/-! ## Premise-free exponential tail -/

/-- For nonnegative horizontal shift, one direct term is bounded by the
elementary sequence `n exp(-n/X)`, uniformly in character and ordinate. -/
theorem norm_shiftedDirectTerm_le_nat_mul_exp
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    {n : ℕ} (hn : 0 < n) {sigma X t : ℝ}
    (hsigma : 0 ≤ sigma) :
    ‖shiftedDirectTerm psi sigma X t n‖ ≤
      (n : ℝ) * Real.exp (-((n : ℝ) / X)) := by
  rw [shiftedDirectTerm_eq_blockTerm psi hn sigma X t]
  unfold shiftedSmoothedDivisorBlockCoeff shiftedDivisorBlockCoeff
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_natCast,
    Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    norm_twistedPhase]
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrpow : (n : ℝ) ^ (-sigma) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hnOne (neg_nonpos.mpr hsigma)
  have hchi : ‖psi (n : ZMod d)‖ ≤ 1 := psi.norm_le_one _
  have hdivNat := orderedDivisorCount_two_le_self hn
  have hdiv : (orderedDivisorCount 2 n : ℝ) ≤ n := by
    exact_mod_cast hdivNat
  have hexp : 0 ≤ Real.exp (-((n : ℝ) / X)) := Real.exp_nonneg _
  calc
    (orderedDivisorCount 2 n : ℝ) * (n : ℝ) ^ (-sigma) *
          Real.exp (-((n : ℝ) / X)) * ‖psi (n : ZMod d)‖ * 1 ≤
        (orderedDivisorCount 2 n : ℝ) * 1 *
          Real.exp (-((n : ℝ) / X)) * 1 * 1 := by
      gcongr
    _ ≤ (n : ℝ) * Real.exp (-((n : ℝ) / X)) := by
      simpa using mul_le_mul_of_nonneg_right hdiv hexp

theorem exp_neg_nat_div_eq_pow {X : ℝ} (n : ℕ) :
    Real.exp (-((n : ℝ) / X)) =
      (Real.exp (-(1 / X))) ^ n := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem tsum_succ_mul_geometric
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' k : ℕ, (k + 1 : ℝ) * r ^ k) =
      r / (1 - r) ^ 2 + (1 - r)⁻¹ := by
  have hrnorm : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hk := (hasSum_coe_mul_geometric_of_norm_lt_one hrnorm).summable
  have hg := (hasSum_geometric_of_norm_lt_one hrnorm).summable
  calc
    (∑' k : ℕ, (k + 1 : ℝ) * r ^ k) =
        ∑' k : ℕ, ((k : ℝ) * r ^ k + r ^ k) := by
      apply tsum_congr
      intro k
      ring
    _ = (∑' k : ℕ, (k : ℝ) * r ^ k) + ∑' k : ℕ, r ^ k :=
      hk.tsum_add hg
    _ = r / (1 - r) ^ 2 + (1 - r)⁻¹ := by
      rw [tsum_coe_mul_geometric_of_norm_lt_one hrnorm,
        tsum_geometric_of_norm_lt_one hrnorm]

/-- Explicit, character-uniform norm bound for the tail after `M`.  This
formalizes the truncation step left as “with a small error” in Lemma 4. -/
theorem norm_shiftedDirectTail_le
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (M : ℕ) {sigma X t : ℝ} (hsigma : 0 ≤ sigma) (hX : 0 < X) :
    ‖∑' k : ℕ,
        shiftedDirectTerm psi sigma X t (k + (M + 1))‖ ≤
      (M + 1 : ℝ) * (Real.exp (-(1 / X))) ^ (M + 1) *
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
    (M + 1 : ℝ) * r ^ (M + 1) * ((k + 1 : ℝ) * r ^ k)
  have hsuccSummable : Summable (fun k : ℕ =>
      (k + 1 : ℝ) * r ^ k) := by
    have hk := (hasSum_coe_mul_geometric_of_norm_lt_one hrnorm).summable
    have hg := (hasSum_geometric_of_norm_lt_one hrnorm).summable
    exact (hk.add hg).congr (fun k => by ring)
  have hgSummable : Summable g :=
    hsuccSummable.mul_left ((M + 1 : ℝ) * r ^ (M + 1))
  have hterm : ∀ k : ℕ,
      ‖shiftedDirectTerm psi sigma X t (k + (M + 1))‖ ≤ g k := by
    intro k
    have hn : 0 < k + (M + 1) := by omega
    have hraw := norm_shiftedDirectTerm_le_nat_mul_exp
      psi hn (X := X) (t := t) hsigma
    rw [exp_neg_nat_div_eq_pow (X := X) (k + (M + 1))] at hraw
    have hnat : (k + (M + 1) : ℝ) ≤
        (M + 1 : ℝ) * (k + 1 : ℝ) := by
      nlinarith [Nat.zero_le (k * M)]
    have hpow : r ^ (k + (M + 1)) =
        r ^ (M + 1) * r ^ k := by
      rw [show k + (M + 1) = (M + 1) + k by omega, pow_add]
    rw [show Real.exp (-(1 / X)) = r by rfl, hpow] at hraw
    calc
      ‖shiftedDirectTerm psi sigma X t (k + (M + 1))‖ ≤
          (k + (M + 1) : ℝ) * (r ^ (M + 1) * r ^ k) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hraw
      _ ≤ ((M + 1 : ℝ) * (k + 1 : ℝ)) *
          (r ^ (M + 1) * r ^ k) := by
        exact mul_le_mul_of_nonneg_right hnat (by positivity)
      _ = g k := by dsimp [g]; ring
  have hnormSummable : Summable (fun k : ℕ =>
      ‖shiftedDirectTerm psi sigma X t (k + (M + 1))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hgSummable
  calc
    ‖∑' k : ℕ,
        shiftedDirectTerm psi sigma X t (k + (M + 1))‖ ≤
        ∑' k : ℕ,
          ‖shiftedDirectTerm psi sigma X t (k + (M + 1))‖ :=
      norm_tsum_le_tsum_norm hnormSummable
    _ ≤ ∑' k : ℕ, g k :=
      hnormSummable.tsum_le_tsum hterm hgSummable
    _ = (M + 1 : ℝ) * r ^ (M + 1) *
        (r / (1 - r) ^ 2 + (1 - r)⁻¹) := by
      unfold g
      rw [tsum_mul_left, tsum_succ_mul_geometric hrpos.le hrlt]
    _ = _ := by rfl

theorem summable_shiftedDirectTerm
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    {sigma X t : ℝ} (hsigma : 0 ≤ sigma) (hX : 0 < X) :
    Summable (shiftedDirectTerm psi sigma X t) := by
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
  have hmajorSummable : Summable (fun n : ℕ => (n : ℝ) * r ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hrnorm).summable
  have hterm : ∀ n : ℕ,
      ‖shiftedDirectTerm psi sigma X t n‖ ≤ (n : ℝ) * r ^ n := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [shiftedDirectTerm, LSeries.term_zero]
    · have h := norm_shiftedDirectTerm_le_nat_mul_exp psi
        (Nat.pos_of_ne_zero hn) (X := X) (t := t) hsigma
      rw [exp_neg_nat_div_eq_pow (X := X) n] at h
      simpa [r] using h
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    hterm hmajorSummable

/-- Exact prefix-plus-tail identity for the shifted direct series. -/
theorem primitiveShiftedDirect_eq_prefix_add_tail
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (M : ℕ) {sigma T t : ℝ} (hsigma : 0 ≤ sigma)
    (hscale : 0 < primitiveShiftedScale d T) :
    primitiveShiftedDirect psi T sigma t =
      (∑ n ∈ Finset.range (M + 1),
        shiftedDirectTerm psi sigma (primitiveShiftedScale d T) t n) +
      ∑' k : ℕ,
        shiftedDirectTerm psi sigma (primitiveShiftedScale d T) t
          (k + (M + 1)) := by
  have hs := summable_shiftedDirectTerm psi hsigma hscale (t := t)
  have hsplit := hs.sum_add_tsum_nat_add (M + 1)
  unfold primitiveShiftedDirect ramachandraShiftedDirect
  rw [show (fun n : ℕ =>
      LSeries.term (ramachandraDivisorCoeff psi)
          (ramachandraShiftedPoint sigma t) n *
        (Real.exp (-((n : ℝ) / primitiveShiftedScale d T)) : ℂ)) =
      shiftedDirectTerm psi sigma (primitiveShiftedScale d T) t by rfl]
  rw [← hsplit]

end
end RamachandraShiftedDirectSeries

#print axioms RamachandraShiftedDirectSeries.shiftedDirectTerm_eq_blockTerm
#print axioms RamachandraShiftedDirectSeries.shiftedDirectDyadicBlock_eq_ramachandraDyadicBlock
#print axioms RamachandraShiftedDirectSeries.integral_sum_norm_shiftedDirectDyadicBlock_sq_le
#print axioms RamachandraShiftedDirectSeries.norm_shiftedDirectTail_le
#print axioms RamachandraShiftedDirectSeries.primitiveShiftedDirect_eq_prefix_add_tail
