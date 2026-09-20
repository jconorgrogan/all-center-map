import HBPerronPacketIndexedSourceV2

/-!
# Exact dyadic partition for MRT Lemma 2.15

This is the finite combinatorial layer used when the factors in the
Heath--Brown identity are split into standard shells.  The value at `1` is
kept separate because the positive natural dyadic cells `(M,2M]` begin at
`M = 1` and therefore cannot contain it.
-/

namespace MRTLemma215DyadicPartition

open scoped BigOperators
open scoped ArithmeticFunction
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPHBPerronSourceData
open ArithmeticFunction

noncomputable section

/-- Number of standard shells required to cover `2 ≤ n ≤ N`. -/
def sourceDyadicCount (N : ℕ) : ℕ := (N - 1).log2 + 1

private theorem log2_mono_of_pos_le {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    m.log2 ≤ n.log2 := by
  by_contra h
  have hsucc : n.log2 + 1 ≤ m.log2 := by omega
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hn0 : n ≠ 0 := Nat.ne_of_gt (hm.trans_le hmn)
  have hlower : 2 ^ (n.log2 + 1) ≤ m :=
    (Nat.le_log2 hm0).mp hsucc
  have hupper : n < 2 ^ (n.log2 + 1) :=
    (Nat.log2_lt hn0).mp (lt_add_one n.log2)
  omega

/-- The shifted logarithmic bucket is exactly `(2^j,2^(j+1)]`. -/
theorem log2_sub_one_eq_iff_mem_Ioc
    {n j : ℕ} (hn : 2 ≤ n) :
    (n - 1).log2 = j ↔ n ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j) := by
  have hm0 : n - 1 ≠ 0 := by omega
  rw [Finset.mem_Ioc]
  constructor
  · intro hlog
    have hlo : 2 ^ (n - 1).log2 ≤ n - 1 := Nat.log2_self_le hm0
    have hhi : n - 1 < 2 ^ ((n - 1).log2 + 1) :=
      (Nat.log2_lt hm0).mp (lt_add_one (n - 1).log2)
    rw [hlog] at hlo hhi
    constructor
    · omega
    · rw [pow_succ] at hhi
      omega
  · rintro ⟨hlo, hhi⟩
    have hlowpow : 2 ^ j ≤ n - 1 := by omega
    have hhighpow : n - 1 < 2 ^ (j + 1) := by
      rw [pow_succ]
      omega
    have hjlow : j ≤ (n - 1).log2 := (Nat.le_log2 hm0).mpr hlowpow
    have hjhigh : (n - 1).log2 < j + 1 :=
      (Nat.log2_lt hm0).mpr hhighpow
    omega

/-- One exact dyadic shell of a coefficient truncated to `[1,N]`. -/
def sourceDyadicCoeff (N : ℕ) (f : ℕ → ℂ)
    (j : Fin (sourceDyadicCount N)) (n : ℕ) : ℂ :=
  if 2 ≤ n ∧ n ≤ N ∧ (n - 1).log2 = (j : ℕ) then f n else 0

/-- The unit-scale coefficient omitted from all positive natural shells. -/
def sourceUnitCoeff (N : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 1 ∧ 1 ≤ N then f n else 0

theorem sourceDyadicCoeff_supported
    (N : ℕ) (f : ℕ → ℂ)
    (j : Fin (sourceDyadicCount N)) :
    SupportedNatDyadic (2 ^ (j : ℕ)) (sourceDyadicCoeff N f j) := by
  intro n hn
  unfold sourceDyadicCoeff
  split_ifs with h
  · exfalso
    apply hn
    exact (log2_sub_one_eq_iff_mem_Ioc h.1).mp h.2.2
  · rfl

theorem sourceDyadicIndex_lt
    {N n : ℕ} (hn2 : 2 ≤ n) (hnN : n ≤ N) :
    (n - 1).log2 < sourceDyadicCount N := by
  unfold sourceDyadicCount
  apply Nat.lt_succ_iff.mpr
  exact log2_mono_of_pos_le (by omega)
    (Nat.sub_le_sub_right hnN 1)

/-- Every coefficient on `[2,N]` is recovered exactly by its unique shell. -/
theorem sum_sourceDyadicCoeff_eq
    (N : ℕ) (f : ℕ → ℂ) {n : ℕ}
    (hn2 : 2 ≤ n) (hnN : n ≤ N) :
    (∑ j : Fin (sourceDyadicCount N), sourceDyadicCoeff N f j n) = f n := by
  let j : Fin (sourceDyadicCount N) :=
    ⟨(n - 1).log2, sourceDyadicIndex_lt hn2 hnN⟩
  rw [Finset.sum_eq_single j]
  · simp [sourceDyadicCoeff, hn2, hnN, j]
  · intro b hb hbj
    unfold sourceDyadicCoeff
    rw [if_neg]
    intro h
    apply hbj
    exact Fin.ext h.2.2.symm
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

theorem sum_sourceDyadicCoeff_eq_zero_of_outside
    (N : ℕ) (f : ℕ → ℂ) {n : ℕ}
    (hn : ¬ (2 ≤ n ∧ n ≤ N)) :
    (∑ j : Fin (sourceDyadicCount N), sourceDyadicCoeff N f j n) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  simp only [sourceDyadicCoeff]
  rw [if_neg]
  exact fun h => hn ⟨h.1, h.2.1⟩

/-- Exact `[1,N]` split into the unit coefficient and positive dyadic cells. -/
theorem unit_add_sum_sourceDyadicCoeff_eq_truncation
    (N : ℕ) (f : ℕ → ℂ) (n : ℕ) :
    sourceUnitCoeff N f n +
        ∑ j : Fin (sourceDyadicCount N), sourceDyadicCoeff N f j n =
      if 1 ≤ n ∧ n ≤ N then f n else 0 := by
  by_cases hn1 : n = 1
  · subst n
    by_cases hN : 1 ≤ N
    · simp [sourceUnitCoeff, hN,
        sum_sourceDyadicCoeff_eq_zero_of_outside]
    · simp [sourceUnitCoeff, hN,
        sum_sourceDyadicCoeff_eq_zero_of_outside]
  · by_cases hnrange : 2 ≤ n ∧ n ≤ N
    · rw [sum_sourceDyadicCoeff_eq N f hnrange.1 hnrange.2]
      rw [sourceUnitCoeff, if_neg (fun h => hn1 h.1)]
      rw [if_pos ⟨hnrange.1.trans' (by norm_num), hnrange.2⟩]
      simp
    · rw [sum_sourceDyadicCoeff_eq_zero_of_outside N f hnrange]
      rw [sourceUnitCoeff, if_neg (fun h => hn1 h.1)]
      simp only [zero_add]
      rw [if_neg]
      intro h
      apply hnrange
      exact ⟨by omega, h.2⟩

/-! ## Arithmetic-function form consumed by the HB convolution -/

def truncatedComplexArithmetic (N : ℕ) (f : ArithmeticFunction ℂ) :
    ArithmeticFunction ℂ where
  toFun n := if 1 ≤ n ∧ n ≤ N then f n else 0
  map_zero' := by simp

def sourceUnitArithmetic (N : ℕ) (f : ArithmeticFunction ℂ) :
    ArithmeticFunction ℂ where
  toFun := sourceUnitCoeff N f
  map_zero' := by simp [sourceUnitCoeff]

def sourceDyadicArithmetic (N : ℕ) (f : ArithmeticFunction ℂ)
    (j : Fin (sourceDyadicCount N)) : ArithmeticFunction ℂ where
  toFun := sourceDyadicCoeff N f j
  map_zero' := by simp [sourceDyadicCoeff]

theorem sourceDyadicArithmetic_supported
    (N : ℕ) (f : ArithmeticFunction ℂ)
    (j : Fin (sourceDyadicCount N)) :
    SupportedNatDyadic (2 ^ (j : ℕ)) (sourceDyadicArithmetic N f j) :=
  sourceDyadicCoeff_supported N f j

theorem arithmeticFunction_finsetSum_apply
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (F : ι → ArithmeticFunction ℂ) (n : ℕ) :
    (∑ i ∈ S, F i) n = ∑ i ∈ S, F i n := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      simp [ha, ih, ArithmeticFunction.add_apply]

/-- Equality in the Dirichlet-convolution ring, not only coefficientwise. -/
theorem truncatedComplexArithmetic_eq_unit_add_sum
    (N : ℕ) (f : ArithmeticFunction ℂ) :
    truncatedComplexArithmetic N f =
      sourceUnitArithmetic N f +
        ∑ j : Fin (sourceDyadicCount N), sourceDyadicArithmetic N f j := by
  ext n
  rw [ArithmeticFunction.add_apply]
  have hsum :
      (∑ j : Fin (sourceDyadicCount N), sourceDyadicArithmetic N f j) n =
        ∑ j : Fin (sourceDyadicCount N), (sourceDyadicArithmetic N f j) n := by
    simpa using arithmeticFunction_finsetSum_apply
      (Finset.univ : Finset (Fin (sourceDyadicCount N)))
      (fun j => sourceDyadicArithmetic N f j) n
  rw [hsum]
  simpa [truncatedComplexArithmetic, sourceUnitArithmetic, sourceDyadicArithmetic] using
      (unit_add_sum_sourceDyadicCoeff_eq_truncation N f n).symm

/-- Exact two-factor expansion after isolating both unit coefficients. -/
theorem truncatedComplexArithmetic_mul_eq_shell_expansion
    (N M : ℕ) (f g : ArithmeticFunction ℂ) :
    truncatedComplexArithmetic N f * truncatedComplexArithmetic M g =
      sourceUnitArithmetic N f * sourceUnitArithmetic M g +
      sourceUnitArithmetic N f *
        (∑ j : Fin (sourceDyadicCount M), sourceDyadicArithmetic M g j) +
      (∑ i : Fin (sourceDyadicCount N), sourceDyadicArithmetic N f i) *
        sourceUnitArithmetic M g +
      (∑ i : Fin (sourceDyadicCount N), sourceDyadicArithmetic N f i) *
        (∑ j : Fin (sourceDyadicCount M), sourceDyadicArithmetic M g j) := by
  rw [truncatedComplexArithmetic_eq_unit_add_sum,
    truncatedComplexArithmetic_eq_unit_add_sum]
  ring

/-! ## Complexification of the published real HB identity -/

def complexifyArithmetic (f : ArithmeticFunction ℝ) : ArithmeticFunction ℂ where
  toFun n := (f n : ℂ)
  map_zero' := by simp

@[simp] theorem complexifyArithmetic_apply
    (f : ArithmeticFunction ℝ) (n : ℕ) :
    complexifyArithmetic f n = (f n : ℂ) := rfl

theorem complexifyArithmetic_zero :
    complexifyArithmetic (0 : ArithmeticFunction ℝ) = 0 := by
  ext n
  simp [complexifyArithmetic]

theorem complexifyArithmetic_one :
    complexifyArithmetic (1 : ArithmeticFunction ℝ) = 1 := by
  ext n
  by_cases hn : n = 1
  · subst n
    simp [complexifyArithmetic]
  · simp [complexifyArithmetic, hn]

theorem complexifyArithmetic_add (f g : ArithmeticFunction ℝ) :
    complexifyArithmetic (f + g) =
      complexifyArithmetic f + complexifyArithmetic g := by
  ext n
  simp [complexifyArithmetic, ArithmeticFunction.add_apply]

theorem complexifyArithmetic_mul (f g : ArithmeticFunction ℝ) :
    complexifyArithmetic (f * g) =
      complexifyArithmetic f * complexifyArithmetic g := by
  ext n
  change (((f * g) n : ℝ) : ℂ) =
    (complexifyArithmetic f * complexifyArithmetic g) n
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro z hz
  exact Complex.ofReal_mul (f z.1) (g z.2)

theorem complexifyArithmetic_pow (f : ArithmeticFunction ℝ) (k : ℕ) :
    complexifyArithmetic (f ^ k) = complexifyArithmetic f ^ k := by
  induction k with
  | zero => simp [complexifyArithmetic_one]
  | succ k ih =>
      rw [pow_succ, pow_succ, complexifyArithmetic_mul, ih]

theorem complexifyArithmetic_finsetSum
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (F : ι → ArithmeticFunction ℝ) :
    complexifyArithmetic (∑ i ∈ S, F i) =
      ∑ i ∈ S, complexifyArithmetic (F i) := by
  induction S using Finset.induction_on with
  | empty => simp [complexifyArithmetic_zero]
  | @insert a S ha ih =>
      simp [ha, ih, complexifyArithmetic_add]

/-! ## Truncation is exact inside finite Dirichlet convolutions -/

theorem antidiagonal_left_le
    {n : ℕ} {z : ℕ × ℕ} (hz : z ∈ n.divisorsAntidiagonal) : z.1 ≤ n := by
  have hmul : z.1 * z.2 = n := (Nat.mem_divisorsAntidiagonal.mp hz).1
  have hn0 : n ≠ 0 := (Nat.mem_divisorsAntidiagonal.mp hz).2
  have hright0 : z.2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hmul
    exact hn0 hmul.symm
  have hpos : 0 < z.2 := Nat.pos_of_ne_zero hright0
  rw [← hmul]
  exact Nat.le_mul_of_pos_right z.1 hpos

theorem mul_apply_congr_on_divisors
    {f f' g g' : ArithmeticFunction ℂ} {n : ℕ}
    (hf : ∀ d, d ≤ n → f d = f' d)
    (hg : ∀ d, d ≤ n → g d = g' d) :
    (f * g) n = (f' * g') n := by
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro z hz
  rw [hf z.1 (antidiagonal_left_le hz),
    hg z.2 (MAPHeathBrownFiniteIdentity.antidiagonal_right_le hz)]

theorem pow_apply_congr_on_divisors
    {f g : ArithmeticFunction ℂ} {n k : ℕ}
    (hfg : ∀ d, d ≤ n → f d = g d) :
    (f ^ k) n = (g ^ k) n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, pow_succ]
      apply mul_apply_congr_on_divisors
      · intro d hd
        exact ih (fun e he => hfg e (he.trans hd))
      · exact hfg

theorem truncatedComplexArithmetic_apply_of_mem
    {N n : ℕ} (f : ArithmeticFunction ℂ)
    (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    truncatedComplexArithmetic N f n = f n := by
  simp [truncatedComplexArithmetic, hn1, hnN]

theorem mul_truncation_apply_of_le
    {N n : ℕ} (f g : ArithmeticFunction ℂ)
    (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    (f * g) n =
      (truncatedComplexArithmetic N f * truncatedComplexArithmetic N g) n := by
  apply mul_apply_congr_on_divisors
  · intro d hd
    by_cases hd0 : d = 0
    · subst d
      exact f.map_zero'.trans (truncatedComplexArithmetic N f).map_zero'.symm
    · exact (truncatedComplexArithmetic_apply_of_mem f
        (Nat.one_le_iff_ne_zero.mpr hd0) (hd.trans hnN)).symm
  · intro d hd
    by_cases hd0 : d = 0
    · subst d
      exact g.map_zero'.trans (truncatedComplexArithmetic N g).map_zero'.symm
    · exact (truncatedComplexArithmetic_apply_of_mem g
        (Nat.one_le_iff_ne_zero.mpr hd0) (hd.trans hnN)).symm

end
end MRTLemma215DyadicPartition

#print axioms MRTLemma215DyadicPartition.sourceDyadicCoeff_supported
#print axioms MRTLemma215DyadicPartition.unit_add_sum_sourceDyadicCoeff_eq_truncation
#print axioms MRTLemma215DyadicPartition.truncatedComplexArithmetic_eq_unit_add_sum
#print axioms MRTLemma215DyadicPartition.truncatedComplexArithmetic_mul_eq_shell_expansion
#print axioms MRTLemma215DyadicPartition.complexifyArithmetic_mul
#print axioms MRTLemma215DyadicPartition.complexifyArithmetic_pow
#print axioms MRTLemma215DyadicPartition.mul_apply_congr_on_divisors
#print axioms MRTLemma215DyadicPartition.pow_apply_congr_on_divisors
