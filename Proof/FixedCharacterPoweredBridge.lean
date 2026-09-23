import CGLProofDAG
import ShiuAnalyticLayer
import AppendixTypeIPowerAlgebra

/-!
# Fixed-character powered large-value bridge: finite and exponent layer

This staging module extends the frozen `CGLProofDAG` certificate without
modifying the authoritative module.  It proves the remaining elementary
parts of the power argument: identification and subpolynomial growth of the
ordered divisor majorant, an exact multiplicative dyadic decomposition, a
common-block pigeonhole lemma, and the bounded choice of power in the
Guth--Maynard window.  The two published analytic inequalities remain explicit
proposition inputs.
-/

namespace FixedCharacterPoweredBridge

open scoped BigOperators ArithmeticFunction.zeta
open ArithmeticFunction
open CGLProofDAG

noncomputable section

/-! ## Uniform coefficient majorant -/

theorem orderedDivisorCount_eq_tauAF (k : ℕ) :
    orderedDivisorCount k = MixedMellinCert.tauAF k := by
  rfl

/-- A positive ordered divisor count is at least one.  Stating the premise
explicitly avoids a false claim at `n = 0`. -/
theorem one_le_orderedDivisorCount_of_pos
    (k n : ℕ) (hn : 0 < orderedDivisorCount k n) :
    1 ≤ orderedDivisorCount k n := hn

/-- For fixed positive power `k`, the exact convolution majorant is
subpolynomial.  This is an elementary consequence of the already-certified
integer-moment bound for `tau_k^2`; no analytic divisor estimate is imported. -/
theorem orderedDivisorCount_subpolynomial (k : ℕ) (hk : 1 ≤ k) :
    ∀ η : ℝ, 0 < η →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
        (orderedDivisorCount k n : ℝ) ≤ C * Real.rpow n η := by
  intro η hη
  obtain ⟨C, hC, hbound⟩ :=
    ShiuAnalyticLayer.tauAF_square_subpolynomial k hk η hη
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hnat : 1 ≤ orderedDivisorCount k n := by
    rw [orderedDivisorCount_eq_tauAF]
    have hkpos : 0 < k := Nat.zero_lt_of_lt hk
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    rw [ShiuFoundation.tauAF_eq_factorization_prod k n hn0]
    exact Finset.one_le_prod₀ (fun p hp => by
      change 1 ≤ k.multichoose (n.factorization p)
      rw [Nat.multichoose_eq]
      exact Nat.choose_pos (by omega))
  have hsquareNat : orderedDivisorCount k n ≤ orderedDivisorCount k n ^ 2 := by
    have hmul := Nat.mul_le_mul_left (orderedDivisorCount k n) hnat
    simpa [pow_two] using hmul
  have hsquare :
      (orderedDivisorCount k n : ℝ) ≤
        ((orderedDivisorCount k n ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hsquareNat
  calc
    (orderedDivisorCount k n : ℝ) ≤
        (orderedDivisorCount k n ^ 2 : ℕ) := hsquare
    _ = (MixedMellinCert.tauAF k n ^ 2 : ℕ) := by
      rw [orderedDivisorCount_eq_tauAF]
    _ ≤ C * Real.rpow n η := by
      simpa [orderedDivisorCount_eq_tauAF] using hbound n hn

/-! ## Exact multiplicative dyadic blocks -/

/-- The `i`-th dyadic subblock of the literal powered support
`(N^k,(2N)^k]`. -/
def poweredDyadicBlock (baseN k : ℕ) (a : ℕ → ℂ)
    (i m : ℕ) : ℂ :=
  if m ∈ Finset.Ioc (baseN ^ k * 2 ^ i)
      (baseN ^ k * 2 ^ (i + 1)) then
    (dyadicCoefficient baseN a ^ k) m
  else 0

/-- The finite union of the `k` consecutive multiplicative dyadic blocks. -/
def multiplicativeDyadicUnion (baseN k : ℕ) : Finset ℕ :=
  Finset.univ.biUnion (fun i : Fin k =>
    Finset.Ioc (baseN ^ k * 2 ^ (i : ℕ))
      (baseN ^ k * 2 ^ ((i : ℕ) + 1)))

theorem multiplicativeDyadicUnion_eq_Ioc (baseN k : ℕ) :
    multiplicativeDyadicUnion baseN k =
      Finset.Ioc (baseN ^ k) ((2 * baseN) ^ k) := by
  classical
  ext m
  simp only [multiplicativeDyadicUnion, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_Ioc]
  constructor
  · rintro ⟨i, hiLower, hiUpper⟩
    constructor
    · exact lt_of_le_of_lt
        (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos (i : ℕ))) hiLower
    · calc
        m ≤ baseN ^ k * 2 ^ ((i : ℕ) + 1) := hiUpper
        _ ≤ baseN ^ k * 2 ^ k := by
          exact Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right (by omega) (Nat.succ_le_iff.mpr i.isLt))
        _ = (2 * baseN) ^ k := by ring
  · rintro ⟨hmLower, hmUpper⟩
    by_cases hk : k = 0
    · subst k
      simp at hmLower hmUpper
      omega
    · let S : Finset ℕ := Finset.filter
          (fun i => m ≤ baseN ^ k * 2 ^ (i + 1)) (Finset.range k)
      have hS : S.Nonempty := by
        refine ⟨k - 1, ?_⟩
        simp only [S, Finset.mem_filter, Finset.mem_range]
        constructor
        · omega
        · have hpow : (k - 1) + 1 = k := by omega
          rw [hpow]
          simpa [mul_pow, mul_comm] using hmUpper
      let i : ℕ := S.min' hS
      have hiS : i ∈ S := Finset.min'_mem S hS
      have hik : i < k := Finset.mem_range.mp (Finset.mem_filter.mp hiS).1
      refine ⟨⟨i, hik⟩, ?_, (Finset.mem_filter.mp hiS).2⟩
      by_cases hi0 : i = 0
      · simpa [hi0] using hmLower
      · have him1 : i - 1 ∈ Finset.range k := by
          simp [Finset.mem_range]
          omega
        have hnot : i - 1 ∉ S := by
          intro hmem
          have := Finset.min'_le S (i - 1) hmem
          omega
        have hfail : ¬m ≤ baseN ^ k * 2 ^ ((i - 1) + 1) := by
          intro h
          exact hnot (Finset.mem_filter.mpr ⟨him1, h⟩)
        have hidx : (i - 1) + 1 = i := by omega
        rw [hidx] at hfail
        change baseN ^ k * 2 ^ i < m
        omega

/-- Distinct dyadic indices have disjoint half-open blocks. -/
theorem multiplicative_dyadic_index_unique
    {baseN k m : ℕ} {i j : Fin k}
    (hi : m ∈ Finset.Ioc (baseN ^ k * 2 ^ (i : ℕ))
      (baseN ^ k * 2 ^ ((i : ℕ) + 1)))
    (hj : m ∈ Finset.Ioc (baseN ^ k * 2 ^ (j : ℕ))
      (baseN ^ k * 2 ^ ((j : ℕ) + 1))) : i = j := by
  apply Fin.ext
  rcases Finset.mem_Ioc.mp hi with ⟨hiLower, hiUpper⟩
  rcases Finset.mem_Ioc.mp hj with ⟨hjLower, hjUpper⟩
  by_contra hij
  have hor : (i : ℕ) < j ∨ (j : ℕ) < i := lt_or_gt_of_ne (by simpa using hij)
  cases hor with
  | inl hlt =>
      have hpow : 2 ^ ((i : ℕ) + 1) ≤ 2 ^ (j : ℕ) := by
        exact Nat.pow_le_pow_right (by omega) (by omega)
      have : baseN ^ k * 2 ^ ((i : ℕ) + 1) ≤
          baseN ^ k * 2 ^ (j : ℕ) := Nat.mul_le_mul_left _ hpow
      omega
  | inr hlt =>
      have hpow : 2 ^ ((j : ℕ) + 1) ≤ 2 ^ (i : ℕ) := by
        exact Nat.pow_le_pow_right (by omega) (by omega)
      have : baseN ^ k * 2 ^ ((j : ℕ) + 1) ≤
          baseN ^ k * 2 ^ (i : ℕ) := Nat.mul_le_mul_left _ hpow
      omega

/-- Pointwise reconstruction of a powered coefficient from its `k` dyadic
blocks, on the exact powered support. -/
theorem sum_poweredDyadicBlock_eq
    {baseN k m : ℕ} {a : ℕ → ℂ}
    (hm : m ∈ Finset.Ioc (baseN ^ k) ((2 * baseN) ^ k)) :
    (∑ i : Fin k, poweredDyadicBlock baseN k a i m) =
      (dyadicCoefficient baseN a ^ k) m := by
  classical
  have hmem : m ∈ multiplicativeDyadicUnion baseN k := by
    rw [multiplicativeDyadicUnion_eq_Ioc]
    exact hm
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hmem
  have hiValue : poweredDyadicBlock baseN k a i m =
      (dyadicCoefficient baseN a ^ k) m := by
    simp [poweredDyadicBlock, hi]
  rw [← hiValue]
  apply Finset.sum_eq_single i
  · intro j hj hji
    have hnot : m ∉ Finset.Ioc (baseN ^ k * 2 ^ (j : ℕ))
        (baseN ^ k * 2 ^ ((j : ℕ) + 1)) := by
      intro hjm
      exact hji (multiplicative_dyadic_index_unique hjm hi)
    simp [poweredDyadicBlock, hnot]
  · intro hiNot
    exact (hiNot (Finset.mem_univ i)).elim

/-! ## Phase-preserving powered polynomial identity -/

theorem term_eq_phase (f : ArithmeticFunction ℂ) (t : ℝ) (n : ℕ) :
    LSeries.term f (-(Complex.I * (t : ℂ))) n =
      f n * Complex.exp (Complex.I * (t * Real.log n)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_def₀ f.map_zero]
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn)]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_log hnpos.le]
    congr 2
    push_cast
    ring


theorem dyadicCoefficient_mem_of_ne_zero
    {N : ℕ} {a : ℕ → ℂ} {n : ℕ}
    (hn : CGLProofDAG.dyadicCoefficient N a n ≠ 0) :
    n ∈ Finset.Ioc N (2 * N) := by
  by_contra hmem
  have hz : CGLProofDAG.dyadicCoefficient N a n = 0 := by
    change (if n ∈ Finset.Ioc N (2 * N) then a n else 0) = 0
    rw [if_neg hmem]
  exact hn hz

theorem dyadic_powered_coefficient_support
    {N k m : ℕ} {a : ℕ → ℂ} (hk : 0 < k)
    (hm : (CGLProofDAG.dyadicCoefficient N a ^ k) m ≠ 0) :
    m ∈ Finset.Ioc (N ^ k) ((2 * N) ^ k) := by
  induction k using Nat.twoStepInduction generalizing m with
  | zero => simp at hk
  | one =>
      simpa using dyadicCoefficient_mem_of_ne_zero (by simpa using hm)
  | more k ih0 ih1 =>
      rw [pow_succ, ArithmeticFunction.mul_apply] at hm
      obtain ⟨p, hp, hpne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
      rcases mul_ne_zero_iff.mp hpne with ⟨hp1ne, hp2ne⟩
      have hp1 := ih1 (by omega) hp1ne
      have hp2 := dyadicCoefficient_mem_of_ne_zero hp2ne
      rcases Finset.mem_Ioc.mp hp1 with ⟨hp1lo, hp1hi⟩
      rcases Finset.mem_Ioc.mp hp2 with ⟨hp2lo, hp2hi⟩
      have hprod : p.1 * p.2 = m := (Nat.mem_divisorsAntidiagonal.mp hp).1
      rw [← hprod, Finset.mem_Ioc]
      constructor
      · rw [pow_succ]
        by_cases hN : N = 0
        · subst N
          simp at hp1lo hp2lo ⊢
          exact ⟨hp1lo, hp2lo⟩
        · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
          calc
            N ^ (k + 1) * N < p.1 * N :=
              Nat.mul_lt_mul_of_pos_right hp1lo hNpos
            _ < p.1 * p.2 :=
              Nat.mul_lt_mul_of_pos_left hp2lo (Nat.zero_lt_of_lt hp1lo)
      · rw [pow_succ]
        exact Nat.mul_le_mul hp1hi hp2hi


theorem LSeries_eq_intervalPolynomial_of_support
    (f : ArithmeticFunction ℂ) (A B : ℕ) (t : ℝ)
    (hsupport : ∀ {n : ℕ}, f n ≠ 0 → n ∈ Finset.Ioc A B) :
    LSeries f (-(Complex.I * (t : ℂ))) =
      ∑ n ∈ Finset.Ioc A B,
        f n * Complex.exp (Complex.I * (t * Real.log n)) := by
  unfold LSeries
  calc
    (∑' n, LSeries.term f (-(Complex.I * (t : ℂ))) n) =
        ∑ n ∈ Finset.Ioc A B,
          LSeries.term f (-(Complex.I * (t : ℂ))) n := by
      apply tsum_eq_sum
      intro n hn
      by_cases hfn : f n = 0
      · rw [term_eq_phase, hfn]
        simp
      · exact (hn (hsupport hfn)).elim
    _ = ∑ n ∈ Finset.Ioc A B,
        f n * Complex.exp (Complex.I * (t * Real.log n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact term_eq_phase f t n

theorem LSeriesSummable_of_finite_interval_support
    (f : ArithmeticFunction ℂ) (A B : ℕ) (s : ℂ)
    (hsupport : ∀ {n : ℕ}, f n ≠ 0 → n ∈ Finset.Ioc A B) :
    LSeriesSummable f s := by
  unfold LSeriesSummable
  apply summable_of_hasFiniteSupport
  rw [Function.HasFiniteSupport]
  exact (Finset.finite_toSet (Finset.Ioc A B)).subset (by
    intro n hn
    by_contra hnmem
    have hfn : f n = 0 := by
      by_contra hne
      exact hnmem (hsupport hne)
    rw [Function.mem_support] at hn
    apply hn
    by_cases hn0 : n = 0
    · subst n
      simp
    · rw [LSeries.term_of_ne_zero hn0, hfn]
      simp)

theorem LSeries_dyadic_power_eq_power
    {N k : ℕ} {a : ℕ → ℂ} (hk : 0 < k) (s : ℂ) :
    LSeries (⇑((CGLProofDAG.dyadicCoefficient N a) ^ k)) s =
      LSeries (CGLProofDAG.dyadicCoefficient N a) s ^ k := by
  induction k using Nat.twoStepInduction with
  | zero => simp at hk
  | one => simp
  | more k ih0 ih1 =>
      have hpowSummable :
          LSeriesSummable
            (⇑((CGLProofDAG.dyadicCoefficient N a) ^ (k + 1))) s :=
        LSeriesSummable_of_finite_interval_support
          (CGLProofDAG.dyadicCoefficient N a ^ (k + 1))
          (N ^ (k + 1)) ((2 * N) ^ (k + 1)) s
          (dyadic_powered_coefficient_support (by omega))
      have hbaseSummable :
          LSeriesSummable (CGLProofDAG.dyadicCoefficient N a) s :=
        LSeriesSummable_of_finite_interval_support
          (CGLProofDAG.dyadicCoefficient N a) N (2 * N) s
          dyadicCoefficient_mem_of_ne_zero
      rw [pow_succ, ArithmeticFunction.LSeries_mul' hpowSummable hbaseSummable,
        ih1 (by omega)]
      ring

theorem LSeries_dyadicCoefficient_eq_dirichletPolynomial
    (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    LSeries (CGLProofDAG.dyadicCoefficient N a)
        (-(Complex.I * (t : ℂ))) =
      CGLProofDAG.dirichletPolynomial a N t := by
  rw [LSeries_eq_intervalPolynomial_of_support _ N (2 * N) t
    dyadicCoefficient_mem_of_ne_zero]
  unfold CGLProofDAG.dirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hcoeff : CGLProofDAG.dyadicCoefficient N a n = a n := by
    change (if n ∈ Finset.Ioc N (2 * N) then a n else 0) = a n
    rw [if_pos hn]
  rw [hcoeff]

/-- Literal phase-preserving power identity.  Equal product tuples are grouped
by Dirichlet convolution, and the phase remains `exp(i t log m)`. -/
theorem dirichletPolynomial_pow_eq_powered_interval
    {N k : ℕ} {a : ℕ → ℂ} (hk : 0 < k) (t : ℝ) :
    CGLProofDAG.dirichletPolynomial a N t ^ k =
      ∑ m ∈ Finset.Ioc (N ^ k) ((2 * N) ^ k),
        (CGLProofDAG.dyadicCoefficient N a ^ k) m *
          Complex.exp (Complex.I * (t * Real.log m)) := by
  calc
    CGLProofDAG.dirichletPolynomial a N t ^ k =
        LSeries (CGLProofDAG.dyadicCoefficient N a)
          (-(Complex.I * (t : ℂ))) ^ k := by
      rw [LSeries_dyadicCoefficient_eq_dirichletPolynomial]
    _ = LSeries (⇑((CGLProofDAG.dyadicCoefficient N a) ^ k))
          (-(Complex.I * (t : ℂ))) :=
      (LSeries_dyadic_power_eq_power hk _).symm
    _ = ∑ m ∈ Finset.Ioc (N ^ k) ((2 * N) ^ k),
        (CGLProofDAG.dyadicCoefficient N a ^ k) m *
          Complex.exp (Complex.I * (t * Real.log m)) :=
      LSeries_eq_intervalPolynomial_of_support _ _ _ t
        (dyadic_powered_coefficient_support hk)

/-- The full collected polynomial, before the multiplicative dyadic split. -/
def poweredIntervalPolynomial (baseN k : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioc (baseN ^ k) ((2 * baseN) ^ k),
    (dyadicCoefficient baseN a ^ k) m *
      Complex.exp (Complex.I * (t * Real.log m))

/-- A block written over the common full support with an indicator
coefficient.  This representation makes the simultaneous block decomposition
an exact finite sum identity. -/
def poweredBlockPolynomial (baseN k : ℕ) (a : ℕ → ℂ)
    (i : Fin k) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioc (baseN ^ k) ((2 * baseN) ^ k),
    poweredDyadicBlock baseN k a i m *
      Complex.exp (Complex.I * (t * Real.log m))

theorem sum_poweredBlockPolynomial_eq
    {baseN k : ℕ} {a : ℕ → ℂ} (t : ℝ) :
    (∑ i : Fin k, poweredBlockPolynomial baseN k a i t) =
      poweredIntervalPolynomial baseN k a t := by
  classical
  unfold poweredBlockPolynomial poweredIntervalPolynomial
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_mul, sum_poweredDyadicBlock_eq hm]

/-- Each full-support indicator block is literally the standard dyadic
Dirichlet polynomial to which the published estimates apply. -/
theorem poweredBlockPolynomial_eq_dirichletPolynomial
    {baseN k : ℕ} {a : ℕ → ℂ} (i : Fin k) (t : ℝ) :
    poweredBlockPolynomial baseN k a i t =
      dirichletPolynomial (fun m => (dyadicCoefficient baseN a ^ k) m)
        (baseN ^ k * 2 ^ (i : ℕ)) t := by
  classical
  let blockN := baseN ^ k * 2 ^ (i : ℕ)
  let full := Finset.Ioc (baseN ^ k) ((2 * baseN) ^ k)
  let block := Finset.Ioc blockN (2 * blockN)
  have hupper : 2 * blockN = baseN ^ k * 2 ^ ((i : ℕ) + 1) := by
    dsimp [blockN]
    rw [pow_succ]
    ring
  have hsubset : block ⊆ full := by
    intro m hm
    rcases Finset.mem_Ioc.mp hm with ⟨hmLower, hmUpper⟩
    apply Finset.mem_Ioc.mpr
    constructor
    · exact lt_of_le_of_lt
        (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos (i : ℕ))) hmLower
    · calc
        m ≤ 2 * blockN := hmUpper
        _ = baseN ^ k * 2 ^ ((i : ℕ) + 1) := hupper
        _ ≤ baseN ^ k * 2 ^ k := by
          exact Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right (by omega) (Nat.succ_le_iff.mpr i.isLt))
        _ = (2 * baseN) ^ k := by ring
  have hzero : ∀ m ∈ full, m ∉ block →
      poweredDyadicBlock baseN k a i m *
        Complex.exp (Complex.I * (t * Real.log m)) = 0 := by
    intro m hmFull hmBlock
    have hmLiteral : m ∉ Finset.Ioc (baseN ^ k * 2 ^ (i : ℕ))
        (baseN ^ k * 2 ^ ((i : ℕ) + 1)) := by
      simpa [block, blockN, hupper] using hmBlock
    simp [poweredDyadicBlock, hmLiteral]
  unfold poweredBlockPolynomial dirichletPolynomial
  change (∑ m ∈ full,
      poweredDyadicBlock baseN k a i m *
        Complex.exp (Complex.I * (t * Real.log m))) = _
  rw [← Finset.sum_subset hsubset hzero]
  apply Finset.sum_congr
  · simp [block, blockN]
  · intro m hm
    have hmLiteral : m ∈ Finset.Ioc (baseN ^ k * 2 ^ (i : ℕ))
        (baseN ^ k * 2 ^ ((i : ℕ) + 1)) := by
      simpa [block, blockN, hupper] using hm
    simp [poweredDyadicBlock, hmLiteral]

theorem dirichletPolynomial_pow_eq_sum_blocks
    {N k : ℕ} {a : ℕ → ℂ} (hk : 0 < k) (t : ℝ) :
    dirichletPolynomial a N t ^ k =
      ∑ i : Fin k, poweredBlockPolynomial N k a i t := by
  calc
    dirichletPolynomial a N t ^ k = poweredIntervalPolynomial N k a t := by
      simpa [poweredIntervalPolynomial] using
        dirichletPolynomial_pow_eq_powered_interval hk t
    _ = ∑ i : Fin k, poweredBlockPolynomial N k a i t :=
      (sum_poweredBlockPolynomial_eq t).symm


/-! ## Bounded power and one common block -/

/-- A real interval of width at least the starting exponent contains a
positive integral multiple of the base length.  This is the exact bounded
power choice in GM Section 13.1. -/
theorem exists_power_in_guthMaynard_window
    {σ lam : ℝ}
    (hσlow : 7 / 10 ≤ σ) (hσhigh : σ ≤ 4 / 5)
    (hlam : 0 < lam) (hlamHigh : lam ≤ 1 / 2) :
    ∃ k : ℕ, 1 ≤ k ∧
      AppendixTypeIPower.poweredLengthLower σ ≤ k * lam ∧
      k * lam ≤ AppendixTypeIPower.poweredLengthUpper σ := by
  let L := AppendixTypeIPower.poweredLengthLower σ
  let U := AppendixTypeIPower.poweredLengthUpper σ
  have hden : 0 < 6 + 10 * σ := by nlinarith
  have hL : 0 < L := by
    dsimp [L, AppendixTypeIPower.poweredLengthLower]
    positivity
  have hUL : U = (3 / 2 : ℝ) * L := by
    dsimp [U, L, AppendixTypeIPower.poweredLengthUpper,
      AppendixTypeIPower.poweredLengthLower]
    field_simp
    ring
  by_cases hlarge : L / 2 ≤ lam
  · refine ⟨2, by omega, ?_, ?_⟩
    · change L ≤ (2 : ℝ) * lam
      nlinarith
    · change (2 : ℝ) * lam ≤ U
      have hUone : 1 ≤ U := by
        dsimp [U, AppendixTypeIPower.poweredLengthUpper]
        rw [one_le_div hden]
        nlinarith
      nlinarith [hlamHigh]
  · let k : ℕ := ⌈L / lam⌉₊
    have hratio : 0 < L / lam := div_pos hL hlam
    have hkpos : 1 ≤ k := by
      exact Nat.one_le_iff_ne_zero.mpr (by
        intro hk0
        have := Nat.ceil_pos.mpr hratio
        omega)
    refine ⟨k, hkpos, ?_, ?_⟩
    · have hceil : L / lam ≤ k := Nat.le_ceil (L / lam)
      have := mul_le_mul_of_nonneg_right hceil hlam.le
      change L ≤ (k : ℝ) * lam
      simpa [div_mul_cancel₀ _ (ne_of_gt hlam)] using this
    · have hceil : (k : ℝ) < L / lam + 1 := Nat.ceil_lt_add_one hratio.le
      have hbound : (k : ℝ) * lam < L + lam := by
        have := mul_lt_mul_of_pos_right hceil hlam
        field_simp [ne_of_gt hlam] at this
        nlinarith
      have hsmall : lam < L / 2 := lt_of_not_ge hlarge
      change (k : ℝ) * lam ≤ U
      rw [hUL]
      nlinarith

/-- If the original dyadic length has exponent at least `κ`, the selected
power is bounded solely in terms of `κ`.  This makes the subsequent divisor
constant uniform in `T`, `N`, and the ordinate set. -/
theorem exists_bounded_power_in_guthMaynard_window
    {σ lam κ : ℝ}
    (hσlow : 7 / 10 ≤ σ) (hσhigh : σ ≤ 4 / 5)
    (hκ : 0 < κ) (hκlam : κ ≤ lam)
    (hlamHigh : lam ≤ 1 / 2) :
    ∃ k : ℕ, 1 ≤ k ∧
      k ≤ ⌈AppendixTypeIPower.poweredLengthUpper σ / κ⌉₊ ∧
      AppendixTypeIPower.poweredLengthLower σ ≤ k * lam ∧
      k * lam ≤ AppendixTypeIPower.poweredLengthUpper σ := by
  have hlam : 0 < lam := hκ.trans_le hκlam
  obtain ⟨k, hk, hlow, hhigh⟩ :=
    exists_power_in_guthMaynard_window hσlow hσhigh hlam hlamHigh
  have hkκ : (k : ℝ) * κ ≤ AppendixTypeIPower.poweredLengthUpper σ := by
    exact (mul_le_mul_of_nonneg_left hκlam (Nat.cast_nonneg k)).trans hhigh
  have hkdiv : (k : ℝ) ≤ AppendixTypeIPower.poweredLengthUpper σ / κ := by
    exact (le_div_iff₀ hκ).2 (by simpa [mul_comm] using hkκ)
  have hkceil : (k : ℝ) ≤
      ⌈AppendixTypeIPower.poweredLengthUpper σ / κ⌉₊ :=
    hkdiv.trans (Nat.le_ceil _)
  refine ⟨k, hk, ?_, hlow, hhigh⟩
  exact_mod_cast hkceil

/-- Uniform `d_k(m) ≤ T^η` after the fixed-power subpolynomial bound and the
standard absorption of its constant.  The two absorption premises are later
discharged by enlarging the global `T₀`; all exponent arithmetic is proved
here. -/
theorem orderedDivisorCount_le_time_subpower
    {k m : ℕ} {T B η : ℝ}
    (hk : 1 ≤ k) (hm : 0 < m)
    (hT : 1 ≤ T) (hB : 0 < B) (hη : 0 < η)
    (hmT : (m : ℝ) ≤ Real.rpow T B) :
    ∃ C : ℝ, 0 < C ∧
      (C ≤ Real.rpow T (η / 2) →
        (orderedDivisorCount k m : ℝ) ≤ Real.rpow T η) := by
  let e : ℝ := η / (2 * B)
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨C, hC, hdiv⟩ := orderedDivisorCount_subpolynomial k hk e he
  refine ⟨C, hC, ?_⟩
  intro hCabs
  have hmnonneg : (0 : ℝ) ≤ m := by positivity
  have hpowm : Real.rpow m e ≤ Real.rpow (Real.rpow T B) e :=
    Real.rpow_le_rpow hmnonneg hmT he.le
  have hTnonneg : 0 ≤ T := le_trans (by norm_num) hT
  have hbe : B * e = η / 2 := by
    dsimp [e]
    field_simp
  have hpowm' : Real.rpow m e ≤ Real.rpow T (η / 2) := by
    calc
      Real.rpow m e ≤ Real.rpow (Real.rpow T B) e := hpowm
      _ = Real.rpow T (B * e) := (Real.rpow_mul hTnonneg B e).symm
      _ = Real.rpow T (η / 2) := by rw [hbe]
  calc
    (orderedDivisorCount k m : ℝ) ≤ C * Real.rpow m e := hdiv m hm
    _ ≤ Real.rpow T (η / 2) * Real.rpow T (η / 2) :=
      mul_le_mul hCabs hpowm' (Real.rpow_nonneg hmnonneg _)
        (Real.rpow_nonneg hTnonneg _)
    _ = Real.rpow T η := by
      calc
        Real.rpow T (η / 2) * Real.rpow T (η / 2) =
            Real.rpow T (η / 2 + η / 2) :=
          (Real.rpow_add (lt_of_lt_of_le (by norm_num) hT) _ _).symm
        _ = Real.rpow T η := by congr 1; ring

/-! ## Exact GM/mean-value exponent weld -/

/-- The three Guth--Maynard exponents and the complementary mean-value
exponent are simultaneously bounded by the advertised Section 13.1 exponent.
This is the complete local branch split, independent of any analytic theorem. -/
theorem powered_length_branch_exponents
    {σ mu : ℝ}
    (hσlow : 7 / 10 ≤ σ) (hσhigh : σ ≤ 4 / 5)
    (hmuLow : AppendixTypeIPower.poweredLengthLower σ ≤ mu)
    (hmuHigh : mu ≤ AppendixTypeIPower.poweredLengthUpper σ) :
    2 * mu * (1 - σ) ≤ AppendixTypeIPower.gmExponent σ ∧
    1 + (12 / 5 - 4 * σ) * mu ≤ AppendixTypeIPower.gmExponent σ ∧
    (mu ≤ AppendixTypeIPower.gmSwitchExponent σ →
      (18 / 5 - 4 * σ) * mu ≤ AppendixTypeIPower.gmExponent σ) ∧
    (AppendixTypeIPower.gmSwitchExponent σ ≤ mu →
      1 + (1 - 2 * σ) * mu ≤ AppendixTypeIPower.gmExponent σ) := by
  have hone : 0 ≤ 1 - σ := by nlinarith
  have hfirst := AppendixTypeIPower.first_term_at_powered_upper hσlow
  have hthird := AppendixTypeIPower.third_term_at_powered_lower hσlow
  have hmiddle := AppendixTypeIPower.middle_term_at_switch hσlow hσhigh
  have hmean := AppendixTypeIPower.mean_value_switch_le_gm hσlow hσhigh
  constructor
  · calc
      2 * mu * (1 - σ) ≤
          2 * AppendixTypeIPower.poweredLengthUpper σ * (1 - σ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmuHigh (by norm_num)) hone
      _ = AppendixTypeIPower.gmExponent σ := hfirst
  constructor
  · have hc : 12 / 5 - 4 * σ ≤ 0 := by nlinarith
    calc
      1 + (12 / 5 - 4 * σ) * mu ≤
          1 + (12 / 5 - 4 * σ) *
            AppendixTypeIPower.poweredLengthLower σ := by
        linarith [mul_le_mul_of_nonpos_left hmuLow hc]
      _ = AppendixTypeIPower.gmExponent σ := hthird
  constructor
  · intro hmuSwitch
    have hc : 0 ≤ 18 / 5 - 4 * σ := by nlinarith
    calc
      (18 / 5 - 4 * σ) * mu ≤
          (18 / 5 - 4 * σ) * AppendixTypeIPower.gmSwitchExponent σ :=
        mul_le_mul_of_nonneg_left hmuSwitch hc
      _ = AppendixTypeIPower.gmExponent σ := hmiddle
  · intro hswitchMu
    have hc : 1 - 2 * σ ≤ 0 := by nlinarith
    calc
      1 + (1 - 2 * σ) * mu ≤
          1 + (1 - 2 * σ) * AppendixTypeIPower.gmSwitchExponent σ := by
        linarith [mul_le_mul_of_nonpos_left hswitchMu hc]
      _ ≤ AppendixTypeIPower.gmExponent σ := hmean

/-- Rpow form of the preceding branch weld, suitable for direct substitution
into the two published cardinality estimates. -/
theorem powered_length_branch_rpow_bounds
    {T σ mu : ℝ} (hT : 1 ≤ T)
    (hσlow : 7 / 10 ≤ σ) (hσhigh : σ ≤ 4 / 5)
    (hmuLow : AppendixTypeIPower.poweredLengthLower σ ≤ mu)
    (hmuHigh : mu ≤ AppendixTypeIPower.poweredLengthUpper σ) :
    Real.rpow T (2 * mu * (1 - σ)) ≤
        Real.rpow T (AppendixTypeIPower.gmExponent σ) ∧
    Real.rpow T (1 + (12 / 5 - 4 * σ) * mu) ≤
        Real.rpow T (AppendixTypeIPower.gmExponent σ) ∧
    (mu ≤ AppendixTypeIPower.gmSwitchExponent σ →
      Real.rpow T ((18 / 5 - 4 * σ) * mu) ≤
        Real.rpow T (AppendixTypeIPower.gmExponent σ)) ∧
    (AppendixTypeIPower.gmSwitchExponent σ ≤ mu →
      Real.rpow T (1 + (1 - 2 * σ) * mu) ≤
        Real.rpow T (AppendixTypeIPower.gmExponent σ)) := by
  obtain ⟨h1, h3, h2, hmv⟩ :=
    powered_length_branch_exponents hσlow hσhigh hmuLow hmuHigh
  exact ⟨Real.rpow_le_rpow_of_exponent_le hT h1,
    Real.rpow_le_rpow_of_exponent_le hT h3,
    fun h => Real.rpow_le_rpow_of_exponent_le hT (h2 h),
    fun h => Real.rpow_le_rpow_of_exponent_le hT (hmv h)⟩

/-- If every point has a large sum of `r` blocks, one fixed block is large on
at least a `1/r` fraction.  This is the simultaneous, rather than pointwise,
dyadic pigeonhole step required before applying a large-values theorem. -/
theorem exists_common_large_block
    {r : ℕ} {W : Finset ℝ} {block : Fin r → ℝ → ℂ}
    {total : ℝ → ℂ} {V : ℝ}
    (hr : 0 < r)
    (hdecomp : ∀ t ∈ W, total t = ∑ i, block i t)
    (hlarge : ∀ t ∈ W, V ≤ ‖total t‖) :
    ∃ i : Fin r, ∃ S : Finset ℝ,
      S ⊆ W ∧
      W.card ≤ r * S.card ∧
      ∀ t ∈ S, V ≤ r * ‖block i t‖ := by
  classical
  let chooseIndex : ℝ → Fin r := fun t =>
    if ht : t ∈ W then
      Classical.choose (AppendixTypeIPower.exists_block_with_large_norm
        hr (fun i => block i t))
    else ⟨0, hr⟩
  have hchoice : ∀ t ∈ W,
      ‖total t‖ ≤ r * ‖block (chooseIndex t) t‖ := by
    intro t ht
    rw [hdecomp t ht]
    simpa [chooseIndex, ht] using
      (Classical.choose_spec (AppendixTypeIPower.exists_block_with_large_norm
        hr (fun i => block i t)))
  let fiber : Fin r → Finset ℝ := fun i => W.filter (fun t => chooseIndex t = i)
  have hcard : W.card = ∑ i, (fiber i).card := by
    calc
      W.card = ∑ t ∈ W, 1 := by simp
      _ = ∑ i : Fin r, ∑ t ∈ W with chooseIndex t = i, 1 := by
        symm
        exact Finset.sum_fiberwise W chooseIndex (fun _ => 1)
      _ = ∑ i, (fiber i).card := by simp [fiber]
  have hsum :
      (∑ _i : Fin r, W.card) ≤ ∑ i : Fin r, r * (fiber i).card := by
    calc
      (∑ _i : Fin r, W.card) = r * W.card := by simp
      _ = r * ∑ i : Fin r, (fiber i).card := by rw [← hcard]
      _ ≤ ∑ i : Fin r, r * (fiber i).card := by
        rw [Finset.mul_sum]
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le
    ⟨⟨0, hr⟩, Finset.mem_univ _⟩ hsum
  refine ⟨i, fiber i, ?_, ?_, ?_⟩
  · exact Finset.filter_subset _ _
  · exact hi
  · intro t ht
    have htW : t ∈ W := (Finset.mem_filter.mp ht).1
    have hti : chooseIndex t = i := (Finset.mem_filter.mp ht).2
    calc
      V ≤ ‖total t‖ := hlarge t htW
      _ ≤ r * ‖block (chooseIndex t) t‖ := hchoice t htW
      _ = r * ‖block i t‖ := by rw [hti]

/-- Exact simultaneous consequence for a powered Dirichlet polynomial.  The
large-value threshold is raised to the same power, then one literal standard
dyadic block survives on a `1/k` fraction of ordinates. -/
theorem exists_common_powered_dirichlet_block
    {N k : ℕ} {a : ℕ → ℂ} {W : Finset ℝ} {V : ℝ}
    (hk : 0 < k) (hV : 0 ≤ V)
    (hlarge : ∀ t ∈ W, V ≤ ‖dirichletPolynomial a N t‖) :
    ∃ i : Fin k, ∃ S : Finset ℝ,
      S ⊆ W ∧ W.card ≤ k * S.card ∧
      ∀ t ∈ S, V ^ k ≤ k *
        ‖dirichletPolynomial
          (fun m => (dyadicCoefficient N a ^ k) m)
          (N ^ k * 2 ^ (i : ℕ)) t‖ := by
  have hpowered : ∀ t ∈ W,
      V ^ k ≤ ‖dirichletPolynomial a N t ^ k‖ := by
    intro t ht
    rw [norm_pow]
    exact pow_le_pow_left₀ hV (hlarge t ht) k
  obtain ⟨i, S, hSW, hcard, hblock⟩ :=
    exists_common_large_block hk
      (W := W)
      (block := fun i t => poweredBlockPolynomial N k a i t)
      (total := fun t => dirichletPolynomial a N t ^ k)
      (V := V ^ k)
      (fun t ht => dirichletPolynomial_pow_eq_sum_blocks hk t)
      hpowered
  refine ⟨i, S, hSW, hcard, ?_⟩
  intro t ht
  simpa [poweredBlockPolynomial_eq_dirichletPolynomial] using hblock t ht

/-! ## Deep published inputs kept separate -/

/-- The classical discrete mean-value estimate used in the complementary
branch of GM Section 13.1.  This proposition is source data, not an axiom. -/
def DiscreteDirichletMeanValue : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T V : ℝ) (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 1 ≤ N → 0 < V →
        (∀ n, ‖b n‖ ≤ 1) →
        OneSeparated W →
        (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
        (∀ t ∈ W, V ≤ ‖dirichletPolynomial b N t‖) →
        (W.card : ℝ) ≤
          C * Real.rpow T η * (((N : ℝ) ^ 2 + T * N) / V ^ 2)

end

end FixedCharacterPoweredBridge

#print axioms FixedCharacterPoweredBridge.orderedDivisorCount_subpolynomial
#print axioms FixedCharacterPoweredBridge.multiplicativeDyadicUnion_eq_Ioc
#print axioms FixedCharacterPoweredBridge.multiplicative_dyadic_index_unique
#print axioms FixedCharacterPoweredBridge.sum_poweredDyadicBlock_eq
#print axioms FixedCharacterPoweredBridge.term_eq_phase
#print axioms FixedCharacterPoweredBridge.dyadic_powered_coefficient_support
#print axioms FixedCharacterPoweredBridge.LSeries_dyadic_power_eq_power
#print axioms FixedCharacterPoweredBridge.dirichletPolynomial_pow_eq_powered_interval
#print axioms FixedCharacterPoweredBridge.sum_poweredBlockPolynomial_eq
#print axioms FixedCharacterPoweredBridge.poweredBlockPolynomial_eq_dirichletPolynomial
#print axioms FixedCharacterPoweredBridge.dirichletPolynomial_pow_eq_sum_blocks
#print axioms FixedCharacterPoweredBridge.exists_power_in_guthMaynard_window
#print axioms FixedCharacterPoweredBridge.exists_bounded_power_in_guthMaynard_window
#print axioms FixedCharacterPoweredBridge.orderedDivisorCount_le_time_subpower
#print axioms FixedCharacterPoweredBridge.powered_length_branch_exponents
#print axioms FixedCharacterPoweredBridge.powered_length_branch_rpow_bounds
#print axioms FixedCharacterPoweredBridge.exists_common_large_block
#print axioms FixedCharacterPoweredBridge.exists_common_powered_dirichlet_block
