import BudgetedPoweredConnector
import BudgetedBranchAssembly

/-!
# The selected-powered-block assembly

This file discharges the sole function-valued premise of
`budgetedBridge_of_selectedPoweredBlockAssembly`.  The logarithmic collar is
charged to the reserved detector loss, while the bounded power, dyadic factor,
and fixed divisor constant are retained in the final constant.
-/

namespace BudgetedSelectedPoweredBlockAssembly

open scoped BigOperators
open CGLProofDAG FixedCharacterPoweredBridge AppendixTypeIPower

noncomputable section

set_option maxHeartbeats 3000000

theorem eventually_const_le_rpow {c a : ℝ} (ha : 0 < a) :
    ∃ T₀ : ℝ, Real.exp 1 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → c ≤ Real.rpow T a := by
  have hlim := tendsto_rpow_atTop ha
  have hev : ∀ᶠ T : ℝ in Filter.atTop, c ≤ Real.rpow T a :=
    hlim.eventually (Filter.eventually_ge_atTop c)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨A, hA⟩ := hev
  refine ⟨max A (Real.exp 1), le_max_right _ _, ?_⟩
  intro T hT
  exact hA T ((le_max_left _ _).trans hT)

theorem self_mul_rpow_eq {T x : ℝ} (hT : 0 < T) :
    T * Real.rpow T x = Real.rpow T (1 + x) := by
  calc
    T * Real.rpow T x = Real.rpow T 1 * Real.rpow T x := by
      rw [show Real.rpow T 1 = T by exact Real.rpow_one T]
    _ = Real.rpow T (1 + x) := (Real.rpow_add hT _ _).symm

theorem rpow_mul_rpow_eq {T x y : ℝ} (hT : 0 < T) :
    Real.rpow T x * Real.rpow T y = Real.rpow T (x + y) :=
  (Real.rpow_add hT _ _).symm

theorem orderedDivisorCount_mono_order {k K n : ℕ} (hk : k ≤ K) :
    orderedDivisorCount k n ≤ orderedDivisorCount K n := by
  rw [FixedCharacterPoweredBridge.orderedDivisorCount_eq_tauAF,
    FixedCharacterPoweredBridge.orderedDivisorCount_eq_tauAF]
  exact ShiuAnalyticLayer.tauAF_mono_order hk n

theorem pow_two_ratio_le
    {T X V A B x v : ℝ}
    (hT : 0 < T) (hX0 : 0 ≤ X) (hV : 0 < V)
    (hA : 0 ≤ A) (hB : 0 < B)
    (hX : X ≤ A * Real.rpow T x)
    (hVlow : B * Real.rpow T v ≤ V) :
    X ^ 2 / V ^ 2 ≤
      (A / B) ^ 2 * Real.rpow T (2 * x - 2 * v) := by
  have hnum : X ^ 2 ≤ (A * Real.rpow T x) ^ 2 := by gcongr
  have hBlow : 0 < B * Real.rpow T v := mul_pos hB (Real.rpow_pos_of_pos hT _)
  have hden0 : 0 < (B * Real.rpow T v) ^ 2 := sq_pos_of_pos hBlow
  have hden : (B * Real.rpow T v) ^ 2 ≤ V ^ 2 := by
    gcongr
  calc
    X ^ 2 / V ^ 2 ≤
        (A * Real.rpow T x) ^ 2 /
          (B * Real.rpow T v) ^ 2 := by
      exact div_le_div₀ (sq_nonneg _) hnum hden0 hden
    _ = (A / B) ^ 2 * Real.rpow T (2 * x - 2 * v) := by
      rw [show (A * Real.rpow T x) ^ 2 /
          (B * Real.rpow T v) ^ 2 =
          (A / B) ^ 2 *
            (Real.rpow T x / Real.rpow T v) ^ 2 by field_simp]
      have hratio : (Real.rpow T x / Real.rpow T v) ^ 2 =
          Real.rpow T (2 * x - 2 * v) := by
        have hsub : Real.rpow T (x - v) =
            Real.rpow T x / Real.rpow T v := Real.rpow_sub hT x v
        rw [← hsub]
        calc
          (Real.rpow T (x - v)) ^ 2 =
              Real.rpow (Real.rpow T (x - v)) (2 : ℝ) :=
            (Real.rpow_natCast _ 2).symm
          _ = Real.rpow T ((x - v) * (2 : ℝ)) :=
            (Real.rpow_mul hT.le _ _).symm
          _ = Real.rpow T (2 * x - 2 * v) := by congr 1 <;> ring
      rw [hratio]

theorem rpow_ratio_four_le
    {T X V A B x v p : ℝ}
    (hT : 0 < T) (hX0 : 0 ≤ X) (hV : 0 < V)
    (hA : 0 ≤ A) (hB : 0 < B) (hp : 0 ≤ p)
    (hX : X ≤ A * Real.rpow T x)
    (hVlow : B * Real.rpow T v ≤ V) :
    Real.rpow X p / V ^ 4 ≤
      Real.rpow A p / B ^ 4 * Real.rpow T (p * x - 4 * v) := by
  have hnum : Real.rpow X p ≤ Real.rpow (A * Real.rpow T x) p :=
    Real.rpow_le_rpow hX0 hX hp
  have hBlow : 0 < B * Real.rpow T v := mul_pos hB (Real.rpow_pos_of_pos hT _)
  have hden0 : 0 < (B * Real.rpow T v) ^ 4 := pow_pos hBlow _
  have hden : (B * Real.rpow T v) ^ 4 ≤ V ^ 4 := by gcongr
  calc
    Real.rpow X p / V ^ 4 ≤
        Real.rpow (A * Real.rpow T x) p /
          (B * Real.rpow T v) ^ 4 := by
      exact div_le_div₀ (Real.rpow_nonneg (mul_nonneg hA (Real.rpow_nonneg hT.le _)) _)
        hnum hden0 hden
    _ = Real.rpow A p / B ^ 4 * Real.rpow T (p * x - 4 * v) := by
      have hmul : Real.rpow (A * Real.rpow T x) p =
          Real.rpow A p * Real.rpow (Real.rpow T x) p :=
        Real.mul_rpow hA (Real.rpow_nonneg hT.le _)
      rw [hmul]
      rw [show Real.rpow A p * Real.rpow (Real.rpow T x) p /
          (B * Real.rpow T v) ^ 4 =
          Real.rpow A p / B ^ 4 *
            (Real.rpow (Real.rpow T x) p /
              (Real.rpow T v) ^ 4) by field_simp]
      have hinner : Real.rpow (Real.rpow T x) p /
          (Real.rpow T v) ^ 4 = Real.rpow T (p * x - 4 * v) := by
        have hxmul : Real.rpow (Real.rpow T x) p =
            Real.rpow T (x * p) := (Real.rpow_mul hT.le x p).symm
        have hvmul : (Real.rpow T v) ^ 4 =
            Real.rpow T (v * (4 : ℝ)) := by
          calc
            (Real.rpow T v) ^ 4 =
                Real.rpow (Real.rpow T v) (4 : ℝ) :=
              (Real.rpow_natCast _ 4).symm
            _ = Real.rpow T (v * (4 : ℝ)) :=
              (Real.rpow_mul hT.le _ _).symm
        rw [hxmul, hvmul]
        have hsub : Real.rpow T (x * p - v * 4) =
            Real.rpow T (x * p) / Real.rpow T (v * 4) :=
          Real.rpow_sub hT (x * p) (v * 4)
        rw [← hsub]
        congr 1 <;> ring
      rw [hinner]

theorem linear_ratio_two_le
    {T X V A B x v : ℝ}
    (hT : 0 < T) (hX0 : 0 ≤ X) (hV : 0 < V)
    (hA : 0 ≤ A) (hB : 0 < B)
    (hX : X ≤ A * Real.rpow T x)
    (hVlow : B * Real.rpow T v ≤ V) :
    X / V ^ 2 ≤
      A / B ^ 2 * Real.rpow T (x - 2 * v) := by
  have hBlow : 0 < B * Real.rpow T v := mul_pos hB (Real.rpow_pos_of_pos hT _)
  have hden0 : 0 < (B * Real.rpow T v) ^ 2 := sq_pos_of_pos hBlow
  have hden : (B * Real.rpow T v) ^ 2 ≤ V ^ 2 := by gcongr
  calc
    X / V ^ 2 ≤ (A * Real.rpow T x) /
        (B * Real.rpow T v) ^ 2 :=
      div_le_div₀ (mul_nonneg hA (Real.rpow_nonneg hT.le _)) hX hden0 hden
    _ = A / B ^ 2 * Real.rpow T (x - 2 * v) := by
      rw [show (A * Real.rpow T x) / (B * Real.rpow T v) ^ 2 =
          A / B ^ 2 * (Real.rpow T x / (Real.rpow T v) ^ 2) by field_simp]
      have hvpow : (Real.rpow T v) ^ 2 = Real.rpow T (2 * v) := by
        calc
          (Real.rpow T v) ^ 2 = Real.rpow (Real.rpow T v) (2 : ℝ) :=
            (Real.rpow_natCast _ 2).symm
          _ = Real.rpow T (v * 2) := (Real.rpow_mul hT.le _ _).symm
          _ = Real.rpow T (2 * v) := by congr 1 <;> ring
      rw [hvpow]
      have hsub :
          Real.rpow T x / Real.rpow T (2 * v) =
            Real.rpow T (x - 2 * v) :=
        (Real.rpow_sub hT x (2 * v)).symm
      exact congrArg (fun z : ℝ => A / B ^ 2 * z) hsub

/-- The logarithmic collar and the finite dyadic index give an exact upper
power bound, retaining `2^K` in the final constant. -/
theorem poweredBlock_upper_of_log_collar
    {T lam delta : ℝ} {N k K : ℕ} (i : Fin k)
    (hT : 1 ≤ T) (hdelta : 0 ≤ delta) (hkK : k ≤ K)
    (hN : (N : ℝ) ≤ Real.rpow T (lam + delta)) :
    ((N ^ k * 2 ^ (i : ℕ) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ K * Real.rpow T ((k : ℝ) * lam + (k : ℝ) * delta) := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hNpow : (N : ℝ) ^ k ≤ (Real.rpow T (lam + delta)) ^ k := by gcongr
  have hT0 : 0 ≤ T := (zero_le_one.trans hT)
  have hNpow' : (N : ℝ) ^ k ≤
      Real.rpow T ((k : ℝ) * lam + (k : ℝ) * delta) := by
    calc
      (N : ℝ) ^ k ≤ (Real.rpow T (lam + delta)) ^ k := hNpow
      _ = Real.rpow (Real.rpow T (lam + delta)) (k : ℝ) :=
        (Real.rpow_natCast _ k).symm
      _ = Real.rpow T ((lam + delta) * (k : ℝ)) :=
        (Real.rpow_mul hT0 _ _).symm
      _ = Real.rpow T ((k : ℝ) * lam + (k : ℝ) * delta) := by
        congr 1 <;> ring
  have hiK : (i : ℕ) ≤ K := i.isLt.le.trans hkK
  have htwo : (2 : ℝ) ^ (i : ℕ) ≤ (2 : ℝ) ^ K := by
    gcongr
    norm_num
  calc
    ((N ^ k * 2 ^ (i : ℕ) : ℕ) : ℝ) =
        (N : ℝ) ^ k * (2 : ℝ) ^ (i : ℕ) := by norm_num
    _ ≤ Real.rpow T ((k : ℝ) * lam + (k : ℝ) * delta) *
        (2 : ℝ) ^ K :=
      mul_le_mul hNpow' htwo (by positivity) (Real.rpow_nonneg hT0 _)
    _ = (2 : ℝ) ^ K *
        Real.rpow T ((k : ℝ) * lam + (k : ℝ) * delta) := by ring

/-- The selected block begins no earlier than the uncollared powered base. -/
theorem poweredBlock_lower
    {T lam : ℝ} {N k : ℕ} (i : Fin k)
    (hT : 0 ≤ T) (hlam : 0 ≤ lam)
    (hN : Real.rpow T lam ≤ (N : ℝ)) :
    Real.rpow T ((k : ℝ) * lam) ≤
      ((N ^ k * 2 ^ (i : ℕ) : ℕ) : ℝ) := by
  have hpow : (Real.rpow T lam) ^ k ≤ (N : ℝ) ^ k := by
    gcongr
    exact Real.rpow_nonneg hT _
  calc
    Real.rpow T ((k : ℝ) * lam) =
        Real.rpow T (lam * (k : ℝ)) := by congr 1 <;> ring
    _ = Real.rpow (Real.rpow T lam) (k : ℝ) :=
      Real.rpow_mul hT _ _
    _ = (Real.rpow T lam) ^ k := Real.rpow_natCast _ k
    _ ≤ (N : ℝ) ^ k := hpow
    _ ≤ (N : ℝ) ^ k * (2 : ℝ) ^ (i : ℕ) := by
      exact le_mul_of_one_le_right (by positivity)
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    _ = ((N ^ k * 2 ^ (i : ℕ) : ℕ) : ℝ) := by norm_num

/-- Powering the detector threshold converts its base-length lower bound into
the exact exponent used in the two large-value branches. -/
theorem powered_threshold_lower
    {T N sigma lam delta : ℝ} {k : ℕ}
    (hT : 0 < T) (hN0 : 0 ≤ N) (hsigma : 0 ≤ sigma)
    (hN : Real.rpow T lam ≤ N) :
    Real.rpow T (sigma * ((k : ℝ) * lam) - (k : ℝ) * delta) ≤
      (Real.rpow N sigma * Real.rpow T (-delta)) ^ k := by
  have hbase : Real.rpow T (lam * sigma) ≤ Real.rpow N sigma := by
    calc
      Real.rpow T (lam * sigma) =
          Real.rpow (Real.rpow T lam) sigma := Real.rpow_mul hT.le lam sigma
      _ ≤ Real.rpow N sigma :=
        Real.rpow_le_rpow (Real.rpow_nonneg hT.le _) hN hsigma
  have hprod : Real.rpow T (lam * sigma) * Real.rpow T (-delta) ≤
      Real.rpow N sigma * Real.rpow T (-delta) :=
    mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hT.le _)
  calc
    Real.rpow T (sigma * ((k : ℝ) * lam) - (k : ℝ) * delta) =
        Real.rpow T ((lam * sigma - delta) * (k : ℝ)) := by
      congr 1 <;> ring
    _ = Real.rpow (Real.rpow T (lam * sigma - delta)) (k : ℝ) :=
      Real.rpow_mul hT.le _ _
    _ = (Real.rpow T (lam * sigma - delta)) ^ k := Real.rpow_natCast _ k
    _ = (Real.rpow T (lam * sigma) * Real.rpow T (-delta)) ^ k := by
      have hadd : Real.rpow T (lam * sigma + (-delta)) =
          Real.rpow T (lam * sigma) * Real.rpow T (-delta) :=
        Real.rpow_add hT _ _
      rw [show lam * sigma - delta = lam * sigma + (-delta) by ring, hadd]
    _ ≤ (Real.rpow N sigma * Real.rpow T (-delta)) ^ k := by
      gcongr
      exact mul_nonneg (Real.rpow_nonneg hT.le _) (Real.rpow_nonneg hT.le _)

/-- Exact lower bound after the selected powered block is divided first by
the pigeonhole factor `k` and then by the time-dependent divisor majorant
`A*T^delta`. -/
theorem normalized_powered_threshold_lower
    {T source A v delta : ℝ} {k : ℕ}
    (hT : 0 < T) (hk : 0 < k) (hA : 0 < A)
    (hsource : Real.rpow T v ≤ source) :
    (1 / ((k : ℝ) * A)) * Real.rpow T (v - delta) ≤
      (source / (k : ℝ)) / (A * Real.rpow T delta) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hden : 0 < (k : ℝ) * (A * Real.rpow T delta) := by
    exact mul_pos hkR (mul_pos hA (Real.rpow_pos_of_pos hT _))
  have heq :
      (1 / ((k : ℝ) * A)) * Real.rpow T (v - delta) =
        Real.rpow T v / ((k : ℝ) * (A * Real.rpow T delta)) := by
    have hsub := Real.rpow_sub hT v delta
    change (1 / ((k : ℝ) * A)) * (T ^ (v - delta)) =
      (T ^ v) / ((k : ℝ) * (A * (T ^ delta)))
    rw [hsub]
    field_simp
  rw [heq]
  rw [show (source / (k : ℝ)) / (A * Real.rpow T delta) =
      source / ((k : ℝ) * (A * Real.rpow T delta)) by field_simp]
  exact div_le_div_of_nonneg_right hsource hden.le

/-- A single divisor constant at `K` controls every selected `k ≤ K` block.
All growth in the block length is exposed as `T^(B*e)`; the finite dyadic
factor stays in the fixed constant. -/
theorem orderedDivisorCount_selectedBlock_le
    {T B e D x : ℝ} {K k blockN : ℕ}
    (hT : 1 ≤ T) (hB : 0 ≤ B) (he : 0 ≤ e) (hD : 0 ≤ D)
    (hkK : k ≤ K) (hxB : x ≤ B)
    (hblock : (blockN : ℝ) ≤ (2 : ℝ) ^ K * Real.rpow T x)
    (hdiv : ∀ n : ℕ, 0 < n →
      (orderedDivisorCount K n : ℝ) ≤ D * Real.rpow n e) :
    ∀ m ∈ Finset.Ioc blockN (2 * blockN),
      (orderedDivisorCount k m : ℝ) ≤
        (D * Real.rpow ((2 : ℝ) ^ (K + 1)) e) * Real.rpow T (B * e) := by
  intro m hm
  have hmpos : 0 < m := by
    have := (Finset.mem_Ioc.mp hm).1
    omega
  have hmupper : (m : ℝ) ≤
      (2 : ℝ) ^ (K + 1) * Real.rpow T B := by
    have hmblock : (m : ℝ) ≤ 2 * (blockN : ℝ) := by
      exact_mod_cast (Finset.mem_Ioc.mp hm).2
    have hTxB : Real.rpow T x ≤ Real.rpow T B :=
      Real.rpow_le_rpow_of_exponent_le hT hxB
    calc
      (m : ℝ) ≤ 2 * (blockN : ℝ) := hmblock
      _ ≤ 2 * ((2 : ℝ) ^ K * Real.rpow T x) :=
        mul_le_mul_of_nonneg_left hblock (by norm_num)
      _ ≤ 2 * ((2 : ℝ) ^ K * Real.rpow T B) := by gcongr
      _ = (2 : ℝ) ^ (K + 1) * Real.rpow T B := by
        rw [pow_succ]
        ring
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hmajor : (orderedDivisorCount k m : ℝ) ≤
      D * Real.rpow m e := by
    calc
      (orderedDivisorCount k m : ℝ) ≤ orderedDivisorCount K m := by
        exact_mod_cast orderedDivisorCount_mono_order hkK
      _ ≤ D * Real.rpow m e := hdiv m hmpos
  have hrpowm := Real.rpow_le_rpow hm0 hmupper he
  calc
    (orderedDivisorCount k m : ℝ) ≤ D * Real.rpow m e := hmajor
    _ ≤ D * Real.rpow ((2 : ℝ) ^ (K + 1) * Real.rpow T B) e :=
      mul_le_mul_of_nonneg_left hrpowm hD
    _ = (D * Real.rpow ((2 : ℝ) ^ (K + 1)) e) *
        Real.rpow T (B * e) := by
      have hmul : Real.rpow ((2 : ℝ) ^ (K + 1) * Real.rpow T B) e =
          Real.rpow ((2 : ℝ) ^ (K + 1)) e *
            Real.rpow (Real.rpow T B) e :=
        Real.mul_rpow (by positivity) (Real.rpow_nonneg (zero_le_one.trans hT) _)
      rw [hmul]
      have hiter : Real.rpow (Real.rpow T B) e = Real.rpow T (B * e) :=
        (Real.rpow_mul (zero_le_one.trans hT) B e).symm
      rw [hiter]
      ring

/-! ## The exact selected-block assembly -/

/-- The function-valued premise at `BudgetedPoweredConnector.lean:195`.
The two analytic inputs are used only through their proved transfer lemmas. -/
theorem selectedPoweredBlockAssembly :
    ∀ (_hGM : GuthMaynardTheorem11) (_hMV : DiscreteDirichletMeanValue)
        (κ η : ℝ), 0 < κ → κ ≤ 1 / 2 → 0 < η →
      ∃ C T₀ : ℝ, 0 < C ∧ Real.exp 1 ≤ T₀ ∧
        ∀ (T σ : ℝ) (N k : ℕ) (b : ℕ → ℂ)
            (W S : Finset ℝ) (i : Fin k),
          T₀ ≤ T → 7 / 10 ≤ σ → σ ≤ 4 / 5 →
          Real.rpow T κ ≤ (N : ℝ) →
          (N : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 →
          1 ≤ k → k ≤ powerCap κ →
          poweredLengthLower σ ≤
            (k : ℝ) * min (Real.logb T N) (1 / 2) →
          (k : ℝ) * min (Real.logb T N) (1 / 2) ≤
            poweredLengthUpper σ →
          (∀ n, ‖b n‖ ≤ 1) →
          OneSeparated W →
          (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
          S ⊆ W → W.card ≤ k * S.card →
          (∀ t ∈ S,
            (Real.rpow N σ * Real.rpow T (-inputLoss κ η)) ^ k ≤
              (k : ℝ) *
                ‖dirichletPolynomial
                  (fun m => (dyadicCoefficient N b ^ k) m)
                  (N ^ k * 2 ^ (i : ℕ)) t‖) →
          (W.card : ℝ) ≤
            C * Real.rpow T (gmExponent σ + η) := by
  intro hGM hMV κ η hκ hκhalf hη
  let Kcap : ℕ := powerCap κ
  let delta : ℝ := inputLoss κ η
  have hKcap : 0 < Kcap := by
    dsimp [Kcap]
    exact powerCap_pos hκ
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact inputLoss_pos hκ hη
  let Bexp : ℝ := 15 / 13 + (Kcap : ℝ) * delta
  have hBexp : 0 < Bexp := by
    dsimp [Bexp]
    positivity
  let e : ℝ := delta / Bexp
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨D, hD, hdivD⟩ :=
    orderedDivisorCount_subpolynomial Kcap hKcap e he
  let A : ℝ := D * Real.rpow ((2 : ℝ) ^ (Kcap + 1)) e
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨KGM, TGM, hKGM, hTGM, hGMbound⟩ :=
    CGLProofDAG.guthMaynard_powered_block_transfer hGM delta hdelta
  obtain ⟨KMV, TMV, hKMV, hTMV, hMVbound⟩ :=
    BudgetedConnectorAnalysis.discreteMeanValue_powered_block_transfer
      hMV delta hdelta
  obtain ⟨Tlog, hTlog, hlog⟩ :=
    BudgetedConnectorAnalysis.eventually_log_sq_lt_rpow hdelta
  let Lconst : ℝ := (2 : ℝ) ^ Kcap
  let Cquad : ℝ := (Lconst * (Kcap : ℝ) * A) ^ 2
  let Cfour18 : ℝ :=
    Real.rpow Lconst (18 / 5 : ℝ) * ((Kcap : ℝ) * A) ^ 4
  let Cfour12 : ℝ :=
    Real.rpow Lconst (12 / 5 : ℝ) * ((Kcap : ℝ) * A) ^ 4
  let Clinear : ℝ := Lconst * ((Kcap : ℝ) * A) ^ 2
  let CGM : ℝ := (Kcap : ℝ) * KGM * (Cquad + Cfour18 + Cfour12)
  let CMV : ℝ := (Kcap : ℝ) * KMV * (Cquad + Clinear)
  let C : ℝ := max CGM CMV
  let T₀ : ℝ := max Tlog (max TGM TMV)
  have hLconst : 0 < Lconst := by dsimp [Lconst]; positivity
  have hCquad : 0 < Cquad := by dsimp [Cquad]; positivity
  have hCfour18 : 0 < Cfour18 := by dsimp [Cfour18]; positivity
  have hCfour12 : 0 < Cfour12 := by dsimp [Cfour12]; positivity
  have hClinear : 0 < Clinear := by dsimp [Clinear]; positivity
  have hCGM : 0 < CGM := by dsimp [CGM]; positivity
  have hCMV : 0 < CMV := by dsimp [CMV]; positivity
  refine ⟨C, T₀, lt_of_lt_of_le hCGM (le_max_left _ _), ?_, ?_⟩
  · dsimp [T₀]
    exact hTlog.trans (le_max_left _ _)
  · intro T σ N k b W S i hT hσlow hσhigh hNlow hNhigh hk hkcap
      hmuLow hmuHigh hb hsep hheight hSW hcard hlarge
    have hET : Real.exp 1 ≤ T := by
      exact hTlog.trans ((le_max_left _ _).trans hT)
    have hTone : 1 ≤ T := by
      exact (show (1 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]).trans hET
    have hTpos : 0 < T := zero_lt_one.trans_le hTone
    have hTGM' : TGM ≤ T :=
      (le_max_left TGM TMV).trans ((le_max_right Tlog (max TGM TMV)).trans hT)
    have hTMV' : TMV ≤ T :=
      (le_max_right TGM TMV).trans ((le_max_right Tlog (max TGM TMV)).trans hT)
    have hlog' : (Real.log T) ^ 2 ≤ Real.rpow T delta :=
      (hlog T ((le_max_left Tlog (max TGM TMV)).trans hT)).le
    let lam : ℝ := min (Real.logb T N) (1 / 2)
    let mu : ℝ := (k : ℝ) * lam
    have hlamData := BudgetedConnectorAnalysis.capped_logb_length_collar
      hκhalf hET hNlow hNhigh
    have hlamLow : κ ≤ lam := by simpa [lam] using hlamData.1
    have hlamNonneg : 0 ≤ lam := hκ.le.trans hlamLow
    have hNlamLow : Real.rpow T lam ≤ (N : ℝ) := by
      simpa [lam] using hlamData.2.2.1
    have hNlamUpper0 : (N : ℝ) ≤ Real.rpow T lam * (Real.log T) ^ 2 := by
      simpa [lam] using hlamData.2.2.2
    have hNlamUpper : (N : ℝ) ≤ Real.rpow T (lam + delta) := by
      calc
        (N : ℝ) ≤ Real.rpow T lam * (Real.log T) ^ 2 := hNlamUpper0
        _ ≤ Real.rpow T lam * Real.rpow T delta :=
          mul_le_mul_of_nonneg_left hlog' (Real.rpow_nonneg hTpos.le _)
        _ = Real.rpow T (lam + delta) := (Real.rpow_add hTpos _ _).symm
    have hkK : k ≤ Kcap := by simpa [Kcap] using hkcap
    have hkR : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
    have hmuLow' : poweredLengthLower σ ≤ mu := by simpa [mu, lam] using hmuLow
    have hmuHigh' : mu ≤ poweredLengthUpper σ := by simpa [mu, lam] using hmuHigh
    have hmuGlobal : mu ≤ 15 / 13 :=
      hmuHigh'.trans (poweredLengthUpper_le_global hσlow)
    let blockN : ℕ := N ^ k * 2 ^ (i : ℕ)
    have hblockUpper : (blockN : ℝ) ≤
        Lconst * Real.rpow T (mu + (k : ℝ) * delta) := by
      simpa [blockN, Lconst, mu] using
        poweredBlock_upper_of_log_collar i hTone hdelta.le hkK hNlamUpper
    have hblockLower : Real.rpow T mu ≤ (blockN : ℝ) := by
      simpa [blockN, mu] using
        poweredBlock_lower i hTpos.le hlamNonneg hNlamLow
    have hNpos : (0 : ℝ) < N :=
      (Real.rpow_pos_of_pos hTpos κ).trans_le hNlow
    have hblockOne : 1 ≤ blockN := by
      dsimp [blockN]
      have hNnat : 1 ≤ N := by exact_mod_cast hNpos
      have hN0 : N ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hNnat)
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (pow_ne_zero _ hN0) (pow_ne_zero _ (by omega)))
    have hBidentity : Bexp * e = delta := by
      dsimp [e]
      field_simp
    have hxB : mu + (k : ℝ) * delta ≤ Bexp := by
      have hkReal : (k : ℝ) ≤ Kcap := by exact_mod_cast hkK
      dsimp [Bexp]
      nlinarith [mul_le_mul_of_nonneg_right hkReal hdelta.le]
    have hdiv : ∀ m ∈ Finset.Ioc blockN (2 * blockN),
        (orderedDivisorCount k m : ℝ) ≤ A * Real.rpow T delta := by
      intro m hm
      have h := orderedDivisorCount_selectedBlock_le hTone hBexp.le he.le hD.le
        hkK hxB hblockUpper hdivD m hm
      simpa [A, hBidentity] using h
    let source : ℝ := Real.rpow N σ * Real.rpow T (-delta)
    let V : ℝ := source ^ k / (k : ℝ)
    let Cnorm : ℝ := A * Real.rpow T delta
    have hsource : 0 < source := by dsimp [source]; positivity
    have hV : 0 < V := by dsimp [V]; positivity
    have hCnorm : 0 < Cnorm := by dsimp [Cnorm]; positivity
    have hlargeV : ∀ t ∈ S, V ≤
        ‖dirichletPolynomial
          (fun m => (dyadicCoefficient N b ^ k) m) blockN t‖ := by
      intro t ht
      have htlarge := hlarge t ht
      dsimp [source, delta] at htlarge
      dsimp [V, source, blockN]
      exact (div_le_iff₀ hkR).2 (by simpa [mul_comm] using htlarge)
    have hsourceLower :
        Real.rpow T (σ * mu - (k : ℝ) * delta) ≤ source ^ k := by
      dsimp [source]
      simpa [mu] using powered_threshold_lower hTpos hNpos.le
        (by linarith : 0 ≤ σ) hNlamLow
    let vexp : ℝ := σ * mu - ((k : ℝ) + 1) * delta
    have hqLower :
        (1 / ((k : ℝ) * A)) * Real.rpow T vexp ≤ V / Cnorm := by
      have hnorm := normalized_powered_threshold_lower hTpos
        (delta := delta) (Nat.zero_lt_of_lt hk) hA hsourceLower
      change (1 / ((k : ℝ) * A)) * Real.rpow T vexp ≤
        (source ^ k / (k : ℝ)) / (A * Real.rpow T delta)
      rw [show vexp = (σ * mu - (k : ℝ) * delta) - delta by
        dsimp [vexp]; ring]
      exact hnorm
    have hqpos : 0 < V / Cnorm := div_pos hV hCnorm
    have hBq : 0 < 1 / ((k : ℝ) * A) := by positivity
    have hfirstBase : 2 * mu * (1 - σ) ≤ gmExponent σ :=
      (powered_length_branch_exponents hσlow hσhigh hmuLow' hmuHigh').1
    have hthirdBase : 1 + (12 / 5 - 4 * σ) * mu ≤ gmExponent σ :=
      (powered_length_branch_exponents hσlow hσhigh hmuLow' hmuHigh').2.1
    have hbudget32 := thirtyTwo_powered_inputLoss_le_half hη.le hkcap
    have hreserve : 16 * ((k : ℝ) + 1) * delta ≤ η := by
      dsimp [delta]
      nlinarith
    have hfinalExp :
        gmExponent σ + (8 * ((k : ℝ) + 1) + 1) * delta ≤
          gmExponent σ + η := by
      have hcoef :
          8 * ((k : ℝ) + 1) + 1 ≤ 16 * ((k : ℝ) + 1) := by
        nlinarith [hkR]
      simpa [add_comm] using add_le_add_left
        ((mul_le_mul_of_nonneg_right hcoef hdelta.le).trans hreserve)
        (gmExponent σ)
    have hconstQuad :
        (Lconst / (1 / ((k : ℝ) * A))) ^ 2 ≤ Cquad := by
      have hkReal : (k : ℝ) ≤ Kcap := by exact_mod_cast hkK
      dsimp [Cquad]
      rw [show Lconst / (1 / ((k : ℝ) * A)) =
        Lconst * (k : ℝ) * A by field_simp]
      gcongr
    have hconstFour18 :
        Real.rpow Lconst (18 / 5 : ℝ) /
            (1 / ((k : ℝ) * A)) ^ 4 ≤ Cfour18 := by
      have hkReal : (k : ℝ) ≤ Kcap := by exact_mod_cast hkK
      dsimp [Cfour18]
      calc
        Real.rpow Lconst (18 / 5 : ℝ) / (1 / ((k : ℝ) * A)) ^ 4 =
            Real.rpow Lconst (18 / 5 : ℝ) * ((k : ℝ) * A) ^ 4 := by
          field_simp
        _ ≤ Real.rpow Lconst (18 / 5 : ℝ) * ((Kcap : ℝ) * A) ^ 4 := by
          exact mul_le_mul_of_nonneg_left (by gcongr)
            (Real.rpow_nonneg hLconst.le _)
    have hconstFour12 :
        Real.rpow Lconst (12 / 5 : ℝ) /
            (1 / ((k : ℝ) * A)) ^ 4 ≤ Cfour12 := by
      have hkReal : (k : ℝ) ≤ Kcap := by exact_mod_cast hkK
      dsimp [Cfour12]
      calc
        Real.rpow Lconst (12 / 5 : ℝ) / (1 / ((k : ℝ) * A)) ^ 4 =
            Real.rpow Lconst (12 / 5 : ℝ) * ((k : ℝ) * A) ^ 4 := by
          field_simp
        _ ≤ Real.rpow Lconst (12 / 5 : ℝ) * ((Kcap : ℝ) * A) ^ 4 := by
          exact mul_le_mul_of_nonneg_left (by gcongr)
            (Real.rpow_nonneg hLconst.le _)
    have hconstLinear :
        Lconst / (1 / ((k : ℝ) * A)) ^ 2 ≤ Clinear := by
      have hkReal : (k : ℝ) ≤ Kcap := by exact_mod_cast hkK
      dsimp [Clinear]
      rw [show Lconst / (1 / ((k : ℝ) * A)) ^ 2 =
        Lconst * ((k : ℝ) * A) ^ 2 by field_simp]
      gcongr
    have hcardReal : (W.card : ℝ) ≤ (Kcap : ℝ) * (S.card : ℝ) := by
      calc
        (W.card : ℝ) ≤ (k * S.card : ℕ) := by exact_mod_cast hcard
        _ = (k : ℝ) * (S.card : ℝ) := by norm_num
        _ ≤ (Kcap : ℝ) * (S.card : ℝ) := by
          gcongr
    have hexpFirst :
        2 * (mu + (k : ℝ) * delta) - 2 * vexp ≤
          gmExponent σ + 8 * ((k : ℝ) + 1) * delta := by
      calc
        2 * (mu + (k : ℝ) * delta) - 2 * vexp =
            2 * mu * (1 - σ) + (4 * (k : ℝ) + 2) * delta := by
          dsimp [vexp]
          ring
        _ ≤ gmExponent σ + (4 * (k : ℝ) + 2) * delta :=
          add_le_add hfirstBase le_rfl
        _ ≤ gmExponent σ + 8 * ((k : ℝ) + 1) * delta := by
          have hk0 : (0 : ℝ) ≤ k := by positivity
          nlinarith
    have hexpThird :
        1 + ((12 / 5 : ℝ) * (mu + (k : ℝ) * delta) - 4 * vexp) ≤
          gmExponent σ + 8 * ((k : ℝ) + 1) * delta := by
      calc
        1 + ((12 / 5 : ℝ) * (mu + (k : ℝ) * delta) - 4 * vexp) =
            (1 + (12 / 5 - 4 * σ) * mu) +
              ((12 / 5 : ℝ) * (k : ℝ) + 4 * ((k : ℝ) + 1)) * delta := by
          dsimp [vexp]
          ring
        _ ≤ gmExponent σ +
              ((12 / 5 : ℝ) * (k : ℝ) + 4 * ((k : ℝ) + 1)) * delta :=
          add_le_add hthirdBase le_rfl
        _ ≤ gmExponent σ + 8 * ((k : ℝ) + 1) * delta := by
          have hk0 : (0 : ℝ) ≤ k := by positivity
          nlinarith
    by_cases hswitch : mu ≤ gmSwitchExponent σ
    · have hsecondBase : (18 / 5 - 4 * σ) * mu ≤ gmExponent σ :=
        (powered_length_branch_exponents hσlow hσhigh hmuLow' hmuHigh').2.2.1 hswitch
      have hexpSecond :
          (18 / 5 : ℝ) * (mu + (k : ℝ) * delta) - 4 * vexp ≤
            gmExponent σ + 8 * ((k : ℝ) + 1) * delta := by
        calc
          (18 / 5 : ℝ) * (mu + (k : ℝ) * delta) - 4 * vexp =
              (18 / 5 - 4 * σ) * mu +
                ((18 / 5 : ℝ) * (k : ℝ) + 4 * ((k : ℝ) + 1)) * delta := by
            dsimp [vexp]
            ring
          _ ≤ gmExponent σ +
                ((18 / 5 : ℝ) * (k : ℝ) + 4 * ((k : ℝ) + 1)) * delta :=
            add_le_add hsecondBase le_rfl
          _ ≤ gmExponent σ + 8 * ((k : ℝ) + 1) * delta := by
            have hk0 : (0 : ℝ) ≤ k := by positivity
            nlinarith
      have hterm1raw := pow_two_ratio_le hTpos (by positivity : 0 ≤ (blockN : ℝ))
        hqpos hLconst.le hBq hblockUpper hqLower
      have hterm1 : (blockN : ℝ) ^ 2 / (V / Cnorm) ^ 2 ≤
          Cquad * Real.rpow T (gmExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
        calc
          (blockN : ℝ) ^ 2 / (V / Cnorm) ^ 2 ≤
              (Lconst / (1 / ((k : ℝ) * A))) ^ 2 *
                Real.rpow T
                  (2 * (mu + (k : ℝ) * delta) - 2 * vexp) := hterm1raw
          _ ≤ Cquad * Real.rpow T
                (2 * (mu + (k : ℝ) * delta) - 2 * vexp) := by
            exact mul_le_mul_of_nonneg_right hconstQuad
              (Real.rpow_nonneg hTpos.le _)
          _ ≤ Cquad * Real.rpow T
                (gmExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hTone hexpFirst) hCquad.le
      have hterm2raw := rpow_ratio_four_le hTpos
        (by positivity : 0 ≤ (blockN : ℝ)) hqpos hLconst.le hBq
        (by norm_num : 0 ≤ (18 / 5 : ℝ)) hblockUpper hqLower
      have hterm2 : Real.rpow blockN (18 / 5 : ℝ) / (V / Cnorm) ^ 4 ≤
          Cfour18 * Real.rpow T
            (gmExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
        calc
          Real.rpow blockN (18 / 5 : ℝ) / (V / Cnorm) ^ 4 ≤
              Real.rpow Lconst (18 / 5 : ℝ) /
                  (1 / ((k : ℝ) * A)) ^ 4 *
                Real.rpow T
                  ((18 / 5 : ℝ) * (mu + (k : ℝ) * delta) - 4 * vexp) := hterm2raw
          _ ≤ Cfour18 * Real.rpow T
                  ((18 / 5 : ℝ) * (mu + (k : ℝ) * delta) - 4 * vexp) := by
            exact mul_le_mul_of_nonneg_right hconstFour18
              (Real.rpow_nonneg hTpos.le _)
          _ ≤ Cfour18 * Real.rpow T
                (gmExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hTone hexpSecond) hCfour18.le
      have hterm3raw := rpow_ratio_four_le hTpos
        (by positivity : 0 ≤ (blockN : ℝ)) hqpos hLconst.le hBq
        (by norm_num : 0 ≤ (12 / 5 : ℝ)) hblockUpper hqLower
      have hterm3 : T * Real.rpow blockN (12 / 5 : ℝ) /
          (V / Cnorm) ^ 4 ≤
          Cfour12 * Real.rpow T
            (gmExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
        have hmul := mul_le_mul_of_nonneg_left hterm3raw hTpos.le
        calc
          T * Real.rpow blockN (12 / 5 : ℝ) / (V / Cnorm) ^ 4 =
              T * (Real.rpow blockN (12 / 5 : ℝ) / (V / Cnorm) ^ 4) := by ring
          _ ≤ T * (Real.rpow Lconst (12 / 5 : ℝ) /
                  (1 / ((k : ℝ) * A)) ^ 4 *
                Real.rpow T
                  ((12 / 5 : ℝ) * (mu + (k : ℝ) * delta) - 4 * vexp)) := hmul
          _ = (Real.rpow Lconst (12 / 5 : ℝ) /
                  (1 / ((k : ℝ) * A)) ^ 4) *
              Real.rpow T
                (1 + ((12 / 5 : ℝ) * (mu + (k : ℝ) * delta) - 4 * vexp)) := by
            rw [show T * (Real.rpow Lconst (12 / 5 : ℝ) /
                    (1 / ((k : ℝ) * A)) ^ 4 *
                  Real.rpow T
                    ((12 / 5 : ℝ) * (mu + (k : ℝ) * delta) - 4 * vexp)) =
                (Real.rpow Lconst (12 / 5 : ℝ) /
                    (1 / ((k : ℝ) * A)) ^ 4) *
                  (T * Real.rpow T
                    ((12 / 5 : ℝ) * (mu + (k : ℝ) * delta) - 4 * vexp)) by ring]
            rw [self_mul_rpow_eq hTpos]
          _ ≤ Cfour12 * Real.rpow T
              (1 + ((12 / 5 : ℝ) * (mu + (k : ℝ) * delta) - 4 * vexp)) := by
            exact mul_le_mul_of_nonneg_right hconstFour12
              (Real.rpow_nonneg hTpos.le _)
          _ ≤ Cfour12 * Real.rpow T
                (gmExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hTone hexpThird) hCfour12.le
      have hraw := hGMbound T V Cnorm N k blockN b S hTGM' hblockOne hV hCnorm
        (fun n hnmem => hb n) hdiv (fun t ht u hu hne => hsep t (hSW ht) u (hSW hu) hne)
        (fun t ht => hheight t (hSW ht)) hlargeV
      have hsum :
          (blockN : ℝ) ^ 2 / (V / Cnorm) ^ 2 +
            Real.rpow blockN (18 / 5 : ℝ) / (V / Cnorm) ^ 4 +
            T * Real.rpow blockN (12 / 5 : ℝ) / (V / Cnorm) ^ 4 ≤
          (Cquad + Cfour18 + Cfour12) *
            Real.rpow T (gmExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
        linarith
      calc
        (W.card : ℝ) ≤ (Kcap : ℝ) * (S.card : ℝ) := hcardReal
        _ ≤ (Kcap : ℝ) * (KGM * Real.rpow T delta *
            ((blockN : ℝ) ^ 2 / (V / Cnorm) ^ 2 +
              Real.rpow blockN (18 / 5 : ℝ) / (V / Cnorm) ^ 4 +
              T * Real.rpow blockN (12 / 5 : ℝ) / (V / Cnorm) ^ 4)) := by
          exact mul_le_mul_of_nonneg_left hraw (by positivity)
        _ ≤ CGM * Real.rpow T
            (gmExponent σ + (8 * ((k : ℝ) + 1) + 1) * delta) := by
          dsimp [CGM]
          calc
            (Kcap : ℝ) * (KGM * Real.rpow T delta *
                ((blockN : ℝ) ^ 2 / (V / Cnorm) ^ 2 +
                  Real.rpow blockN (18 / 5 : ℝ) / (V / Cnorm) ^ 4 +
                  T * Real.rpow blockN (12 / 5 : ℝ) / (V / Cnorm) ^ 4)) ≤
                (Kcap : ℝ) * (KGM * Real.rpow T delta *
                  ((Cquad + Cfour18 + Cfour12) *
                    Real.rpow T (gmExponent σ + 8 * ((k : ℝ) + 1) * delta))) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hsum
                  (mul_nonneg hKGM.le (Real.rpow_nonneg hTpos.le _)))
                (by positivity)
            _ = (Kcap : ℝ) * KGM * (Cquad + Cfour18 + Cfour12) *
                Real.rpow T
                  (gmExponent σ + (8 * ((k : ℝ) + 1) + 1) * delta) := by
              rw [show (Kcap : ℝ) * (KGM * Real.rpow T delta *
                    ((Cquad + Cfour18 + Cfour12) *
                      Real.rpow T (gmExponent σ + 8 * ((k : ℝ) + 1) * delta))) =
                  (Kcap : ℝ) * KGM * (Cquad + Cfour18 + Cfour12) *
                    (Real.rpow T delta *
                      Real.rpow T (gmExponent σ + 8 * ((k : ℝ) + 1) * delta)) by ring]
              rw [rpow_mul_rpow_eq hTpos]
              congr 2 <;> ring
        _ ≤ CGM * Real.rpow T (gmExponent σ + η) := by
          apply mul_le_mul_of_nonneg_left _ hCGM.le
          apply Real.rpow_le_rpow_of_exponent_le hTone
          exact hfinalExp
        _ ≤ C * Real.rpow T (gmExponent σ + η) := by
          exact mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.rpow_nonneg hTpos.le _)
    · have hswitch' : gmSwitchExponent σ ≤ mu := le_of_not_ge hswitch
      have hmeanBase : 1 + (1 - 2 * σ) * mu ≤ gmExponent σ :=
        (powered_length_branch_exponents hσlow hσhigh hmuLow' hmuHigh').2.2.2 hswitch'
      have hexpMean :
          1 + ((mu + (k : ℝ) * delta) - 2 * vexp) ≤
            gmExponent σ + 8 * ((k : ℝ) + 1) * delta := by
        calc
          1 + ((mu + (k : ℝ) * delta) - 2 * vexp) =
              (1 + (1 - 2 * σ) * mu) + (3 * (k : ℝ) + 2) * delta := by
            dsimp [vexp]
            ring
          _ ≤ gmExponent σ + (3 * (k : ℝ) + 2) * delta :=
            add_le_add hmeanBase le_rfl
          _ ≤ gmExponent σ + 8 * ((k : ℝ) + 1) * delta := by
            have hk0 : (0 : ℝ) ≤ k := by positivity
            nlinarith
      have hterm1raw := pow_two_ratio_le hTpos (by positivity : 0 ≤ (blockN : ℝ))
        hqpos hLconst.le hBq hblockUpper hqLower
      have hterm1 : (blockN : ℝ) ^ 2 / (V / Cnorm) ^ 2 ≤
          Cquad * Real.rpow T (gmExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
        calc
          (blockN : ℝ) ^ 2 / (V / Cnorm) ^ 2 ≤
              (Lconst / (1 / ((k : ℝ) * A))) ^ 2 *
                Real.rpow T
                  (2 * (mu + (k : ℝ) * delta) - 2 * vexp) := hterm1raw
          _ ≤ Cquad * Real.rpow T
                (2 * (mu + (k : ℝ) * delta) - 2 * vexp) := by
            exact mul_le_mul_of_nonneg_right hconstQuad
              (Real.rpow_nonneg hTpos.le _)
          _ ≤ Cquad * Real.rpow T
                (gmExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hTone hexpFirst) hCquad.le
      have htermLinear : T * (blockN : ℝ) / (V / Cnorm) ^ 2 ≤
          Clinear * Real.rpow T
            (gmExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
        have hblockRatio : (blockN : ℝ) / (V / Cnorm) ^ 2 ≤
            (Lconst / (1 / ((k : ℝ) * A)) ^ 2) *
              Real.rpow T ((mu + (k : ℝ) * delta) - 2 * vexp) := by
          exact linear_ratio_two_le hTpos (by positivity) hqpos hLconst.le hBq
            hblockUpper hqLower
        have hmul := mul_le_mul_of_nonneg_left hblockRatio hTpos.le
        calc
          T * (blockN : ℝ) / (V / Cnorm) ^ 2 =
              T * ((blockN : ℝ) / (V / Cnorm) ^ 2) := by ring
          _ ≤ T * ((Lconst / (1 / ((k : ℝ) * A)) ^ 2) *
              Real.rpow T ((mu + (k : ℝ) * delta) - 2 * vexp)) := hmul
          _ = (Lconst / (1 / ((k : ℝ) * A)) ^ 2) *
              Real.rpow T (1 + ((mu + (k : ℝ) * delta) - 2 * vexp)) := by
            rw [show T * ((Lconst / (1 / ((k : ℝ) * A)) ^ 2) *
                    Real.rpow T ((mu + (k : ℝ) * delta) - 2 * vexp)) =
                (Lconst / (1 / ((k : ℝ) * A)) ^ 2) *
                  (T * Real.rpow T ((mu + (k : ℝ) * delta) - 2 * vexp)) by ring]
            rw [self_mul_rpow_eq hTpos]
          _ ≤ Clinear * Real.rpow T
              (1 + ((mu + (k : ℝ) * delta) - 2 * vexp)) := by
            exact mul_le_mul_of_nonneg_right hconstLinear
              (Real.rpow_nonneg hTpos.le _)
          _ ≤ Clinear * Real.rpow T
                (gmExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hTone hexpMean) hClinear.le
      have hraw := hMVbound T V Cnorm N k blockN b S hTMV' hblockOne hV hCnorm
        (fun n hnmem => hb n) hdiv (fun t ht u hu hne => hsep t (hSW ht) u (hSW hu) hne)
        (fun t ht => hheight t (hSW ht)) hlargeV
      have hsum : ((blockN : ℝ) ^ 2 + T * blockN) / (V / Cnorm) ^ 2 ≤
          (Cquad + Clinear) *
            Real.rpow T (gmExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
        rw [add_div]
        linarith
      calc
        (W.card : ℝ) ≤ (Kcap : ℝ) * (S.card : ℝ) := hcardReal
        _ ≤ (Kcap : ℝ) * (KMV * Real.rpow T delta *
            (((blockN : ℝ) ^ 2 + T * blockN) / (V / Cnorm) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hraw (by positivity)
        _ ≤ CMV * Real.rpow T
            (gmExponent σ + (8 * ((k : ℝ) + 1) + 1) * delta) := by
          dsimp [CMV]
          calc
            (Kcap : ℝ) * (KMV * Real.rpow T delta *
                (((blockN : ℝ) ^ 2 + T * blockN) / (V / Cnorm) ^ 2)) ≤
                (Kcap : ℝ) * (KMV * Real.rpow T delta *
                  ((Cquad + Clinear) *
                    Real.rpow T (gmExponent σ + 8 * ((k : ℝ) + 1) * delta))) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hsum
                  (mul_nonneg hKMV.le (Real.rpow_nonneg hTpos.le _)))
                (by positivity)
            _ = (Kcap : ℝ) * KMV * (Cquad + Clinear) *
                Real.rpow T
                  (gmExponent σ + (8 * ((k : ℝ) + 1) + 1) * delta) := by
              rw [show (Kcap : ℝ) * (KMV * Real.rpow T delta *
                    ((Cquad + Clinear) *
                      Real.rpow T (gmExponent σ + 8 * ((k : ℝ) + 1) * delta))) =
                  (Kcap : ℝ) * KMV * (Cquad + Clinear) *
                    (Real.rpow T delta *
                      Real.rpow T (gmExponent σ + 8 * ((k : ℝ) + 1) * delta)) by ring]
              rw [rpow_mul_rpow_eq hTpos]
              congr 2 <;> ring
        _ ≤ CMV * Real.rpow T (gmExponent σ + η) := by
          apply mul_le_mul_of_nonneg_left _ hCMV.le
          apply Real.rpow_le_rpow_of_exponent_le hTone
          exact hfinalExp
        _ ≤ C * Real.rpow T (gmExponent σ + η) := by
          exact mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Real.rpow_nonneg hTpos.le _)

/-- The public budgeted powered bridge is now a direct consequence of the
selected-block assembly and the unconditional finite mean-value theorem. -/
theorem budgetedFixedCharacterPoweredLargeValueBridge
    (hGM : GuthMaynardTheorem11) :
    BudgetedFixedCharacterPoweredLargeValueBridge :=
  BudgetedConnectorAnalysis.budgetedBridge_of_selectedPoweredBlockAssembly
    selectedPoweredBlockAssembly hGM

end
end BudgetedSelectedPoweredBlockAssembly

#print axioms BudgetedSelectedPoweredBlockAssembly.eventually_const_le_rpow
#print axioms BudgetedSelectedPoweredBlockAssembly.pow_two_ratio_le
#print axioms BudgetedSelectedPoweredBlockAssembly.rpow_ratio_four_le
