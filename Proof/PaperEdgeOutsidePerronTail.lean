import UniformPsiDeterministicBridge
import MertensAnalyticLeaf
import VonMangoldtPSeriesBound

/-!
# Outside Perron tail at the paper right edge

This is the `y < 1` companion to the finite inside estimate.  The right edge
is exactly `1 + 1 / log (halfIntegerPoint N)`, and the logarithmic kernel
denominator is retained as a shifted harmonic denominator.
-/

namespace PaperEdgeOutsidePerronTail

open scoped BigOperators ArithmeticFunction
open PrimitiveExplicitFormulaSpine PrimitiveTruncatedExplicitFormulaBridge
open TruncatedTwistedPerron

noncomputable section

/-- Outside the half-integer endpoint, the reciprocal logarithmic distance is
bounded by the exact shifted harmonic factor `n / (n - x)`. -/
theorem one_div_abs_log_halfInteger_outside_le
    {N n : ℕ} (hn0 : n ≠ 0) (hNn : N < n) :
    1 / |Real.log (halfIntegerPoint N / (n : ℝ))| ≤
      (n : ℝ) / ((n : ℝ) - halfIntegerPoint N) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hxpos : 0 < halfIntegerPoint N := halfIntegerPoint_pos N
  have hxlt : halfIntegerPoint N < (n : ℝ) := by
    have hcast : ((N + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.add_one_le_iff.mpr hNn)
    unfold halfIntegerPoint
    norm_num at hcast ⊢
    linarith
  have hfrac : 0 < ((n : ℝ) - halfIntegerPoint N) / (n : ℝ) :=
    div_pos (sub_pos.mpr hxlt) hnpos
  have hlog := PerronKernel.abs_log_div_ge_abs_sub_div_max hxpos hnpos
  rw [max_eq_right hxlt.le, abs_of_neg (sub_neg.mpr hxlt), neg_sub] at hlog
  calc
    1 / |Real.log (halfIntegerPoint N / (n : ℝ))| ≤
        1 / (((n : ℝ) - halfIntegerPoint N) / (n : ℝ)) :=
      one_div_le_one_div_of_le hfrac hlog
    _ = (n : ℝ) / ((n : ℝ) - halfIntegerPoint N) := by
      field_simp [(sub_pos.mpr hxlt).ne', hnpos.ne']

/-- Exact algebraic cancellation at the paper edge. -/
theorem standardEdge_rpow_mul_outsideDistance
    {x n : ℝ} (hx : 1 < x) (hn : 0 < n) (hxn : x < n) :
    (x / n) ^ (1 + (Real.log x)⁻¹) * (n / (n - x)) =
      Real.exp 1 * x /
        (n ^ (Real.log x)⁻¹ * (n - x)) := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hδ := Real.rpow_inv_log hxpos hx.ne'
  rw [Real.div_rpow hxpos.le hn.le,
    Real.rpow_add hxpos 1 (Real.log x)⁻¹,
    Real.rpow_add hn 1 (Real.log x)⁻¹,
    Real.rpow_one, Real.rpow_one, hδ]
  field_simp [hn.ne', (sub_pos.mpr hxn).ne',
    (Real.rpow_pos_of_pos hn (Real.log x)⁻¹).ne']

/-- Termwise sharp outside-kernel estimate at the manuscript right edge. -/
theorem norm_tail_kernel_term_standardEdge_le
    {q : ℕ} (χ : DirichletCharacter ℂ q) (N n : ℕ) {T : ℝ}
    (hN : 1 ≤ N) (hT : 0 < T) (hn : n ∉ Finset.Icc 1 N) :
    ‖twistedMangoldtCoeff χ n *
        PerronKernel.kernel (halfIntegerPoint N / n)
          (1 + (Real.log (halfIntegerPoint N))⁻¹) T‖ ≤
      (Real.exp 1 * halfIntegerPoint N / (Real.pi * T)) *
        (ArithmeticFunction.vonMangoldt n /
          ((n : ℝ) ^ (Real.log (halfIntegerPoint N))⁻¹ *
            ((n : ℝ) - halfIntegerPoint N))) := by
  by_cases hn0 : n = 0
  · subst n
    simp [twistedMangoldtCoeff]
  have hnOne : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hNn : N < n := by
    by_contra hnot
    exact hn (Finset.mem_Icc.mpr ⟨hnOne, Nat.le_of_not_gt hnot⟩)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hxpos : 0 < halfIntegerPoint N := halfIntegerPoint_pos N
  have hxone : 1 < halfIntegerPoint N := by
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    unfold halfIntegerPoint
    linarith
  have hxlt : halfIntegerPoint N < (n : ℝ) := by
    have hcast : ((N + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.add_one_le_iff.mpr hNn)
    unfold halfIntegerPoint
    norm_num at hcast ⊢
    linarith
  have hyratio : 0 < halfIntegerPoint N / (n : ℝ) := div_pos hxpos hnpos
  have hyratioOne : halfIntegerPoint N / (n : ℝ) < 1 :=
    (div_lt_one hnpos).2 hxlt
  have hc : 0 < 1 + (Real.log (halfIntegerPoint N))⁻¹ := by
    have hinv : 0 < (Real.log (halfIntegerPoint N))⁻¹ :=
      inv_pos.mpr (Real.log_pos hxone)
    linarith
  have hkernel := SharpFinitePerronStep.norm_kernel_le_of_lt_one
    hyratio hyratioOne hc hT
  have hloginv := one_div_abs_log_halfInteger_outside_le hn0 hNn
  have hcoeff : ‖twistedMangoldtCoeff χ n‖ ≤
      ArithmeticFunction.vonMangoldt n := norm_twistedMangoldtCoeff_le χ n
  have hvm0 : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hpow0 : 0 ≤
      (halfIntegerPoint N / (n : ℝ)) ^
        (1 + (Real.log (halfIntegerPoint N))⁻¹) :=
    Real.rpow_nonneg hyratio.le _
  have hden : 0 < Real.pi * T := mul_pos Real.pi_pos hT
  rw [norm_mul]
  calc
    ‖twistedMangoldtCoeff χ n‖ *
        ‖PerronKernel.kernel (halfIntegerPoint N / n)
          (1 + (Real.log (halfIntegerPoint N))⁻¹) T‖ ≤
      ArithmeticFunction.vonMangoldt n *
        ((halfIntegerPoint N / (n : ℝ)) ^
          (1 + (Real.log (halfIntegerPoint N))⁻¹) /
        (Real.pi * T *
          |Real.log (halfIntegerPoint N / (n : ℝ))|)) :=
      mul_le_mul hcoeff hkernel (norm_nonneg _) hvm0
    _ = ArithmeticFunction.vonMangoldt n *
        (((halfIntegerPoint N / (n : ℝ)) ^
          (1 + (Real.log (halfIntegerPoint N))⁻¹) /
            (Real.pi * T)) *
          (1 / |Real.log (halfIntegerPoint N / (n : ℝ))|)) := by ring
    _ ≤ ArithmeticFunction.vonMangoldt n *
        (((halfIntegerPoint N / (n : ℝ)) ^
          (1 + (Real.log (halfIntegerPoint N))⁻¹) /
            (Real.pi * T)) *
          ((n : ℝ) / ((n : ℝ) - halfIntegerPoint N))) := by
      gcongr
    _ = (Real.exp 1 * halfIntegerPoint N / (Real.pi * T)) *
        (ArithmeticFunction.vonMangoldt n /
          ((n : ℝ) ^ (Real.log (halfIntegerPoint N))⁻¹ *
            ((n : ℝ) - halfIntegerPoint N))) := by
      rw [show ArithmeticFunction.vonMangoldt n *
            (((halfIntegerPoint N / (n : ℝ)) ^
                (1 + (Real.log (halfIntegerPoint N))⁻¹) /
              (Real.pi * T)) *
              ((n : ℝ) / ((n : ℝ) - halfIntegerPoint N))) =
            (ArithmeticFunction.vonMangoldt n / (Real.pi * T)) *
              ((halfIntegerPoint N / (n : ℝ)) ^
                (1 + (Real.log (halfIntegerPoint N))⁻¹) *
                ((n : ℝ) / ((n : ℝ) - halfIntegerPoint N))) by ring]
      rw [standardEdge_rpow_mul_outsideDistance hxone hnpos hxlt]
      field_simp [hden.ne', (sub_pos.mpr hxlt).ne',
        (Real.rpow_pos_of_pos hnpos
          (Real.log (halfIntegerPoint N))⁻¹).ne']

/-- The shifted-harmonic outside majorant is summable.  For convergence only,
it is compared with the ordinary von Mangoldt Dirichlet series on the same
right edge; the sharp shifted denominator is retained in subsequent bounds. -/
theorem summable_outsideShiftedHarmonic_standardEdge
    (N : ℕ) (hN : 1 ≤ N) :
    Summable fun n : {n // n ∉ Finset.Icc 1 N} =>
      ArithmeticFunction.vonMangoldt n /
        ((n : ℝ) ^ (Real.log (halfIntegerPoint N))⁻¹ *
          ((n : ℝ) - halfIntegerPoint N)) := by
  let c : ℝ := 1 + (Real.log (halfIntegerPoint N))⁻¹
  let K : ℝ := 2 * (N + 1 : ℝ)
  let g : {n // n ∉ Finset.Icc 1 N} → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n /
      ((n : ℝ) ^ (Real.log (halfIntegerPoint N))⁻¹ *
        ((n : ℝ) - halfIntegerPoint N))
  let a : {n // n ∉ Finset.Icc 1 N} → ℝ := fun n =>
    ‖LSeries.term (fun k : ℕ =>
      (ArithmeticFunction.vonMangoldt k : ℂ)) (c : ℂ) n‖
  have hxone : 1 < halfIntegerPoint N := by
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    unfold halfIntegerPoint
    linarith
  have hc : 1 < c := by
    dsimp only [c]
    have hinv : 0 < (Real.log (halfIntegerPoint N))⁻¹ :=
      inv_pos.mpr (Real.log_pos hxone)
    linarith
  have haBase : Summable fun n : ℕ =>
      ‖LSeries.term (fun k : ℕ =>
        (ArithmeticFunction.vonMangoldt k : ℂ)) (c : ℂ) n‖ := by
    apply summable_norm_iff.mpr
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc)
  have ha : Summable a := by
    simpa only [a, Function.comp_apply] using
      haBase.subtype {n : ℕ | n ∉ Finset.Icc 1 N}
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hg0 : ∀ n, 0 ≤ g n := by
    intro n
    by_cases hn0 : (n : ℕ) = 0
    · simp [g, hn0]
    have hnOne : 1 ≤ (n : ℕ) := Nat.one_le_iff_ne_zero.mpr hn0
    have hNn : N < (n : ℕ) := by
      by_contra hnot
      exact n.property (Finset.mem_Icc.mpr
        ⟨hnOne, Nat.le_of_not_gt hnot⟩)
    have hnpos : 0 < ((n : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn0
    have hxlt : halfIntegerPoint N < ((n : ℕ) : ℝ) := by
      have hcast : ((N + 1 : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by
        exact_mod_cast (Nat.add_one_le_iff.mpr hNn)
      unfold halfIntegerPoint
      norm_num at hcast ⊢
      linarith
    dsimp only [g]
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (mul_nonneg (Real.rpow_nonneg hnpos.le _)
        (sub_pos.mpr hxlt).le)
  have hga : ∀ n, g n ≤ K * a n := by
    intro n
    by_cases hn0 : (n : ℕ) = 0
    · simp [g, a, hn0]
    have hnOne : 1 ≤ (n : ℕ) := Nat.one_le_iff_ne_zero.mpr hn0
    have hNn : N < (n : ℕ) := by
      by_contra hnot
      exact n.property (Finset.mem_Icc.mpr
        ⟨hnOne, Nat.le_of_not_gt hnot⟩)
    have hnpos : 0 < ((n : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn0
    have hNnReal : (N + 1 : ℝ) ≤ ((n : ℕ) : ℝ) := by
      exact_mod_cast (Nat.add_one_le_iff.mpr hNn)
    have hxlt : halfIntegerPoint N < ((n : ℕ) : ℝ) := by
      unfold halfIntegerPoint
      norm_num at hNnReal ⊢
      linarith
    have hratio :
        ((n : ℕ) : ℝ) /
            (((n : ℕ) : ℝ) - halfIntegerPoint N) ≤ K := by
      have hN0 : (0 : ℝ) ≤ N := by positivity
      have hprod : 0 ≤
          (((n : ℕ) : ℝ) - (N + 1 : ℝ)) * (2 * (N : ℝ) + 1) :=
        mul_nonneg (sub_nonneg.mpr hNnReal) (by positivity)
      apply (div_le_iff₀ (sub_pos.mpr hxlt)).2
      dsimp only [K]
      unfold halfIntegerPoint
      nlinarith
    have ha0 : 0 ≤ a n := norm_nonneg _
    have hid : g n = a n *
        (((n : ℕ) : ℝ) /
          (((n : ℕ) : ℝ) - halfIntegerPoint N)) := by
      dsimp only [g, a, c]
      rw [LSeries.norm_term_eq, if_neg hn0]
      norm_num [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      rw [Real.rpow_add hnpos 1
        (Real.log (halfIntegerPoint N))⁻¹, Real.rpow_one]
      field_simp [hnpos.ne', (sub_pos.mpr hxlt).ne',
        (Real.rpow_pos_of_pos hnpos
          (Real.log (halfIntegerPoint N))⁻¹).ne']
    rw [hid]
    exact (mul_le_mul_of_nonneg_left hratio ha0).trans_eq (mul_comm _ _)
  exact Summable.of_nonneg_of_le hg0 hga (ha.mul_left K)

/-- Summed sharp outside coefficient tail at the standard paper edge.  The
right side is character-uniform and retains the exact shifted harmonic
series that yields the classical `x log^2 x / T` estimate after the usual
near/far split. -/
theorem norm_coefficientTail_standardEdge_le_shiftedHarmonic
    {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) {T : ℝ}
    (hN : 1 ≤ N) (hT : 0 < T) :
    ‖coefficientTail χ (halfIntegerPoint N)
        (1 + (Real.log (halfIntegerPoint N))⁻¹) T
        (Finset.Icc 1 N)‖ ≤
      (Real.exp 1 * halfIntegerPoint N / (Real.pi * T)) *
        ∑' n : {n // n ∉ Finset.Icc 1 N},
          ArithmeticFunction.vonMangoldt n /
            ((n : ℝ) ^ (Real.log (halfIntegerPoint N))⁻¹ *
              ((n : ℝ) - halfIntegerPoint N)) := by
  let f : {n // n ∉ Finset.Icc 1 N} → ℂ := fun n =>
    twistedMangoldtCoeff χ n *
      PerronKernel.kernel (halfIntegerPoint N / n)
        (1 + (Real.log (halfIntegerPoint N))⁻¹) T
  let g : {n // n ∉ Finset.Icc 1 N} → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n /
      ((n : ℝ) ^ (Real.log (halfIntegerPoint N))⁻¹ *
        ((n : ℝ) - halfIntegerPoint N))
  let K : ℝ := Real.exp 1 * halfIntegerPoint N / (Real.pi * T)
  have hg : Summable g := by
    simpa only [g] using summable_outsideShiftedHarmonic_standardEdge N hN
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact div_nonneg
      (mul_nonneg (Real.exp_pos 1).le (halfIntegerPoint_pos N).le)
      (mul_pos Real.pi_pos hT).le
  have hpoint : ∀ n, ‖f n‖ ≤ K * g n := by
    intro n
    exact norm_tail_kernel_term_standardEdge_le χ N n hN hT n.property
  have hKg : Summable fun n => K * g n := hg.mul_left K
  have hnorm : Summable fun n => ‖f n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg (f n)) hpoint hKg
  rw [UniformPsiDeterministicBridge.coefficientTail_eq_tsum_kernels
    χ (halfIntegerPoint_pos N) (Finset.Icc 1 N)]
  change ‖∑' n, f n‖ ≤ K * ∑' n, g n
  calc
    ‖∑' n, f n‖ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n, K * g n := hnorm.tsum_le_tsum hpoint hKg
    _ = K * ∑' n, g n := by rw [tsum_mul_left]

/-- The finite portion immediately outside the half-integer endpoint is at
most twice an ordinary harmonic number. -/
theorem nearOutside_reciprocal_sum_le_harmonic (N : ℕ) :
    (∑ n ∈ Finset.Icc (N + 1) (2 * N + 1),
      1 / ((n : ℝ) - halfIntegerPoint N)) ≤
        2 * ((harmonic (N + 1) : ℚ) : ℝ) := by
  have hreindex :
      (∑ n ∈ Finset.Icc (N + 1) (2 * N + 1),
        1 / ((n : ℝ) - halfIntegerPoint N)) =
      ∑ k ∈ Finset.Icc 1 (N + 1),
        1 / ((k : ℝ) - 1 / 2) := by
    apply Finset.sum_bij (fun n _ => n - N)
    · intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_Icc] at ha hb
      omega
    · intro k hk
      refine ⟨N + k, ?_, ?_⟩
      · simp only [Finset.mem_Icc] at hk ⊢
        omega
      · omega
    · intro n hn
      have hNn : N ≤ n := by
        simp only [Finset.mem_Icc] at hn
        omega
      rw [Nat.cast_sub hNn]
      unfold halfIntegerPoint
      ring
  rw [hreindex]
  calc
    (∑ k ∈ Finset.Icc 1 (N + 1),
      1 / ((k : ℝ) - 1 / 2)) ≤
        ∑ k ∈ Finset.Icc 1 (N + 1), 2 / (k : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkNat : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hkNat)
      have hhalf : (k : ℝ) / 2 ≤ (k : ℝ) - 1 / 2 := by
        have hkReal : (1 : ℝ) ≤ k := by exact_mod_cast hkNat
        linarith
      calc
        1 / ((k : ℝ) - 1 / 2) ≤ 1 / ((k : ℝ) / 2) :=
          one_div_le_one_div_of_le (div_pos hkpos (by norm_num)) hhalf
        _ = 2 / (k : ℝ) := by field_simp [hkpos.ne']
    _ = 2 * ((harmonic (N + 1) : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- The complete shifted-harmonic outside series at the paper edge has the
explicit `O(log^2 x)` bound obtained by splitting at `2N+1`. -/
theorem tsum_outsideShiftedHarmonic_standardEdge_le
    (N : ℕ) (hN : 1 ≤ N) :
    (∑' n : {n // n ∉ Finset.Icc 1 N},
      ArithmeticFunction.vonMangoldt n /
        ((n : ℝ) ^ (Real.log (halfIntegerPoint N))⁻¹ *
          ((n : ℝ) - halfIntegerPoint N))) ≤
      2 * Real.log (2 * N + 1 : ℝ) *
          ((harmonic (N + 1) : ℚ) : ℝ) +
        (4 / (Real.log (halfIntegerPoint N))⁻¹) *
          (1 + (((Real.log (halfIntegerPoint N))⁻¹ / 2)⁻¹)) := by
  let δ : ℝ := (Real.log (halfIntegerPoint N))⁻¹
  let U : ℕ := 2 * N + 1
  let tail := {n // n ∉ Finset.Icc 1 N}
  let S : Finset tail := (Finset.Icc (N + 1) U).subtype
    (fun n => n ∉ Finset.Icc 1 N)
  let g : tail → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n /
      ((n : ℝ) ^ δ * ((n : ℝ) - halfIntegerPoint N))
  let near : tail → ℝ := fun n =>
    if (n : ℕ) ∈ Finset.Icc (N + 1) U then
      Real.log (U : ℝ) / ((n : ℝ) - halfIntegerPoint N)
    else 0
  let far : tail → ℝ := fun n =>
    2 * (ArithmeticFunction.vonMangoldt n /
      (n : ℝ) ^ (1 + δ))
  have hxone : 1 < halfIntegerPoint N := by
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    unfold halfIntegerPoint
    linarith
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact inv_pos.mpr (Real.log_pos hxone)
  have hnearSupport : Function.HasFiniteSupport near := by
    refine S.finite_toSet.subset ?_
    intro n hnSupport
    by_contra hnS
    have hnNotMem : (n : ℕ) ∉ Finset.Icc (N + 1) U := by
      intro hnMem
      change n ∉ S at hnS
      apply hnS
      dsimp only [S]
      exact Finset.mem_subtype.mpr hnMem
    change near n ≠ 0 at hnSupport
    dsimp only [near] at hnSupport
    rw [if_neg hnNotMem] at hnSupport
    exact hnSupport rfl
  have hnearSummable : Summable near :=
    summable_of_hasFiniteSupport hnearSupport
  have hvBase : Summable fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + δ) := by
    let a : ℕ → ℝ := fun n =>
      (2 / δ) * (n : ℝ) ^ (-(1 + δ / 2))
    have hs : 1 < 1 + δ / 2 := by linarith
    have hseries : Summable fun n : ℕ =>
        (n : ℝ) ^ (-(1 + δ / 2)) := by
      simpa only [MAPMertensAnalyticLeaf.realRpowSummandHom_apply] using
        (MAPMertensAnalyticLeaf.summable_realRpowSummandHom hs)
    have ha : Summable a := hseries.mul_left (2 / δ)
    exact Summable.of_nonneg_of_le
      (fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (fun n => VonMangoldtPSeriesBound.vonMangoldt_div_rpow_le hδ n)
      ha
  have hfarSummable : Summable far := by
    dsimp only [far]
    exact (hvBase.subtype {n : ℕ | n ∉ Finset.Icc 1 N}).mul_left 2
  have hg : Summable g := by
    simpa only [g, δ] using
      summable_outsideShiftedHarmonic_standardEdge N hN
  have hpoint : ∀ n, g n ≤ near n + far n := by
    intro n
    by_cases hn0 : (n : ℕ) = 0
    · simp [g, near, far, hn0, U]
    have hnOne : 1 ≤ (n : ℕ) := Nat.one_le_iff_ne_zero.mpr hn0
    have hNn : N < (n : ℕ) := by
      by_contra hnot
      exact n.property (Finset.mem_Icc.mpr
        ⟨hnOne, Nat.le_of_not_gt hnot⟩)
    have hnpos : 0 < ((n : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn0
    have hnLower : N + 1 ≤ (n : ℕ) := Nat.add_one_le_iff.mpr hNn
    have hxlt : halfIntegerPoint N < ((n : ℕ) : ℝ) := by
      have hnLowerReal : (N + 1 : ℝ) ≤ ((n : ℕ) : ℝ) := by
        exact_mod_cast hnLower
      unfold halfIntegerPoint
      linarith
    by_cases hnNear : (n : ℕ) ≤ U
    · have hnMem : (n : ℕ) ∈ Finset.Icc (N + 1) U :=
        Finset.mem_Icc.mpr ⟨hnLower, hnNear⟩
      have hUpos : 0 < (U : ℝ) := by
        dsimp only [U]
        positivity
      have hnU : ((n : ℕ) : ℝ) ≤ (U : ℝ) := by exact_mod_cast hnNear
      have hvm : ArithmeticFunction.vonMangoldt n ≤ Real.log (U : ℝ) :=
        ArithmeticFunction.vonMangoldt_le_log.trans
          (Real.log_le_log hnpos hnU)
      have hpowOne : 1 ≤ ((n : ℕ) : ℝ) ^ δ :=
        Real.one_le_rpow (by exact_mod_cast hnOne) hδ.le
      have hdist : 0 < ((n : ℕ) : ℝ) - halfIntegerPoint N :=
        sub_pos.mpr hxlt
      have hnearBound : g n ≤
          Real.log (U : ℝ) /
            (((n : ℕ) : ℝ) - halfIntegerPoint N) := by
        dsimp only [g]
        apply (div_le_div_iff₀
          (mul_pos (Real.rpow_pos_of_pos hnpos δ) hdist)
          hdist).2
        have hlogU0 : 0 ≤ Real.log (U : ℝ) :=
          Real.log_nonneg (by exact_mod_cast hnOne.trans hnNear)
        nlinarith [mul_le_mul_of_nonneg_right hpowOne hlogU0]
      dsimp only [near, far]
      rw [if_pos hnMem]
      exact hnearBound.trans (le_add_of_nonneg_right
        (mul_nonneg (by norm_num)
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.rpow_nonneg hnpos.le _))))
    · have hnFar : U + 1 ≤ (n : ℕ) := Nat.add_one_le_iff.mpr
        (Nat.lt_of_not_ge hnNear)
      have hnFarReal : (2 * N + 2 : ℝ) ≤ ((n : ℕ) : ℝ) := by
        dsimp only [U] at hnFar
        exact_mod_cast hnFar
      have hdistHalf : ((n : ℕ) : ℝ) / 2 ≤
          ((n : ℕ) : ℝ) - halfIntegerPoint N := by
        unfold halfIntegerPoint
        linarith
      have hdist : 0 < ((n : ℕ) : ℝ) - halfIntegerPoint N :=
        sub_pos.mpr hxlt
      have hfarBound : g n ≤
          2 * (ArithmeticFunction.vonMangoldt n /
            ((n : ℝ) ^ (1 + δ))) := by
        have hvm0 : 0 ≤ ArithmeticFunction.vonMangoldt n :=
          ArithmeticFunction.vonMangoldt_nonneg
        have hpowpos : 0 < ((n : ℕ) : ℝ) ^ δ :=
          Real.rpow_pos_of_pos hnpos δ
        rw [show ((n : ℕ) : ℝ) ^ (1 + δ) =
            ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) ^ δ by
          rw [Real.rpow_add hnpos 1 δ, Real.rpow_one]]
        rw [show 2 * (ArithmeticFunction.vonMangoldt n /
            (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) ^ δ)) =
          (2 * ArithmeticFunction.vonMangoldt n) /
            (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) ^ δ) by ring]
        dsimp only [g]
        apply (div_le_div_iff₀ (mul_pos hpowpos hdist)
          (mul_pos hnpos hpowpos)).2
        have hmul := mul_le_mul_of_nonneg_left hdistHalf hvm0
        nlinarith
      dsimp only [near, far]
      rw [if_neg]
      · simpa using hfarBound
      · exact fun hmem => hnNear (Finset.mem_Icc.mp hmem).2
  have hsum := hg.tsum_le_tsum hpoint (hnearSummable.add hfarSummable)
  rw [hnearSummable.tsum_add hfarSummable] at hsum
  have hnearTsum : (∑' n, near n) ≤
      2 * Real.log (U : ℝ) * ((harmonic (N + 1) : ℚ) : ℝ) := by
    rw [tsum_eq_sum (s := S)]
    · have hsumEq :
          (∑ n ∈ S, near n) =
            Real.log (U : ℝ) *
              ∑ k ∈ Finset.Icc (N + 1) U,
                1 / ((k : ℝ) - halfIntegerPoint N) := by
        rw [Finset.mul_sum]
        apply Finset.sum_bij (s := S) (t := Finset.Icc (N + 1) U)
          (f := near)
          (g := fun k => Real.log (U : ℝ) *
            (1 / ((k : ℝ) - halfIntegerPoint N)))
          (fun n _ => (n : ℕ))
        · intro n hn
          dsimp only [S] at hn
          exact Finset.mem_subtype.mp hn
        · intro a ha b hb hab
          exact Subtype.ext hab
        · intro k hk
          have hkLower := (Finset.mem_Icc.mp hk).1
          have hkTail : k ∉ Finset.Icc 1 N := by
            simp only [Finset.mem_Icc, not_and]
            intro _
            omega
          refine ⟨⟨k, hkTail⟩, ?_, rfl⟩
          dsimp only [S]
          exact Finset.mem_subtype.mpr hk
        · intro n hn
          have hnMem : (n : ℕ) ∈ Finset.Icc (N + 1) U := by
            dsimp only [S] at hn
            exact Finset.mem_subtype.mp hn
          dsimp only [near]
          rw [if_pos hnMem]
          ring
      rw [hsumEq]
      have hrecip := nearOutside_reciprocal_sum_le_harmonic N
      have hrecipU :
          (∑ k ∈ Finset.Icc (N + 1) U,
            1 / ((k : ℝ) - halfIntegerPoint N)) ≤
              2 * ((harmonic (N + 1) : ℚ) : ℝ) := by
        simpa only [U] using hrecip
      have hlog0 : 0 ≤ Real.log (U : ℝ) := by
        apply Real.log_nonneg
        exact_mod_cast (show 1 ≤ U by dsimp only [U]; omega)
      calc
        Real.log (U : ℝ) *
            ∑ k ∈ Finset.Icc (N + 1) U,
              1 / ((k : ℝ) - halfIntegerPoint N) ≤
          Real.log (U : ℝ) *
            (2 * ((harmonic (N + 1) : ℚ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hrecipU hlog0
        _ = 2 * Real.log (U : ℝ) *
            ((harmonic (N + 1) : ℚ) : ℝ) := by ring
    · intro n hnS
      have hnNotMem : (n : ℕ) ∉ Finset.Icc (N + 1) U := by
        intro hnMem
        change n ∉ S at hnS
        apply hnS
        dsimp only [S]
        exact Finset.mem_subtype.mpr hnMem
      dsimp only [near]
      exact if_neg hnNotMem
  have hfarTsum : (∑' n, far n) ≤
      (4 / δ) * (1 + (δ / 2)⁻¹) := by
    dsimp only [far]
    rw [tsum_mul_left]
    have hsub := (hvBase.tsum_subtype_le
      (fun n : ℕ => ArithmeticFunction.vonMangoldt n /
        (n : ℝ) ^ (1 + δ))
      {n : ℕ | n ∉ Finset.Icc 1 N}
      (fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
    have hfull := VonMangoldtPSeriesBound.tsum_vonMangoldt_div_rpow_le hδ
    calc
      2 * ∑' n : {n // n ∉ Finset.Icc 1 N},
          ArithmeticFunction.vonMangoldt n /
            (n : ℝ) ^ (1 + δ) ≤
        2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
            (n : ℝ) ^ (1 + δ) :=
        mul_le_mul_of_nonneg_left hsub (by norm_num)
      _ ≤ 2 * ((2 / δ) * (1 + (δ / 2)⁻¹)) :=
        mul_le_mul_of_nonneg_left hfull (by norm_num)
      _ = (4 / δ) * (1 + (δ / 2)⁻¹) := by ring
  change (∑' n, g n) ≤ _
  have htotal := hsum.trans (add_le_add hnearTsum hfarTsum)
  simpa only [U, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one, δ] using htotal

/-- Fully quantitative outside coefficient-tail estimate at the manuscript
right edge.  The bracket is explicitly `O(log^2 x)`, with no dependence on
the character or modulus. -/
theorem norm_coefficientTail_standardEdge_le_logSquaredMajorant
    {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) {T : ℝ}
    (hN : 1 ≤ N) (hT : 0 < T) :
    ‖coefficientTail χ (halfIntegerPoint N)
        (1 + (Real.log (halfIntegerPoint N))⁻¹) T
        (Finset.Icc 1 N)‖ ≤
      (Real.exp 1 * halfIntegerPoint N / (Real.pi * T)) *
        (2 * Real.log (2 * N + 1 : ℝ) *
            ((harmonic (N + 1) : ℚ) : ℝ) +
          (4 / (Real.log (halfIntegerPoint N))⁻¹) *
            (1 + (((Real.log (halfIntegerPoint N))⁻¹ / 2)⁻¹))) := by
  have hbase := norm_coefficientTail_standardEdge_le_shiftedHarmonic
    χ N hN hT
  have hseries := tsum_outsideShiftedHarmonic_standardEdge_le N hN
  have hfactor :
      0 ≤ Real.exp 1 * halfIntegerPoint N / (Real.pi * T) :=
    div_nonneg
      (mul_nonneg (Real.exp_pos 1).le (halfIntegerPoint_pos N).le)
      (mul_pos Real.pi_pos hT).le
  exact hbase.trans (mul_le_mul_of_nonneg_left hseries hfactor)

/-- Short canonical name for the fully collapsed paper-edge outside tail. -/
theorem norm_coefficientTail_standardEdge_le
    {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) {T : ℝ}
    (hN : 1 ≤ N) (hT : 0 < T) :
    ‖coefficientTail χ (halfIntegerPoint N)
        (1 + (Real.log (halfIntegerPoint N))⁻¹) T
        (Finset.Icc 1 N)‖ ≤
      (Real.exp 1 * halfIntegerPoint N / (Real.pi * T)) *
        (2 * Real.log (2 * N + 1 : ℝ) *
            ((harmonic (N + 1) : ℚ) : ℝ) +
          (4 / (Real.log (halfIntegerPoint N))⁻¹) *
            (1 + (((Real.log (halfIntegerPoint N))⁻¹ / 2)⁻¹))) :=
  norm_coefficientTail_standardEdge_le_logSquaredMajorant χ N hN hT

end

end PaperEdgeOutsidePerronTail
