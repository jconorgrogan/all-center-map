import BHPCorrectedPerronKernel

/-!
# Ramachandra Theorem 6: exact shifted-strip source boundary

K. Ramachandra, *A simple proof of the mean fourth power estimate for
zeta(1/2+it) and L(1/2+it, chi)*, Ann. Scuola Norm. Sup. Pisa (4) 1
(1974), 81--97, Theorem 6 (printed p. 88).

The printed theorem is a continuous mean value over **all** characters
modulo `q`.  It is not the primitive-character, separated-ordinate theorem
stated as Theorem 3.  At `k = 2`, Theorem 6 gives, uniformly for

`|sigma - 1/2| <= (100 log(qT))^-1`, `T >= 3`,

the bound

`sum_(chi mod q) integral_(-T)^T |L(sigma+it,chi)|^4 dt
  << q T log(qT)^400 exp(sqrt(log q))`.

The proposition `RamachandraTheorem6K2Source` records exactly that source
boundary with one absolute constant.  It is intentionally not inhabited here.
Everything after it is deterministic parameter bookkeeping.  The robust
contour weld uses height `4T`, so its canonical offset is
`delta = 1/(400 log x0)`.  The sharper `1/(200 log x0)` choice is retained
only behind the extra product inequality that actually puts it in the source
strip.
-/

namespace RamachandraTheorem6ShiftedStripSource

open scoped BigOperators
open Complex MeasureTheory
open MAPBHPCorrectedPerronKernel

noncomputable section

/-- The shifted-line fourth power appearing in Theorem 6 at `k = 2`. -/
def shiftedStripLFourth {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma t : ℝ) : ℝ :=
  ‖DirichletCharacter.LFunction chi
    ((sigma : ℂ) + t * Complex.I)‖ ^ 4

/-- The literal continuous all-character mean in Ramachandra Theorem 6. -/
def allCharacterShiftedStripFourthIntegral
    (q : ℕ) [NeZero q] (T sigma : ℝ) : ℝ :=
  ∑ chi : DirichletCharacter ℂ q,
    ∫ t in (-T)..T, shiftedStripLFourth chi sigma t

/-- The exact right-hand scale in Ramachandra Theorem 6 after setting `k=2`.
The source's two factors become `log(qT)^400` and `exp(sqrt(log q))`. -/
def ramachandraTheorem6K2Scale (q : ℕ) (T : ℝ) : ℝ :=
  (q : ℝ) * T * Real.log ((q : ℝ) * T) ^ 400 *
    Real.exp (Real.sqrt (Real.log (q : ℝ)))

/-- Source-facing form of Ramachandra 1974, Theorem 6, specialized to `k=2`.

The existential constant precedes `q`, `T`, and `sigma`, recording Remark 1's
assertion that the implied constant is absolute.  The family contains all
Dirichlet characters modulo `q`; there is deliberately no primitivity
hypothesis or principal-character deletion.

This proposition is intentionally not proved in this module. -/
def RamachandraTheorem6K2Source : Prop :=
  ∃ C₆ : ℝ, 0 < C₆ ∧
    ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
      3 ≤ T →
      |sigma - (1 / 2 : ℝ)| ≤
        (100 * Real.log ((q : ℝ) * T))⁻¹ →
      allCharacterShiftedStripFourthIntegral q T sigma ≤
        C₆ * ramachandraTheorem6K2Scale q T

/-- The canonical positive Perron offset used by the corrected BHP contour. -/
def canonicalRamachandraOffset (x0 : ℝ) : ℝ :=
  (400 * Real.log x0)⁻¹

/-- The sharper offset available when the source height and conductor obey the
stronger product inequality `q U ≤ x0²`. -/
def sharpRamachandraOffset (x0 : ℝ) : ℝ :=
  (200 * Real.log x0)⁻¹

/-- At the corrected Perron line, the displacement from `1/2` is exactly the
canonical positive offset. -/
theorem abs_canonicalShift_sub_half
    {x0 : ℝ} (hx0 : 1 < x0) :
    |((1 / 2 : ℝ) + canonicalRamachandraOffset x0) - (1 / 2 : ℝ)| =
      canonicalRamachandraOffset x0 := by
  have hlog : 0 < Real.log x0 := Real.log_pos hx0
  have hoffset : 0 ≤ canonicalRamachandraOffset x0 := by
    unfold canonicalRamachandraOffset
    positivity
  rw [add_sub_cancel_left]
  exact abs_of_nonneg hoffset

/-- Exact source-strip admissibility of the corrected Perron offset.

The hypotheses are the deterministic comparisons actually required to pass
from the ambient MAP scale `x0` to Ramachandra's source variables: the source
height condition `T >= 3`, and `q,T <= x0`.  No BHP hard-range estimate is
assumed. -/
theorem canonicalShift_mem_theorem6Strip
    {q : ℕ} [NeZero q] {T x0 : ℝ}
    (hT : 3 ≤ T) (hqx : (q : ℝ) ≤ x0) (hTx : T ≤ x0) :
    |((1 / 2 : ℝ) + canonicalRamachandraOffset x0) - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹ := by
  have hx0 : 1 < x0 := by linarith
  rw [abs_canonicalShift_sub_half hx0]
  have h200 := ambientOffset_le_ramachandraWindow
    (q := q) (T := T) (x0 := x0) (by linarith) hqx hTx
  have hlog : 0 < Real.log x0 := Real.log_pos hx0
  have hsmall : canonicalRamachandraOffset x0 ≤
      (200 * Real.log x0)⁻¹ := by
    unfold canonicalRamachandraOffset
    apply (inv_le_inv₀ (by positivity) (by positivity)).2
    nlinarith
  exact hsmall.trans h200

/-- Deterministic specialization of the exact source theorem at the corrected
Perron line.  The analytic theorem remains an explicit hypothesis. -/
theorem canonicalShiftedFourthIntegral_le
    (hRamachandra : RamachandraTheorem6K2Source)
    {q : ℕ} [NeZero q] {T x0 : ℝ}
    (hT : 3 ≤ T) (hqx : (q : ℝ) ≤ x0) (hTx : T ≤ x0) :
    ∃ C₆ : ℝ, 0 < C₆ ∧
      allCharacterShiftedStripFourthIntegral q T
          ((1 / 2 : ℝ) + canonicalRamachandraOffset x0) ≤
        C₆ * ramachandraTheorem6K2Scale q T := by
  obtain ⟨C₆, hC₆, hsource⟩ := hRamachandra
  refine ⟨C₆, hC₆, hsource q T
    ((1 / 2 : ℝ) + canonicalRamachandraOffset x0) hT ?_⟩
  exact canonicalShift_mem_theorem6Strip hT hqx hTx

/-- The source integral is definitionally the fourth moment of the corrected
Perron norm at the canonical positive offset. -/
theorem allCharacterShiftedStripFourthIntegral_eq_correctedPerronNorm
    (q : ℕ) [NeZero q] (T x0 : ℝ) :
    allCharacterShiftedStripFourthIntegral q T
        ((1 / 2 : ℝ) + canonicalRamachandraOffset x0) =
      ∑ chi : DirichletCharacter ℂ q,
        ∫ t in (-T)..T,
          shiftedCriticalLineLNorm chi (canonicalRamachandraOffset x0) t ^ 4 := by
  rfl

/-! ## Robust `4T` contour adapter -/

/-- If `q,T ≤ x0` and `x0 ≥ 2`, then the robust offset
`1/(400 log x0)` lies in Ramachandra's strip at source height `4T`.

The factor `400` is forced by the honest ledger
`log (q * (4*T)) ≤ 4 log x0`.  This is the endpoint-safe version: it does
not use the stronger polylog-conductor inequality. -/
theorem canonicalShift_mem_theorem6Strip_fourfoldHeight
    {q : ℕ} [NeZero q] {T x0 : ℝ}
    (hT : 1 ≤ T) (hx0 : 2 ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hTx : T ≤ x0) :
    |((1 / 2 : ℝ) + canonicalRamachandraOffset x0) - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * (4 * T)))⁻¹ := by
  have hx0one : 1 < x0 := lt_of_lt_of_le (by norm_num) hx0
  rw [abs_canonicalShift_sub_half hx0one]
  have hqone : (1 : ℝ) ≤ q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hqone
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hx0pos : 0 < x0 := zero_lt_one.trans hx0one
  have hprodOne : 1 < (q : ℝ) * (4 * T) := by
    nlinarith [mul_le_mul hqone hT (by norm_num : (0 : ℝ) ≤ 1) hqpos.le]
  have hlogprod : 0 < Real.log ((q : ℝ) * (4 * T)) :=
    Real.log_pos hprodOne
  have hlogx : 0 < Real.log x0 := Real.log_pos hx0one
  have hqt : (q : ℝ) * T ≤ x0 ^ 2 := by
    nlinarith [mul_le_mul hqx hTx hTpos.le hx0pos.le]
  have hfour : (4 : ℝ) ≤ x0 ^ 2 := by nlinarith
  have hprodLe : (q : ℝ) * (4 * T) ≤ x0 ^ 4 := by
    calc
      (q : ℝ) * (4 * T) = 4 * ((q : ℝ) * T) := by ring
      _ ≤ 4 * x0 ^ 2 := mul_le_mul_of_nonneg_left hqt (by norm_num)
      _ ≤ x0 ^ 2 * x0 ^ 2 :=
        mul_le_mul_of_nonneg_right hfour (sq_nonneg x0)
      _ = x0 ^ 4 := by ring
  have hlogLe : Real.log ((q : ℝ) * (4 * T)) ≤
      4 * Real.log x0 := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (mul_pos hqpos (mul_pos (by norm_num) hTpos))
      (pow_pos hx0pos 4) hprodLe
    rw [Real.log_pow] at hmono
    simpa using hmono
  unfold canonicalRamachandraOffset
  apply (inv_le_inv₀
    (mul_pos (by norm_num : (0 : ℝ) < 400) hlogx)
    (mul_pos (by norm_num : (0 : ℝ) < 100) hlogprod)).2
  nlinarith

/-- Sharper optional source-strip check for `delta = 1/(200 log x0)`.
Unlike the robust `4T` theorem, this form exposes the extra inequality
`q U ≤ x0²`; callers may use it when the polylogarithmic conductor range
has already supplied that comparison. -/
theorem sharpShift_mem_theorem6Strip_of_product
    {q : ℕ} [NeZero q] {U x0 : ℝ}
    (hU : 3 ≤ U) (hx0 : 1 < x0)
    (hproduct : (q : ℝ) * U ≤ x0 ^ 2) :
    |((1 / 2 : ℝ) + sharpRamachandraOffset x0) - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * U))⁻¹ := by
  have hqone : (1 : ℝ) ≤ q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hqone
  have hUpos : 0 < U := by linarith
  have hx0pos : 0 < x0 := zero_lt_one.trans hx0
  have hprodOne : 1 < (q : ℝ) * U := by
    nlinarith [mul_le_mul hqone hU (by norm_num : (0 : ℝ) ≤ 3) hqpos.le]
  have hlogprod : 0 < Real.log ((q : ℝ) * U) := Real.log_pos hprodOne
  have hlogx : 0 < Real.log x0 := Real.log_pos hx0
  have hlogLe : Real.log ((q : ℝ) * U) ≤ 2 * Real.log x0 := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (mul_pos hqpos hUpos) (pow_pos hx0pos 2) hproduct
    rw [Real.log_pow] at hmono
    simpa using hmono
  rw [add_sub_cancel_left, abs_of_nonneg]
  · unfold sharpRamachandraOffset
    apply (inv_le_inv₀
      (mul_pos (by norm_num : (0 : ℝ) < 200) hlogx)
      (mul_pos (by norm_num : (0 : ℝ) < 100) hlogprod)).2
    nlinarith
  · unfold sharpRamachandraOffset
    positivity

/-- Exact source specialization at the sharper offset.  Its stronger product
hypothesis is part of the public type, preventing accidental use at height
`4T` without first proving the necessary polylog-conductor inequality. -/
theorem sharpShiftedFourthIntegral_le_of_product
    (hRamachandra : RamachandraTheorem6K2Source)
    {q : ℕ} [NeZero q] {U x0 : ℝ}
    (hU : 3 ≤ U) (hx0 : 1 < x0)
    (hproduct : (q : ℝ) * U ≤ x0 ^ 2) :
    ∃ C₆ : ℝ, 0 < C₆ ∧
      allCharacterShiftedStripFourthIntegral q U
          ((1 / 2 : ℝ) + sharpRamachandraOffset x0) ≤
        C₆ * ramachandraTheorem6K2Scale q U := by
  obtain ⟨C₆, hC₆, hsource⟩ := hRamachandra
  exact ⟨C₆, hC₆, hsource q U
    ((1 / 2 : ℝ) + sharpRamachandraOffset x0) hU
      (sharpShift_mem_theorem6Strip_of_product hU hx0 hproduct)⟩

/-- The exact source theorem specialized to the endpoint-safe height `4T`
and offset `1/(400 log x0)`.  The theorem from the paper remains an explicit
source premise; this result performs only the certified parameter transfer. -/
theorem canonicalFourfoldHeightShiftedFourthIntegral_le
    (hRamachandra : RamachandraTheorem6K2Source)
    {q : ℕ} [NeZero q] {T x0 : ℝ}
    (hT : 1 ≤ T) (hx0 : 2 ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hTx : T ≤ x0) :
    ∃ C₆ : ℝ, 0 < C₆ ∧
      allCharacterShiftedStripFourthIntegral q (4 * T)
          ((1 / 2 : ℝ) + canonicalRamachandraOffset x0) ≤
        C₆ * ramachandraTheorem6K2Scale q (4 * T) := by
  obtain ⟨C₆, hC₆, hsource⟩ := hRamachandra
  refine ⟨C₆, hC₆, hsource q (4 * T)
    ((1 / 2 : ℝ) + canonicalRamachandraOffset x0) (by linarith) ?_⟩
  exact canonicalShift_mem_theorem6Strip_fourfoldHeight hT hx0 hqx hTx

/-- Exact reciprocal cost of the endpoint-safe offset. -/
theorem canonicalRamachandraOffset_inv (x0 : ℝ) :
    (canonicalRamachandraOffset x0)⁻¹ = 400 * Real.log x0 := by
  simp [canonicalRamachandraOffset]

/-- The factor `X^delta` from the corrected Perron kernel is an absolute
constant at the canonical offset. -/
theorem rpow_canonicalRamachandraOffset_le
    {X x0 : ℝ} (hX : 0 < X) (hXx : X ≤ x0) (hx0 : 1 < x0) :
    X ^ canonicalRamachandraOffset x0 ≤ Real.exp (1 / 400 : ℝ) := by
  have hx0pos : 0 < x0 := zero_lt_one.trans hx0
  have hlog : 0 < Real.log x0 := Real.log_pos hx0
  have hoffset : 0 ≤ canonicalRamachandraOffset x0 := by
    unfold canonicalRamachandraOffset
    positivity
  have hmono : X ^ canonicalRamachandraOffset x0 ≤
      x0 ^ canonicalRamachandraOffset x0 :=
    Real.rpow_le_rpow hX.le hXx hoffset
  have hx0pow : x0 ^ canonicalRamachandraOffset x0 =
      Real.exp (1 / 400 : ℝ) := by
    rw [Real.rpow_def_of_pos hx0pos]
    congr 1
    unfold canonicalRamachandraOffset
    field_simp [hlog.ne']
  exact hmono.trans_eq hx0pow

/-! ## Absorbing the imprimitive-character source factor -/

/-- A concrete threshold that supplies `K ≤ log(log x0)`.  This avoids an
opaque eventuality in the final MAP weld: it is enough to take
`x0 ≥ exp(exp K)`. -/
theorem loglog_threshold_of_exp_exp_le
    {x0 K : ℝ} (hthreshold : Real.exp (Real.exp K) ≤ x0) :
    K ≤ Real.log (Real.log x0) := by
  have houterOne : 1 < Real.exp (Real.exp K) := by
    rw [Real.one_lt_exp_iff]
    positivity
  have hx0one : 1 < x0 := houterOne.trans_le hthreshold
  have houterPos : 0 < Real.exp (Real.exp K) := Real.exp_pos _
  have hx0pos : 0 < x0 := zero_lt_one.trans hx0one
  have hfirst := Real.strictMonoOn_log.monotoneOn
    houterPos hx0pos hthreshold
  rw [Real.log_exp] at hfirst
  have hlogxpos : 0 < Real.log x0 := Real.log_pos hx0one
  have hsecond := Real.strictMonoOn_log.monotoneOn
    (Real.exp_pos K) hlogxpos hfirst
  simpa using hsecond

/-- On the actual MAP conductor range `q ≤ (log x0)^K`, the source factor
`exp(sqrt(log q))` costs one further power of `log x0` once the explicit
threshold `K ≤ log(log x0)` is reached. -/
theorem exp_sqrt_log_conductor_le_log
    {q : ℕ} [NeZero q] {x0 K : ℝ}
    (hK : 0 ≤ K) (hx0 : 1 < x0)
    (hthreshold : K ≤ Real.log (Real.log x0))
    (hqpoly : (q : ℝ) ≤ (Real.log x0) ^ K) :
    Real.exp (Real.sqrt (Real.log (q : ℝ))) ≤ Real.log x0 := by
  have hqone : (1 : ℝ) ≤ q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hqone
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqone
  have hlogx : 0 < Real.log x0 := Real.log_pos hx0
  have hrpowpos : 0 < (Real.log x0) ^ K :=
    Real.rpow_pos_of_pos hlogx K
  have hlogq_le : Real.log (q : ℝ) ≤
      K * Real.log (Real.log x0) := by
    have hmono := Real.strictMonoOn_log.monotoneOn hqpos hrpowpos hqpoly
    rw [Real.log_rpow hlogx] at hmono
    exact hmono
  have hloglog : 0 ≤ Real.log (Real.log x0) := hK.trans hthreshold
  have hKmul : K * Real.log (Real.log x0) ≤
      Real.log (Real.log x0) ^ 2 := by
    nlinarith [mul_nonneg hloglog (sub_nonneg.mpr hthreshold)]
  have hsqrt : Real.sqrt (Real.log (q : ℝ)) ≤
      Real.log (Real.log x0) := by
    rw [Real.sqrt_le_iff]
    exact ⟨hloglog, hlogq_le.trans hKmul⟩
  have hexp := Real.exp_le_exp.mpr hsqrt
  rw [Real.exp_log hlogx] at hexp
  exact hexp

/-- Fully absorbed robust source scale.  The exponent `401` is transparent:
`400` powers come from Theorem 6 and one from its
`exp(sqrt(log q))` imprimitive-character factor. -/
theorem canonicalFourfoldHeightShiftedFourthIntegral_polylog_le
    (hRamachandra : RamachandraTheorem6K2Source)
    {q : ℕ} [NeZero q] {T x0 K : ℝ}
    (hT : 1 ≤ T) (hx0 : 2 ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hTx : T ≤ x0)
    (hK : 0 ≤ K) (hthreshold : K ≤ Real.log (Real.log x0))
    (hqpoly : (q : ℝ) ≤ (Real.log x0) ^ K) :
    ∃ C₆ : ℝ, 0 < C₆ ∧
      allCharacterShiftedStripFourthIntegral q (4 * T)
          ((1 / 2 : ℝ) + canonicalRamachandraOffset x0) ≤
        (4 * C₆ * (4 : ℝ) ^ 400) * (q : ℝ) * T *
          Real.log x0 ^ 401 := by
  obtain ⟨C₆, hC₆, hsource⟩ :=
    canonicalFourfoldHeightShiftedFourthIntegral_le hRamachandra
      hT hx0 hqx hTx
  refine ⟨C₆, hC₆, hsource.trans ?_⟩
  have hx0one : 1 < x0 := lt_of_lt_of_le (by norm_num) hx0
  have hx0pos : 0 < x0 := zero_lt_one.trans hx0one
  have hlogx : 0 < Real.log x0 := Real.log_pos hx0one
  have hqone : (1 : ℝ) ≤ q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hqone
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hexp := exp_sqrt_log_conductor_le_log hK hx0one hthreshold hqpoly
  have hqt : (q : ℝ) * T ≤ x0 ^ 2 := by
    nlinarith [mul_le_mul hqx hTx hTpos.le hx0pos.le]
  have hfour : (4 : ℝ) ≤ x0 ^ 2 := by nlinarith
  have hprodLe : (q : ℝ) * (4 * T) ≤ x0 ^ 4 := by
    calc
      (q : ℝ) * (4 * T) = 4 * ((q : ℝ) * T) := by ring
      _ ≤ 4 * x0 ^ 2 := mul_le_mul_of_nonneg_left hqt (by norm_num)
      _ ≤ x0 ^ 2 * x0 ^ 2 :=
        mul_le_mul_of_nonneg_right hfour (sq_nonneg x0)
      _ = x0 ^ 4 := by ring
  have hlogprod0 : 0 ≤ Real.log ((q : ℝ) * (4 * T)) := by
    apply Real.log_nonneg
    nlinarith [mul_le_mul hqone hT (by norm_num : (0 : ℝ) ≤ 1) hqpos.le]
  have hlogLe : Real.log ((q : ℝ) * (4 * T)) ≤
      4 * Real.log x0 := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (mul_pos hqpos (mul_pos (by norm_num) hTpos))
      (pow_pos hx0pos 4) hprodLe
    rw [Real.log_pow] at hmono
    simpa using hmono
  have hlogpow : Real.log ((q : ℝ) * (4 * T)) ^ 400 ≤
      (4 * Real.log x0) ^ 400 :=
    pow_le_pow_left₀ hlogprod0 hlogLe 400
  unfold ramachandraTheorem6K2Scale
  calc
    C₆ * ((q : ℝ) * (4 * T) *
          Real.log ((q : ℝ) * (4 * T)) ^ 400 *
          Real.exp (Real.sqrt (Real.log (q : ℝ)))) ≤
        C₆ * ((q : ℝ) * (4 * T) *
          (4 * Real.log x0) ^ 400 * Real.log x0) := by
      gcongr
    _ = (4 * C₆ * (4 : ℝ) ^ 400) * (q : ℝ) * T *
          Real.log x0 ^ 401 := by
      rw [mul_pow, pow_succ]
      ring

end
end RamachandraTheorem6ShiftedStripSource

#print axioms RamachandraTheorem6ShiftedStripSource.abs_canonicalShift_sub_half
#print axioms RamachandraTheorem6ShiftedStripSource.canonicalShift_mem_theorem6Strip
#print axioms RamachandraTheorem6ShiftedStripSource.canonicalShiftedFourthIntegral_le
#print axioms RamachandraTheorem6ShiftedStripSource.allCharacterShiftedStripFourthIntegral_eq_correctedPerronNorm
#print axioms RamachandraTheorem6ShiftedStripSource.canonicalShift_mem_theorem6Strip_fourfoldHeight
#print axioms RamachandraTheorem6ShiftedStripSource.sharpShift_mem_theorem6Strip_of_product
#print axioms RamachandraTheorem6ShiftedStripSource.sharpShiftedFourthIntegral_le_of_product
#print axioms RamachandraTheorem6ShiftedStripSource.canonicalFourfoldHeightShiftedFourthIntegral_le
#print axioms RamachandraTheorem6ShiftedStripSource.rpow_canonicalRamachandraOffset_le
#print axioms RamachandraTheorem6ShiftedStripSource.loglog_threshold_of_exp_exp_le
#print axioms RamachandraTheorem6ShiftedStripSource.exp_sqrt_log_conductor_le_log
#print axioms RamachandraTheorem6ShiftedStripSource.canonicalFourfoldHeightShiftedFourthIntegral_polylog_le
