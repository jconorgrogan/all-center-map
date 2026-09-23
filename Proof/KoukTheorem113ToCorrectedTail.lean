import APCorrectedPaperEdgeTail
import APTailReserveAbsorption

/-!
# Koukoulopoulos 11.3 to the corrected common-height tail

This module is the deterministic consumer for the source-faithful form of
Koukoulopoulos, Theorem 11.3 / equation (11.5).  The source formula retains
the complete primitive divisor `zeroSupport primitive 0 T`.  A legal paper
edge is used only to identify the already-defined endpoint remainder with the
formula residual; no positive-real-part truncation is introduced.
-/

namespace MAPKoukTheorem113ToCorrectedTail

open MeasureTheory Set Filter
open scoped BigOperators ENNReal ArithmeticFunction
open APFoundation MAPFixedScaleAPZeroRoute
open APExplicitFormulaMajorantAdapter
open MAPAPCorrectedCommonHeightContract MAPAPCorrectedPaperEdgeTail
open MAPEndpointRegularizedZeroPrimitive
open PaperEdgePrimitiveComponents

noncomputable section

/-- The literal full-support residual in Koukoulopoulos (11.5). -/
def fullSupportEndpointResidual {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (T t : ℝ) : ℂ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact ambientTwistedPsi chi t -
    (principalCoefficient chi * t -
      endpointMultiplicityWeightedZeroTerm
        chi.primitiveCharacter 0 T t)

/-- Universal-height quantitative form of Theorem 11.3.  The current source
descent treats the good-height contour estimate and then transports the zero
cutoff to arbitrary `T`; the final aggregation has not yet landed.  The `+ 2`
makes the logarithm harmless at the endpoint. -/
def KoukTheorem113FullSupportPointwise : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (T t : ℝ),
      2 ≤ T → T ≤ t →
        ‖fullSupportEndpointResidual chi T t‖ ≤
          C * t * (Real.log (t * (q : ℝ) + 2)) ^ 2 / T

/-- Source-faithful selected-height form of Koukoulopoulos (11.5).

This localized alternative packages the common good height directly, without
requiring the subsequent arbitrary-cutoff transport.  The endpoint range is
exactly the range touched by the short-interval difference.  It remains the
canonical live surface until the universal-height aggregation lands. -/
def KoukTheorem113SelectedCommonHeight : Prop :=
  ∀ K epsilon : ℝ,
    0 < K → 0 < epsilon → epsilon ≤ 13 / 30 →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
        let reserve := min epsilon (1 / 10)
        let H := apZeroHeight reserve X
        let Q := ⌊Real.rpow (Real.log X) K⌋₊
        ∃ T ∈ Set.Ioo H (H + 1),
          ∃ sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ,
            (∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
                (chi : DirichletCharacter ℂ q),
              @paperEdgeContourLegal q
                ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
                chi (sigma q chi) T) ∧
            (∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
                (chi : DirichletCharacter ℂ q),
              letI : NeZero q :=
                ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
              ∀ t ∈ Set.Icc (X / 2) (5 * X),
                ‖fullSupportEndpointResidual chi T t‖ ≤
                  C * t * (Real.log (t * (q : ℝ) + 2)) ^ 2 / T)

/-- Formula uniqueness: the paper-edge remainder is exactly the full-support
11.3 residual whenever the auxiliary contour is legal. -/
theorem endpointRemainder_eq_fullSupportEndpointResidual
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T t : ℝ}
    (hlegal : paperEdgeContourLegal chi sigma T)
    (hN : 1 ≤ ⌊t⌋₊) :
    endpointRemainder chi sigma T t =
      fullSupportEndpointResidual chi T t := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hformula :=
    ambientTwistedPsi_eq_principal_sub_endpoint_add_paperEdgeRemainder
      chi hlegal hN
  unfold fullSupportEndpointResidual
  rw [hformula]
  ring

/-- Pointwise source bound transferred to the exact paper-edge remainder.
No estimate is used in this adapter. -/
theorem norm_endpointRemainder_le_of_kouk113
    (h113 : KoukTheorem113FullSupportPointwise)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T t : ℝ}
    (hlegal : paperEdgeContourLegal chi sigma T)
    (hN : 1 ≤ ⌊t⌋₊) (hTtwo : 2 ≤ T) (hTt : T ≤ t) :
    ∃ C : ℝ, 0 < C ∧
      ‖endpointRemainder chi sigma T t‖ ≤
        C * t * (Real.log (t * (q : ℝ) + 2)) ^ 2 / T := by
  rcases h113 with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  rw [endpointRemainder_eq_fullSupportEndpointResidual chi hlegal hN]
  exact hbound q chi T t hTtwo hTt

/-- The selected zero height is eventually below every endpoint in the
integration range. -/
theorem eventually_apZeroHeight_add_one_le_half
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℝ in atTop,
      apZeroHeight (min epsilon (1 / 10)) X + 1 ≤ X / 2 := by
  have hsmall : ∀ᶠ X : ℝ in atTop,
      Real.rpow X (-(2 / 15 : ℝ)) ≤ 1 / 4 := by
    have ht := tendsto_rpow_neg_atTop
      (show 0 < (2 / 15 : ℝ) by norm_num)
    have hnhds : Set.Iio (1 / 4 : ℝ) ∈ nhds (0 : ℝ) :=
      Iio_mem_nhds (by norm_num)
    exact (ht.eventually hnhds).mono fun _ h => h.le
  filter_upwards [hsmall, eventually_ge_atTop (4 : ℝ)] with X hsmallX hX
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hheight :
      apZeroHeight (min epsilon (1 / 10)) X ≤
        Real.rpow X (13 / 15 : ℝ) := by
    unfold apZeroHeight
    apply Real.rpow_le_rpow_of_exponent_le hXone
    have hreserve : 0 ≤ min epsilon (1 / 10) :=
      le_min hepsilon.le (by norm_num)
    linarith
  have hsplit : Real.rpow X (13 / 15 : ℝ) =
      X * Real.rpow X (-(2 / 15 : ℝ)) := by
    calc
      Real.rpow X (13 / 15 : ℝ) =
          Real.rpow X (1 + (-(2 / 15 : ℝ))) := by norm_num
      _ = Real.rpow X 1 * Real.rpow X (-(2 / 15 : ℝ)) :=
        Real.rpow_add hXpos 1 (-(2 / 15 : ℝ))
      _ = X * Real.rpow X (-(2 / 15 : ℝ)) := by
        rw [show Real.rpow X 1 = X by exact Real.rpow_one X]
  have hquarter : Real.rpow X (13 / 15 : ℝ) ≤ X / 4 := by
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_left hsmallX hXpos.le]
  linarith [hheight, hquarter]

/-- Uniform logarithmic collapse on the polylogarithmic conductor family and
the enlarged endpoint range `[X/2,5X]`. -/
theorem log_endpoint_level_le
    {K X t : ℝ} {q : ℕ} [NeZero q]
    (hK : 0 < K) (hX : Real.exp 2 ≤ X)
    (hq : (q : ℝ) ≤ Real.rpow (Real.log X) K)
    (ht0 : 0 ≤ t) (ht : t ≤ 5 * X) :
    Real.log (t * (q : ℝ) + 2) ≤ (K + 4) * Real.log X := by
  have hXpos : 0 < X := (Real.exp_pos 2).trans_le hX
  have hXtwo : 2 ≤ X := by
    have : 2 < Real.exp 2 := by nlinarith [Real.exp_one_gt_d9, Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 2)]
    exact this.le.trans hX
  have hXone : 1 ≤ X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hXone
  have hlogX : Real.log X ≤ X := by
    linarith [Real.log_le_sub_one_of_pos hXpos]
  have hlogPow : Real.rpow (Real.log X) K ≤ Real.rpow X K :=
    Real.rpow_le_rpow hlog hlogX hK.le
  have hqX : (q : ℝ) ≤ Real.rpow X K := hq.trans hlogPow
  have hXK0 : 0 ≤ Real.rpow X K := Real.rpow_nonneg hXpos.le _
  have hXKone : 1 ≤ Real.rpow X K := Real.one_le_rpow hXone hK.le
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have htq : t * (q : ℝ) ≤ 5 * X * Real.rpow X K := by
    exact mul_le_mul ht hqX hq0 (by positivity)
  have htwo : 2 ≤ 2 * (X * Real.rpow X K) := by
    nlinarith [mul_le_mul hXone hXKone (by norm_num : (0 : ℝ) ≤ 1) hXpos.le]
  have harg : t * (q : ℝ) + 2 ≤
      7 * (X * Real.rpow X K) := by
    nlinarith
  have hmulPow : X * Real.rpow X K = Real.rpow X (K + 1) := by
    calc
      X * Real.rpow X K = Real.rpow X 1 * Real.rpow X K := by
        rw [show Real.rpow X 1 = X by exact Real.rpow_one X]
      _ = Real.rpow X (1 + K) := (Real.rpow_add hXpos 1 K).symm
      _ = Real.rpow X (K + 1) := by ring_nf
  have hseven : (7 : ℝ) ≤ Real.rpow X 3 := by
    have hpow3 : Real.rpow X (3 : ℝ) = X ^ (3 : ℕ) := by
      exact Real.rpow_natCast X 3
    rw [hpow3]
    calc
      (7 : ℝ) ≤ 2 ^ (3 : ℕ) := by norm_num
      _ ≤ X ^ (3 : ℕ) := by gcongr
  have hpowK : 0 ≤ Real.rpow X (K + 1) := Real.rpow_nonneg hXpos.le _
  have hargPow : t * (q : ℝ) + 2 ≤ Real.rpow X (K + 4) := by
    calc
      t * (q : ℝ) + 2 ≤ 7 * (X * Real.rpow X K) := harg
      _ = 7 * Real.rpow X (K + 1) := by rw [hmulPow]
      _ ≤ Real.rpow X 3 * Real.rpow X (K + 1) :=
        mul_le_mul_of_nonneg_right hseven hpowK
      _ = Real.rpow X (3 + (K + 1)) :=
        (Real.rpow_add hXpos 3 (K + 1)).symm
      _ = Real.rpow X (K + 4) := by ring_nf
  have hargPos : 0 < t * (q : ℝ) + 2 := by positivity
  calc
    Real.log (t * (q : ℝ) + 2) ≤ Real.log (Real.rpow X (K + 4)) :=
      Real.log_le_log hargPos hargPow
    _ = (K + 4) * Real.log X := Real.log_rpow hXpos (K + 4)

/-- Scale envelope supplied by the pointwise 11.3 remainder after taking one
legal short-interval difference. -/
def kouk113ScaleEnvelope
    (C K T epsilon X : ℝ) : ℝ :=
  10 * C * X * ((K + 4) * Real.log X) ^ 2 /
    (T * Real.rpow X (2 / 15 + epsilon))

/-- The uncountable legal-aperture maximum is bounded pointwise by the single
11.3 scale envelope.  Both endpoints use the same full-support formula. -/
theorem paperEdgeRemainderMaxSq_le_kouk113ScaleEnvelope
    {C K T epsilon X x : ℝ} {q Q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {sigma : ℝ}
    (hC : 0 < C) (hK : 0 < K) (hepsilon : 0 < epsilon)
    (hX : Real.exp 2 ≤ X)
    (hQ : (Q : ℝ) ≤ Real.rpow (Real.log X) K)
    (hqQ : q ≤ Q)
    (hheight : apZeroHeight (min epsilon (1 / 10)) X + 1 ≤ X / 2)
    (hT : T ∈ Set.Ioo (apZeroHeight (min epsilon (1 / 10)) X)
      (apZeroHeight (min epsilon (1 / 10)) X + 1))
    (hlegal : paperEdgeContourLegal chi sigma T)
    (hx : x ∈ Set.Icc (X / 2) (4 * X))
    (hbound : ∀ t ∈ Set.Icc (X / 2) (5 * X),
        ‖fullSupportEndpointResidual chi T t‖ ≤
          C * t * (Real.log (t * (q : ℝ) + 2)) ^ 2 / T) :
    paperEdgeRemainderMaxSq chi sigma T epsilon X x ≤
      ENNReal.ofReal (kouk113ScaleEnvelope C K T epsilon X) ^ 2 := by
  have hXpos : 0 < X := (Real.exp_pos 2).trans_le hX
  have hXtwo : 2 ≤ X := by
    have : 2 < Real.exp 2 :=
      Real.exp_one_gt_two.trans
        (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 2))
    exact this.le.trans hX
  have hHpos : 0 < Real.rpow X (2 / 15 + epsilon) :=
    Real.rpow_pos_of_pos hXpos _
  have hTpos : 0 < T := hlegal.1
  have hTtwo : 2 ≤ T := by
    have hheightTwo : 2 ≤ apZeroHeight (min epsilon (1 / 10)) X := by
      unfold apZeroHeight
      have hexpPos : 0 < 13 / 15 - min epsilon (1 / 10) / 2 := by
        have hminle : min epsilon (1 / 10) ≤ 1 / 10 := min_le_right _ _
        linarith
      have hbase : Real.exp 2 ≤ X := hX
      have hp := Real.rpow_le_rpow (Real.exp_pos 2).le hbase hexpPos.le
      have hlow : 2 ≤ Real.rpow (Real.exp 2)
          (13 / 15 - min epsilon (1 / 10) / 2) := by
        have hrpow : Real.rpow (Real.exp 2)
            (13 / 15 - min epsilon (1 / 10) / 2) =
            Real.exp (2 * (13 / 15 - min epsilon (1 / 10) / 2)) := by
          have hdef := Real.rpow_def_of_pos (Real.exp_pos 2)
            (13 / 15 - min epsilon (1 / 10) / 2)
          simpa [Real.log_exp, mul_comm] using hdef
        rw [hrpow]
        have hminle : min epsilon (1 / 10) ≤ 1 / 10 := min_le_right _ _
        have hexp : 1 ≤ 2 * (13 / 15 - min epsilon (1 / 10) / 2) := by
          linarith
        exact (Real.exp_one_gt_two.le.trans
          (Real.exp_le_exp.mpr hexp))
      exact hlow.trans hp
    exact hheightTwo.trans hT.1.le
  have hq : (q : ℝ) ≤ Real.rpow (Real.log X) K :=
    (by exact_mod_cast hqQ : (q : ℝ) ≤ Q) |>.trans hQ
  unfold paperEdgeRemainderMaxSq
  apply iSup_le
  intro Y
  apply iSup_le
  intro hYlow
  apply iSup_le
  intro hYhigh
  have hYpos : 0 < Y := hHpos.trans_le hYlow
  have hTx : T ≤ x := hT.2.le.trans (hheight.trans hx.1)
  have hTxy : T ≤ x + Y := hTx.trans (le_add_of_nonneg_right hYpos.le)
  have hxone : 1 ≤ x := by linarith [hx.1]
  have hxyone : 1 ≤ x + Y := by linarith
  have hNx : 1 ≤ ⌊x⌋₊ :=
    Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x by simpa using hxone)
  have hNxy : 1 ≤ ⌊x + Y⌋₊ :=
    Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x + Y by simpa using hxyone)
  have hx0 : 0 ≤ x := zero_le_one.trans hxone
  have hxy0 : 0 ≤ x + Y := zero_le_one.trans hxyone
  have hx5 : x ≤ 5 * X := hx.2.trans (by linarith)
  have hxy5 : x + Y ≤ 5 * X := by linarith [hx.2, hYhigh]
  have hlogx := log_endpoint_level_le hK hX hq hx0 hx5
  have hlogxy := log_endpoint_level_le hK hX hq hxy0 hxy5
  have hlogx0 : 0 ≤ Real.log (x * (q : ℝ) + 2) := by
    apply Real.log_nonneg
    have hqNat : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqNat
    nlinarith
  have hlogxy0 : 0 ≤ Real.log ((x + Y) * (q : ℝ) + 2) := by
    apply Real.log_nonneg
    have hqNat : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqNat
    nlinarith
  have hlogXpos : 0 < Real.log X :=
    Real.log_pos (by linarith [hXtwo] : 1 < X)
  have hL0 : 0 ≤ (K + 4) * Real.log X := by
    positivity
  have hRx := hbound x ⟨hx.1, hx5⟩
  have hRxy := hbound (x + Y) ⟨by linarith [hx.1], hxy5⟩
  have hRx' : ‖endpointRemainder chi sigma T x‖ ≤
      C * x * (((K + 4) * Real.log X) ^ 2) / T := by
    rw [endpointRemainder_eq_fullSupportEndpointResidual chi hlegal hNx]
    refine hRx.trans ?_
    have hsquare : (Real.log (x * (q : ℝ) + 2)) ^ 2 ≤
        ((K + 4) * Real.log X) ^ 2 :=
      (sq_le_sq₀ hlogx0 hL0).2 hlogx
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsquare (mul_nonneg hC.le hx0)) hTpos.le
  have hRxy' : ‖endpointRemainder chi sigma T (x + Y)‖ ≤
      C * (x + Y) * (((K + 4) * Real.log X) ^ 2) / T := by
    rw [endpointRemainder_eq_fullSupportEndpointResidual chi hlegal hNxy]
    refine hRxy.trans ?_
    have hsquare : (Real.log ((x + Y) * (q : ℝ) + 2)) ^ 2 ≤
        ((K + 4) * Real.log X) ^ 2 :=
      (sq_le_sq₀ hlogxy0 hL0).2 hlogxy
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsquare (mul_nonneg hC.le hxy0)) hTpos.le
  have hnum :
      ‖endpointRemainder chi sigma T (x + Y) -
          endpointRemainder chi sigma T x‖ ≤
        10 * C * X * (((K + 4) * Real.log X) ^ 2) / T := by
    calc
      ‖endpointRemainder chi sigma T (x + Y) -
          endpointRemainder chi sigma T x‖ ≤
        ‖endpointRemainder chi sigma T (x + Y)‖ +
          ‖endpointRemainder chi sigma T x‖ := norm_sub_le _ _
      _ ≤ C * (x + Y) * (((K + 4) * Real.log X) ^ 2) / T +
          C * x * (((K + 4) * Real.log X) ^ 2) / T :=
        add_le_add hRxy' hRx'
      _ ≤ 10 * C * X * (((K + 4) * Real.log X) ^ 2) / T := by
        have hsquare0 : 0 ≤ (((K + 4) * Real.log X) ^ 2) := sq_nonneg _
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ hTpos.le
        calc
          C * (x + Y) * (((K + 4) * Real.log X) ^ 2) +
              C * x * (((K + 4) * Real.log X) ^ 2) =
            (C * (((K + 4) * Real.log X) ^ 2)) * (x + Y + x) := by ring
          _ ≤ (C * (((K + 4) * Real.log X) ^ 2)) * (10 * X) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le hsquare0)
            linarith [hx.2, hYhigh]
          _ = 10 * C * X * (((K + 4) * Real.log X) ^ 2) := by ring
  have hquot :
      ‖(endpointRemainder chi sigma T (x + Y) -
          endpointRemainder chi sigma T x) / Y‖ ≤
        kouk113ScaleEnvelope C K T epsilon X := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hYpos]
    unfold kouk113ScaleEnvelope
    have hnum0 : 0 ≤
        10 * C * X * (((K + 4) * Real.log X) ^ 2) / T := by positivity
    calc
      ‖endpointRemainder chi sigma T (x + Y) -
          endpointRemainder chi sigma T x‖ / Y ≤
        (10 * C * X * (((K + 4) * Real.log X) ^ 2) / T) / Y :=
          div_le_div_of_nonneg_right hnum hYpos.le
      _ ≤ (10 * C * X * (((K + 4) * Real.log X) ^ 2) / T) /
          Real.rpow X (2 / 15 + epsilon) := by
        exact div_le_div_of_nonneg_left hnum0 hHpos hYlow
      _ = 10 * C * X * (((K + 4) * Real.log X) ^ 2) /
          (T * Real.rpow X (2 / 15 + epsilon)) := by field_simp
  rw [← ENNReal.ofReal_pow (norm_nonneg _) 2]
  have henv0 : 0 ≤ kouk113ScaleEnvelope C K T epsilon X := by
    unfold kouk113ScaleEnvelope
    positivity
  rw [← ENNReal.ofReal_pow henv0 2]
  exact ENNReal.ofReal_le_ofReal
    ((sq_le_sq₀ (norm_nonneg _) henv0).2 hquot)

/-- Exact character normalization collapses the finite family to one factor
of `Q`; no extra number of characters is lost. -/
theorem familyPaperEdgeTailMajorant_le_kouk113ScaleEnvelope
    {C K T epsilon X x : ℝ} {Q : ℕ}
    (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (hC : 0 < C) (hK : 0 < K) (hepsilon : 0 < epsilon)
    (hX : Real.exp 2 ≤ X)
    (hQ : (Q : ℝ) ≤ Real.rpow (Real.log X) K)
    (hheight : apZeroHeight (min epsilon (1 / 10)) X + 1 ≤ X / 2)
    (hT : T ∈ Set.Ioo (apZeroHeight (min epsilon (1 / 10)) X)
      (apZeroHeight (min epsilon (1 / 10)) X + 1))
    (hlegal : ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
        (chi : DirichletCharacter ℂ q),
      @paperEdgeContourLegal q
        ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
        chi (sigma q chi) T)
    (hx : x ∈ Set.Icc (X / 2) (4 * X))
    (hbound : ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
        (chi : DirichletCharacter ℂ q),
        letI : NeZero q :=
          ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
        ∀ t ∈ Set.Icc (X / 2) (5 * X),
          ‖fullSupportEndpointResidual chi T t‖ ≤
            C * t * (Real.log (t * (q : ℝ) + 2)) ^ 2 / T) :
    familyPaperEdgeTailMajorant Q sigma T epsilon X x ≤
      (Q : ℝ≥0∞) *
        ENNReal.ofReal (kouk113ScaleEnvelope C K T epsilon X) ^ 2 := by
  let B : ℝ≥0∞ :=
    ENNReal.ofReal (kouk113ScaleEnvelope C K T epsilon X) ^ 2
  unfold familyPaperEdgeTailMajorant
  calc
    (∑ q ∈ Finset.Icc 1 Q,
      if hq : q = 0 then 0 else
        letI : NeZero q := ⟨hq⟩
        (q.totient : ℝ≥0∞)⁻¹ *
          ∑ chi : DirichletCharacter ℂ q,
            paperEdgeRemainderMaxSq chi (sigma q chi) T epsilon X x) ≤
      ∑ _q ∈ Finset.Icc 1 Q, B := by
        apply Finset.sum_le_sum
        intro q hqmem
        have hqpos : 1 ≤ q := (Finset.mem_Icc.mp hqmem).1
        have hqQ : q ≤ Q := (Finset.mem_Icc.mp hqmem).2
        have hq0 : q ≠ 0 := Nat.ne_of_gt hqpos
        simp only [dif_neg hq0]
        letI : NeZero q := ⟨hq0⟩
        have hchars :
            (∑ chi : DirichletCharacter ℂ q,
              paperEdgeRemainderMaxSq chi (sigma q chi) T epsilon X x) ≤
            ∑ _chi : DirichletCharacter ℂ q, B := by
          apply Finset.sum_le_sum
          intro chi _hchimem
          exact paperEdgeRemainderMaxSq_le_kouk113ScaleEnvelope
            chi hC hK hepsilon hX hQ hqQ hheight hT
              (hlegal q hqmem chi) hx (hbound q hqmem chi)
        calc
          (q.totient : ℝ≥0∞)⁻¹ *
              ∑ chi : DirichletCharacter ℂ q,
                paperEdgeRemainderMaxSq chi (sigma q chi) T epsilon X x ≤
            (q.totient : ℝ≥0∞)⁻¹ *
              ∑ _chi : DirichletCharacter ℂ q, B :=
                mul_le_mul_right hchars _
          _ = B := by
            rw [Finset.sum_const]
            have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
              rw [← Nat.card_eq_fintype_card]
              exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
            rw [Finset.card_univ, hcard, nsmul_eq_mul]
            have hphi0 : (q.totient : ℝ≥0∞) ≠ 0 := by
              exact_mod_cast
                (Nat.totient_pos.mpr (Nat.zero_lt_of_lt hqpos)).ne'
            rw [← mul_assoc, ENNReal.inv_mul_cancel hphi0 (by simp)]
            simp
    _ = (Q : ℝ≥0∞) * B := by
      rw [Finset.sum_const, Nat.card_Icc]
      norm_num [nsmul_eq_mul]
    _ = _ := rfl

/-- Outer integration adds only the exact length `7X/2`. -/
theorem lintegral_familyPaperEdgeTailMajorant_le_kouk113ScaleEnvelope
    {C K T epsilon X : ℝ} {Q : ℕ}
    (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (hC : 0 < C) (hK : 0 < K) (hepsilon : 0 < epsilon)
    (hX : Real.exp 2 ≤ X)
    (hQ : (Q : ℝ) ≤ Real.rpow (Real.log X) K)
    (hheight : apZeroHeight (min epsilon (1 / 10)) X + 1 ≤ X / 2)
    (hT : T ∈ Set.Ioo (apZeroHeight (min epsilon (1 / 10)) X)
      (apZeroHeight (min epsilon (1 / 10)) X + 1))
    (hlegal : ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
        (chi : DirichletCharacter ℂ q),
      @paperEdgeContourLegal q
        ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
        chi (sigma q chi) T)
    (hbound : ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
        (chi : DirichletCharacter ℂ q),
        letI : NeZero q :=
          ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
        ∀ t ∈ Set.Icc (X / 2) (5 * X),
          ‖fullSupportEndpointResidual chi T t‖ ≤
            C * t * (Real.log (t * (q : ℝ) + 2)) ^ 2 / T) :
    (∫⁻ x in Set.Icc (X / 2) (4 * X),
      familyPaperEdgeTailMajorant Q sigma T epsilon X x) ≤
      ((Q : ℝ≥0∞) *
        ENNReal.ofReal (kouk113ScaleEnvelope C K T epsilon X) ^ 2) *
          ENNReal.ofReal (7 * X / 2) := by
  calc
    (∫⁻ x in Set.Icc (X / 2) (4 * X),
      familyPaperEdgeTailMajorant Q sigma T epsilon X x) ≤
      ∫⁻ _x in Set.Icc (X / 2) (4 * X),
        ((Q : ℝ≥0∞) *
          ENNReal.ofReal (kouk113ScaleEnvelope C K T epsilon X) ^ 2) := by
        apply MeasureTheory.setLIntegral_mono' measurableSet_Icc
        intro x hx
        exact familyPaperEdgeTailMajorant_le_kouk113ScaleEnvelope
          sigma hC hK hepsilon hX hQ hheight hT hlegal hx hbound
    _ = ((Q : ℝ≥0∞) *
        ENNReal.ofReal (kouk113ScaleEnvelope C K T epsilon X) ^ 2) *
          ENNReal.ofReal (7 * X / 2) := by
      rw [MeasureTheory.setLIntegral_const, Real.volume_Icc]
      congr 2
      ring

/-- The explicit `T*Y` reserve turns the 11.3 scale envelope into arbitrary
logarithmic saving, uniformly over the selected unit height interval. -/
theorem eventually_kouk113ScaleEnvelope_le
    (C K M epsilon : ℝ) (hC : 0 < C) (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℝ in atTop,
      ∀ T ∈ Set.Ioo (apZeroHeight (min epsilon (1 / 10)) X)
          (apZeroHeight (min epsilon (1 / 10)) X + 1),
        kouk113ScaleEnvelope C K T epsilon X ≤
          10 * C * (K + 4) ^ 2 *
            Real.rpow (Real.log X) (-M) := by
  have hreserve :=
    MAPAPTailReserveAbsorption.eventually_literal_tail_ratio_mul_polylog_le
      M 2 epsilon hepsilon
  filter_upwards [hreserve, eventually_ge_atTop (Real.exp 1)] with X hreserveX hX
  intro T hT
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog : 0 < Real.log X :=
    zero_lt_one.trans_le ((Real.le_log_iff_exp_le hXpos).2 hX)
  have hH0pos : 0 < apZeroHeight (min epsilon (1 / 10)) X :=
    Real.rpow_pos_of_pos hXpos _
  have hHpos : 0 < Real.rpow X (2 / 15 + epsilon) :=
    Real.rpow_pos_of_pos hXpos _
  have hTpos : 0 < T := hH0pos.trans hT.1
  have hratio : X / (T * Real.rpow X (2 / 15 + epsilon)) ≤
      Real.rpow X 1 /
        (apZeroHeight (min epsilon (1 / 10)) X *
          Real.rpow X (2 / 15 + epsilon)) := by
    have hnum : X = Real.rpow X 1 := (Real.rpow_one X).symm
    rw [← hnum]
    apply div_le_div_of_nonneg_left hXpos.le
      (mul_pos hH0pos hHpos) (mul_le_mul_of_nonneg_right hT.1.le hHpos.le)
  have htrade :
      (X / (T * Real.rpow X (2 / 15 + epsilon))) *
          Real.rpow (Real.log X) 2 ≤
        Real.rpow (Real.log X) (-M) := by
    exact (mul_le_mul_of_nonneg_right hratio
      (Real.rpow_nonneg hlog.le 2)).trans hreserveX
  have hpow : (Real.log X) ^ (2 : ℕ) =
      Real.rpow (Real.log X) 2 := by
    exact (Real.rpow_natCast (Real.log X) 2).symm
  unfold kouk113ScaleEnvelope
  rw [mul_pow, hpow]
  have hconst : 0 ≤ 10 * C * (K + 4) ^ 2 := by positivity
  calc
    10 * C * X * ((K + 4) ^ 2 * Real.rpow (Real.log X) 2) /
        (T * Real.rpow X (2 / 15 + epsilon)) =
      (10 * C * (K + 4) ^ 2) *
        ((X / (T * Real.rpow X (2 / 15 + epsilon))) *
          Real.rpow (Real.log X) 2) := by field_simp
    _ ≤ (10 * C * (K + 4) ^ 2) *
        Real.rpow (Real.log X) (-M) :=
      mul_le_mul_of_nonneg_left htrade hconst

/-- The universal-height 11.3 estimate supplies the corrected common-height
tail.  The localized selected-height route below is an independent alternative. -/
theorem correctedAPExplicitFormulaTailFamilySquare_of_kouk113
    (h113 : KoukTheorem113FullSupportPointwise) :
    CorrectedAPExplicitFormulaTailFamilySquare := by
  rcases h113 with ⟨C0, hC0, hsource⟩
  intro K A epsilon hK hA hepsilon hepsilonCap
  let M : ℝ := A + K + 1
  let D : ℝ := 10 * C0 * (K + 4) ^ 2
  have henv := eventually_kouk113ScaleEnvelope_le
    C0 K M epsilon hC0 hepsilon
  have hhalf := eventually_apZeroHeight_add_one_le_half epsilon hepsilon
  have hall : ∀ᶠ X : ℝ in atTop,
      (∀ T ∈ Set.Ioo (apZeroHeight (min epsilon (1 / 10)) X)
          (apZeroHeight (min epsilon (1 / 10)) X + 1),
        kouk113ScaleEnvelope C0 K T epsilon X ≤
          D * Real.rpow (Real.log X) (-M)) ∧
      apZeroHeight (min epsilon (1 / 10)) X + 1 ≤ X / 2 ∧
      Real.exp 2 ≤ X := by
    filter_upwards [henv, hhalf, eventually_ge_atTop (Real.exp 2)] with X henvX hhalfX hX
    exact ⟨by simpa [D] using henvX, hhalfX, hX⟩
  rw [eventually_atTop] at hall
  rcases hall with ⟨Xevent, hXevent⟩
  let C : ℝ := 7 * D ^ 2 / 2
  let X0 : ℝ := max 2 Xevent
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, X0, hC, le_max_left _ _, ?_⟩
  intro X hXX0
  have hXe : Xevent ≤ X := (le_max_right 2 Xevent).trans hXX0
  rcases hXevent X hXe with ⟨henvX, hhalfX, hX⟩
  have hXpos : 0 < X := (Real.exp_pos 2).trans_le hX
  have hXone : 1 ≤ X := by
    have : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
    exact this.le.trans hX
  have hlogOne : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hX
  have hlog : 0 < Real.log X := zero_lt_one.trans_le hlogOne
  let reserve : ℝ := min epsilon (1 / 10)
  let H : ℝ := apZeroHeight reserve X
  let Q : ℕ := ⌊Real.rpow (Real.log X) K⌋₊
  have hHpos : 0 < H := by
    dsimp [H, reserve]
    exact Real.rpow_pos_of_pos hXpos _
  have hQ : (Q : ℝ) ≤ Real.rpow (Real.log X) K := by
    dsimp [Q]
    exact Nat.floor_le (Real.rpow_nonneg hlog.le K)
  obtain ⟨T, hT, sigma, hlegal⟩ :=
    MAPAPCorrectedCommonHeightContract.exists_commonHeight_familyPaperEdgeContours_total
      Q hHpos
  refine ⟨T, by simpa [H, reserve] using hT, sigma, ?_, ?_⟩
  · intro q hq chi
    exact hlegal q hq chi
  · have hTtwo : 2 ≤ T := by
      have hheightTwo : 2 ≤ apZeroHeight reserve X := by
        dsimp [reserve]
        unfold apZeroHeight
        have hexpPos : 0 < 13 / 15 - min epsilon (1 / 10) / 2 := by
          have hminle : min epsilon (1 / 10) ≤ 1 / 10 := min_le_right _ _
          linarith
        have hp := Real.rpow_le_rpow (Real.exp_pos 2).le hX hexpPos.le
        have hlow : 2 ≤ Real.rpow (Real.exp 2)
            (13 / 15 - min epsilon (1 / 10) / 2) := by
          have hrpow : Real.rpow (Real.exp 2)
              (13 / 15 - min epsilon (1 / 10) / 2) =
              Real.exp (2 * (13 / 15 - min epsilon (1 / 10) / 2)) := by
            have hdef := Real.rpow_def_of_pos (Real.exp_pos 2)
              (13 / 15 - min epsilon (1 / 10) / 2)
            simpa [Real.log_exp, mul_comm] using hdef
          rw [hrpow]
          have hminle : min epsilon (1 / 10) ≤ 1 / 10 := min_le_right _ _
          exact Real.exp_one_gt_two.le.trans
            (Real.exp_le_exp.mpr (by linarith))
        exact hlow.trans hp
      exact hheightTwo.trans hT.1.le
    have hsourceLocal :
        ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
            (chi : DirichletCharacter ℂ q),
          letI : NeZero q :=
            ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
          ∀ t ∈ Set.Icc (X / 2) (5 * X),
            ‖fullSupportEndpointResidual chi T t‖ ≤
              C0 * t * (Real.log (t * (q : ℝ) + 2)) ^ 2 / T := by
      intro q hq chi t ht
      letI : NeZero q := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
      apply hsource q chi T t hTtwo
      exact hT.2.le.trans (hhalfX.trans ht.1)
    have hraw :=
      lintegral_familyPaperEdgeTailMajorant_le_kouk113ScaleEnvelope
        sigma hC0 hK hepsilon hX hQ
          (by simpa [reserve] using hhalfX)
          (by simpa [H, reserve] using hT) hlegal hsourceLocal
    have hE := henvX T (by simpa [H, reserve] using hT)
    have hE0 : 0 ≤ kouk113ScaleEnvelope C0 K T epsilon X := by
      unfold kouk113ScaleEnvelope
      have hTpos : 0 < T := hHpos.trans hT.1
      exact div_nonneg (by positivity)
        (mul_nonneg hTpos.le
          (Real.rpow_nonneg hXpos.le (2 / 15 + epsilon)))
    have hLM0 : 0 ≤ Real.rpow (Real.log X) (-M) :=
      Real.rpow_nonneg hlog.le _
    have hEsq : (kouk113ScaleEnvelope C0 K T epsilon X) ^ 2 ≤
        (D * Real.rpow (Real.log X) (-M)) ^ 2 :=
      (sq_le_sq₀ hE0 (mul_nonneg hD.le hLM0)).2 hE
    have hpowprod :
        Real.rpow (Real.log X) K *
            (Real.rpow (Real.log X) (-M)) ^ 2 ≤
          Real.rpow (Real.log X) (-A) := by
      have hsq : (Real.rpow (Real.log X) (-M)) ^ 2 =
          Real.rpow (Real.log X) (-M + -M) := by
        calc
          (Real.rpow (Real.log X) (-M)) ^ 2 =
              Real.rpow (Real.log X) (-M) *
                Real.rpow (Real.log X) (-M) := by ring
          _ = Real.rpow (Real.log X) (-M + -M) :=
            (Real.rpow_add hlog (-M) (-M)).symm
      rw [hsq]
      calc
        Real.rpow (Real.log X) K *
            Real.rpow (Real.log X) (-M + -M) =
          Real.rpow (Real.log X) (K + (-M + -M)) :=
            (Real.rpow_add hlog K (-M + -M)).symm
        _ ≤ Real.rpow (Real.log X) (-A) := by
          apply Real.rpow_le_rpow_of_exponent_le hlogOne
          dsimp [M]
          linarith
    have hreal :
        (Q : ℝ) * (kouk113ScaleEnvelope C0 K T epsilon X) ^ 2 *
            (7 * X / 2) ≤
          C * X * Real.rpow (Real.log X) (-A) := by
      have hQ0 : 0 ≤ (Q : ℝ) := Nat.cast_nonneg Q
      have hDsq0 : 0 ≤ D ^ 2 := sq_nonneg D
      have hLK0 : 0 ≤ Real.rpow (Real.log X) K :=
        Real.rpow_nonneg hlog.le _
      calc
        (Q : ℝ) * (kouk113ScaleEnvelope C0 K T epsilon X) ^ 2 *
            (7 * X / 2) ≤
          Real.rpow (Real.log X) K *
              (D * Real.rpow (Real.log X) (-M)) ^ 2 *
                (7 * X / 2) := by
            gcongr
        _ = C * X *
            (Real.rpow (Real.log X) K *
              (Real.rpow (Real.log X) (-M)) ^ 2) := by
            dsimp [C]
            ring
        _ ≤ C * X * Real.rpow (Real.log X) (-A) := by
          gcongr
    calc
      (∫⁻ x in Set.Icc (X / 2) (4 * X),
          familyPaperEdgeTailMajorant Q sigma T epsilon X x) ≤
        ((Q : ℝ≥0∞) *
          ENNReal.ofReal (kouk113ScaleEnvelope C0 K T epsilon X) ^ 2) *
            ENNReal.ofReal (7 * X / 2) := hraw
      _ = ENNReal.ofReal
          ((Q : ℝ) * (kouk113ScaleEnvelope C0 K T epsilon X) ^ 2 *
            (7 * X / 2)) := by
        rw [← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_pow hE0,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg Q)]
        have hleft0 : 0 ≤
            (Q : ℝ) * (kouk113ScaleEnvelope C0 K T epsilon X) ^ 2 := by
          positivity
        rw [← ENNReal.ofReal_mul hleft0]
      _ ≤ ENNReal.ofReal
          (C * X * Real.rpow (Real.log X) (-A)) :=
        ENNReal.ofReal_mono hreal

/-- The selected common-height form of Koukoulopoulos (11.5) supplies the
corrected family-square tail.  Unlike the legacy pointwise adapter above,
this theorem never asks for the source estimate at an arbitrarily prescribed
height: legality and the remainder estimate travel with the same selected
`T ∈ (H,H+1)`. -/
theorem correctedAPExplicitFormulaTailFamilySquare_of_selectedCommonHeight
    (h113 : KoukTheorem113SelectedCommonHeight) :
    CorrectedAPExplicitFormulaTailFamilySquare := by
  intro K A epsilon hK hA hepsilon hepsilonCap
  rcases h113 K epsilon hK hepsilon hepsilonCap with
    ⟨C0, Xsource, hC0, hXsourceTwo, hsource⟩
  let M : ℝ := A + K + 1
  let D : ℝ := 10 * C0 * (K + 4) ^ 2
  have henv := eventually_kouk113ScaleEnvelope_le
    C0 K M epsilon hC0 hepsilon
  have hhalf := eventually_apZeroHeight_add_one_le_half epsilon hepsilon
  have hall : ∀ᶠ X : ℝ in atTop,
      (∀ T ∈ Set.Ioo (apZeroHeight (min epsilon (1 / 10)) X)
          (apZeroHeight (min epsilon (1 / 10)) X + 1),
        kouk113ScaleEnvelope C0 K T epsilon X ≤
          D * Real.rpow (Real.log X) (-M)) ∧
      apZeroHeight (min epsilon (1 / 10)) X + 1 ≤ X / 2 ∧
      Real.exp 2 ≤ X := by
    filter_upwards [henv, hhalf, eventually_ge_atTop (Real.exp 2)] with X henvX hhalfX hX
    exact ⟨by simpa [D] using henvX, hhalfX, hX⟩
  rw [eventually_atTop] at hall
  rcases hall with ⟨Xevent, hXevent⟩
  let C : ℝ := 7 * D ^ 2 / 2
  let X0 : ℝ := max Xsource (max 2 Xevent)
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hX0two : 2 ≤ X0 := by
    exact (le_max_left 2 Xevent).trans
      ((le_max_right Xsource (max 2 Xevent)))
  refine ⟨C, X0, hC, hX0two, ?_⟩
  intro X hXX0
  have hXs : Xsource ≤ X :=
    (le_max_left Xsource (max 2 Xevent)).trans hXX0
  have hXe : Xevent ≤ X :=
    (le_max_right 2 Xevent).trans
      ((le_max_right Xsource (max 2 Xevent)).trans hXX0)
  rcases hXevent X hXe with ⟨henvX, hhalfX, hX⟩
  have hXpos : 0 < X := (Real.exp_pos 2).trans_le hX
  have hXone : 1 ≤ X := by
    have : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
    exact this.le.trans hX
  have hlogOne : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hX
  have hlog : 0 < Real.log X := zero_lt_one.trans_le hlogOne
  let reserve : ℝ := min epsilon (1 / 10)
  let H : ℝ := apZeroHeight reserve X
  let Q : ℕ := ⌊Real.rpow (Real.log X) K⌋₊
  have hHpos : 0 < H := by
    dsimp [H, reserve]
    exact Real.rpow_pos_of_pos hXpos _
  have hQ : (Q : ℝ) ≤ Real.rpow (Real.log X) K := by
    dsimp [Q]
    exact Nat.floor_le (Real.rpow_nonneg hlog.le K)
  have hselected := hsource X hXs
  dsimp only at hselected
  rcases hselected with ⟨T, hT, sigma, hlegal, hsourceLocal⟩
  refine ⟨T, by simpa [H, reserve] using hT, sigma, ?_, ?_⟩
  · intro q hq chi
    exact hlegal q (by simpa [Q] using hq) chi
  · have hraw :=
      lintegral_familyPaperEdgeTailMajorant_le_kouk113ScaleEnvelope
        sigma hC0 hK hepsilon hX hQ
          (by simpa [reserve] using hhalfX)
          (by simpa [H, reserve] using hT)
          (by
            intro q hq chi
            exact hlegal q (by simpa [Q] using hq) chi)
          (by
            intro q hq chi t ht
            exact hsourceLocal q (by simpa [Q] using hq) chi t ht)
    have hE := henvX T (by simpa [H, reserve] using hT)
    have hE0 : 0 ≤ kouk113ScaleEnvelope C0 K T epsilon X := by
      unfold kouk113ScaleEnvelope
      have hTpos : 0 < T := hHpos.trans hT.1
      exact div_nonneg (by positivity)
        (mul_nonneg hTpos.le
          (Real.rpow_nonneg hXpos.le (2 / 15 + epsilon)))
    have hLM0 : 0 ≤ Real.rpow (Real.log X) (-M) :=
      Real.rpow_nonneg hlog.le _
    have hEsq : (kouk113ScaleEnvelope C0 K T epsilon X) ^ 2 ≤
        (D * Real.rpow (Real.log X) (-M)) ^ 2 :=
      (sq_le_sq₀ hE0 (mul_nonneg hD.le hLM0)).2 hE
    have hpowprod :
        Real.rpow (Real.log X) K *
            (Real.rpow (Real.log X) (-M)) ^ 2 ≤
          Real.rpow (Real.log X) (-A) := by
      have hsq : (Real.rpow (Real.log X) (-M)) ^ 2 =
          Real.rpow (Real.log X) (-M + -M) := by
        calc
          (Real.rpow (Real.log X) (-M)) ^ 2 =
              Real.rpow (Real.log X) (-M) *
                Real.rpow (Real.log X) (-M) := by ring
          _ = Real.rpow (Real.log X) (-M + -M) :=
            (Real.rpow_add hlog (-M) (-M)).symm
      rw [hsq]
      calc
        Real.rpow (Real.log X) K *
            Real.rpow (Real.log X) (-M + -M) =
          Real.rpow (Real.log X) (K + (-M + -M)) :=
            (Real.rpow_add hlog K (-M + -M)).symm
        _ ≤ Real.rpow (Real.log X) (-A) := by
          apply Real.rpow_le_rpow_of_exponent_le hlogOne
          dsimp [M]
          linarith
    have hreal :
        (Q : ℝ) * (kouk113ScaleEnvelope C0 K T epsilon X) ^ 2 *
            (7 * X / 2) ≤
          C * X * Real.rpow (Real.log X) (-A) := by
      have hDsq0 : 0 ≤ D ^ 2 := sq_nonneg D
      have hLK0 : 0 ≤ Real.rpow (Real.log X) K :=
        Real.rpow_nonneg hlog.le _
      calc
        (Q : ℝ) * (kouk113ScaleEnvelope C0 K T epsilon X) ^ 2 *
            (7 * X / 2) ≤
          Real.rpow (Real.log X) K *
              (D * Real.rpow (Real.log X) (-M)) ^ 2 *
                (7 * X / 2) := by
            gcongr
        _ = C * X *
            (Real.rpow (Real.log X) K *
              (Real.rpow (Real.log X) (-M)) ^ 2) := by
            dsimp [C]
            ring
        _ ≤ C * X * Real.rpow (Real.log X) (-A) := by
          gcongr
    calc
      (∫⁻ x in Set.Icc (X / 2) (4 * X),
          familyPaperEdgeTailMajorant Q sigma T epsilon X x) ≤
        ((Q : ℝ≥0∞) *
          ENNReal.ofReal (kouk113ScaleEnvelope C0 K T epsilon X) ^ 2) *
            ENNReal.ofReal (7 * X / 2) := hraw
      _ = ENNReal.ofReal
          ((Q : ℝ) * (kouk113ScaleEnvelope C0 K T epsilon X) ^ 2 *
            (7 * X / 2)) := by
        rw [← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_pow hE0,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg Q)]
        have hleft0 : 0 ≤
            (Q : ℝ) * (kouk113ScaleEnvelope C0 K T epsilon X) ^ 2 := by
          positivity
        rw [← ENNReal.ofReal_mul hleft0]
      _ ≤ ENNReal.ofReal
          (C * X * Real.rpow (Real.log X) (-A)) :=
        ENNReal.ofReal_mono hreal

end
end MAPKoukTheorem113ToCorrectedTail

#print axioms MAPKoukTheorem113ToCorrectedTail.endpointRemainder_eq_fullSupportEndpointResidual
#print axioms MAPKoukTheorem113ToCorrectedTail.norm_endpointRemainder_le_of_kouk113
#print axioms MAPKoukTheorem113ToCorrectedTail.paperEdgeRemainderMaxSq_le_kouk113ScaleEnvelope
#print axioms MAPKoukTheorem113ToCorrectedTail.correctedAPExplicitFormulaTailFamilySquare_of_kouk113
#print axioms MAPKoukTheorem113ToCorrectedTail.correctedAPExplicitFormulaTailFamilySquare_of_selectedCommonHeight
