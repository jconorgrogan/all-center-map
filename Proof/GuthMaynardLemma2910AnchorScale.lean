import GuthMaynardLowAnchorTransfer
import GuthMaynardTPowerCardinality

/-!
# The coarse scale check for the low anchor in Lemma 29.10

The last paragraph of Lemma 29.10 chooses an anchor of the form
`D * R^(1/4) * T^((1+epsilon)/2)`.  The low-anchor transfer only needs this
quantity to be at most `T^2`.  This file isolates the elementary exponent
ledger which proves that fact after the subpower and cardinality factors have
been bounded separately.
-/

namespace GuthMaynardLemma2910AnchorScale

noncomputable section

open GuthMaynardJutilaReflection2941
open GuthMaynardTPowerCardinality
open GuthMaynardLowAnchorTransfer
open GuthMaynardLengthComparison

def sourceLowAnchor (T epsilon R D : ℝ) : ℝ :=
  D * Real.rpow R (1 / 4 : ℝ) *
    Real.rpow T ((1 + epsilon) / 2)

def sourceSubpowerEnvelope (C T : ℝ) : ℝ :=
  Real.exp (C * Real.log T / Real.log (Real.log T))

def sourceSubpowerThreshold (C : ℝ) : ℝ :=
  Real.exp (Real.exp (max (4 * C) 1))

/-- One explicit threshold simultaneously makes `log log T` positive and at
least `4C`. -/
theorem sourceSubpowerThreshold_facts
    (C : ℝ) {T : ℝ} (hT : sourceSubpowerThreshold C ≤ T) :
    1 < T ∧ 0 < Real.log (Real.log T) ∧
      4 * C ≤ Real.log (Real.log T) := by
  let L : ℝ := max (4 * C) 1
  have hL : 1 ≤ L := by exact le_max_right _ _
  have hexpL : 1 < Real.exp L := by
    exact Real.one_lt_exp_iff.mpr (zero_lt_one.trans_le hL)
  have hthresholdOne : 1 < sourceSubpowerThreshold C := by
    unfold sourceSubpowerThreshold
    exact Real.one_lt_exp_iff.mpr (Real.exp_pos _)
  have hTone : 1 < T := hthresholdOne.trans_le hT
  have hlogT : Real.exp L ≤ Real.log T := by
    have hlogmono := Real.log_le_log (Real.exp_pos (Real.exp L)) hT
    simpa [sourceSubpowerThreshold, L] using hlogmono
  have hloglog : L ≤ Real.log (Real.log T) := by
    have hmono := Real.log_le_log (Real.exp_pos L) hlogT
    simpa using hmono
  refine ⟨hTone, ?_, ?_⟩
  · exact (show (0 : ℝ) < 1 by norm_num).trans_le hL |>.trans_le hloglog
  · exact (le_max_left (4 * C) 1).trans hloglog

/-- The explicit threshold calculation behind `D(T) <= T^(1/4)`.
Writing the eventual condition as `4C <= log log T` keeps this lemma finite
and lets the final weld enlarge `T₀` once. -/
theorem sourceSubpowerEnvelope_le_quarter_power
    {C T : ℝ} (hT : 1 < T)
    (hloglog : 0 < Real.log (Real.log T))
    (hthreshold : 4 * C ≤ Real.log (Real.log T)) :
    sourceSubpowerEnvelope C T ≤ Real.rpow T (1 / 4 : ℝ) := by
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hratio : C / Real.log (Real.log T) ≤ 1 / 4 := by
    apply (div_le_iff₀ hloglog).2
    nlinarith
  have hexponent :
      C * Real.log T / Real.log (Real.log T) ≤
        Real.log T * (1 / 4 : ℝ) := by
    calc
      C * Real.log T / Real.log (Real.log T) =
          Real.log T * (C / Real.log (Real.log T)) := by ring
      _ ≤ Real.log T * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hratio hlog.le
  unfold sourceSubpowerEnvelope
  calc
    Real.exp (C * Real.log T / Real.log (Real.log T)) ≤
        Real.exp (Real.log T * (1 / 4 : ℝ)) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.rpow T (1 / 4 : ℝ) :=
      (Real.rpow_def_of_pos (by linarith : 0 < T) _).symm

/-- A coarse cardinality estimate `R <= T^2` supplies the quarter-power
factor used by the anchor ledger. -/
theorem quarter_power_le_half_power_of_le_square
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) (hRT : R ≤ T ^ 2) :
    Real.rpow R (1 / 4 : ℝ) ≤ Real.rpow T (1 / 2 : ℝ) := by
  have hmono : Real.rpow R (1 / 4 : ℝ) ≤
      Real.rpow (T ^ 2) (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hR hRT (by norm_num)
  calc
    Real.rpow R (1 / 4 : ℝ) ≤
        Real.rpow (T ^ 2) (1 / 4 : ℝ) := hmono
    _ = Real.rpow T (1 / 2 : ℝ) := by
      calc
        Real.rpow (T ^ 2) (1 / 4 : ℝ) =
            Real.rpow (Real.rpow T 2) (1 / 4 : ℝ) :=
          congrArg (fun x : ℝ => Real.rpow x (1 / 4 : ℝ))
            (Real.rpow_natCast T 2).symm
        _ = Real.rpow T ((2 : ℝ) * (1 / 4 : ℝ)) :=
          (Real.rpow_mul hT (2 : ℝ) (1 / 4 : ℝ)).symm
        _ = Real.rpow T (1 / 2 : ℝ) := by norm_num

/-- The manuscript's spacing hypotheses supply the quarter-power anchor
factor with no extra analytic input. -/
theorem card_quarter_power_le_time_half
    {T delta : ℝ} {G : Finset ℝ}
    (hT : 2 ≤ T) (hdelta : 0 ≤ delta)
    (hsep : TPowerSeparated G T delta)
    (hheight : InOpenClosedZeroT G T) :
    Real.rpow (G.card : ℝ) (1 / 4 : ℝ) ≤
      Real.rpow T (1 / 2 : ℝ) := by
  have hcard := card_cast_le_two_mul_T hT hdelta hsep hheight
  have hcardSq : (G.card : ℝ) ≤ T ^ 2 := by
    have hT0 : 0 ≤ T := by linarith
    nlinarith [sq_nonneg (T - 1)]
  exact quarter_power_le_half_power_of_le_square
    (by linarith) (Nat.cast_nonneg _) hcardSq

/-- The exact multiplicative ledger behind `P <= T^2`.  The assumptions are
the two independently supplied source estimates: `D <= T^(1/4)` and
`R^(1/4) <= T^(1/2)`. -/
theorem sourceLowAnchor_le_time_squared
    {T epsilon R D : ℝ}
    (hT : 1 ≤ T) (hepsilon : epsilon ≤ 1)
    (hD : D ≤ Real.rpow T (1 / 4 : ℝ))
    (hRquarter0 : 0 ≤ Real.rpow R (1 / 4 : ℝ))
    (hRquarter : Real.rpow R (1 / 4 : ℝ) ≤
      Real.rpow T (1 / 2 : ℝ)) :
    sourceLowAnchor T epsilon R D ≤ T ^ 2 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTepsilon :
      Real.rpow T ((1 + epsilon) / 2) ≤ Real.rpow T 1 := by
    apply Real.rpow_le_rpow_of_exponent_le hT
    linarith
  have hTquarter0 : 0 ≤ Real.rpow T (1 / 4 : ℝ) :=
    Real.rpow_nonneg hTpos.le _
  have hThalf0 : 0 ≤ Real.rpow T (1 / 2 : ℝ) :=
    Real.rpow_nonneg hTpos.le _
  have hTepsilon0 : 0 ≤ Real.rpow T ((1 + epsilon) / 2) :=
    Real.rpow_nonneg hTpos.le _
  have hproduct :
      sourceLowAnchor T epsilon R D ≤
        Real.rpow T (1 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ) *
          Real.rpow T 1 := by
    unfold sourceLowAnchor
    exact mul_le_mul
      (mul_le_mul hD hRquarter hRquarter0 hTquarter0)
      hTepsilon hTepsilon0
      (mul_nonneg hTquarter0 hThalf0)
  have hcombine :
      Real.rpow T (1 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ) *
          Real.rpow T 1 = Real.rpow T (7 / 4 : ℝ) := by
    calc
      Real.rpow T (1 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ) *
          Real.rpow T 1 =
          Real.rpow T ((1 / 4 : ℝ) + 1 / 2) * Real.rpow T 1 := by
            exact congrArg (fun x : ℝ => x * Real.rpow T 1)
              (Real.rpow_add hTpos (1 / 4 : ℝ) (1 / 2 : ℝ)).symm
      _ = Real.rpow T (((1 / 4 : ℝ) + 1 / 2) + 1) :=
        (Real.rpow_add hTpos _ _).symm
      _ = Real.rpow T (7 / 4 : ℝ) := by norm_num
  have hexponent : Real.rpow T (7 / 4 : ℝ) ≤ Real.rpow T 2 :=
    Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  calc
    sourceLowAnchor T epsilon R D ≤
        Real.rpow T (1 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ) *
          Real.rpow T 1 := hproduct
    _ = Real.rpow T (7 / 4 : ℝ) := hcombine
    _ ≤ Real.rpow T 2 := hexponent
    _ = T ^ 2 := Real.rpow_natCast T 2

/-- Fully assembled actual-anchor check.  This is the only scale fact needed
by `jutilaSecondMoment_low_anchor_time_squared_certified`. -/
theorem sourceLowAnchor_actual_le_time_squared
    {C T epsilon delta : ℝ} {G : Finset ℝ}
    (hT : 2 ≤ T) (hepsilon : epsilon ≤ 1)
    (hdelta : 0 ≤ delta)
    (hsep : TPowerSeparated G T delta)
    (hheight : InOpenClosedZeroT G T)
    (hloglog : 0 < Real.log (Real.log T))
    (hthreshold : 4 * C ≤ Real.log (Real.log T)) :
    sourceLowAnchor T epsilon (G.card : ℝ)
        (sourceSubpowerEnvelope C T) ≤ T ^ 2 := by
  apply sourceLowAnchor_le_time_squared (by linarith) hepsilon
  · exact sourceSubpowerEnvelope_le_quarter_power
      (by linarith) hloglog hthreshold
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact card_quarter_power_le_time_half hT hdelta hsep hheight

/-- Eventual form with an explicit single threshold and no logarithmic side
conditions left at the call site. -/
theorem sourceLowAnchor_eventually_le_time_squared
    {C T epsilon delta : ℝ} {G : Finset ℝ}
    (hT : max 2 (sourceSubpowerThreshold C) ≤ T)
    (hepsilon : epsilon ≤ 1) (hdelta : 0 ≤ delta)
    (hsep : TPowerSeparated G T delta)
    (hheight : InOpenClosedZeroT G T) :
    sourceLowAnchor T epsilon (G.card : ℝ)
        (sourceSubpowerEnvelope C T) ≤ T ^ 2 := by
  have hTtwo : 2 ≤ T := (le_max_left _ _).trans hT
  have hTthreshold : sourceSubpowerThreshold C ≤ T :=
    (le_max_right _ _).trans hT
  obtain ⟨_, hloglog, hthreshold⟩ :=
    sourceSubpowerThreshold_facts C hTthreshold
  exact sourceLowAnchor_actual_le_time_squared hTtwo hepsilon hdelta
    hsep hheight hloglog hthreshold

/-- The literal last-paragraph transfer in Lemma 29.10, now for its actual
anchor rather than an abstract `P`.  The lower assumptions `1 <= N <= P` and
`2 <= P` are precisely the low-regime hypotheses; every scale and logarithm
conversion is discharged here. -/
theorem jutilaSecondMoment_to_sourceLowAnchor_certified :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C T epsilon delta N : ℝ) (G : Finset ℝ),
        max 2 (sourceSubpowerThreshold C) ≤ T →
        epsilon ≤ 1 → 0 ≤ delta →
        TPowerSeparated G T delta → InOpenClosedZeroT G T →
        1 ≤ N →
        N ≤ sourceLowAnchor T epsilon (G.card : ℝ)
          (sourceSubpowerEnvelope C T) →
        2 ≤ sourceLowAnchor T epsilon (G.card : ℝ)
          (sourceSubpowerEnvelope C T) →
        jutilaSecondMoment N G ≤
          K * (Real.log T) ^ 3 *
            jutilaSecondMoment
              (sourceLowAnchor T epsilon (G.card : ℝ)
                (sourceSubpowerEnvelope C T)) G := by
  obtain ⟨K, hK, htransfer⟩ :=
    jutilaSecondMoment_low_anchor_time_squared_certified
  refine ⟨K, hK, ?_⟩
  intro C T epsilon delta N G hT hepsilon hdelta hsep hheight
    hN hNP hP
  have hTtwo : 2 ≤ T := (le_max_left _ _).trans hT
  exact htransfer T N
    (sourceLowAnchor T epsilon (G.card : ℝ)
      (sourceSubpowerEnvelope C T)) G hTtwo hN hNP hP
    (sourceLowAnchor_eventually_le_time_squared hT hepsilon hdelta
      hsep hheight)

end

end GuthMaynardLemma2910AnchorScale

#print axioms GuthMaynardLemma2910AnchorScale.sourceLowAnchor_le_time_squared
#print axioms GuthMaynardLemma2910AnchorScale.quarter_power_le_half_power_of_le_square
#print axioms GuthMaynardLemma2910AnchorScale.card_quarter_power_le_time_half
#print axioms GuthMaynardLemma2910AnchorScale.sourceSubpowerEnvelope_le_quarter_power
#print axioms GuthMaynardLemma2910AnchorScale.sourceLowAnchor_actual_le_time_squared
#print axioms GuthMaynardLemma2910AnchorScale.sourceSubpowerThreshold_facts
#print axioms GuthMaynardLemma2910AnchorScale.sourceLowAnchor_eventually_le_time_squared
#print axioms GuthMaynardLemma2910AnchorScale.jutilaSecondMoment_to_sourceLowAnchor_certified
