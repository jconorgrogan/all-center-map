import APWeightedZeroMassIntegrationScaffold
import APZeroFieldEnergy28Grouping
import PrincipalZetaFullStrip
import SupportBoundaryQuantitative

/-!
# Global low-strip aggregation for equation (2.7)

This file spends only the certified full-strip Appendix-A.5 unit-window count.
It retains the literal ambient-character indexing, primitive-inducer repetition,
and analytic multiplicity of `apLowRangeMass`.  No zero-density or zero-free
source is introduced.
-/

namespace MAPAPLowRangeGlobal

open scoped BigOperators
open DirichletZeros MAPLocalZeroWindow
open MAPFixedScaleAPZeroRoute MAPLowBetaMeshClosure
open MAPAPWeightedZeroMassIntegration MAPAPZeroDensityCert CGLPolylogBypass
open MAPGuthMaynard

noncomputable section

private theorem principalA5_1683 :
    ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi.IsPrimitive → chi = 1 → ∀ t : ℝ,
        (closedUnitWindowCount chi 0 t : ℝ) ≤
          1683 * Real.log (arithmeticScale q t) := by
  intro q _inst chi hprim hchi t
  have hq : q = 1 := by
    rw [DirichletCharacter.isPrimitive_def, hchi,
      DirichletCharacter.conductor_one] at hprim
    exact hprim.symm
  subst q
  have hchi' : chi = (1 : DirichletCharacter ℂ 1) := hchi
  subst chi
  exact MAPPrincipalZetaFullStrip.principal_fullStrip_count_le_log t

private theorem zeroSupport_im_abs_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {T : ℝ} {rho : ℂ} (hrho : rho ∈ zeroSupport chi 0 T) :
    |rho.im| ≤ T := by
  have hrect :=
    PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
      chi 0 T hrho
  exact abs_le.mpr (Complex.mem_reProdIm.mp hrect).2

/-- One primitive character's full multiplicity-weighted rectangle count is
controlled by the certified sign-symmetric unit-window count.  The deliberately
common constant covers both the nonprincipal A.5 theorem and conductor-one
zeta. -/
theorem dirichletZeroCount_le_uniformRow
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) {T : ℝ} (hT : 0 ≤ T) :
    (dirichletZeroCount chi 0 T : ℝ) ≤
      (1 + 2 * T) *
        (2 * (1 + 1989 * Real.log ((q : ℝ) * (T + 4))) *
          (harmonic (⌊2 * T⌋₊ + 1) : ℝ)) := by
  classical
  let S := zeroSupport chi 0 T
  let H := 2 * (1 + 1989 * Real.log ((q : ℝ) * (T + 4))) *
    (harmonic (⌊2 * T⌋₊ + 1) : ℝ)
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hscale : 1 ≤ (q : ℝ) * (T + 4) := by nlinarith
  have hlog : 0 ≤ Real.log ((q : ℝ) * (T + 4)) :=
    Real.log_nonneg hscale
  have hharm : 0 ≤ (harmonic (⌊2 * T⌋₊ + 1) : ℝ) := by
    norm_cast
    unfold harmonic
    positivity
  have hH : 0 ≤ H := by
    dsimp [H]
    exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hharm
  by_cases hS : S.Nonempty
  · obtain ⟨rho0, hrho0⟩ := hS
    have hrow :
        (∑ rho ∈ S, (zeroMultiplicity chi 0 T rho : ℝ) /
          (1 + |rho.im - rho0.im|)) ≤ H := by
      apply MAPHarmonicRowGrouping.finite_reciprocal_row_le_harmonic
        S (fun rho => (zeroMultiplicity chi 0 T rho : ℝ))
        (fun rho => rho.im) hT
      · have : 0 ≤ 1 + 1989 * Real.log ((q : ℝ) * (T + 4)) := by positivity
        exact this
      · intro rho hrho
        positivity
      · intro rho hrho
        exact zeroSupport_im_abs_le chi hrho
      · intro a
        by_cases hchi : chi = 1
        · have hp :=
            MAPPrincipalFullStripA5Source.principal_globalUnitWindowMass_le_uniform
              1683 (by norm_num) principalA5_1683 chi hprim hchi hT a
          exact hp.trans (by nlinarith)
        · have hnp :=
            MAPAPZeroFieldEnergy28Grouping.globalUnitWindowMass_le_uniform
              chi hprim hchi hT a
          exact hnp.trans (by nlinarith)
      · exact hrho0
    have hden : ∀ rho ∈ S, 1 + |rho.im - rho0.im| ≤ 1 + 2 * T := by
      intro rho hrho
      have hrhoT := zeroSupport_im_abs_le chi hrho
      have hrho0T := zeroSupport_im_abs_le chi hrho0
      have hgap : |rho.im - rho0.im| ≤ 2 * T := by
        calc
          |rho.im - rho0.im| ≤ |rho.im| + |rho0.im| := abs_sub _ _
          _ ≤ T + T := add_le_add hrhoT hrho0T
          _ = 2 * T := by ring
      linarith
    unfold dirichletZeroCount
    push_cast
    change (∑ rho ∈ S, (zeroMultiplicity chi 0 T rho : ℝ)) ≤ _
    calc
      (∑ rho ∈ S, (zeroMultiplicity chi 0 T rho : ℝ)) =
          ∑ rho ∈ S,
            ((zeroMultiplicity chi 0 T rho : ℝ) /
              (1 + |rho.im - rho0.im|)) *
                (1 + |rho.im - rho0.im|) := by
        apply Finset.sum_congr rfl
        intro rho hrho
        field_simp
      _ ≤ ∑ rho ∈ S,
          ((zeroMultiplicity chi 0 T rho : ℝ) /
            (1 + |rho.im - rho0.im|)) * (1 + 2 * T) := by
        apply Finset.sum_le_sum
        intro rho hrho
        apply mul_le_mul_of_nonneg_left (hden rho hrho)
        positivity
      _ = (∑ rho ∈ S,
          (zeroMultiplicity chi 0 T rho : ℝ) /
            (1 + |rho.im - rho0.im|)) * (1 + 2 * T) := by
        rw [Finset.sum_mul]
      _ ≤ H * (1 + 2 * T) := by
        apply mul_le_mul_of_nonneg_right hrow
        linarith
      _ = (1 + 2 * T) * H := by ring
  · have hSempt : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    unfold dirichletZeroCount
    push_cast
    change (∑ rho ∈ S, (zeroMultiplicity chi 0 T rho : ℝ)) ≤
      (1 + 2 * T) * H
    rw [show (∑ rho ∈ S, (zeroMultiplicity chi 0 T rho : ℝ)) = 0 by
      simp [S, hSempt]]
    exact mul_nonneg (by linarith) hH

private theorem harmonic_nonneg_real (n : ℕ) :
    (0 : ℝ) ≤ (harmonic n : ℝ) := by
  norm_cast
  unfold harmonic
  positivity

private theorem zeroHeight_nonneg (epsilon X : ℝ) (hX : 0 ≤ X) :
    0 ≤ apZeroHeight epsilon X :=
  Real.rpow_nonneg hX _

private theorem zeroHeight_le_X
    {epsilon X : ℝ} (hepsilon : 0 ≤ epsilon) (hX : 1 ≤ X) :
    apZeroHeight epsilon X ≤ X := by
  unfold apZeroHeight
  calc
    Real.rpow X (13 / 15 - epsilon / 2) ≤ Real.rpow X 1 := by
      apply Real.rpow_le_rpow_of_exponent_le hX
      linarith
    _ = X := Real.rpow_one X

/-- Uniform collapse of the certified full-strip row factor on a
polylogarithmic conductor range. -/
theorem uniformRowFactor_le_polylog
    (K : ℝ) (hK : 0 < K) {q Q : ℕ} [NeZero q]
    {epsilon X : ℝ}
    (hqQ : q ≤ Q)
    (hQ : Q ≤ ⌊Real.rpow (Real.log X) K⌋₊)
    (hepsilon : 0 < epsilon)
    (hX : Real.exp 1 ≤ X) :
    2 * (1 + 1989 *
        Real.log ((q : ℝ) * (apZeroHeight epsilon X + 4))) *
        (harmonic (⌊2 * apZeroHeight epsilon X⌋₊ + 1) : ℝ) ≤
      (8 * (1 + 1989 * (K + 5))) * (Real.log X) ^ 2 := by
  let L := Real.log X
  let T := apZeroHeight epsilon X
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hXone : 1 ≤ X := by
    have : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    linarith
  have hX0 : 0 ≤ X := zero_le_one.trans hXone
  have hL : 1 ≤ L := by
    dsimp [L]
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hX
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hLX : L ≤ X := by
    have h := Real.log_le_sub_one_of_pos hXpos
    dsimp [L]
    linarith
  have hQreal : (Q : ℝ) ≤ Real.rpow L K := by
    have hQcast : (Q : ℝ) ≤ (⌊Real.rpow L K⌋₊ : ℕ) := by
      exact_mod_cast hQ
    exact hQcast.trans (Nat.floor_le (Real.rpow_nonneg hL0 _))
  have hqcast : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hqreal : (q : ℝ) ≤ Real.rpow L K := hqcast.trans hQreal
  have hLKXK : Real.rpow L K ≤ Real.rpow X K :=
    Real.rpow_le_rpow hL0 hLX hK.le
  have hqXK : (q : ℝ) ≤ Real.rpow X K := hqreal.trans hLKXK
  have hT0 : 0 ≤ T := zeroHeight_nonneg epsilon X hX0
  have hTX : T ≤ X := zeroHeight_le_X hepsilon.le hXone
  have hT4 : T + 4 ≤ 5 * X := by nlinarith
  have hscalePos : 0 < (q : ℝ) * (T + 4) := by
    exact mul_pos (by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q)))
      (by linarith)
  have hscaleUpper : (q : ℝ) * (T + 4) ≤
      5 * Real.rpow X (K + 1) := by
    have hone : Real.rpow X 1 = X := Real.rpow_one X
    have hadd : Real.rpow X (K + 1) =
        Real.rpow X K * Real.rpow X 1 :=
      Real.rpow_add hXpos K 1
    calc
      (q : ℝ) * (T + 4) ≤ Real.rpow X K * (5 * X) :=
        mul_le_mul hqXK hT4 (by linarith) (Real.rpow_nonneg hX0 _)
      _ = 5 * Real.rpow X (K + 1) := by
        calc
          Real.rpow X K * (5 * X) = 5 * (Real.rpow X K * X) := by ring
          _ = 5 * (Real.rpow X K * Real.rpow X 1) := by rw [hone]
          _ = 5 * Real.rpow X (K + 1) := by rw [hadd]
  have hlogscale : Real.log ((q : ℝ) * (T + 4)) ≤
      (K + 5) * L := by
    have hpowPos : 0 < Real.rpow X (K + 1) :=
      Real.rpow_pos_of_pos hXpos _
    have hlogpow : Real.log (Real.rpow X (K + 1)) =
        (K + 1) * Real.log X := Real.log_rpow hXpos (K + 1)
    have hlog5 : Real.log 5 ≤ 4 * L := by
      have h5 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
      nlinarith
    calc
      Real.log ((q : ℝ) * (T + 4)) ≤
          Real.log (5 * Real.rpow X (K + 1)) :=
        Real.log_le_log hscalePos hscaleUpper
      _ = Real.log 5 + (K + 1) * Real.log X := by
        rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) hpowPos.ne']
        congr 1
      _ ≤ (K + 5) * L := by
        dsimp [L] at hlog5 ⊢
        nlinarith
  have hnCast : ((⌊2 * T⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * X := by
    have hfloor : (⌊2 * T⌋₊ : ℝ) ≤ 2 * T :=
      Nat.floor_le (by positivity)
    norm_num at hfloor ⊢
    nlinarith
  have hnPos : (0 : ℝ) < (⌊2 * T⌋₊ + 1 : ℕ) := by positivity
  have hlogn : Real.log ((⌊2 * T⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * L := by
    have hlog := Real.log_le_log hnPos hnCast
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hXpos.ne'] at hlog
    have hlog3 : Real.log 3 ≤ 2 * L := by
      have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      nlinarith
    dsimp [L] at hlog ⊢
    nlinarith
  have hharm0 := harmonic_nonneg_real (⌊2 * T⌋₊ + 1)
  have hharm : (harmonic (⌊2 * T⌋₊ + 1) : ℝ) ≤ 4 * L := by
    have hh := harmonic_le_one_add_log (⌊2 * T⌋₊ + 1)
    exact hh.trans (by nlinarith)
  have hcoef : 1 + 1989 * Real.log ((q : ℝ) * (T + 4)) ≤
      (1 + 1989 * (K + 5)) * L := by
    calc
      1 + 1989 * Real.log ((q : ℝ) * (T + 4)) ≤
          1 + 1989 * ((K + 5) * L) := by gcongr
      _ ≤ (1 + 1989 * (K + 5)) * L := by nlinarith
  have hbigcoef : 0 ≤ 1 + 1989 * (K + 5) := by nlinarith
  have hBL0 : 0 ≤ (1 + 1989 * (K + 5)) * L :=
    mul_nonneg hbigcoef hL0
  calc
    2 * (1 + 1989 * Real.log ((q : ℝ) * (T + 4))) *
        (harmonic (⌊2 * T⌋₊ + 1) : ℝ) ≤
      2 * ((1 + 1989 * (K + 5)) * L) *
        (harmonic (⌊2 * T⌋₊ + 1) : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcoef (by norm_num)) hharm0
    _ ≤ 2 * ((1 + 1989 * (K + 5)) * L) * (4 * L) := by
          exact mul_le_mul_of_nonneg_left hharm
            (mul_nonneg (by norm_num) hBL0)
    _ = (8 * (1 + 1989 * (K + 5))) * L ^ 2 := by ring

/-- The certified local count gives the elementary global estimate needed for
the low strip, uniformly for primitive characters at polylogarithmic level. -/
theorem dirichletZeroCount_le_polylogHeight
    (K : ℝ) (hK : 0 < K) {q Q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hprim : chi.IsPrimitive)
    {epsilon X : ℝ}
    (hqQ : q ≤ Q)
    (hQ : Q ≤ ⌊Real.rpow (Real.log X) K⌋₊)
    (hepsilon : 0 < epsilon) (hepsilonCap : epsilon ≤ 1 / 10)
    (hX : Real.exp 1 ≤ X) :
    (dirichletZeroCount chi 0 (apZeroHeight epsilon X) : ℝ) ≤
      (24 * (1 + 1989 * (K + 5))) *
        Real.rpow X (tau epsilon) * (Real.log X) ^ 2 := by
  let T := apZeroHeight epsilon X
  let D := 8 * (1 + 1989 * (K + 5))
  have hXone : 1 ≤ X := by
    have : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    linarith
  have htau : 0 ≤ tau epsilon := (tau_pos hepsilonCap).le
  have hTone : 1 ≤ T := by
    dsimp [T, apZeroHeight]
    exact Real.one_le_rpow hXone htau
  have hT : 0 ≤ T := zero_le_one.trans hTone
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hL2 : 0 ≤ (Real.log X) ^ 2 := sq_nonneg _
  have hrow := dirichletZeroCount_le_uniformRow chi hprim hT
  have hpoly := uniformRowFactor_le_polylog K hK hqQ hQ hepsilon hX
  change (dirichletZeroCount chi 0 T : ℝ) ≤ _
  calc
    (dirichletZeroCount chi 0 T : ℝ) ≤
        (1 + 2 * T) *
          (2 * (1 + 1989 * Real.log ((q : ℝ) * (T + 4))) *
            (harmonic (⌊2 * T⌋₊ + 1) : ℝ)) := hrow
    _ ≤ (1 + 2 * T) * (D * (Real.log X) ^ 2) := by
      apply mul_le_mul_of_nonneg_left hpoly
      linarith
    _ ≤ (3 * T) * (D * (Real.log X) ^ 2) := by
      apply mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hD hL2)
    _ = (3 * D) * T * (Real.log X) ^ 2 := by ring
    _ = (24 * (1 + 1989 * (K + 5))) *
        Real.rpow X (tau epsilon) * (Real.log X) ^ 2 := by
      have hTeq : T = Real.rpow X (tau epsilon) := by
        rfl
      rw [hTeq]
      dsimp [D]
      ring

/-- Exact family count obtained from the preceding fixed-primitive estimate;
the `Q^2` factor is precisely the ambient-character/inducer repetition cost. -/
theorem polylogFamilyZeroCount_zero_le_polylogHeight
    (K : ℝ) (hK : 0 < K) (Q : ℕ)
    {epsilon X : ℝ}
    (hQ : Q ≤ ⌊Real.rpow (Real.log X) K⌋₊)
    (hepsilon : 0 < epsilon) (hepsilonCap : epsilon ≤ 1 / 10)
    (hX : Real.exp 1 ≤ X) :
    (polylogFamilyZeroCount Q 0 (apZeroHeight epsilon X) : ℝ) ≤
      (Q : ℝ) ^ 2 *
        ((24 * (1 + 1989 * (K + 5))) *
          Real.rpow X (tau epsilon) * (Real.log X) ^ 2) := by
  let B := (24 * (1 + 1989 * (K + 5))) *
    Real.rpow X (tau epsilon) * (Real.log X) ^ 2
  have hB : 0 ≤ B := by
    dsimp [B]
    have hcoef : 0 ≤ 24 * (1 + 1989 * (K + 5)) := by nlinarith
    have hX0 : 0 ≤ X := by
      exact (Real.exp_pos 1).le.trans hX
    exact mul_nonneg
      (mul_nonneg hcoef (Real.rpow_nonneg hX0 _))
      (sq_nonneg _)
  apply fixed_primitive_bound_to_family hB
  intro q _inst chi hprim hqQ
  change (dirichletZeroCount chi 0 (apZeroHeight epsilon X) : ℝ) ≤ B
  exact dirichletZeroCount_le_polylogHeight
    K hK chi hprim hqQ hQ hepsilon hepsilonCap hX

/-- The scaffold's ambient-character low mass is exactly the low-beta mass of
the primitive inducer used by the certified low-strip lemma. -/
theorem primitiveLowRangeMass_eq_actualLowBetaMass
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (epsilon X T : ℝ) :
    primitiveLowRangeMass chi epsilon X T =
      letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
      actualLowBetaMass chi.primitiveCharacter X T epsilon := by
  rfl

/-- Exact family aggregation before any growth estimate: every low-strip
weight is bounded at the endpoint and the remaining sum is literally
`polylogFamilyZeroCount`, including repeated primitive inducers. -/
theorem apLowRangeMass_le_familyCount_weight
    (Q : ℕ) {epsilon X T : ℝ} (hX : 1 ≤ X) :
    apLowRangeMass Q epsilon X T ≤
      (polylogFamilyZeroCount Q 0 T : ℝ) *
        Real.rpow X (-1 + 2 * paperDelta0 epsilon) := by
  classical
  let W := Real.rpow X (-1 + 2 * paperDelta0 epsilon)
  unfold apLowRangeMass polylogFamilyZeroCount
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro q hq
  have hq0 : q ≠ 0 := by
    have hqpos := (Finset.mem_Icc.mp hq).1
    omega
  letI : NeZero q := ⟨hq0⟩
  simp only [hq0, dite_false, zeroCountAtLevel_eq]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro chi _hchi
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  rw [primitiveLowRangeMass_eq_actualLowBetaMass]
  exact actualLowBetaMass_le_fullCount chi.primitiveCharacter hX

/-- The complete low-strip estimate before the final polylogarithmic trade.
All dependence on the ambient family is visible in the literal `Q^2` factor. -/
theorem apLowRangeMass_le_polylogEnvelope
    (K : ℝ) (hK : 0 < K) (Q : ℕ)
    {epsilon X : ℝ}
    (hQ : Q ≤ ⌊Real.rpow (Real.log X) K⌋₊)
    (hepsilon : 0 < epsilon) (hepsilonCap : epsilon ≤ 1 / 10)
    (hX : Real.exp 1 ≤ X) :
    apLowRangeMass Q epsilon X (apZeroHeight epsilon X) ≤
      (24 * (1 + 1989 * (K + 5))) *
        ((Q : ℝ) ^ 2 * (Real.log X) ^ 2) *
          Real.rpow X (-(2 / 15 : ℝ)) := by
  let C0 : ℝ := 24 * (1 + 1989 * (K + 5))
  let T := apZeroHeight epsilon X
  let W := Real.rpow X (-1 + 2 * paperDelta0 epsilon)
  have hXone : 1 ≤ X := by
    have : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    linarith
  have hX0 : 0 ≤ X := zero_le_one.trans hXone
  have hXpos : 0 < X := zero_lt_one.trans_le hXone
  have hW : 0 ≤ W := Real.rpow_nonneg hX0 _
  have hC0 : 0 ≤ C0 := by dsimp [C0]; nlinarith
  have hfamily := polylogFamilyZeroCount_zero_le_polylogHeight
    K hK Q hQ hepsilon hepsilonCap hX
  have hmass := apLowRangeMass_le_familyCount_weight
    Q (epsilon := epsilon) (X := X) (T := T) hXone
  have hinsert := hmass.trans
    (mul_le_mul_of_nonneg_right hfamily hW)
  have hexp := low_beta_exponent_le_neg_two_fifteenths hepsilon.le
  have hpower : Real.rpow X
      (tau epsilon - 1 + 2 * paperDelta0 epsilon) ≤
      Real.rpow X (-(2 / 15 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hXone hexp
  change apLowRangeMass Q epsilon X T ≤ _
  calc
    apLowRangeMass Q epsilon X T ≤
        ((Q : ℝ) ^ 2 *
          (C0 * Real.rpow X (tau epsilon) * (Real.log X) ^ 2)) * W := by
      simpa only [C0, T, W] using hinsert
    _ = C0 * ((Q : ℝ) ^ 2 * (Real.log X) ^ 2) *
        Real.rpow X (tau epsilon - 1 + 2 * paperDelta0 epsilon) := by
      dsimp [W]
      have hrpow :
          Real.rpow X (tau epsilon - 1 + 2 * paperDelta0 epsilon) =
            Real.rpow X (tau epsilon) *
              Real.rpow X (-1 + 2 * paperDelta0 epsilon) := by
        rw [show tau epsilon - 1 + 2 * paperDelta0 epsilon =
          tau epsilon + (-1 + 2 * paperDelta0 epsilon) by ring]
        exact Real.rpow_add hXpos _ _
      change (Q : ℝ) ^ 2 *
          (C0 * Real.rpow X (tau epsilon) * (Real.log X) ^ 2) *
            Real.rpow X (-1 + 2 * paperDelta0 epsilon) =
        C0 * ((Q : ℝ) ^ 2 * (Real.log X) ^ 2) *
          Real.rpow X (tau epsilon - 1 + 2 * paperDelta0 epsilon)
      rw [hrpow]
      ring
    _ ≤ C0 * ((Q : ℝ) ^ 2 * (Real.log X) ^ 2) *
        Real.rpow X (-(2 / 15 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hpower
      exact mul_nonneg hC0 (mul_nonneg (sq_nonneg _) (sq_nonneg _))

private theorem eventually_log_pow_le_rpow_mul_negative
    (A : ℝ) (n : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ X : ℝ in Filter.atTop,
      (Real.log X) ^ n ≤
        Real.rpow X eta * Real.rpow (Real.log X) (-A) := by
  have hpoly := SupportBoundaryQuantitative.polylog_absorption
    (A + n) eta heta
  filter_upwards [hpoly, Filter.eventually_ge_atTop (Real.exp 1)] with X hpoly hX
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXpos).2 hX
  have hlogpos : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hneg : 0 ≤ Real.rpow (Real.log X) (-A) :=
    Real.rpow_nonneg hlogpos.le _
  have hmul := mul_le_mul_of_nonneg_right hpoly hneg
  have hnat : Real.rpow (Real.log X) (n : ℝ) = (Real.log X) ^ n :=
    Real.rpow_natCast (Real.log X) n
  have hadd : Real.rpow (Real.log X) ((A + n) + (-A)) =
      Real.rpow (Real.log X) (A + n) *
        Real.rpow (Real.log X) (-A) :=
    Real.rpow_add hlogpos _ _
  calc
    (Real.log X) ^ n = Real.rpow (Real.log X) (n : ℝ) := hnat.symm
    _ = Real.rpow (Real.log X) ((A + n) + (-A)) := by
      congr 1
      ring
    _ = Real.rpow (Real.log X) (A + n) *
          Real.rpow (Real.log X) (-A) := hadd
    _ ≤ Real.rpow X eta * Real.rpow (Real.log X) (-A) := hmul

/-- Premise-free inhabitant of the exact low-range hypothesis consumed by
`apWeightedZeroMassLogSaving_of_range_bounds`. -/
theorem apLowRangeMass_logSaving :
    ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
          apLowRangeMass ⌊Real.rpow (Real.log X) K⌋₊ epsilon X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A) := by
  intro K A epsilon hK hA hepsilon hepsilonCap
  let m : ℕ := ⌈2 * K⌉₊
  let n : ℕ := m + 2
  let C : ℝ := 24 * (1 + 1989 * (K + 5))
  have hC : 0 < C := by dsimp [C]; nlinarith
  have htrade := eventually_log_pow_le_rpow_mul_negative
    A n (eta := 1 / 30) (by norm_num)
  have hevent : ∀ᶠ X : ℝ in Filter.atTop,
      Real.exp 1 ≤ X ∧
        (Real.log X) ^ n ≤
          Real.rpow X (1 / 30 : ℝ) *
            Real.rpow (Real.log X) (-A) := by
    filter_upwards [Filter.eventually_ge_atTop (Real.exp 1), htrade] with X hX ht
    exact ⟨hX, ht⟩
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.1 hevent
  have hX0exp : Real.exp 1 ≤ X0 := (hX0 X0 le_rfl).1
  refine ⟨C, X0, hC, ?_, ?_⟩
  · exact Real.exp_one_gt_two.le.trans hX0exp
  intro X hXX0
  obtain ⟨hX, htradeX⟩ := hX0 X hXX0
  let L := Real.log X
  let Q := ⌊Real.rpow L K⌋₊
  have hXone : 1 ≤ X := by
    have : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    linarith
  have hXpos : 0 < X := zero_lt_one.trans_le hXone
  have hL : 1 ≤ L := by
    dsimp [L]
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hX
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hQreal : (Q : ℝ) ≤ Real.rpow L K := by
    dsimp [Q]
    exact Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hL) _)
  have hQnonneg : 0 ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have hbasepow : 0 ≤ Real.rpow L K :=
    Real.rpow_nonneg (zero_le_one.trans hL) _
  have hQsq : (Q : ℝ) ^ 2 ≤ Real.rpow L (2 * K) := by
    have hmul := mul_le_mul hQreal hQreal hQnonneg hbasepow
    have hadd : Real.rpow L (2 * K) =
        Real.rpow L K * Real.rpow L K := by
      rw [show 2 * K = K + K by ring]
      exact Real.rpow_add hLpos _ _
    calc
      (Q : ℝ) ^ 2 = (Q : ℝ) * Q := by ring
      _ ≤ Real.rpow L K * Real.rpow L K := hmul
      _ = Real.rpow L (2 * K) := hadd.symm
  have hceil : (2 * K : ℝ) ≤ (m : ℕ) := by
    dsimp [m]
    exact Nat.le_ceil (2 * K)
  have hrpowceil : Real.rpow L (2 * K) ≤ Real.rpow L (m : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL hceil
  have hnatpow : Real.rpow L (m : ℝ) = L ^ m :=
    Real.rpow_natCast L m
  have hpolyFamily : (Q : ℝ) ^ 2 * L ^ 2 ≤ L ^ n := by
    calc
      (Q : ℝ) ^ 2 * L ^ 2 ≤ Real.rpow L (2 * K) * L ^ 2 := by
        exact mul_le_mul_of_nonneg_right hQsq (sq_nonneg L)
      _ ≤ Real.rpow L (m : ℝ) * L ^ 2 := by
        exact mul_le_mul_of_nonneg_right hrpowceil (sq_nonneg L)
      _ = L ^ m * L ^ 2 := by rw [hnatpow]
      _ = L ^ n := by
        dsimp [n]
        rw [pow_add]
  have henv := apLowRangeMass_le_polylogEnvelope
    K hK Q (le_rfl) hepsilon hepsilonCap hX
  have hpowneg : Real.rpow X (-(2 / 15 : ℝ)) ≥ 0 :=
    Real.rpow_nonneg (zero_le_one.trans hXone) _
  have htradeL : L ^ n ≤
      Real.rpow X (1 / 30 : ℝ) * Real.rpow L (-A) := by
    simpa only [L] using htradeX
  have hxcombine :
      Real.rpow X (1 / 30 : ℝ) * Real.rpow X (-(2 / 15 : ℝ)) =
        Real.rpow X (-(1 / 10 : ℝ)) := by
    have hadd := Real.rpow_add hXpos (1 / 30 : ℝ) (-(2 / 15 : ℝ))
    rw [show (1 / 30 : ℝ) + -(2 / 15 : ℝ) = -(1 / 10 : ℝ) by norm_num] at hadd
    exact hadd.symm
  have hxdecay : Real.rpow X (-(1 / 10 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hXone (by norm_num)
  have hlogneg : 0 ≤ Real.rpow L (-A) :=
    Real.rpow_nonneg (zero_le_one.trans hL) _
  change apLowRangeMass Q epsilon X (apZeroHeight epsilon X) ≤
    C * Real.rpow L (-A)
  calc
    apLowRangeMass Q epsilon X (apZeroHeight epsilon X) ≤
        C * ((Q : ℝ) ^ 2 * L ^ 2) *
          Real.rpow X (-(2 / 15 : ℝ)) := by
      simpa only [C, L] using henv
    _ ≤ C * (L ^ n) * Real.rpow X (-(2 / 15 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpolyFamily hC.le) hpowneg
    _ ≤ C *
        (Real.rpow X (1 / 30 : ℝ) * Real.rpow L (-A)) *
          Real.rpow X (-(2 / 15 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htradeL hC.le) hpowneg
    _ = C * Real.rpow X (-(1 / 10 : ℝ)) * Real.rpow L (-A) := by
      rw [← hxcombine]
      ring
    _ ≤ C * 1 * Real.rpow L (-A) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hxdecay hC.le) hlogneg
    _ = C * Real.rpow L (-A) := by ring

/-- The equation-(2.7) synchronization weld with the now-certified low branch
filled in.  The three remaining parameters are exactly the compact, regular
near-one, and exceptional range statements. -/
theorem apWeightedZeroMassLogSaving_of_remaining_ranges
    (hCompact : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
          apCompactRangeMass ⌊Real.rpow (Real.log X) K⌋₊ epsilon X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A))
    (hRegularNear : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
          apRegularNearOneRangeMass ⌊Real.rpow (Real.log X) K⌋₊ X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A))
    (hExceptional : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
          apExceptionalNearOneRangeMass
              ⌊Real.rpow (Real.log X) K⌋₊ X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A)) :
    APWeightedZeroMassLogSaving :=
  apWeightedZeroMassLogSaving_of_range_bounds
    apLowRangeMass_logSaving hCompact hRegularNear hExceptional


end
end MAPAPLowRangeGlobal

#print axioms MAPAPLowRangeGlobal.dirichletZeroCount_le_uniformRow
#print axioms MAPAPLowRangeGlobal.uniformRowFactor_le_polylog
#print axioms MAPAPLowRangeGlobal.dirichletZeroCount_le_polylogHeight
#print axioms MAPAPLowRangeGlobal.polylogFamilyZeroCount_zero_le_polylogHeight
#print axioms MAPAPLowRangeGlobal.primitiveLowRangeMass_eq_actualLowBetaMass
#print axioms MAPAPLowRangeGlobal.apLowRangeMass_le_familyCount_weight
#print axioms MAPAPLowRangeGlobal.apLowRangeMass_le_polylogEnvelope
#print axioms MAPAPLowRangeGlobal.apLowRangeMass_logSaving
#print axioms MAPAPLowRangeGlobal.apWeightedZeroMassLogSaving_of_remaining_ranges
