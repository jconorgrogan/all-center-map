import APLowRangeGlobal
import SiegelExceptionalUnconditional

/-!
# Unconditional AP exceptional-real-zero range

The exceptional range is supported on the real axis.  Its multiplicity budget
is therefore the divisor count at literal height zero, rather than the full
Perron height.  This avoids the artificial `X ^ tau` loss from a full-height
zero count.
-/

namespace MAPAPExceptionalUnconditional

open scoped BigOperators
open DirichletZeros MAPAPWeightedZeroMassIntegration
open CGLPolylogBypass MAPAPLowRangeGlobal MAPAPZeroDensityCert

noncomputable section

/-- A real-axis exceptional sub-sum in an arbitrary Perron rectangle is
bounded by the height-zero divisor count times a common pointwise weight. -/
theorem primitiveExceptionalNearOneRangeMass_le_zeroHeightCount_mul
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X T W : ℝ} (hT : 0 ≤ T) (hW : 0 ≤ W)
    (hpoint : ∀ beta : ℝ,
      4 / 5 < beta →
      letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
      let psi := chi.primitiveCharacter
      psi ≠ 1 → psi ^ 2 = 1 →
      DirichletCharacter.LFunction psi beta = 0 →
        Real.rpow X (2 * (beta - 1)) ≤ W) :
    primitiveExceptionalNearOneRangeMass chi X T ≤
      letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
      (dirichletZeroCount chi.primitiveCharacter 0 0 : ℝ) * W := by
  classical
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  let S := (zeroSupport psi 0 T).filter (fun rho =>
      4 / 5 < rho.re ∧ psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0)
  have hsupport : S ⊆ zeroSupport psi 0 0 := by
    intro rho hrho
    have hfull : rho ∈ zeroSupport psi 0 T := (Finset.mem_filter.mp hrho).1
    have helig := (Finset.mem_filter.mp hrho).2
    have hfullRect :=
      PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
        psi 0 T hfull
    have hzero : regularizedLFunction psi rho = 0 :=
      regularizedLFunction_eq_zero_of_mem_zeroSupport psi 0 T hfull
    have hrect0 : rho ∈ zeroRectangle 0 0 := by
      rw [zeroRectangle, Complex.mem_reProdIm]
      constructor
      · exact hfullRect.1
      · simpa [helig.2.2.2]
    exact (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
      psi 0 0 hrect0).mpr hzero
  have hmult :
      (∑ rho ∈ S, zeroMultiplicity psi 0 T rho) ≤
        dirichletZeroCount psi 0 0 := by
    have hrewrite :
        (∑ rho ∈ S, zeroMultiplicity psi 0 T rho) =
          ∑ rho ∈ S, zeroMultiplicity psi 0 0 rho := by
      apply Finset.sum_congr rfl
      intro rho hrho
      have hfull : rho ∈ zeroSupport psi 0 T := (Finset.mem_filter.mp hrho).1
      have hzero0 : rho ∈ zeroSupport psi 0 0 := hsupport hrho
      exact MAPMellinDetectorLeaf.zeroMultiplicity_eq_of_mem_rectangles psi
        (PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
          psi 0 T hfull)
        (PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
          psi 0 0 hzero0)
    rw [hrewrite]
    unfold dirichletZeroCount
    exact Finset.sum_le_sum_of_subset_of_nonneg hsupport
      (fun _ _ _ => Nat.zero_le _)
  unfold primitiveExceptionalNearOneRangeMass
  change (∑ rho ∈ S,
      (zeroMultiplicity psi 0 T rho : ℝ) *
        Real.rpow X (2 * (rho.re - 1))) ≤ _
  calc
    (∑ rho ∈ S,
        (zeroMultiplicity psi 0 T rho : ℝ) *
          Real.rpow X (2 * (rho.re - 1))) ≤
        ∑ rho ∈ S, (zeroMultiplicity psi 0 T rho : ℝ) * W := by
      apply Finset.sum_le_sum
      intro rho hrho
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have hfull : rho ∈ zeroSupport psi 0 T := (Finset.mem_filter.mp hrho).1
      have helig := (Finset.mem_filter.mp hrho).2
      have hregzero : regularizedLFunction psi rho = 0 :=
        regularizedLFunction_eq_zero_of_mem_zeroSupport psi 0 T hfull
      have hLzeroComplex : DirichletCharacter.LFunction psi rho = 0 := by
        simpa [regularizedLFunction, helig.2.1] using hregzero
      have hrho : rho = (rho.re : ℂ) := by
        apply Complex.ext
        · simp
        · simpa using helig.2.2.2
      apply hpoint rho.re helig.1 helig.2.1 helig.2.2.1
      rw [hrho] at hLzeroComplex
      exact hLzeroComplex
    _ = ((∑ rho ∈ S, zeroMultiplicity psi 0 T rho : ℕ) : ℝ) * W := by
      push_cast
      rw [Finset.sum_mul]
    _ ≤ (dirichletZeroCount psi 0 0 : ℝ) * W := by
      apply mul_le_mul_of_nonneg_right _ hW
      exact_mod_cast hmult

/-- Exact ambient-family aggregation of the real-axis exceptional range. -/
theorem apExceptionalNearOneRangeMass_le_zeroHeightFamilyCount_mul
    {Q : ℕ} {X T W : ℝ} (hT : 0 ≤ T) (hW : 0 ≤ W)
    (hpoint : ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q) (beta : ℝ),
      q ≤ Q → chi.IsPrimitive → chi ≠ 1 → chi ^ 2 = 1 →
      DirichletCharacter.LFunction chi beta = 0 →
        Real.rpow X (2 * (beta - 1)) ≤ W) :
    apExceptionalNearOneRangeMass Q X T ≤
      (polylogFamilyZeroCount Q 0 0 : ℝ) * W := by
  classical
  unfold apExceptionalNearOneRangeMass polylogFamilyZeroCount
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro q hq
  split_ifs with hq0
  · simp [zeroCountAtLevel, hq0, hW]
  · letI : NeZero q := ⟨hq0⟩
    simp only [zeroCountAtLevel, hq0, dite_false]
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro chi _hchi
    letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    apply primitiveExceptionalNearOneRangeMass_le_zeroHeightCount_mul
      chi hT hW
    intro beta hbeta
    dsimp
    intro hne hreal hzero
    exact hpoint chi.conductor chi.primitiveCharacter beta
      ((ZeroDensityInterface.conductor_le_level chi).trans (Finset.mem_Icc.mp hq).2)
      chi.primitiveCharacter_isPrimitive hne hreal hzero


/-- The full real-axis primitive-inducer family has only `Q^2 log Q`
multiplicity.  This is the certified A.5 row estimate at literal height zero. -/
theorem polylogFamilyZeroCount_zero_zero_le
    (Q : ℕ) (hQ : 1 ≤ Q) :
    (polylogFamilyZeroCount Q 0 0 : ℝ) ≤
      (Q : ℝ) ^ 2 *
        (2 * (1 + 1989 * Real.log (4 * (Q : ℝ)))) := by
  let B : ℝ := 2 * (1 + 1989 * Real.log (4 * (Q : ℝ)))
  have hscale : 1 ≤ 4 * (Q : ℝ) := by
    have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    nlinarith
  have hB : 0 ≤ B := by
    dsimp [B]
    have := Real.log_nonneg hscale
    positivity
  apply fixed_primitive_bound_to_family hB
  intro q _inst chi hprim hqQ
  have hrow := dirichletZeroCount_le_uniformRow chi hprim
    (T := 0) (le_rfl : (0 : ℝ) ≤ 0)
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast NeZero.pos q
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ)
  have hscaleq : (0 : ℝ) < (q : ℝ) * (0 + 4) := by positivity
  have hscalele : (q : ℝ) * (0 + 4) ≤ 4 * (Q : ℝ) := by
    have hqQr : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    nlinarith
  have hlog := Real.log_le_log hscaleq hscalele
  dsimp [B]
  norm_num [harmonic] at hrow ⊢
  have hlog' : Real.log ((q : ℝ) * 4) ≤
      Real.log (4 * (Q : ℝ)) := by
    simpa [mul_comm] using hlog
  exact hrow.trans (by nlinarith)


/-- On the paper's polylogarithmic conductor range, the literal height-zero
family divisor count is itself polylogarithmic. -/
theorem polylogFamilyZeroCount_zero_zero_le_polylog
    {K X : ℝ} (hK : 0 < K) (hX : Real.exp 1 ≤ X) :
    let Q := ⌊Real.rpow (Real.log X) K⌋₊
    (polylogFamilyZeroCount Q 0 0 : ℝ) ≤
      (2 * (1 + 1989 * (K + 3))) *
        Real.rpow (Real.log X) (2 * K + 1) := by
  let L := Real.log X
  let Q := ⌊Real.rpow L K⌋₊
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hL : 1 ≤ L := by
    dsimp [L]
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hX
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hLKone : 1 ≤ Real.rpow L K := Real.one_le_rpow hL hK.le
  have hQone : 1 ≤ Q := by
    dsimp [Q]
    exact Nat.le_floor (by simpa using hLKone)
  have hQreal : (Q : ℝ) ≤ Real.rpow L K := by
    dsimp [Q]
    exact Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hL) _)
  have hLX : L ≤ X := by
    have := Real.log_le_sub_one_of_pos hXpos
    linarith
  have hLXpow : Real.rpow L K ≤ Real.rpow X K :=
    Real.rpow_le_rpow (zero_le_one.trans hL) hLX hK.le
  have hQXK : (Q : ℝ) ≤ Real.rpow X K := hQreal.trans hLXpow
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQone)
  have hscalePos : 0 < 4 * (Q : ℝ) := by positivity
  have hscaleUpper : 4 * (Q : ℝ) ≤ 4 * Real.rpow X K := by
    gcongr
  have hlogpow : Real.log (Real.rpow X K) = K * Real.log X :=
    Real.log_rpow hXpos K
  have hlogscale : Real.log (4 * (Q : ℝ)) ≤ (K + 3) * L := by
    calc
      Real.log (4 * (Q : ℝ)) ≤ Real.log (4 * Real.rpow X K) :=
        Real.log_le_log hscalePos hscaleUpper
      _ = Real.log 4 + Real.log (Real.rpow X K) :=
        Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
          (Real.rpow_pos_of_pos hXpos K).ne'
      _ = Real.log 4 + K * Real.log X := by rw [hlogpow]
      _ ≤ (K + 3) * L := by
        have hlog4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
        dsimp [L]
        nlinarith
  have hcoef :
      2 * (1 + 1989 * Real.log (4 * (Q : ℝ))) ≤
        (2 * (1 + 1989 * (K + 3))) * L := by
    have hbig : 0 ≤ 1 + 1989 * (K + 3) := by nlinarith
    calc
      2 * (1 + 1989 * Real.log (4 * (Q : ℝ))) ≤
          2 * (1 + 1989 * ((K + 3) * L)) := by gcongr
      _ ≤ (2 * (1 + 1989 * (K + 3))) * L := by nlinarith
  have hcount := polylogFamilyZeroCount_zero_zero_le Q hQone
  have hQsq : (Q : ℝ) ^ 2 ≤ Real.rpow L (2 * K) := by
    have hmul := mul_le_mul hQreal hQreal (Nat.cast_nonneg Q)
      (Real.rpow_nonneg (zero_le_one.trans hL) K)
    have hadd : Real.rpow L (2 * K) =
        Real.rpow L K * Real.rpow L K := by
      rw [show 2 * K = K + K by ring]
      exact Real.rpow_add hLpos K K
    calc
      (Q : ℝ) ^ 2 = (Q : ℝ) * Q := by ring
      _ ≤ Real.rpow L K * Real.rpow L K := hmul
      _ = Real.rpow L (2 * K) := hadd.symm
  have hcoefNonneg :
      0 ≤ 2 * (1 + 1989 * Real.log (4 * (Q : ℝ))) := by
    have hscaleOne : 1 ≤ 4 * (Q : ℝ) := by
      have hQoneReal : (1 : ℝ) ≤ Q := by exact_mod_cast hQone
      nlinarith
    have : 0 ≤ Real.log (4 * (Q : ℝ)) :=
      Real.log_nonneg hscaleOne
    positivity
  have hbigNonneg : 0 ≤ 2 * (1 + 1989 * (K + 3)) := by nlinarith
  change (polylogFamilyZeroCount Q 0 0 : ℝ) ≤ _
  calc
    (polylogFamilyZeroCount Q 0 0 : ℝ) ≤
        (Q : ℝ) ^ 2 *
          (2 * (1 + 1989 * Real.log (4 * (Q : ℝ)))) := hcount
    _ ≤ Real.rpow L (2 * K) *
          ((2 * (1 + 1989 * (K + 3))) * L) :=
      mul_le_mul hQsq hcoef hcoefNonneg
        (Real.rpow_nonneg (zero_le_one.trans hL) (2 * K))
    _ = (2 * (1 + 1989 * (K + 3))) *
          Real.rpow L (2 * K + 1) := by
      have hadd := Real.rpow_add hLpos (2 * K) 1
      rw [Real.rpow_one] at hadd
      calc
        Real.rpow L (2 * K) *
              (2 * (1 + 1989 * (K + 3)) * L) =
            (2 * (1 + 1989 * (K + 3))) *
              (Real.rpow L (2 * K) * L) := by ring
        _ = (2 * (1 + 1989 * (K + 3))) *
              Real.rpow L (2 * K + 1) := by
          congr 1
          exact hadd.symm


/-- The exceptional-real-zero hypothesis of the equation-(2.7) range weld is
an unconditional theorem.  All ambient-character repetition and analytic
multiplicity are paid by the height-zero `Q^2 log Q` divisor count. -/
theorem apExceptionalNearOneRangeMass_logSaving :
    ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
          apExceptionalNearOneRangeMass
              ⌊Real.rpow (Real.log X) K⌋₊ X
              (MAPFixedScaleAPZeroRoute.apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A) := by
  intro K A epsilon hK hA hepsilon _hepsilonCap
  let P : ℝ := 2 * K + 1
  let Aprime : ℝ := A + P
  let C : ℝ := 2 * (1 + 1989 * (K + 3))
  have hP : 0 ≤ P := by dsimp [P]; linarith
  have hAprime : 0 < Aprime := by dsimp [Aprime, P]; linarith
  have hC : 0 < C := by dsimp [C]; nlinarith
  obtain ⟨Xs, hXs, hsource⟩ :=
    MAPGoldfeldSiegel.exists_prefactor_mul_exceptionalWeight_le
      hK hAprime (show (0 : ℝ) ≤ 0 by norm_num)
  let X0 := max Xs (Real.exp 1)
  refine ⟨C, X0, hC, ?_, ?_⟩
  · exact hXs.trans (le_max_left _ _)
  intro X hXX0
  have hXXs : Xs ≤ X := (le_max_left Xs (Real.exp 1)).trans hXX0
  have hXexp : Real.exp 1 ≤ X := (le_max_right Xs (Real.exp 1)).trans hXX0
  let L := Real.log X
  let Q := ⌊Real.rpow L K⌋₊
  let T := MAPFixedScaleAPZeroRoute.apZeroHeight epsilon X
  let W := Real.rpow L (-Aprime)
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hXexp
  have hL : 1 ≤ L := by
    dsimp [L]
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hXexp
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hQreal : (Q : ℝ) ≤ Real.rpow L K := by
    dsimp [Q]
    exact Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hL) _)
  have hT : 0 ≤ T := by
    dsimp [T, MAPFixedScaleAPZeroRoute.apZeroHeight]
    exact Real.rpow_nonneg hXpos.le _
  have hW : 0 ≤ W := Real.rpow_nonneg (zero_le_one.trans hL) _
  have hmass : apExceptionalNearOneRangeMass Q X T ≤
      (polylogFamilyZeroCount Q 0 0 : ℝ) * W := by
    apply apExceptionalNearOneRangeMass_le_zeroHeightFamilyCount_mul hT hW
    intro q _inst chi beta hqQ _hprim hne hreal hzero
    have hqQreal : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have hqbound : (q : ℝ) ≤ Real.rpow (Real.log X) K := by
      change (q : ℝ) ≤ Real.rpow L K
      exact hqQreal.trans hQreal
    have hs := hsource X hXXs q chi beta hqbound hne hreal hzero
    change Real.rpow L 0 * Real.rpow X (2 * (beta - 1)) ≤
      Real.rpow L (-Aprime) at hs
    simpa [W] using hs
  have hcount : (polylogFamilyZeroCount Q 0 0 : ℝ) ≤
      C * Real.rpow L P := by
    simpa [Q, L, C, P] using
      (polylogFamilyZeroCount_zero_zero_le_polylog hK hXexp)
  change apExceptionalNearOneRangeMass Q X T ≤
    C * Real.rpow L (-A)
  calc
    apExceptionalNearOneRangeMass Q X T ≤
        (polylogFamilyZeroCount Q 0 0 : ℝ) * W := hmass
    _ ≤ (C * Real.rpow L P) * W :=
      mul_le_mul_of_nonneg_right hcount hW
    _ = C * Real.rpow L (-A) := by
      have hadd := Real.rpow_add hLpos P (-Aprime)
      have hexp : P + -Aprime = -A := by dsimp [Aprime]; ring
      calc
        (C * Real.rpow L P) * W =
            C * (Real.rpow L P * Real.rpow L (-Aprime)) := by
          dsimp [W]
          ring
        _ = C * Real.rpow L (P + -Aprime) := by
          congr 1
          exact hadd.symm
        _ = C * Real.rpow L (-A) := by rw [hexp]


/-- Equation (2.7) after discharging both the certified low strip and the
exceptional-real-zero strip.  Only the compact and regular-near-one analytic
ranges remain as premises. -/
theorem apWeightedZeroMassLogSaving_of_compact_regular
    (hCompact : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
          apCompactRangeMass ⌊Real.rpow (Real.log X) K⌋₊ epsilon X
              (MAPFixedScaleAPZeroRoute.apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A))
    (hRegularNear : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
          apRegularNearOneRangeMass ⌊Real.rpow (Real.log X) K⌋₊ X
              (MAPFixedScaleAPZeroRoute.apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A)) :
    MAPFixedScaleAPZeroRoute.APWeightedZeroMassLogSaving :=
  MAPAPLowRangeGlobal.apWeightedZeroMassLogSaving_of_remaining_ranges
    hCompact hRegularNear apExceptionalNearOneRangeMass_logSaving

end
end MAPAPExceptionalUnconditional

#print axioms MAPAPExceptionalUnconditional.primitiveExceptionalNearOneRangeMass_le_zeroHeightCount_mul
#print axioms MAPAPExceptionalUnconditional.apExceptionalNearOneRangeMass_le_zeroHeightFamilyCount_mul
#print axioms MAPAPExceptionalUnconditional.polylogFamilyZeroCount_zero_zero_le
#print axioms MAPAPExceptionalUnconditional.polylogFamilyZeroCount_zero_zero_le_polylog
#print axioms MAPAPExceptionalUnconditional.apExceptionalNearOneRangeMass_logSaving
#print axioms MAPAPExceptionalUnconditional.apWeightedZeroMassLogSaving_of_compact_regular
