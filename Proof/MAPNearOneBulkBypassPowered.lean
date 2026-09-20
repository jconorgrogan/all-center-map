import BudgetedSelectedPoweredBlockAssembly
import CGLNearFineMeshSourceAdapter

/-! A weaker powered target that remains valid above the old compact cap.
The literal GM three-term estimate, powerCap and inputLoss are retained.
-/
namespace MAPNearOneBulkBypassPowered
open scoped BigOperators
open AppendixTypeIPower CGLProofDAG FixedCharacterPoweredBridge
open BudgetedSelectedPoweredBlockAssembly BudgetedConnectorAnalysis
noncomputable section

def bulkExponent (sigma : ℝ) : ℝ := (30 / 13) * (1 - sigma)

theorem old_power_window_impossible_above_nine_tenths
    {sigma : ℝ} (hsigma : 9 / 10 < sigma) (hsigmaOne : sigma ≤ 1) :
    ¬ ∃ k : ℕ, poweredLengthLower sigma ≤ (k : ℝ) * (1 / 2) ∧
      (k : ℝ) * (1 / 2) ≤ poweredLengthUpper sigma := by
  have hd : 0 < 6 + 10 * sigma := by linarith
  have hL : 1 / 2 < poweredLengthLower sigma := by
    rw [poweredLengthLower, lt_div_iff₀ hd]
    linarith
  have hU : poweredLengthUpper sigma < 1 := by
    rw [poweredLengthUpper, div_lt_iff₀ hd]
    linarith
  rintro ⟨k, hkL, hkU⟩
  by_cases hk : k ≤ 1
  · have hkR : (k : ℝ) ≤ 1 := by exact_mod_cast hk
    linarith
  · have hkR : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    linarith

/-- The widened window retains a bounded integer power for every legal input
length, including the previously obstructed half-length case. -/
theorem exists_bulk_power_bounded_by_powerCap
    {sigma lam kappa : ℝ}
    (hsigma : 4 / 5 ≤ sigma) (hkappa : 0 < kappa)
    (hkl : kappa ≤ lam) (hlam : lam ≤ 1 / 2) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ powerCap kappa ∧
      poweredLengthLower sigma ≤ (k : ℝ) * lam ∧
      (k : ℝ) * lam ≤ 15 / 13 := by
  have hl : 0 < lam := hkappa.trans_le hkl
  have hd : 0 < 6 + 10 * sigma := by linarith
  let L := poweredLengthLower sigma
  have hL : 0 < L := by dsimp [L, poweredLengthLower]; positivity
  have hUL : (3 / 2 : ℝ) * L ≤ 15 / 13 := by
    have hu := poweredLengthUpper_le_global (show 7 / 10 ≤ sigma by linarith)
    convert hu using 1
    unfold L poweredLengthLower poweredLengthUpper
    field_simp
    <;> ring
  have hex : ∃ k : ℕ, 1 ≤ k ∧ L ≤ (k : ℝ) * lam ∧ (k : ℝ) * lam ≤ 15 / 13 := by
    by_cases hlarge : L / 2 ≤ lam
    · refine ⟨2, by omega, ?_, ?_⟩ <;> norm_num <;> linarith
    · let k : ℕ := ⌈L / lam⌉₊
      have hr : 0 < L / lam := div_pos hL hl
      have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.ceil_pos.mpr hr))
      refine ⟨k, hkpos, ?_, ?_⟩
      · have hc := mul_le_mul_of_nonneg_right (Nat.le_ceil (L / lam)) hl.le
        simpa [k, div_mul_cancel₀ _ hl.ne'] using hc
      · have hc := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one hr.le) hl
        have hkc : (k : ℝ) * lam < L + lam := by
          simpa [k, add_mul, div_mul_cancel₀ _ hl.ne'] using hc
        have hsmall : lam < L / 2 := lt_of_not_ge hlarge
        linarith
  obtain ⟨k, hk, hkL, hkU⟩ := hex
  refine ⟨k, hk, ?_, hkL, hkU⟩
  have hkK : (k : ℝ) * kappa ≤ 15 / 13 :=
    (mul_le_mul_of_nonneg_left hkl (Nat.cast_nonneg k)).trans hkU
  have hkdiv : (k : ℝ) ≤ (15 / 13) / kappa := (le_div_iff₀ hkappa).2 hkK
  have hc := hkdiv.trans (Nat.le_ceil ((15 / 13 : ℝ) / kappa))
  exact_mod_cast hc

/-- All three literal Guth--Maynard exponents fit the weaker uniform target.
Above `4/5`, the middle term is already dominated by the quadratic term. -/
theorem bulk_three_GM_exponents
    {sigma mu : ℝ} (hsigma : 4 / 5 ≤ sigma) (hsigmaOne : sigma ≤ 1)
    (hmuLow : poweredLengthLower sigma ≤ mu) (hmuHigh : mu ≤ 15 / 13) :
    2 * mu * (1 - sigma) ≤ bulkExponent sigma ∧
      (18 / 5 - 4 * sigma) * mu ≤ bulkExponent sigma ∧
      1 + (12 / 5 - 4 * sigma) * mu ≤ bulkExponent sigma := by
  have hsigmaSeven : 7 / 10 ≤ sigma := by linarith
  have hd : 0 < 6 + 10 * sigma := by linarith
  have hmu0 : 0 ≤ mu := (show 0 < poweredLengthLower sigma by
    unfold poweredLengthLower; positivity).le.trans hmuLow
  have hone : 0 ≤ 1 - sigma := by linarith
  have hfirst : 2 * mu * (1 - sigma) ≤ bulkExponent sigma := by
    unfold bulkExponent
    nlinarith [mul_le_mul_of_nonneg_right hmuHigh hone]
  have hmiddle : (18 / 5 - 4 * sigma) * mu ≤ 2 * mu * (1 - sigma) := by
    have hx : (8 / 5 - 2 * sigma) * mu ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hmu0
    nlinarith
  have hgm : gmExponent sigma ≤ bulkExponent sigma := by
    exact mul_le_mul_of_nonneg_right (gmCoefficient_le_uniformCoeff hsigmaSeven) hone
  have hthird : 1 + (12 / 5 - 4 * sigma) * mu ≤ gmExponent sigma := by
    have hx := mul_le_mul_of_nonpos_left hmuLow
      (show 12 / 5 - 4 * sigma ≤ 0 by linarith)
    rw [← third_term_at_powered_lower hsigmaSeven]
    linarith
  exact ⟨hfirst, hmiddle.trans hfirst, hthird.trans hgm⟩

set_option maxHeartbeats 3000000

/-- The existing literal selected-block proof with the weaker bulk exponent;
all powering, dyadic, divisor and input-loss charges are retained. -/
theorem selectedBulkPoweredBlockAssembly :
    ∀ (_hGM : GuthMaynardTheorem11) (_hMV : DiscreteDirichletMeanValue)
        (κ η : ℝ), 0 < κ → κ ≤ 1 / 2 → 0 < η →
      ∃ C T₀ : ℝ, 0 < C ∧ Real.exp 1 ≤ T₀ ∧
        ∀ (T σ : ℝ) (N k : ℕ) (b : ℕ → ℂ)
            (W S : Finset ℝ) (i : Fin k),
          T₀ ≤ T → 4 / 5 ≤ σ → σ ≤ 1 →
          Real.rpow T κ ≤ (N : ℝ) →
          (N : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 →
          1 ≤ k → k ≤ powerCap κ →
          poweredLengthLower σ ≤
            (k : ℝ) * min (Real.logb T N) (1 / 2) →
          (k : ℝ) * min (Real.logb T N) (1 / 2) ≤
            (15 / 13 : ℝ) →
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
            C * Real.rpow T (bulkExponent σ + η) := by
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
    have hmuHigh' : mu ≤ (15 / 13 : ℝ) := by simpa [mu, lam] using hmuHigh
    have hmuGlobal : mu ≤ 15 / 13 := hmuHigh'
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
    have hfirstBase : 2 * mu * (1 - σ) ≤ bulkExponent σ :=
      (bulk_three_GM_exponents hσlow hσhigh hmuLow' hmuHigh').1
    have hthirdBase : 1 + (12 / 5 - 4 * σ) * mu ≤ bulkExponent σ :=
      (bulk_three_GM_exponents hσlow hσhigh hmuLow' hmuHigh').2.2
    have hbudget32 := thirtyTwo_powered_inputLoss_le_half hη.le hkcap
    have hreserve : 16 * ((k : ℝ) + 1) * delta ≤ η := by
      dsimp [delta]
      nlinarith
    have hfinalExp :
        bulkExponent σ + (8 * ((k : ℝ) + 1) + 1) * delta ≤
          bulkExponent σ + η := by
      have hcoef :
          8 * ((k : ℝ) + 1) + 1 ≤ 16 * ((k : ℝ) + 1) := by
        nlinarith [hkR]
      simpa [add_comm] using add_le_add_left
        ((mul_le_mul_of_nonneg_right hcoef hdelta.le).trans hreserve)
        (bulkExponent σ)
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
          bulkExponent σ + 8 * ((k : ℝ) + 1) * delta := by
      calc
        2 * (mu + (k : ℝ) * delta) - 2 * vexp =
            2 * mu * (1 - σ) + (4 * (k : ℝ) + 2) * delta := by
          dsimp [vexp]
          ring
        _ ≤ bulkExponent σ + (4 * (k : ℝ) + 2) * delta :=
          add_le_add hfirstBase le_rfl
        _ ≤ bulkExponent σ + 8 * ((k : ℝ) + 1) * delta := by
          have hk0 : (0 : ℝ) ≤ k := by positivity
          nlinarith
    have hexpThird :
        1 + ((12 / 5 : ℝ) * (mu + (k : ℝ) * delta) - 4 * vexp) ≤
          bulkExponent σ + 8 * ((k : ℝ) + 1) * delta := by
      calc
        1 + ((12 / 5 : ℝ) * (mu + (k : ℝ) * delta) - 4 * vexp) =
            (1 + (12 / 5 - 4 * σ) * mu) +
              ((12 / 5 : ℝ) * (k : ℝ) + 4 * ((k : ℝ) + 1)) * delta := by
          dsimp [vexp]
          ring
        _ ≤ bulkExponent σ +
              ((12 / 5 : ℝ) * (k : ℝ) + 4 * ((k : ℝ) + 1)) * delta :=
          add_le_add hthirdBase le_rfl
        _ ≤ bulkExponent σ + 8 * ((k : ℝ) + 1) * delta := by
          have hk0 : (0 : ℝ) ≤ k := by positivity
          nlinarith
    have hsecondBase : (18 / 5 - 4 * σ) * mu ≤ bulkExponent σ :=
      (bulk_three_GM_exponents hσlow hσhigh hmuLow' hmuHigh').2.1
    have hexpSecond :
        (18 / 5 : ℝ) * (mu + (k : ℝ) * delta) - 4 * vexp ≤
          bulkExponent σ + 8 * ((k : ℝ) + 1) * delta := by
      calc
        (18 / 5 : ℝ) * (mu + (k : ℝ) * delta) - 4 * vexp =
            (18 / 5 - 4 * σ) * mu +
              ((18 / 5 : ℝ) * (k : ℝ) + 4 * ((k : ℝ) + 1)) * delta := by
          dsimp [vexp]
          ring
        _ ≤ bulkExponent σ +
              ((18 / 5 : ℝ) * (k : ℝ) + 4 * ((k : ℝ) + 1)) * delta :=
          add_le_add hsecondBase le_rfl
        _ ≤ bulkExponent σ + 8 * ((k : ℝ) + 1) * delta := by
          have hk0 : (0 : ℝ) ≤ k := by positivity
          nlinarith
    have hterm1raw := pow_two_ratio_le hTpos (by positivity : 0 ≤ (blockN : ℝ))
      hqpos hLconst.le hBq hblockUpper hqLower
    have hterm1 : (blockN : ℝ) ^ 2 / (V / Cnorm) ^ 2 ≤
        Cquad * Real.rpow T (bulkExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
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
              (bulkExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hTone hexpFirst) hCquad.le
    have hterm2raw := rpow_ratio_four_le hTpos
      (by positivity : 0 ≤ (blockN : ℝ)) hqpos hLconst.le hBq
      (by norm_num : 0 ≤ (18 / 5 : ℝ)) hblockUpper hqLower
    have hterm2 : Real.rpow blockN (18 / 5 : ℝ) / (V / Cnorm) ^ 4 ≤
        Cfour18 * Real.rpow T
          (bulkExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
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
              (bulkExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hTone hexpSecond) hCfour18.le
    have hterm3raw := rpow_ratio_four_le hTpos
      (by positivity : 0 ≤ (blockN : ℝ)) hqpos hLconst.le hBq
      (by norm_num : 0 ≤ (12 / 5 : ℝ)) hblockUpper hqLower
    have hterm3 : T * Real.rpow blockN (12 / 5 : ℝ) /
        (V / Cnorm) ^ 4 ≤
        Cfour12 * Real.rpow T
          (bulkExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
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
              (bulkExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
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
          Real.rpow T (bulkExponent σ + 8 * ((k : ℝ) + 1) * delta) := by
      linarith
    calc
      (W.card : ℝ) ≤ (Kcap : ℝ) * (S.card : ℝ) := hcardReal
      _ ≤ (Kcap : ℝ) * (KGM * Real.rpow T delta *
          ((blockN : ℝ) ^ 2 / (V / Cnorm) ^ 2 +
            Real.rpow blockN (18 / 5 : ℝ) / (V / Cnorm) ^ 4 +
            T * Real.rpow blockN (12 / 5 : ℝ) / (V / Cnorm) ^ 4)) := by
        exact mul_le_mul_of_nonneg_left hraw (by positivity)
      _ ≤ CGM * Real.rpow T
          (bulkExponent σ + (8 * ((k : ℝ) + 1) + 1) * delta) := by
        dsimp [CGM]
        calc
          (Kcap : ℝ) * (KGM * Real.rpow T delta *
              ((blockN : ℝ) ^ 2 / (V / Cnorm) ^ 2 +
                Real.rpow blockN (18 / 5 : ℝ) / (V / Cnorm) ^ 4 +
                T * Real.rpow blockN (12 / 5 : ℝ) / (V / Cnorm) ^ 4)) ≤
              (Kcap : ℝ) * (KGM * Real.rpow T delta *
                ((Cquad + Cfour18 + Cfour12) *
                  Real.rpow T (bulkExponent σ + 8 * ((k : ℝ) + 1) * delta))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hsum
                (mul_nonneg hKGM.le (Real.rpow_nonneg hTpos.le _)))
              (by positivity)
          _ = (Kcap : ℝ) * KGM * (Cquad + Cfour18 + Cfour12) *
              Real.rpow T
                (bulkExponent σ + (8 * ((k : ℝ) + 1) + 1) * delta) := by
            rw [show (Kcap : ℝ) * (KGM * Real.rpow T delta *
                  ((Cquad + Cfour18 + Cfour12) *
                    Real.rpow T (bulkExponent σ + 8 * ((k : ℝ) + 1) * delta))) =
                (Kcap : ℝ) * KGM * (Cquad + Cfour18 + Cfour12) *
                  (Real.rpow T delta *
                    Real.rpow T (bulkExponent σ + 8 * ((k : ℝ) + 1) * delta)) by ring]
            rw [rpow_mul_rpow_eq hTpos]
            congr 2 <;> ring
      _ ≤ CGM * Real.rpow T (bulkExponent σ + η) := by
        apply mul_le_mul_of_nonneg_left _ hCGM.le
        apply Real.rpow_le_rpow_of_exponent_le hTone
        exact hfinalExp
      _ ≤ C * Real.rpow T (bulkExponent σ + η) := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg hTpos.le _)

/-- Source-faithful near-one large-value adapter.  This is proved from the
same Guth--Maynard theorem, not postulated as a stronger density statement. -/
theorem nearOneBulkUniformLargeValue (hGM : GuthMaynardTheorem11) :
  ∀ κ η : ℝ, 0 < κ → 0 < η →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T σ : ℝ) (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 4 / 5 ≤ σ → σ ≤ 1 →
        Real.rpow T κ ≤ N →
        (N : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 →
        (∀ n, ‖b n‖ ≤ 1) →
        OneSeparated W →
        (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
        (∀ t ∈ W,
          Real.rpow N σ * Real.rpow T (-inputLoss κ η) ≤
            ‖dirichletPolynomial b N t‖) →
        (W.card : ℝ) ≤
          C * Real.rpow T (bulkExponent σ + η) := by
  intro κ η hκ hη
  by_cases hκhalf : κ ≤ 1 / 2
  · obtain ⟨C, T₀, hC, hT₀, hselected⟩ :=
      selectedBulkPoweredBlockAssembly hGM RecenteredSampling.discreteDirichletMeanValue
        κ η hκ hκhalf hη
    refine ⟨C, T₀, hC, ?_, ?_⟩
    · exact (show (2 : ℝ) ≤ Real.exp 1 by
        linarith [Real.exp_one_gt_d9]).trans hT₀
    · intro T σ N b W hT hσlow hσhigh hNlow hNhigh hb hsep hheight hlarge
      have hET : Real.exp 1 ≤ T := hT₀.trans hT
      obtain ⟨hκlam, hlamHalf, -, -⟩ :=
        capped_logb_length_collar hκhalf hET hNlow hNhigh
      obtain ⟨k, hk, hkcap, hmuLow, hmuHigh⟩ :=
        exists_bulk_power_bounded_by_powerCap
          hσlow hκ hκlam hlamHalf
      let V : ℝ := Real.rpow N σ * Real.rpow T (-inputLoss κ η)
      have hTpos : 0 < T := (Real.exp_pos 1).trans_le hET
      have hNpos : (0 : ℝ) < N :=
        (Real.rpow_pos_of_pos hTpos κ).trans_le hNlow
      have hVpos : 0 < V := by
        dsimp [V]
        exact mul_pos (Real.rpow_pos_of_pos hNpos σ)
          (Real.rpow_pos_of_pos hTpos _)
      obtain ⟨i, S, hSW, hcard, hblock⟩ :=
        exists_common_powered_dirichlet_block
          (N := N) (k := k) (a := b) (W := W) (V := V)
          (Nat.zero_lt_of_lt hk) hVpos.le (by simpa [V] using hlarge)
      exact hselected T σ N k b W S i hT hσlow hσhigh
        hNlow hNhigh hk hkcap hmuLow hmuHigh hb hsep hheight
        hSW hcard (by simpa [V] using hblock)
  · have hκlarge : 1 / 2 < κ := lt_of_not_ge hκhalf
    obtain ⟨T₀, hT₀, hnone⟩ := no_admissible_length_above_half hκlarge
    refine ⟨1, max 2 T₀, by norm_num, le_max_left _ _, ?_⟩
    intro T σ N b W hT _ _ hNlow hNhigh _ _ _ _
    exact (hnone T N ((le_max_right _ _).trans hT) hNlow hNhigh).elim


#print axioms nearOneBulkUniformLargeValue
#print axioms selectedBulkPoweredBlockAssembly
#print axioms old_power_window_impossible_above_nine_tenths
#print axioms exists_bulk_power_bounded_by_powerCap
#print axioms bulk_three_GM_exponents
end
end MAPNearOneBulkBypassPowered
