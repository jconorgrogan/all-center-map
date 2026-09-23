import GuthMaynardProposition46SectorConsumer
import GuthMaynardLemma92SecondPoissonAbsorption

set_option maxHeartbeats 1000000

open scoped BigOperators Real
open GuthMaynardProposition46SectorConsumer
open GuthMaynardS1Source GuthMaynardS1Tail
open GuthMaynardSectionThreeCutoffDerivativeBudget
open GuthMaynardLemma44TraceOne
open GuthMaynardSectionFourTrace
open GuthMaynardJIteration

noncomputable section
namespace GuthMaynardProp31TraceErrors

private lemma trace_one_error_q0_le
    {N : ℕ} {W : Finset ℝ} (hN : 1 ≤ N) :
    sourceTraceOnePoissonError N W 0 ≤
      (W.card : ℝ) * (lemma43DerivativeConstant 2 *
        ((2 : ℝ)^2 * integerQuadraticMass)) / (N : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN2 : (N : ℝ) ^ 2 ≠ 0 := by positivity
  unfold sourceTraceOnePoissonError
  norm_num
  field_simp [hN2]
  exact le_rfl

private lemma trace_one_main_norm_le
    {N : ℕ} {W : Finset ℝ} (hN : 1 ≤ N) :
    ‖sourceTraceMainOne N W‖ ≤
      (N : ℝ) * (W.card : ℝ) * lemma43DerivativeConstant 0 := by
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hR0 : 0 ≤ (W.card : ℝ) := Nat.cast_nonneg _
  calc
    ‖sourceTraceMainOne N W‖ =
        (N : ℝ) * (W.card : ℝ) * ‖sourceHhat 0 0‖ := by
      simp [sourceTraceMainOne, norm_mul]
    _ ≤ (N : ℝ) * (W.card : ℝ) * lemma43DerivativeConstant 0 := by
      gcongr
      exact norm_sourceHhat_le_fixed 0 0

private lemma trace_one_norm_le
    {N : ℕ} {W : Finset ℝ} (hN : 1 ≤ N) (hW : W.Nonempty) :
    ‖sourceTraceOne W N‖ ≤
      (N : ℝ) * (W.card : ℝ) *
          (lemma43DerivativeConstant 0 +
            lemma43DerivativeConstant 2 * ((2 : ℝ)^2 * integerQuadraticMass)) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hRpos : 0 < (W.card : ℝ) := by exact_mod_cast hW.card_pos
  have htail := norm_sourceTraceOne_sub_main_le (N := N) hN (W := W) 0
  have htail' : ‖sourceTraceOne W N - sourceTraceMainOne N W‖ ≤
      (W.card : ℝ) * (lemma43DerivativeConstant 2 *
        ((2 : ℝ)^2 * integerQuadraticMass)) / (N : ℝ) := by
    have hratio : (N : ℝ) / (N : ℝ)^2 = 1 / (N : ℝ) := by
      field_simp [hNpos.ne']
    norm_num at htail
    rw [hratio] at htail
    unfold sourceTraceMainOne
    convert htail using 1 <;> ring
  calc
    ‖sourceTraceOne W N‖ ≤
        ‖sourceTraceMainOne N W‖ +
          ‖sourceTraceOne W N - sourceTraceMainOne N W‖ := by
      calc
        ‖sourceTraceOne W N‖ =
            ‖(sourceTraceOne W N - sourceTraceMainOne N W) +
              sourceTraceMainOne N W‖ := by congr 1; ring
        _ ≤ ‖sourceTraceOne W N - sourceTraceMainOne N W‖ +
            ‖sourceTraceMainOne N W‖ := norm_add_le _ _
        _ = ‖sourceTraceMainOne N W‖ +
            ‖sourceTraceOne W N - sourceTraceMainOne N W‖ := by ring
    _ ≤ (N : ℝ) * (W.card : ℝ) * lemma43DerivativeConstant 0 +
        (W.card : ℝ) * (lemma43DerivativeConstant 2 *
          ((2 : ℝ)^2 * integerQuadraticMass)) / (N : ℝ) := by
      exact add_le_add (trace_one_main_norm_le hN) htail'
    _ ≤ (N : ℝ) * (W.card : ℝ) *
          (lemma43DerivativeConstant 0 +
            lemma43DerivativeConstant 2 * ((2 : ℝ)^2 * integerQuadraticMass)) := by
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hR0 : 0 ≤ (W.card : ℝ) := Nat.cast_nonneg _
      have hK0 : 0 ≤ lemma43DerivativeConstant 2 *
          ((2 : ℝ)^2 * integerQuadraticMass) := by
        exact mul_nonneg (lemma43DerivativeConstant_nonneg 2)
          (mul_nonneg (by positivity) GuthMaynardJIteration.integerQuadraticMass_nonneg)
      have hKle : (W.card : ℝ) *
          (lemma43DerivativeConstant 2 * ((2 : ℝ)^2 * integerQuadraticMass)) / N ≤
          N * (W.card : ℝ) *
            (lemma43DerivativeConstant 2 * ((2 : ℝ)^2 * integerQuadraticMass)) := by
        rw [div_eq_mul_inv]
        have hinv : (N : ℝ)⁻¹ ≤ (N : ℝ) := by
          have hinv0 : (N : ℝ)⁻¹ ≤ 1 := by
            simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hN1
          exact hinv0.trans hN1
        calc
          (W.card : ℝ) *
              (lemma43DerivativeConstant 2 * ((2 : ℝ)^2 * integerQuadraticMass)) *
              (N : ℝ)⁻¹ ≤
              (W.card : ℝ) *
                (lemma43DerivativeConstant 2 * ((2 : ℝ)^2 * integerQuadraticMass)) *
                (N : ℝ) :=
            mul_le_mul_of_nonneg_left hinv (mul_nonneg hR0 hK0)
          _ = (N : ℝ) * (W.card : ℝ) *
              (lemma43DerivativeConstant 2 * ((2 : ℝ)^2 * integerQuadraticMass)) := by ring
      nlinarith

private lemma rpow_power_lower
    {delta T : ℝ} {j : ℕ} (hdelta : 0 < delta) (hT : 1 ≤ T)
    (hj : (3 : ℝ) ≤ delta * (j : ℝ)) :
    T ^ (3 : ℕ) ≤ (Real.rpow T delta) ^ j := by
  calc
    T ^ (3 : ℕ) = Real.rpow T (3 : ℝ) := by
      symm
      exact Real.rpow_natCast T 3
    _ ≤ Real.rpow T (delta * (j : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hT hj
    _ = (Real.rpow T delta) ^ j := by
      exact Real.rpow_mul_natCast (by positivity : 0 ≤ T) delta j

theorem exists_actual_trace_error_budget :
    ∀ delta : ℝ, 0 < delta →
      ∃ C : ℝ, 0 < C ∧ ∃ j : ℕ,
        ∀ (N : ℕ) (W : Finset ℝ) (T : ℝ),
          1 ≤ N → 1 ≤ T → T ≤ (N : ℝ)^2 →
          (W.card : ℝ) ≤ 2*T → W.Nonempty →
          sourceTraceCubePoissonError N W (Real.rpow T delta) j +
            sourceTraceOnePoissonError N W 0 *
              ((sourceTraceMainOne N W).re ^ 2 +
                |(sourceTraceMainOne N W).re * (sourceTraceOne W N).re| +
                (sourceTraceOne W N).re ^ 2) / (W.card : ℝ)^2 ≤
            C * (N : ℝ)^3 := by
  intro delta hdelta
  let j : ℕ := Nat.ceil ((3 : ℝ) / delta)
  let c : ℝ := 2 * Real.pi
  let B0 : ℝ := lemma43DerivativeConstant 0
  let K1 : ℝ := lemma43DerivativeConstant 2 *
    ((2 : ℝ)^2 * integerQuadraticMass)
  let A : ℝ := s1VerticalConstant j
  let D : ℝ := A * B0^2 + B0 * A * B0
  let C0 : ℝ := 8 * c^j * D
  let C1 : ℝ := K1 * (B0^2 + B0 * (B0 + K1) + (B0 + K1)^2)
  let C : ℝ := C0 + 2*C1 + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hB0 : 0 ≤ B0 := by dsimp [B0]; exact lemma43DerivativeConstant_nonneg 0
  have hK1 : 0 ≤ K1 := by
    dsimp [K1]
    exact mul_nonneg (lemma43DerivativeConstant_nonneg 2)
      (mul_nonneg (by positivity) GuthMaynardJIteration.integerQuadraticMass_nonneg)
  have hA : 0 ≤ A := by dsimp [A]; exact GuthMaynardS1Tail.s1VerticalConstant_nonneg _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C, C0, C1]; positivity
  have hj : (3 : ℝ) ≤ delta * (j : ℝ) := by
    dsimp [j]
    simpa [mul_comm] using (div_le_iff₀ hdelta).mp (Nat.le_ceil _)
  refine ⟨C, hC, j, ?_⟩
  intro N W T hN hT hTN hR hW
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hT0 : 0 ≤ T := by linarith
  have hRpos : 0 < (W.card : ℝ) := by exact_mod_cast hW.card_pos
  have hR0 : 0 ≤ (W.card : ℝ) := hRpos.le
  have hRcube : (W.card : ℝ)^3 ≤ 8*T^3 := by
    calc
      (W.card : ℝ)^3 ≤ (2*T)^3 :=
        pow_le_pow_left₀ hR0 hR 3
      _ = 8*T^3 := by ring
  have hTpow : T^3 ≤ (Real.rpow T delta)^j := rpow_power_lower hdelta hT hj
  have hpowpos : 0 < (Real.rpow T delta)^j :=
    pow_pos (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hT) delta) _
  have hratio : T^3 * ((Real.rpow T delta)^j)⁻¹ ≤ 1 := by
    have hh : T^3 / (Real.rpow T delta)^j ≤ 1 :=
      (div_le_iff₀ hpowpos).2 (by simpa using hTpow)
    simpa [div_eq_mul_inv] using hh
  have hdenpos : 0 < (Real.rpow T delta / c)^j := by
    exact pow_pos (div_pos (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hT) delta) hc) _
  have hdeninv : ((Real.rpow T delta / c)^j)⁻¹ =
      c^j * ((Real.rpow T delta)^j)⁻¹ := by
    rw [div_pow]
    field_simp [hc.ne']
  have hbase : (W.card : ℝ)^3 * ((Real.rpow T delta / c)^j)⁻¹ ≤ 8*c^j := by
    rw [hdeninv]
    calc
      (W.card : ℝ)^3 * (c^j * ((Real.rpow T delta)^j)⁻¹) =
          ((W.card : ℝ)^3 * ((Real.rpow T delta)^j)⁻¹) * c^j := by ring
      _ ≤ (8*T^3 * ((Real.rpow T delta)^j)⁻¹) * c^j := by
        gcongr
      _ = 8*c^j * (T^3 * ((Real.rpow T delta)^j)⁻¹) := by ring
      _ ≤ 8*c^j := by
        have hcj : 0 ≤ 8*c^j := by positivity
        simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hratio hcj)
  have hinner :
      (W.card : ℝ)^3 *
          ((A / (Real.rpow T delta / c)^j) * B0^2 +
            B0 * (A / (Real.rpow T delta / c)^j) * B0) ≤ C0 := by
    rw [show A / (Real.rpow T delta / c)^j =
      A * ((Real.rpow T delta / c)^j)⁻¹ by rw [div_eq_mul_inv]]
    calc
      _ = ((W.card : ℝ)^3 * ((Real.rpow T delta / c)^j)⁻¹) * D := by
        dsimp [D]
        ring
      _ ≤ (8*c^j) * D :=
        mul_le_mul_of_nonneg_right hbase hD
      _ = C0 := by rfl
  have hcube : sourceTraceCubePoissonError N W (Real.rpow T delta) j ≤
      C0 * (N : ℝ)^3 := by
    unfold sourceTraceCubePoissonError
    have hh := mul_le_mul_of_nonneg_left hinner
      (by positivity : 0 ≤ (N : ℝ)^3)
    convert hh using 1 <;> ring
  have hE1 : sourceTraceOnePoissonError N W 0 ≤
      (W.card : ℝ) * K1 / (N : ℝ) := trace_one_error_q0_le hN
  have hmainnorm : ‖sourceTraceMainOne N W‖ ≤
      (N : ℝ) * (W.card : ℝ) * B0 := by
    dsimp [B0]
    exact trace_one_main_norm_le hN
  have htracenorm : ‖sourceTraceOne W N‖ ≤
      (N : ℝ) * (W.card : ℝ) * (B0 + K1) := by
    dsimp [B0, K1]
    exact trace_one_norm_le hN hW
  have hq :
      (sourceTraceMainOne N W).re ^ 2 +
          |(sourceTraceMainOne N W).re * (sourceTraceOne W N).re| +
          (sourceTraceOne W N).re ^ 2 ≤
        (B0^2 + B0*(B0+K1) + (B0+K1)^2) *
          ((N : ℝ)^2 * (W.card : ℝ)^2) := by
    have hmre : |(sourceTraceMainOne N W).re| ≤
        (N : ℝ) * (W.card : ℝ) * B0 :=
      (Complex.abs_re_le_norm _).trans hmainnorm
    have htre : |(sourceTraceOne W N).re| ≤
        (N : ℝ) * (W.card : ℝ) * (B0 + K1) :=
      (Complex.abs_re_le_norm _).trans htracenorm
    have hp : 0 ≤ (N : ℝ) * (W.card : ℝ) := by positivity
    have hq1 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hmre
    have hq2 : |(sourceTraceMainOne N W).re * (sourceTraceOne W N).re| ≤
        ((N : ℝ) * (W.card : ℝ) * B0) *
          ((N : ℝ) * (W.card : ℝ) * (B0 + K1)) := by
      calc
        _ = |(sourceTraceMainOne N W).re| *
            |(sourceTraceOne W N).re| := by rw [abs_mul]
        _ ≤ _ := mul_le_mul hmre htre (abs_nonneg _) (by positivity)
    have hq3 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 htre
    have hmain_sq :
        (sourceTraceMainOne N W).re ^ 2 =
          |(sourceTraceMainOne N W).re| ^ 2 := by rw [sq_abs]
    have htrace_sq :
        (sourceTraceOne W N).re ^ 2 =
          |(sourceTraceOne W N).re| ^ 2 := by rw [sq_abs]
    rw [hmain_sq, htrace_sq]
    nlinarith
  have hcorr : sourceTraceOnePoissonError N W 0 *
      ((sourceTraceMainOne N W).re ^ 2 +
        |(sourceTraceMainOne N W).re * (sourceTraceOne W N).re| +
        (sourceTraceOne W N).re ^ 2) / (W.card : ℝ)^2 ≤
      2*C1 * (N : ℝ)^3 := by
    have hcard2 : 0 < (W.card : ℝ)^2 := by positivity
    calc
      _ ≤ ((W.card : ℝ) * K1 / (N : ℝ)) *
          ((B0^2 + B0*(B0+K1) + (B0+K1)^2) *
            ((N : ℝ)^2 * (W.card : ℝ)^2)) / (W.card : ℝ)^2 := by
        gcongr
      _ = K1 * (B0^2 + B0*(B0+K1) + (B0+K1)^2) *
          (N : ℝ) * (W.card : ℝ) := by
        have hNcancel : (N : ℝ)^2 / (N : ℝ) = (N : ℝ) := by
          field_simp [hNpos.ne']
        have hRcancel : (W.card : ℝ)^3 / (W.card : ℝ)^2 = (W.card : ℝ) := by
          field_simp [hRpos.ne']
        calc
          ((W.card : ℝ) * K1 / (N : ℝ)) *
              ((B0^2 + B0*(B0+K1) + (B0+K1)^2) *
                ((N : ℝ)^2 * (W.card : ℝ)^2)) / (W.card : ℝ)^2 =
              K1 * (B0^2 + B0*(B0+K1) + (B0+K1)^2) *
                ((N : ℝ)^2 / (N : ℝ)) *
                ((W.card : ℝ)^3 / (W.card : ℝ)^2) := by ring
          _ = K1 * (B0^2 + B0*(B0+K1) + (B0+K1)^2) *
                (N : ℝ) * (W.card : ℝ) := by rw [hNcancel, hRcancel]
      _ ≤ 2*C1 * (N : ℝ)^3 := by
        dsimp [C1]
        have hRleN2 : (W.card : ℝ) ≤ 2*(N : ℝ)^2 := hR.trans (by
          gcongr)
        have hNcube : (N : ℝ) * (W.card : ℝ) ≤ 2*(N : ℝ)^3 := by
          calc
            (N : ℝ) * (W.card : ℝ) ≤ (N : ℝ) * (2 * (N : ℝ)^2) :=
              mul_le_mul_of_nonneg_left hRleN2 (by positivity)
            _ = 2 * (N : ℝ)^3 := by ring
        have hKQ : 0 ≤ K1 *
            (B0^2 + B0*(B0+K1) + (B0+K1)^2) := by positivity
        calc
          K1 * (B0^2 + B0*(B0+K1) + (B0+K1)^2) *
              (N : ℝ) * (W.card : ℝ) =
              (K1 * (B0^2 + B0*(B0+K1) + (B0+K1)^2)) *
                ((N : ℝ) * (W.card : ℝ)) := by ring
          _ ≤ (K1 * (B0^2 + B0*(B0+K1) + (B0+K1)^2)) *
                (2 * (N : ℝ)^3) :=
              mul_le_mul_of_nonneg_left hNcube hKQ
          _ = 2 * (K1 * (B0^2 + B0*(B0+K1) + (B0+K1)^2)) *
                (N : ℝ)^3 := by ring
  calc
    sourceTraceCubePoissonError N W (Real.rpow T delta) j +
          sourceTraceOnePoissonError N W 0 *
            ((sourceTraceMainOne N W).re ^ 2 +
              |(sourceTraceMainOne N W).re * (sourceTraceOne W N).re| +
              (sourceTraceOne W N).re ^ 2) / (W.card : ℝ)^2 ≤
        C0 * (N : ℝ)^3 + 2*C1 * (N : ℝ)^3 :=
      add_le_add hcube hcorr
    _ ≤ C * (N : ℝ)^3 := by
      dsimp [C]
      nlinarith

theorem exists_actual_trace_average_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (W : Finset ℝ),
      1 ≤ N → W.Nonempty →
      sourceTraceAverageBudget N W 0 ≤ C * (N : ℝ) := by
  let K1 : ℝ := lemma43DerivativeConstant 2 *
    ((2 : ℝ)^2 * integerQuadraticMass)
  let C : ℝ := lemma43DerivativeConstant 0 + K1 + 1
  have hB0 : 0 ≤ lemma43DerivativeConstant 0 := lemma43DerivativeConstant_nonneg 0
  have hK1 : 0 ≤ K1 := by
    dsimp [K1]
    exact mul_nonneg (lemma43DerivativeConstant_nonneg 2)
      (mul_nonneg (by positivity) GuthMaynardJIteration.integerQuadraticMass_nonneg)
  have hC : 0 < C := by dsimp [C]; nlinarith
  refine ⟨C, hC, ?_⟩
  intro N W hN hW
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hRpos : 0 < (W.card : ℝ) := by exact_mod_cast hW.card_pos
  have hE1 := trace_one_error_q0_le hN (W := W)
  unfold sourceTraceAverageBudget
  dsimp [C]
  have htail : sourceTraceOnePoissonError N W 0 / (W.card : ℝ) ≤ K1 := by
    have hK1 : 0 ≤ K1 := by
      dsimp [K1]
      exact mul_nonneg (lemma43DerivativeConstant_nonneg 2)
        (mul_nonneg (by positivity) GuthMaynardJIteration.integerQuadraticMass_nonneg)
    calc
      sourceTraceOnePoissonError N W 0 / (W.card : ℝ) ≤
          ((W.card : ℝ) * K1 / (N : ℝ)) / (W.card : ℝ) :=
        div_le_div_of_nonneg_right hE1 hRpos.le
      _ = K1 / (N : ℝ) := by field_simp [hRpos.ne']
      _ ≤ K1 := by
        apply (div_le_iff₀ hNpos).2
        have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
        nlinarith
  calc
    (N : ℝ) * lemma43DerivativeConstant 0 +
          sourceTraceOnePoissonError N W 0 / (W.card : ℝ) ≤
        (N : ℝ) * lemma43DerivativeConstant 0 + K1 :=
      add_le_add le_rfl htail
    _ ≤ C * (N : ℝ) := by
      dsimp [C]
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith

end GuthMaynardProp31TraceErrors

#print axioms GuthMaynardProp31TraceErrors.exists_actual_trace_error_budget
#print axioms GuthMaynardProp31TraceErrors.exists_actual_trace_average_budget
