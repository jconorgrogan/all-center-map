import GuthMaynardProp31TraceErrors

open scoped BigOperators Real
open GuthMaynardProposition46SectorConsumer
open GuthMaynardS1Source GuthMaynardS1Tail
open GuthMaynardSectionFourTrace
open GuthMaynardEquation55Infinite
open GuthMaynardSectionThreeCutoffDerivativeBudget
open GuthMaynardJIteration

noncomputable section
namespace GuthMaynardProp31TraceCardinality

/-- The trace form gives the exact cubic cardinality inequality while keeping
all three infinite source sectors explicit.  The Poisson and trace-one
remainders are discharged internally through `Prop31TraceErrors`; no trace or
moment estimate is exposed as a public premise. -/
theorem exists_actual_trace_cardinality_bound :
    ∀ delta : ℝ, 0 < delta →
      ∃ C : ℝ, 0 < C ∧
        ∀ (N : ℕ) (W : Finset ℝ) (T : ℝ) (b : ℕ → ℂ) (V : ℝ),
          1 ≤ N → 1 ≤ T → T ≤ (N : ℝ)^2 →
          (W.card : ℝ) ≤ 2*T → W.Nonempty → 0 ≤ V →
          (∀ t₁ ∈ W, ∀ t₂ ∈ W, t₁ ≠ t₂ →
            Real.rpow T delta ≤ |t₁ - t₂|) →
          (∀ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ≤ 1) →
          (∀ t : SourceRow W, V ≤ ‖sourceDN b N t‖) →
          (W.card : ℝ)^3 * V^6 ≤
            C * (N : ℝ)^3 *
              ((N : ℝ)^3 + ‖sourceS1 N W‖ + ‖sourceS2 N W‖ +
                ‖sourceS3 N W‖) := by
  intro delta hdelta
  obtain ⟨Ce, hCe, je, herr⟩ :=
    GuthMaynardProp31TraceErrors.exists_actual_trace_error_budget delta hdelta
  obtain ⟨Ca, hCa, havg⟩ :=
    GuthMaynardProp31TraceErrors.exists_actual_trace_average_budget
  let C : ℝ := 2048 * (Ce + Ca^3 + 1)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro N W T b V hN hT hTN hWcard hW hV hsep hb hlarge
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hRpos : 0 < (W.card : ℝ) := by exact_mod_cast hW.card_pos
  have hVnonneg : 0 ≤ V := hV
  have hR : 0 < Real.rpow T delta := Real.rpow_pos_of_pos hTpos delta
  have hsepR : ∀ t₁ ∈ W, ∀ t₂ ∈ W, t₁ ≠ t₂ →
      Real.rpow T delta ≤ |t₁ - t₂| := hsep
  have hprop := source_proposition46_sector_form W N b V
    (Real.rpow T delta) (by exact_mod_cast hN) hW
    hV hR hb hlarge hsepR je 0
  let B : ℝ := sourceTraceCubeDefectBudget N W (Real.rpow T delta) je 0
  let A : ℝ := sourceTraceAverageBudget N W 0
  let S : ℝ := ‖sourceS1 N W‖ + ‖sourceS2 N W‖ + ‖sourceS3 N W‖
  have hE3 : 0 ≤ sourceTraceCubePoissonError N W (Real.rpow T delta) je := by
    have hden : 0 < (Real.rpow T delta / (2 * Real.pi)) ^ je := by positivity
    unfold sourceTraceCubePoissonError
    have hA0 : 0 ≤ s1VerticalConstant je := s1VerticalConstant_nonneg _
    have hB0 : 0 ≤ lemma43DerivativeConstant 0 := lemma43DerivativeConstant_nonneg _
    positivity
  have hE1 : 0 ≤ sourceTraceOnePoissonError N W 0 := by
    have hden : 0 < (N : ℝ) ^ (0 + 2) := by positivity
    unfold sourceTraceOnePoissonError
    have hC : 0 ≤ lemma43DerivativeConstant (0 + 2) := lemma43DerivativeConstant_nonneg _
    have hM : 0 ≤ integerQuadraticMass := by
      unfold integerQuadraticMass
      exact tsum_nonneg fun j => by
        unfold integerQuadraticEnvelope
        split_ifs <;> positivity
    positivity
  have hQ : 0 ≤
      (sourceTraceMainOne N W).re ^ 2 +
        |(sourceTraceMainOne N W).re * (sourceTraceOne W N).re| +
        (sourceTraceOne W N).re ^ 2 := by positivity
  have hB0 : 0 ≤ B := by
    dsimp [B, sourceTraceCubeDefectBudget]
    exact add_nonneg (add_nonneg hE3 (by positivity))
      (div_nonneg (mul_nonneg hE1 hQ) (sq_nonneg _))
  have hA0 : 0 ≤ A := by
    dsimp [A, sourceTraceAverageBudget]
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg N) (lemma43DerivativeConstant_nonneg 0))
      (div_nonneg hE1 (Nat.cast_nonneg W.card))
  have herror := herr N W T hN hT hTN hWcard hW
  have hB : B ≤ Ce * (N : ℝ)^3 + S := by
    dsimp [B, S]
    have := herror
    dsimp [sourceTraceCubeDefectBudget] at this ⊢
    linarith
  have hA : A ≤ Ca * (N : ℝ) := by
    exact havg N W hN hW
  have hX : (W.card : ℝ) * V^2 ≤ 8 * (N : ℝ) * (B ^ (1 / 3 : ℝ) + A) := by
    simpa [B, A] using hprop
  let X : ℝ := (W.card : ℝ) * V^2
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hroot0 : 0 ≤ B ^ (1 / 3 : ℝ) := Real.rpow_nonneg hB0 _
  have hrootcube : (B ^ (1 / 3 : ℝ))^3 = B := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hB0]
    norm_num
  have hAcube : A^3 ≤ (Ca * (N : ℝ))^3 :=
    pow_le_pow_left₀ hA0 hA 3
  have hsumcube : (B ^ (1 / 3 : ℝ) + A)^3 ≤
      4 * (B + (Ca * (N : ℝ))^3) := by
    have hcross := mul_nonneg (add_nonneg hroot0 hA0)
      (sq_nonneg (B ^ (1 / 3 : ℝ) - A))
    nlinarith [hrootcube, hAcube]
  have hcube : X^3 ≤
      (8 * (N : ℝ) * (B ^ (1 / 3 : ℝ) + A))^3 := by
    exact pow_le_pow_left₀ hX0 hX 3
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hN3 : 0 ≤ (N : ℝ)^3 := by positivity
  have hmain : X^3 ≤
      2048 * (N : ℝ)^3 * ((Ce + Ca^3) * (N : ℝ)^3 + S) := by
    calc
      X^3 ≤ (8 * (N : ℝ) * (B ^ (1 / 3 : ℝ) + A))^3 := hcube
      _ = 512 * (N : ℝ)^3 * (B ^ (1 / 3 : ℝ) + A)^3 := by ring
      _ ≤ 2048 * (N : ℝ)^3 * (B + (Ca * (N : ℝ))^3) := by
        calc
          512 * (N : ℝ)^3 * (B ^ (1 / 3 : ℝ) + A)^3 ≤
              512 * (N : ℝ)^3 * (4 * (B + (Ca * (N : ℝ))^3)) := by
            gcongr
          _ = 2048 * (N : ℝ)^3 * (B + (Ca * (N : ℝ))^3) := by ring
      _ ≤ 2048 * (N : ℝ)^3 * ((Ce + Ca^3) * (N : ℝ)^3 + S) := by
        have hinner : B + (Ca * (N : ℝ))^3 ≤
            (Ce + Ca^3) * (N : ℝ)^3 + S := by
          nlinarith [hB]
        exact mul_le_mul_of_nonneg_left hinner (by positivity)
  calc
    (W.card : ℝ)^3 * V^6 = X^3 := by dsimp [X]; ring
    _ ≤ 2048 * (N : ℝ)^3 * ((Ce + Ca^3) * (N : ℝ)^3 + S) := hmain
    _ ≤ C * (N : ℝ)^3 * ((N : ℝ)^3 + S) := by
      dsimp [C]
      have hcoef : 0 ≤ Ce + Ca^3 := by positivity
      have hinner : (Ce + Ca^3) * (N : ℝ)^3 + S ≤
          (Ce + Ca^3 + 1) * ((N : ℝ)^3 + S) := by
        nlinarith [mul_nonneg hcoef hS0]
      calc
        2048 * (N : ℝ)^3 * ((Ce + Ca^3) * (N : ℝ)^3 + S) ≤
            2048 * (N : ℝ)^3 * ((Ce + Ca^3 + 1) * ((N : ℝ)^3 + S)) := by
          gcongr
        _ = 2048 * (Ce + Ca^3 + 1) * (N : ℝ)^3 * ((N : ℝ)^3 + S) := by ring
    _ = C * (N : ℝ)^3 *
        ((N : ℝ)^3 + ‖sourceS1 N W‖ + ‖sourceS2 N W‖ + ‖sourceS3 N W‖) := by
      dsimp [S]
      ring

end GuthMaynardProp31TraceCardinality

#print axioms GuthMaynardProp31TraceCardinality.exists_actual_trace_cardinality_bound
