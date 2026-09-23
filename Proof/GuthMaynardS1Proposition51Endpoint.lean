import GuthMaynardS1Proposition51
import GuthMaynardS1PowerLedger

/-! # The source `S₁ = O_epsilon(T^{-10})` endpoint -/

namespace GuthMaynardS1Proposition51Endpoint

open scoped Real
open GuthMaynardS1Source GuthMaynardS1Tail
open GuthMaynardS1Proposition51 GuthMaynardS1PowerLedger
open GuthMaynardSectionThreeCutoffDerivativeBudget
open GuthMaynardJIteration

noncomputable section

theorem integerQuadraticMass_nonneg_source :
    0 ≤ integerQuadraticMass := by
  unfold integerQuadraticMass
  exact tsum_nonneg fun m => by
    rw [integerQuadraticEnvelope]
    split_ifs <;> positivity

def sourceS1FiniteContribution (N : ℕ) (W : Finset ℝ) (B : ℝ) : ℝ :=
  3 * (N : ℝ) ^ 3 *
    sourceS1ThirdFiniteMass N W (s1FiniteMRange B)

def sourceS1FarContribution (N : ℕ) (W : Finset ℝ) (B : ℝ) : ℝ :=
  3 * (N : ℝ) ^ 3 * sourceS1ThirdFarMass N W B

theorem sourceS1TotalContribution_le_finite_add_far
    {N : ℕ} (hN : 0 < N) {W : Finset ℝ} {T B : ℝ}
    (hT : 0 ≤ T) (hB : 0 < B)
    (hdiameter : ∀ t ∈ W, ∀ u ∈ W, |t - u| ≤ T) :
    sourceS1TotalContribution N W ≤
      sourceS1FiniteContribution N W B + sourceS1FarContribution N W B := by
  have hsplit := sourceS1TotalContribution_le_split hN hT hB hdiameter
  simpa [sourceS1SplitContribution, sourceS1ThirdSplitMass,
    sourceS1FiniteContribution, sourceS1FarContribution, mul_add] using hsplit

def sourceS1FiniteConstant (j : ℕ) : ℝ :=
  120 * (2 * s1VerticalConstant j * (2 * Real.pi) ^ j *
      lemma43DerivativeConstant 0 ^ 2 +
    lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j)

theorem sourceS1FiniteConstant_nonneg (j : ℕ) :
    0 ≤ sourceS1FiniteConstant j := by
  unfold sourceS1FiniteConstant
  have hV := s1VerticalConstant_nonneg j
  have hC0 := lemma43DerivativeConstant_nonneg 0
  have hCj := lemma43DerivativeConstant_nonneg j
  positivity

/-- The finite-frequency part of Proposition 5.1, including the diagonal
sector with its retained `N^{-j}` factor. -/
theorem sourceS1FiniteContribution_le
    {N : ℕ} (hNnat : 0 < N) {W : Finset ℝ}
    {T epsilon : ℝ}
    (hN : (1 : ℝ) ≤ N)
    (hTdef : T = Real.rpow (N : ℝ) (6 / 5 : ℝ))
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hW : (W.card : ℝ) ≤ 2 * T)
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u →
      Real.rpow T epsilon ≤ |t-u|) :
    sourceS1FiniteContribution N W
        (Real.rpow T (1 + epsilon) / (N : ℝ)) ≤
      sourceS1FiniteConstant (s1DecayOrder epsilon) / T ^ 13 := by
  let j := s1DecayOrder epsilon
  let B := Real.rpow T (1 + epsilon) / (N : ℝ)
  let R := Real.rpow T epsilon
  have hTone := one_le_sourceT hN hTdef
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  have hNT := sourceN_le_T hN hTdef
  have hBbounds := sourceCutoff_bounds hN hTdef hepsilon.le hepsilonHalf rfl
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hBbounds.1
  have hMcard : ((s1FiniteMRange B).card : ℝ) ≤ 5 * B :=
    card_s1FiniteMRange_cast_le_five_mul hBbounds.1
  have hW0 : 0 ≤ (W.card : ℝ) := by positivity
  have hM0 : 0 ≤ ((s1FiniteMRange B).card : ℝ) := by positivity
  have hvertical := finite_prefactor_over_vertical_le
    hN hTone hNT hBbounds.2 hW0 hW hM0 hMcard hepsilon
  have hdiagonal := finite_prefactor_over_diagonal_le
    hN hTone hNT hBbounds.2 hW0 hW hM0 hMcard hTdef
      hepsilon hepsilonHalf
  have hraw := sourceS1ThirdFiniteMass_le_partition_bound_sharp
    (M := s1FiniteMRange B) (R := R)
    hNnat (show 0 < R by exact Real.rpow_pos_of_pos hTpos _)
    (by simpa [R] using hsep)
    (fun m hm => mem_s1FiniteMRange_ne_zero hm) j
  let P : ℝ := 3 * (N : ℝ) ^ 3 *
    ((W.card : ℝ) ^ 3 * ((s1FiniteMRange B).card : ℝ))
  let CV : ℝ := s1VerticalConstant j * (2 * Real.pi) ^ j *
    lemma43DerivativeConstant 0 ^ 2
  let CD : ℝ := lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j
  have hPvertical : P / R ^ j ≤ 120 / T ^ 13 := by
    simpa [P, R, mul_assoc] using hvertical
  have hPdiag : P / (N : ℝ) ^ j ≤ 120 / T ^ 13 := by
    simpa [P, mul_assoc] using hdiagonal
  have hCV0 : 0 ≤ CV := by
    dsimp [CV]
    exact mul_nonneg
      (mul_nonneg (s1VerticalConstant_nonneg j)
        (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi) j))
      (sq_nonneg _)
  have hCD0 : 0 ≤ CD := by
    dsimp [CD]
    exact mul_nonneg (sq_nonneg _) (lemma43DerivativeConstant_nonneg j)
  have hoffIdentity :
      P * ((s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
        lemma43DerivativeConstant 0 ^ 2) = CV * (P / R ^ j) := by
    dsimp [CV]
    have hRpos : 0 < R := Real.rpow_pos_of_pos hTpos _
    have hpi : 0 < 2 * Real.pi := by positivity
    rw [div_pow]
    have hquot : s1VerticalConstant j / (R ^ j / (2 * Real.pi) ^ j) =
        s1VerticalConstant j * (2 * Real.pi) ^ j / R ^ j := by
      field_simp [hRpos.ne', hpi.ne']
    rw [hquot]
    ring
  have hdiagIdentity :
      P * (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j /
        (N : ℝ) ^ j) = CD * (P / (N : ℝ) ^ j) := by
    dsimp [CD]
    ring
  have hoff :
      P * ((s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
        lemma43DerivativeConstant 0 ^ 2) ≤ CV * (120 / T ^ 13) := by
    rw [hoffIdentity]
    exact mul_le_mul_of_nonneg_left hPvertical hCV0
  have hoff' :
      P * (lemma43DerivativeConstant 0 *
        (s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
        lemma43DerivativeConstant 0) ≤ CV * (120 / T ^ 13) := by
    convert hoff using 1 <;> ring
  have hdiag :
      P * (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j /
        (N : ℝ) ^ j) ≤ CD * (120 / T ^ 13) := by
    rw [hdiagIdentity]
    exact mul_le_mul_of_nonneg_left hPdiag hCD0
  have hscaled := mul_le_mul_of_nonneg_left hraw
    (show 0 ≤ 3 * (N : ℝ) ^ 3 by positivity)
  change sourceS1FiniteContribution N W B ≤ _
  calc
    sourceS1FiniteContribution N W B ≤
        P * ((s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
          lemma43DerivativeConstant 0 ^ 2) +
        P * (lemma43DerivativeConstant 0 *
          (s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
          lemma43DerivativeConstant 0) +
        P * (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j /
          (N : ℝ) ^ j) := by
      simpa [sourceS1FiniteContribution, P, B, R, mul_add,
        add_assoc, mul_assoc] using hscaled
    _ ≤ CV * (120 / T ^ 13) + CV * (120 / T ^ 13) +
        CD * (120 / T ^ 13) := add_le_add (add_le_add hoff hoff') hdiag
    _ = sourceS1FiniteConstant j / T ^ 13 := by
      dsimp [sourceS1FiniteConstant, CV, CD]
      ring

def sourceS1FarConstant (j : ℕ) : ℝ :=
  24 * 4 ^ j * lemma43DerivativeConstant 0 ^ 2 *
    lemma43DerivativeConstant j * integerQuadraticMass

theorem sourceS1FarConstant_nonneg (j : ℕ) :
    0 ≤ sourceS1FarConstant j := by
  unfold sourceS1FarConstant
  have hC0 := lemma43DerivativeConstant_nonneg 0
  have hCj := lemma43DerivativeConstant_nonneg j
  have hmass := integerQuadraticMass_nonneg_source
  positivity

/-- Exact algebra of the far-frequency cancellation: the cutoff contributes
`B^{-q}`, cancelling all but `N*T^2/(T^epsilon)^q`. -/
theorem far_frequency_core_le
    {N T R B : ℝ} (hN : 0 < N) (hT : 1 ≤ T) (hR : 0 < R)
    (hB : B = T * R / N) (q : ℕ) :
    N ^ 3 * (1 + T) ^ (q + 2) *
        ((1 / N ^ (q + 2)) *
          (2 ^ (q + 2) * ((1 / B ^ q) * integerQuadraticMass))) ≤
      (4 : ℝ) ^ (q + 2) * integerQuadraticMass *
        (N * T ^ 2 / R ^ q) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hBpos : 0 < B := by rw [hB]; positivity
  have hhor : (1 + T) ^ (q + 2) ≤ (2 * T) ^ (q + 2) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hmass0 := integerQuadraticMass_nonneg_source
  calc
    N ^ 3 * (1 + T) ^ (q + 2) *
        ((1 / N ^ (q + 2)) *
          (2 ^ (q + 2) * ((1 / B ^ q) * integerQuadraticMass))) ≤
      N ^ 3 * (2 * T) ^ (q + 2) *
        ((1 / N ^ (q + 2)) *
          (2 ^ (q + 2) * ((1 / B ^ q) * integerQuadraticMass))) := by
        gcongr
    _ = (4 : ℝ) ^ (q + 2) * integerQuadraticMass *
        (N * T ^ 2 / R ^ q) := by
      have hfour : (4 : ℝ) ^ (q + 2) = 2 ^ ((q + 2) * 2) := by
        calc
          (4 : ℝ) ^ (q + 2) = (2 ^ 2 : ℝ) ^ (q + 2) := by norm_num
          _ = 2 ^ (2 * (q + 2)) := by rw [pow_mul]
          _ = 2 ^ ((q + 2) * 2) := by rw [Nat.mul_comm]
      rw [hB, div_pow]
      field_simp [hN.ne', hTpos.ne', hR.ne']
      rw [hfour]
      ring

/-- The all-integer far tail at the exact Proposition 3.1 aperture. -/
theorem sourceS1FarContribution_le
    {N : ℕ} (hNnat : 0 < N) {W : Finset ℝ}
    {T epsilon : ℝ}
    (hN : (1 : ℝ) ≤ N)
    (hTdef : T = Real.rpow (N : ℝ) (6 / 5 : ℝ))
    (hepsilon : 0 < epsilon)
    (hW : (W.card : ℝ) ≤ 2 * T)
    (hdiameter : ∀ t ∈ W, ∀ u ∈ W, |t-u| ≤ T) :
    sourceS1FarContribution N W
        (Real.rpow T (1 + epsilon) / (N : ℝ)) ≤
      sourceS1FarConstant (s1DecayOrder epsilon) / T ^ 12 := by
  let j := s1DecayOrder epsilon
  let q := j - 2
  let R := Real.rpow T epsilon
  let B := Real.rpow T (1 + epsilon) / (N : ℝ)
  have hTone := one_le_sourceT hN hTdef
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  have hNT := sourceN_le_T hN hTdef
  have hRpos : 0 < R := Real.rpow_pos_of_pos hTpos _
  have hBform : B = T * R / (N : ℝ) := by
    dsimp [B, R]
    calc
      Real.rpow T (1 + epsilon) / (N : ℝ) =
          (Real.rpow T 1 * Real.rpow T epsilon) / (N : ℝ) := by
            exact congrArg (fun x : ℝ => x / (N : ℝ))
              (Real.rpow_add hTpos 1 epsilon)
      _ = T * Real.rpow T epsilon / (N : ℝ) := by
            exact congrArg
              (fun x : ℝ => x * Real.rpow T epsilon / (N : ℝ))
              (Real.rpow_one T)
  have hBpos : 0 < B := by rw [hBform]; positivity
  have hqj : q + 2 = j := by
    dsimp [q, j]
    exact tailOrder_add_two epsilon
  have hraw := sourceS1ThirdFarMass_le hNnat
    (show 0 ≤ T by linarith) hBpos hdiameter q
  have hcore := far_frequency_core_le
    (lt_of_lt_of_le zero_lt_one hN) hTone hRpos hBform q
  have hW0 : 0 ≤ (W.card : ℝ) := by positivity
  have hW3 : (W.card : ℝ) ^ 3 ≤ 8 * T ^ 3 := by
    calc
      (W.card : ℝ) ^ 3 ≤ (2 * T) ^ 3 :=
        pow_le_pow_left₀ hW0 hW 3
      _ = 8 * T ^ 3 := by ring
  have htailPower := eight_over_tail_le_inv_twelve hTone hepsilon
  have hT6to8 : T ^ 6 ≤ T ^ 8 := by
    exact pow_le_pow_right₀ hTone (by omega)
  have hmass0 := integerQuadraticMass_nonneg_source
  have hC0 := lemma43DerivativeConstant_nonneg 0
  have hCj := lemma43DerivativeConstant_nonneg j
  have hnormalized :
      3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
          ((lemma43DerivativeConstant 0 ^ 2 *
              (lemma43DerivativeConstant j * (1 + T) ^ j)) *
            ((1 / (N : ℝ) ^ j) *
              (2 ^ j * ((1 / B ^ q) * integerQuadraticMass)))) ≤
        sourceS1FarConstant j * (T ^ 8 / R ^ q) := by
    have hcore' := hcore
    rw [hqj] at hcore'
    calc
      3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
          ((lemma43DerivativeConstant 0 ^ 2 *
              (lemma43DerivativeConstant j * (1 + T) ^ j)) *
            ((1 / (N : ℝ) ^ j) *
              (2 ^ j * ((1 / B ^ q) * integerQuadraticMass)))) =
        3 * (W.card : ℝ) ^ 3 *
          (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j) *
          ((N : ℝ) ^ 3 * (1 + T) ^ j *
            ((1 / (N : ℝ) ^ j) *
              (2 ^ j * ((1 / B ^ q) * integerQuadraticMass)))) := by ring
      _ ≤ 3 * (8 * T ^ 3) *
          (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j) *
          ((4 : ℝ) ^ j * integerQuadraticMass *
            ((N : ℝ) * T ^ 2 / R ^ q)) := by gcongr
      _ ≤ sourceS1FarConstant j * (T ^ 8 / R ^ q) := by
        have hNT' : (N : ℝ) * T ^ 5 ≤ T ^ 6 := by
          have hm := mul_le_mul_of_nonneg_right hNT
            (pow_nonneg (show 0 ≤ T by linarith) 5)
          calc
            (N : ℝ) * T ^ 5 ≤ T * T ^ 5 := hm
            _ = T ^ 6 := by ring
        have hN8 : (N : ℝ) * T ^ 5 ≤ T ^ 8 := hNT'.trans hT6to8
        have hRq0 : 0 ≤ R ^ q := pow_nonneg (show 0 ≤ R by linarith) _
        calc
          3 * (8 * T ^ 3) *
                (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j) *
                (4 ^ j * integerQuadraticMass * ((N : ℝ) * T ^ 2 / R ^ q)) =
              sourceS1FarConstant j * ((N : ℝ) * T ^ 5 / R ^ q) := by
                unfold sourceS1FarConstant
                ring
          _ ≤ sourceS1FarConstant j * (T ^ 8 / R ^ q) :=
            mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right hN8 hRq0)
              (sourceS1FarConstant_nonneg j)
  have htailPower' : T ^ 8 / R ^ q ≤ 1 / T ^ 12 := by
    simpa [R, q] using htailPower
  have hCfar0 := sourceS1FarConstant_nonneg j
  have hfarScaled := mul_le_mul_of_nonneg_left hraw
    (show 0 ≤ 3 * (N : ℝ) ^ 3 by positivity)
  change sourceS1FarContribution N W B ≤ _
  calc
    sourceS1FarContribution N W B ≤
        3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
          ((lemma43DerivativeConstant 0 ^ 2 *
              (lemma43DerivativeConstant j * (1 + T) ^ j)) *
            ((1 / (N : ℝ) ^ j) *
              (2 ^ j * ((1 / B ^ q) * integerQuadraticMass)))) := by
      simpa [sourceS1FarContribution, hqj, mul_assoc] using hfarScaled
    _ ≤ sourceS1FarConstant j * (T ^ 8 / R ^ q) := hnormalized
    _ ≤ sourceS1FarConstant j * (1 / T ^ 12) :=
      mul_le_mul_of_nonneg_left htailPower' hCfar0
    _ = sourceS1FarConstant j / T ^ 12 := by ring

def sourceS1Proposition51Constant (epsilon : ℝ) : ℝ :=
  sourceS1FiniteConstant (s1DecayOrder epsilon) +
    sourceS1FarConstant (s1DecayOrder epsilon)

/-- Constant-explicit Guth--Maynard Proposition 5.1 in the exact geometry
used by Proposition 3.1. -/
theorem source_proposition5_1
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (N : ℕ) (W : Finset ℝ), 1 ≤ N →
        let T := Real.rpow (N : ℝ) (6 / 5 : ℝ)
        T₀ ≤ T →
        (W.card : ℝ) ≤ 2 * T →
        (∀ t ∈ W, ∀ u ∈ W, t ≠ u →
          Real.rpow T epsilon ≤ |t-u|) →
        (∀ t ∈ W, ∀ u ∈ W, |t-u| ≤ T) →
        sourceS1TotalContribution N W ≤ Real.rpow T (-10 : ℝ) := by
  let C := sourceS1Proposition51Constant epsilon
  have hC0 : 0 ≤ C := add_nonneg
    (sourceS1FiniteConstant_nonneg _)
    (sourceS1FarConstant_nonneg _)
  let Cpos := C + 1
  obtain ⟨T₀, hT₀, habsorb⟩ := fixedConstant_powTwelve_absorbed_by_powTen Cpos
  refine ⟨Cpos, T₀, by dsimp [Cpos]; linarith, hT₀, ?_⟩
  intro N W hN
  dsimp only
  intro hT hW hsep hdiameter
  have hNnat : 0 < N := by omega
  let T := Real.rpow (N : ℝ) (6 / 5 : ℝ)
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hTone : 1 ≤ T := one_le_sourceT hNreal rfl
  let B := Real.rpow T (1 + epsilon) / (N : ℝ)
  have hBpos : 0 < B := by
    have hb := sourceCutoff_bounds hNreal rfl
      hepsilon.le hepsilonHalf rfl
    exact lt_of_lt_of_le zero_lt_one hb.1
  have hsplit := sourceS1TotalContribution_le_finite_add_far
    hNnat (show 0 ≤ T by linarith) hBpos hdiameter
  have hfin := sourceS1FiniteContribution_le hNnat
    hNreal rfl hepsilon hepsilonHalf hW hsep
  have hfar := sourceS1FarContribution_le hNnat
    hNreal rfl hepsilon hW hdiameter
  have hsum : sourceS1TotalContribution N W ≤ C / T ^ 12 := by
    calc
      sourceS1TotalContribution N W ≤
          sourceS1FiniteContribution N W B +
            sourceS1FarContribution N W B := hsplit
      _ ≤ sourceS1FiniteConstant (s1DecayOrder epsilon) / T ^ 13 +
          sourceS1FarConstant (s1DecayOrder epsilon) / T ^ 12 :=
        add_le_add hfin hfar
      _ ≤ sourceS1FiniteConstant (s1DecayOrder epsilon) / T ^ 12 +
          sourceS1FarConstant (s1DecayOrder epsilon) / T ^ 12 := by
        exact add_le_add
          (div_le_div_of_nonneg_left
            (sourceS1FiniteConstant_nonneg _)
            (pow_pos (lt_of_lt_of_le zero_lt_one hTone) 12)
            (pow_le_pow_right₀ hTone (by omega)))
          le_rfl
      _ = C / T ^ 12 := by
        dsimp [C, sourceS1Proposition51Constant]
        ring
  have hsum' : sourceS1TotalContribution N W ≤ Cpos / T ^ 12 := by
    exact hsum.trans (div_le_div_of_nonneg_right (by dsimp [Cpos]; linarith)
      (pow_nonneg (show 0 ≤ T by linarith) _))
  have hfinal := hsum'.trans (habsorb T hT)
  simpa [Real.rpow_neg (show 0 ≤ T by linarith), Real.rpow_natCast] using! hfinal

end
end GuthMaynardS1Proposition51Endpoint

#print axioms GuthMaynardS1Proposition51Endpoint.sourceS1FiniteContribution_le
#print axioms GuthMaynardS1Proposition51Endpoint.sourceS1FarContribution_le
#print axioms GuthMaynardS1Proposition51Endpoint.source_proposition5_1
