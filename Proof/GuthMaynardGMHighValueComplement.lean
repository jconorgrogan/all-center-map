import GuthMaynardLemma41Operator
import HuxleyHalaszFront

open scoped BigOperators ComplexConjugate
open CGLProofDAG
open GuthMaynardSectionFourTrace
open MAPJutilaDeterministicCore
open MAPHuxleyHalaszFront

noncomputable section
namespace GuthMaynardGMHighValueComplement

/-! The exact missing analytic input for the classical high-value branch.

The correlation is over the literal dyadic column `(N,2N]`, the literal
smoothed phase `n^(it)`, and the actual one-separated rows in `[0,T]`.  The
factor `N + T*N^3/V^4` is the minimal off-diagonal shape which, after the
finite Halasz front and coefficient energy `O(N)`, yields
`R << T^eta (N^2/V^2 + T*N^4/V^6)`.
-/
def gmHighValueOffDiagonalSource : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T V : ℝ) (N : ℕ) (W : Finset ℝ),
        T₀ ≤ T → 1 ≤ N → 0 < V →
        (N : ℝ) ^ (4 / 5 : ℝ) ≤ V →
        OneSeparated W →
        (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
        ∀ eta : SourceRow W → ℂ,
          (∀ t : SourceRow W, ‖eta t‖ = 1) →
          correlationEnergy (Finset.univ : Finset (SourceRow W))
            (Finset.univ : Finset (SourceColumn N))
            (fun _ : SourceColumn N => 1) eta
            (fun t n => sourcePhase n.1 t.1) ≤
            C * Real.rpow T η *
              ((Finset.univ : Finset (SourceRow W)).card : ℝ) *
                ((N : ℝ) + T * (N : ℝ) ^ 3 / V ^ 4)

/-- The finite Halasz front plus the exact coefficient energy reduction.
This is the strongest branch available without assuming the analytic
off-diagonal estimate itself. -/
theorem gm_high_value_from_offDiagonalSource
    (hoff : gmHighValueOffDiagonalSource) :
    ∀ η : ℝ, 0 < η →
      ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
        ∀ (T V : ℝ) (N : ℕ) (W : Finset ℝ)
          (a : SourceColumn N → ℂ),
          T₀ ≤ T → 1 ≤ N → 0 < V →
          (N : ℝ) ^ (4 / 5 : ℝ) ≤ V →
          OneSeparated W →
          (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
          (∀ t : SourceRow W,
            V ≤ ‖finitePolynomial (Finset.univ : Finset (SourceColumn N)) a
              (fun t n => sourcePhase n.1 t.1) t‖) →
          (coefficientEnergy (Finset.univ : Finset (SourceColumn N)) a) ≤
            (N : ℝ) →
          ((Finset.univ : Finset (SourceRow W)).card : ℝ) ≤
            C * Real.rpow T η *
              ((N : ℝ) ^ 2 / V ^ 2 +
                T * (N : ℝ) ^ 4 / V ^ 6) := by
  intro η hη
  obtain ⟨C₀, T₀, hC₀, hT₀, hoffη⟩ := hoff η hη
  refine ⟨C₀, T₀, hC₀, hT₀, ?_⟩
  intro T V N W a hT hN hV hVhigh hsep hheight hlarge hcoef
  let rows : Finset (SourceRow W) := Finset.univ
  let cols : Finset (SourceColumn N) := Finset.univ
  let v : SourceRow W → SourceColumn N → ℂ :=
    fun t n => sourcePhase n.1 t.1
  have hV0 : 0 ≤ V := hV.le
  have hlarge' : ∀ i ∈ rows, V ≤ ‖finitePolynomial cols a v i‖ := by
    intro i hi
    simpa [rows, cols, v] using hlarge i
  have hfront := finite_halasz_large_value_front rows cols a v V hV0 hlarge'
  obtain ⟨eta, heta, hhalasz⟩ := hfront
  have hcorr := hoffη T V N W hT hN hV hVhigh hsep hheight eta
    (fun t => heta t (by simp [rows]))
  have hcoef0 : 0 ≤ coefficientEnergy cols a := by
    unfold coefficientEnergy
    positivity
  have hcorr0 : 0 ≤ correlationEnergy rows cols
      (fun _ : SourceColumn N => 1) eta v := by
    unfold correlationEnergy
    positivity
  have hupper :
      coefficientEnergy cols a *
          correlationEnergy rows cols (fun _ : SourceColumn N => 1) eta v ≤
        (N : ℝ) *
          (C₀ * Real.rpow T η * (rows.card : ℝ) *
            ((N : ℝ) + T * (N : ℝ) ^ 3 / V ^ 4)) := by
    have hcorr' := hcorr
    simpa [rows, cols, v] using
      (mul_le_mul hcoef hcorr' hcorr0 (by positivity))
  have hfront' :
      ((rows.card : ℝ) * V) ^ 2 ≤
        (N : ℝ) *
          (C₀ * Real.rpow T η * (rows.card : ℝ) *
            ((N : ℝ) + T * (N : ℝ) ^ 3 / V ^ 4)) :=
    hhalasz.trans hupper
  by_cases hrows : rows.card = 0
  · change (rows.card : ℝ) ≤ _
    rw [hrows]
    have hT₀pos : 0 < T₀ := lt_of_lt_of_le (by norm_num) hT₀
    have hTpos : 0 < T := hT₀pos.trans_le hT
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
    have hpowT : 0 ≤ Real.rpow T η := Real.rpow_nonneg hTpos.le _
    have hV2 : 0 < V ^ 2 := sq_pos_of_pos hV
    have hV6 : 0 < V ^ 6 := pow_pos hV 6
    have hterm : 0 ≤ (N : ℝ) ^ 2 / V ^ 2 +
        T * (N : ℝ) ^ 4 / V ^ 6 := by positivity
    simpa using (mul_nonneg (mul_nonneg hC₀.le hpowT) hterm)
  · have hR : 0 < (rows.card : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hrows)
    have hV2 : 0 < V ^ 2 := sq_pos_of_pos hV
    have hV4 : 0 < V ^ 4 := pow_pos hV 4
    have hV6 : 0 < V ^ 6 := pow_pos hV 6
    have hRV :
        (rows.card : ℝ) * V ^ 2 ≤
          C₀ * Real.rpow T η * (N : ℝ) *
            ((N : ℝ) + T * (N : ℝ) ^ 3 / V ^ 4) := by
      apply (le_of_mul_le_mul_left ?_ hR)
      calc
        (rows.card : ℝ) * ((rows.card : ℝ) * V ^ 2) =
            ((rows.card : ℝ) * V) ^ 2 := by ring
        _ ≤ _ := hfront'
        _ = (rows.card : ℝ) *
            (C₀ * Real.rpow T η * (N : ℝ) *
              ((N : ℝ) + T * (N : ℝ) ^ 3 / V ^ 4)) := by ring
    apply le_of_mul_le_mul_right (a0 := hV2)
    calc
      (rows.card : ℝ) * V ^ 2 ≤
          C₀ * Real.rpow T η * (N : ℝ) *
            ((N : ℝ) + T * (N : ℝ) ^ 3 / V ^ 4) := hRV
      _ = C₀ * Real.rpow T η *
          ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) ^ 4 / V ^ 6) * V ^ 2 := by
        field_simp [ne_of_gt hV]
      _ = C₀ * Real.rpow T η *
          ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) ^ 4 / V ^ 6) * V ^ 2 := by
        ring

end GuthMaynardGMHighValueComplement

#print axioms GuthMaynardGMHighValueComplement.gm_high_value_from_offDiagonalSource
