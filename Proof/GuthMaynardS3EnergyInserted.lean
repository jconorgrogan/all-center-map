import GuthMaynardEnergy111Actual
import GuthMaynardS3FixedSeamSubpower
import GuthMaynardS3Assembly

open scoped BigOperators Real
open GuthMaynardHeathBrownInterface
open CGLProofDAG
open GuthMaynardS3LiteralLemma82
open GuthMaynardS3LiteralLemma83Energy
open GuthMaynardEquation55Infinite
open GuthMaynardS3FixedSeamSubpower
open GuthMaynardEnergy111Actual

noncomputable section
namespace GuthMaynardS3EnergyInserted

theorem exists_actual_prop11_2_bound {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 256 ≤ N0 ∧
      ∀ (N : ℕ) (W : Finset ℝ) (T sigma : ℝ) (b : ℕ → ℂ),
        N0 ≤ N → T = (N : ℝ) ^ (6 / 5 : ℝ) → W.Nonempty →
        TEtaSeparated W T eps → ContainedInIntervalOfLength W T →
        (∀ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ≤ 1) →
        (∀ t ∈ W, Real.rpow (N : ℝ) sigma ≤
          ‖dirichletPolynomial b N t‖) →
        ‖sourceS3 N W‖ ≤ C * Real.rpow T eps *
          (T ^ 2 * Real.rpow (W.card : ℝ) (3 / 2 : ℝ) +
            T * (W.card : ℝ) * Real.rpow (N : ℝ) (3 - 2 * sigma) +
            Real.rpow T (9 / 8 : ℝ) *
              Real.rpow (W.card : ℝ) (29 / 16 : ℝ) *
              Real.rpow (N : ℝ) (3 / 2 - sigma) +
            T * (W.card : ℝ) ^ 2 *
              Real.rpow (N : ℝ) (3 / 2 - sigma)) := by
  obtain ⟨Cs, hCs, Ns, hNs, hsource⟩ :=
    sourceS3_fixed_seam_subpower (show 0 < eps / 4 by positivity)
  obtain ⟨Ce, Te, hCe, hTe, henergy⟩ :=
    exists_actual_large_value_energy_bound (show 0 < eps / 4 by positivity)
  let N0 : ℕ := max 256 (max Ns (Nat.ceil Te + 1))
  let C : ℝ := 2 * Cs * (1 + Real.sqrt Ce)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, N0, ?_, ?_⟩
  · dsimp [N0]
    omega
  · intro N W T sigma b hN0 hTdef hWne hsep hcontained hb hlarge
    have hN256 : 256 ≤ N := by
      dsimp [N0] at hN0
      omega
    have hNsN : Ns ≤ N := by
      dsimp [N0] at hN0
      have hX : max Ns (Nat.ceil Te + 1) ≤ N :=
        (Nat.le_max_right 256 _).trans hN0
      exact (Nat.le_max_left _ _).trans hX
    have hTeN : Nat.ceil Te + 1 ≤ N := by
      dsimp [N0] at hN0
      have hX : max Ns (Nat.ceil Te + 1) ≤ N :=
        (Nat.le_max_right 256 _).trans hN0
      exact (Nat.le_max_right _ _).trans hX
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hNpos : 0 < (N : ℝ) := by positivity
    have hT1 : 1 ≤ T := by
      rw [hTdef]
      exact Real.one_le_rpow hN1 (by norm_num)
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
    have hNT : (N : ℝ) ≤ T := by
      rw [hTdef]
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (1 : ℝ) ≤ 6 / 5)
    have hTeT : Te ≤ T := by
      have hceil : Te ≤ (Nat.ceil Te : ℝ) := Nat.le_ceil _
      have hNreal : (Nat.ceil Te : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast hTeN
      linarith
    have hTscale : Real.rpow T (3 / 4 : ℝ) ≤ (N : ℝ) := by
      rw [hTdef]
      have hpow := Real.rpow_le_rpow_of_exponent_le hN1
        (by norm_num : (9 / 10 : ℝ) ≤ 1)
      have heq : Real.rpow (Real.rpow (N : ℝ) (6 / 5 : ℝ))
          (3 / 4 : ℝ) = Real.rpow (N : ℝ) (9 / 10 : ℝ) := by
        calc
          _ = Real.rpow (N : ℝ) ((6 / 5 : ℝ) * (3 / 4 : ℝ)) :=
            (Real.rpow_mul hNpos.le (6 / 5 : ℝ) (3 / 4 : ℝ)).symm
          _ = Real.rpow (N : ℝ) (9 / 10 : ℝ) := by congr 1 <;> norm_num
      calc
        Real.rpow (Real.rpow (N : ℝ) (6 / 5 : ℝ)) (3 / 4 : ℝ) =
            Real.rpow (N : ℝ) (9 / 10 : ℝ) := heq
        _ ≤ (N : ℝ) := by simpa [Real.rpow_one] using hpow
    have hsep1 : OneSeparated W := by
      intro x hx y hy hxy
      have hone : 1 ≤ Real.rpow T eps := Real.one_le_rpow hT1 heps.le
      exact hone.trans (hsep x hx y hy hxy)
    have hsepSmall : TEtaSeparated W T (eps / 4) := by
      intro x hx y hy hxy
      exact (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)).trans
        (hsep x hx y hy hxy)
    have hsourceRaw := hsource N T W hNsN hTdef hsepSmall hcontained
    have henergyRaw := henergy N W T sigma b
      (by exact_mod_cast (show 1 ≤ N by omega)) hTeT hTscale hsep1
      hcontained hb hlarge
    have hRpos : 0 < (W.card : ℝ) := by exact_mod_cast hWne.card_pos
    have hRone : 1 ≤ (W.card : ℝ) := by
      exact_mod_cast (Finset.one_le_card.mpr hWne)
    let E : ℝ := (sourceApproximateAdditiveEnergy W : ℝ)
    let CE' : ℝ := Ce * Real.rpow T (eps / 4)
    let C3 : ℝ := 2 * Cs * Real.rpow T (eps / 4)
    have hCE' : 0 ≤ CE' := by dsimp [CE']; positivity
    have hC3 : 0 ≤ C3 := by dsimp [C3]; positivity
    have henergy' : E ≤ CE' *
        ((W.card : ℝ) * Real.rpow (N : ℝ) (4 - 4 * sigma) +
          Real.rpow (W.card : ℝ) (21 / 8 : ℝ) *
            Real.rpow T (1 / 4 : ℝ) * Real.rpow (N : ℝ) (1 - 2 * sigma) +
          Real.rpow (W.card : ℝ) (3 : ℝ) *
            Real.rpow (N : ℝ) (1 - 2 * sigma)) := by
      dsimp [E, CE']
      exact henergyRaw
    have hsource' : ‖sourceS3 N W‖ ≤ C3 *
        (T ^ 2 * Real.rpow (W.card : ℝ) (3 / 2 : ℝ) +
          T * (N : ℝ) * Real.rpow (W.card : ℝ) (1 / 2 : ℝ) * Real.sqrt E) := by
      have hs := hsourceRaw
      have htailpow : Real.rpow T (-100 : ℝ) ≤
          Real.rpow T (eps / 4 + 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
      have hRpow : 1 ≤ Real.rpow (W.card : ℝ) (3 / 2 : ℝ) :=
        Real.one_le_rpow hRone (by norm_num)
      have htail : Cs * Real.rpow T (-100 : ℝ) ≤
          Cs * Real.rpow T (eps / 4) *
            (T ^ 2 * Real.rpow (W.card : ℝ) (3 / 2 : ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_left htailpow hCs.le
        have hTpow : Real.rpow T (eps / 4 + 2 : ℝ) =
            Real.rpow T (eps / 4) * T ^ 2 := by
          calc
            _ = Real.rpow T (eps / 4) * Real.rpow T (2 : ℝ) :=
              Real.rpow_add hTpos _ _
            _ = Real.rpow T (eps / 4) * T ^ 2 := by
              norm_num [Real.rpow_two]
        rw [hTpow] at hmul
        have hA : 0 ≤ Cs * Real.rpow T (eps / 4) * T ^ 2 := by
          exact mul_nonneg (mul_nonneg hCs.le (Real.rpow_nonneg hTpos.le _))
            (sq_nonneg T)
        have hAR := mul_le_mul_of_nonneg_left hRpow hA
        exact hmul.trans (by
          simpa [mul_assoc] using hAR)
      have hs0 : ‖sourceS3 N W‖ ≤
          Cs * Real.rpow T (eps / 4) *
            (T ^ 2 * Real.rpow (W.card : ℝ) (3 / 2 : ℝ) +
              T * (N : ℝ) * Real.sqrt (W.card : ℝ) * Real.sqrt E) +
            Cs * Real.rpow T (-100 : ℝ) := by
        simpa [E] using hs
      have hsqrtR : Real.sqrt (W.card : ℝ) =
          Real.rpow (W.card : ℝ) (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
      rw [hsqrtR] at hs0
      calc
        ‖sourceS3 N W‖ ≤
            Cs * Real.rpow T (eps / 4) *
              (T ^ 2 * Real.rpow (W.card : ℝ) (3 / 2 : ℝ) +
                T * (N : ℝ) * Real.rpow (W.card : ℝ) (1 / 2 : ℝ) * Real.sqrt E) +
              Cs * Real.rpow T (-100 : ℝ) := hs0
        _ ≤ Cs * Real.rpow T (eps / 4) *
              (T ^ 2 * Real.rpow (W.card : ℝ) (3 / 2 : ℝ) +
                T * (N : ℝ) * Real.rpow (W.card : ℝ) (1 / 2 : ℝ) * Real.sqrt E) +
              Cs * Real.rpow T (eps / 4) *
                (T ^ 2 * Real.rpow (W.card : ℝ) (3 / 2 : ℝ)) := by
          convert add_le_add_left htail
            (Cs * Real.rpow T (eps / 4) *
              (T ^ 2 * Real.rpow (W.card : ℝ) (3 / 2 : ℝ) +
                T * (N : ℝ) * Real.rpow (W.card : ℝ) (1 / 2 : ℝ) * Real.sqrt E)) using 1 <;> ring
        _ ≤ C3 *
              (T ^ 2 * Real.rpow (W.card : ℝ) (3 / 2 : ℝ) +
                T * (N : ℝ) * Real.rpow (W.card : ℝ) (1 / 2 : ℝ) * Real.sqrt E) := by
          let a : ℝ := Cs * T ^ (eps / 4 : ℝ)
          let x : ℝ := T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ)
          let y : ℝ := T * (N : ℝ) * (W.card : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt E
          have hy : 0 ≤ a * y := by dsimp [a, y]; positivity
          have hC3eq : C3 = 2 * a := by
            change 2 * Cs * T ^ (eps / 4 : ℝ) = 2 * (Cs * T ^ (eps / 4 : ℝ))
            ring
          rw [hC3eq]
          change a * (x + y) + a * x ≤ 2 * a * (x + y)
          nlinarith
    have hassembled := GuthMaynardS3Source.proposition11_2_of_10_1_and_11_1
      hTpos hNpos hRpos hC3 hCE' henergy' hsource'
    have hTpow : Real.rpow T (eps / 4) *
        (1 + Real.sqrt CE') ≤ (1 + Real.sqrt Ce) *
          Real.rpow T (eps / 2 : ℝ) := by
      have hsqrt : Real.sqrt CE' = Real.sqrt Ce *
          Real.rpow T (eps / 8 : ℝ) := by
        dsimp [CE']
        rw [Real.sqrt_mul (x := Ce) (show 0 ≤ Ce by positivity)]
        have hsqrtT : Real.sqrt (Real.rpow T (eps / 4)) =
            Real.rpow T (eps / 8) := by
          convert GuthMaynardS3Source.sqrt_rpow (x := T) (a := eps / 4) hTpos.le using 1 <;> ring
        have hmul := congrArg (fun z : ℝ => Real.sqrt Ce * z) hsqrtT
        simpa only [mul_assoc] using hmul
      rw [hsqrt]
      have hδ : 1 ≤ Real.rpow T (eps / 4 : ℝ) :=
        Real.one_le_rpow hT1 (by positivity)
      have h3 : Real.rpow T (3 * eps / 8 : ℝ) ≤
          Real.rpow T (eps / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
      have hsum : Real.rpow T (eps / 4 : ℝ) *
          Real.rpow T (eps / 8 : ℝ) =
          Real.rpow T (3 * eps / 8 : ℝ) := by
        calc
          _ = Real.rpow T ((eps / 4 : ℝ) + (eps / 8 : ℝ)) :=
            (Real.rpow_add hTpos _ _).symm
          _ = Real.rpow T (3 * eps / 8 : ℝ) := by congr 1 <;> ring
      have hhalf : Real.rpow T (eps / 4 : ℝ) ≤
          Real.rpow T (eps / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
      calc
        Real.rpow T (eps / 4 : ℝ) *
            (1 + Real.sqrt Ce * Real.rpow T (eps / 8 : ℝ)) =
            Real.rpow T (eps / 4 : ℝ) +
              Real.sqrt Ce * Real.rpow T (3 * eps / 8 : ℝ) := by
          rw [← hsum]
          ring
        _ ≤ Real.rpow T (eps / 2 : ℝ) +
              Real.sqrt Ce * Real.rpow T (eps / 2 : ℝ) := by
          exact add_le_add hhalf
            (mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _))
        _ = (1 + Real.sqrt Ce) * Real.rpow T (eps / 2 : ℝ) := by ring
    have hfinalpow : Real.rpow T (eps / 2 : ℝ) ≤ Real.rpow T eps :=
      Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    dsimp [C] at ⊢
    calc
      ‖sourceS3 N W‖ ≤ 2 * Cs * Real.rpow T (eps / 4) *
          ((1 + Real.sqrt CE') *
            (T ^ 2 * Real.rpow (W.card : ℝ) (3 / 2 : ℝ) +
              (T * (W.card : ℝ) * Real.rpow (N : ℝ) (3 - 2 * sigma) +
                Real.rpow T (9 / 8 : ℝ) * Real.rpow (W.card : ℝ) (29 / 16 : ℝ) *
                  Real.rpow (N : ℝ) (3 / 2 - sigma) +
                T * (W.card : ℝ) ^ 2 * Real.rpow (N : ℝ) (3 / 2 - sigma)))) := by
        simpa [C3] using hassembled
      _ ≤ 2 * Cs * ((1 + Real.sqrt Ce) * Real.rpow T (eps / 2)) *
          (T ^ 2 * Real.rpow (W.card : ℝ) (3 / 2 : ℝ) +
            (T * (W.card : ℝ) * Real.rpow (N : ℝ) (3 - 2 * sigma) +
              Real.rpow T (9 / 8 : ℝ) * Real.rpow (W.card : ℝ) (29 / 16 : ℝ) *
                Real.rpow (N : ℝ) (3 / 2 - sigma) +
              T * (W.card : ℝ) ^ 2 * Real.rpow (N : ℝ) (3 / 2 - sigma))) := by
        let S : ℝ :=
          T ^ 2 * Real.rpow (W.card : ℝ) (3 / 2 : ℝ) +
            (T * (W.card : ℝ) * Real.rpow (N : ℝ) (3 - 2 * sigma) +
              Real.rpow T (9 / 8 : ℝ) * Real.rpow (W.card : ℝ) (29 / 16 : ℝ) *
                Real.rpow (N : ℝ) (3 / 2 - sigma) +
              T * (W.card : ℝ) ^ 2 * Real.rpow (N : ℝ) (3 / 2 - sigma))
        have hS : 0 ≤ S := by
          dsimp [S]
          positivity
        have hmul := mul_le_mul_of_nonneg_right hTpow hS
        have hmul' := mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ 2 * Cs)
        dsimp [S] at hmul'
        simpa [mul_assoc] using hmul'
      _ ≤ 2 * Cs * (1 + Real.sqrt Ce) * Real.rpow T eps *
          (T ^ 2 * Real.rpow (W.card : ℝ) (3 / 2 : ℝ) +
            (T * (W.card : ℝ) * Real.rpow (N : ℝ) (3 - 2 * sigma) +
              Real.rpow T (9 / 8 : ℝ) * Real.rpow (W.card : ℝ) (29 / 16 : ℝ) *
                Real.rpow (N : ℝ) (3 / 2 - sigma) +
            T * (W.card : ℝ) ^ 2 * Real.rpow (N : ℝ) (3 / 2 - sigma))) := by
        let S : ℝ :=
          T ^ 2 * Real.rpow (W.card : ℝ) (3 / 2 : ℝ) +
            (T * (W.card : ℝ) * Real.rpow (N : ℝ) (3 - 2 * sigma) +
              Real.rpow T (9 / 8 : ℝ) * Real.rpow (W.card : ℝ) (29 / 16 : ℝ) *
                Real.rpow (N : ℝ) (3 / 2 - sigma) +
              T * (W.card : ℝ) ^ 2 * Real.rpow (N : ℝ) (3 / 2 - sigma))
        have hS : 0 ≤ S := by
          dsimp [S]
          positivity
        have hcoef : 2 * Cs * ((1 + Real.sqrt Ce) * Real.rpow T (eps / 2)) ≤
            2 * Cs * (1 + Real.sqrt Ce) * Real.rpow T eps := by
          have hp := mul_le_mul_of_nonneg_right hfinalpow
            (by positivity : 0 ≤ 1 + Real.sqrt Ce)
          have hp' := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * Cs)
          calc
            2 * Cs * ((1 + Real.sqrt Ce) * Real.rpow T (eps / 2)) =
                2 * Cs * (Real.rpow T (eps / 2) * (1 + Real.sqrt Ce)) := by ring
            _ ≤ 2 * Cs * (Real.rpow T eps * (1 + Real.sqrt Ce)) := hp'
            _ = 2 * Cs * (1 + Real.sqrt Ce) * Real.rpow T eps := by ring
        dsimp [S]
        exact mul_le_mul_of_nonneg_right hcoef hS
      _ = _ := by
        change 2 * Cs * (1 + Real.sqrt Ce) * T ^ eps *
          (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
            (T * (W.card : ℝ) * (N : ℝ) ^ (3 - 2 * sigma : ℝ) +
              T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) *
                (N : ℝ) ^ (3 / 2 - sigma : ℝ) +
              T * (W.card : ℝ) ^ 2 * (N : ℝ) ^ (3 / 2 - sigma : ℝ))) =
          2 * Cs * (1 + Real.sqrt Ce) * T ^ eps *
          (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
            T * (W.card : ℝ) * (N : ℝ) ^ (3 - 2 * sigma : ℝ) +
              T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) *
                (N : ℝ) ^ (3 / 2 - sigma : ℝ) +
              T * (W.card : ℝ) ^ 2 * (N : ℝ) ^ (3 / 2 - sigma : ℝ))
        ring

end GuthMaynardS3EnergyInserted

#print axioms GuthMaynardS3EnergyInserted.exists_actual_prop11_2_bound
