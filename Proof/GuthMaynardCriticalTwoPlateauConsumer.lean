import GuthMaynardTwoPlateauTimeConsumer

/-!
# Critical-range corollary of the two-plateau time consumer

This file only performs the finite algebra after the fixed-weight local
Proposition 3.1 premise.  In the range `N < T` and
`4 N^(7/10) ≤ V ≤ N^(8/10)`, the two local pieces are bounded by the printed
`N^(18/5)/V^4 + T N^(12/5)/V^4` shape.  The analytic fixed-weight premise is
left conditional, and no global theorem is asserted.
-/

namespace GuthMaynardCriticalTwoPlateauConsumer

open CGLProofDAG
open GuthMaynardJutilaReflection2941
open GuthMaynardTwoPlateauSmoothingBridge
open GuthMaynardSmoothedProp31Consumer
open GuthMaynardTwoPlateauTimeConsumer

noncomputable section

def rawPiece (C ε T V M : ℝ) : ℝ :=
  (1 + 2 * (T / Real.rpow M (6 / 5 : ℝ))) *
    (3 * Real.rpow (Real.rpow M (6 / 5 : ℝ)) ε *
      (C * Real.rpow (Real.rpow M (6 / 5 : ℝ)) ε *
        (Real.rpow M (6 / 5 : ℝ) * Real.rpow M (12 / 5 : ℝ) /
          (V / 2) ^ 4)))

private theorem rawPiece_eq
    {C η T V M : ℝ} (hC : 0 ≤ C) (hη : 0 < η)
    (hM : 0 < M) (hT : 0 < T) (hV : 0 < V) :
    rawPiece C (5 * η / 12) T V M =
      48 * C * Real.rpow M η *
        (Real.rpow M (18 / 5 : ℝ) +
          2 * T * Real.rpow M (12 / 5 : ℝ)) / V ^ 4 := by
  let L : ℝ := Real.rpow M (6 / 5 : ℝ)
  have hM0 : 0 ≤ M := hM.le
  have hL : 0 < L := by
    dsimp [L]
    positivity
  have hLpow :
      Real.rpow L (5 * η / 12) * Real.rpow L (5 * η / 12) =
        Real.rpow M η := by
    calc
      _ = Real.rpow L (5 * η / 12 + 5 * η / 12) := by
        exact (Real.rpow_add hL (5 * η / 12) (5 * η / 12)).symm
      _ = Real.rpow L (5 * η / 6) := by congr 1 <;> ring
      _ = Real.rpow M ((6 / 5 : ℝ) * (5 * η / 6)) := by
        dsimp [L]
        exact (Real.rpow_mul hM0 (6 / 5 : ℝ) (5 * η / 6)).symm
      _ = Real.rpow M η := by congr 1 <;> ring
  have hMpow :
      Real.rpow M (6 / 5 : ℝ) * Real.rpow M (12 / 5 : ℝ) =
        Real.rpow M (18 / 5 : ℝ) := by
    calc
      _ = Real.rpow M ((6 / 5 : ℝ) + (12 / 5 : ℝ)) :=
        (Real.rpow_add hM (6 / 5 : ℝ) (12 / 5 : ℝ)).symm
      _ = _ := by congr 1 <;> norm_num
  have hMpow' : M ^ (6 / 5 : ℝ) * M ^ (12 / 5 : ℝ) =
      M ^ (18 / 5 : ℝ) := by simpa using hMpow
  have hV4 : 0 < V ^ 4 := pow_pos hV _
  have hLne : L ≠ 0 := ne_of_gt hL
  have hVne : V ≠ 0 := ne_of_gt hV
  have hM6ne : Real.rpow M (6 / 5 : ℝ) ≠ 0 := by positivity
  have hLpow' :
      Real.rpow (Real.rpow M (6 / 5 : ℝ)) (5 * η / 12) *
          Real.rpow (Real.rpow M (6 / 5 : ℝ)) (5 * η / 12) =
        Real.rpow M η := by
    simpa [L] using hLpow
  have hmid : rawPiece C (5 * η / 12) T V M =
      48 * C * Real.rpow M η *
        (Real.rpow M (6 / 5 : ℝ) * Real.rpow M (12 / 5 : ℝ) +
          2 * T * Real.rpow M (12 / 5 : ℝ)) / V ^ 4 := by
    unfold rawPiece
    rw [← hLpow']
    field_simp [hLne, hM6ne, hVne]
    ring
  calc
    rawPiece C (5 * η / 12) T V M = _ := hmid
    _ = _ := by rw [hMpow]

private theorem rawPiece_le_target
    {C η T V M N : ℝ} (hC : 0 ≤ C) (hη : 0 < η)
    (hT : 0 < T) (hV : 0 < V)
    (hM : 0 < M) (hMN : M ≤ 2 * N) (hMT : M ≤ 2 * T)
    (hN : 0 ≤ N) :
    rawPiece C (5 * η / 12) T V M ≤
      1536 * C * Real.rpow 2 η * Real.rpow T η *
        (Real.rpow N (18 / 5 : ℝ) / V ^ 4 +
          T * Real.rpow N (12 / 5 : ℝ) / V ^ 4) := by
  have hraw := rawPiece_eq hC hη hM hT hV
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  have h2T : 0 ≤ 2 * T := by positivity
  have hMη : Real.rpow M η ≤ Real.rpow (2 * T) η :=
    Real.rpow_le_rpow hM.le hMT hη.le
  have hMη' : Real.rpow M η ≤ Real.rpow 2 η * Real.rpow T η := by
    calc
      Real.rpow M η ≤ Real.rpow (2 * T) η := hMη
      _ = Real.rpow 2 η * Real.rpow T η := by
        exact Real.mul_rpow h2 hT.le
  have hM18 : Real.rpow M (18 / 5 : ℝ) ≤
      Real.rpow 2 (18 / 5 : ℝ) * Real.rpow N (18 / 5 : ℝ) := by
    calc
      _ ≤ Real.rpow (2 * N) (18 / 5 : ℝ) :=
        Real.rpow_le_rpow hM.le hMN (by norm_num)
      _ = Real.rpow 2 (18 / 5 : ℝ) * Real.rpow N (18 / 5 : ℝ) :=
        Real.mul_rpow h2 hN
  have hM12 : Real.rpow M (12 / 5 : ℝ) ≤
      Real.rpow 2 (12 / 5 : ℝ) * Real.rpow N (12 / 5 : ℝ) := by
    calc
      _ ≤ Real.rpow (2 * N) (12 / 5 : ℝ) :=
        Real.rpow_le_rpow hM.le hMN (by norm_num)
      _ = Real.rpow 2 (12 / 5 : ℝ) * Real.rpow N (12 / 5 : ℝ) :=
        Real.mul_rpow h2 hN
  have hA : 0 ≤ Real.rpow N (18 / 5 : ℝ) / V ^ 4 := by
    exact div_nonneg (Real.rpow_nonneg hN _) (pow_nonneg hV.le _)
  have hB : 0 ≤ T * Real.rpow N (12 / 5 : ℝ) / V ^ 4 := by
    exact div_nonneg (mul_nonneg hT.le (Real.rpow_nonneg hN _))
      (pow_nonneg hV.le _)
  have hpow2 : Real.rpow 2 (18 / 5 : ℝ) ≤ 32 := by
    calc
      Real.rpow 2 (18 / 5 : ℝ) ≤ Real.rpow 2 5 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 32 := by norm_num [Real.rpow_natCast]
  have hpow12 : Real.rpow 2 (12 / 5 : ℝ) ≤ 16 := by
    calc
      Real.rpow 2 (12 / 5 : ℝ) ≤ Real.rpow 2 4 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 16 := by norm_num [Real.rpow_natCast]
  have hmain :
      Real.rpow M η *
          (Real.rpow M (18 / 5 : ℝ) +
            2 * T * Real.rpow M (12 / 5 : ℝ)) / V ^ 4 ≤
        32 * Real.rpow 2 η * Real.rpow T η *
          (Real.rpow N (18 / 5 : ℝ) / V ^ 4 +
            T * Real.rpow N (12 / 5 : ℝ) / V ^ 4) := by
    have hleft :
        Real.rpow M η *
            (Real.rpow M (18 / 5 : ℝ) +
              2 * T * Real.rpow M (12 / 5 : ℝ)) / V ^ 4 ≤
          (Real.rpow 2 η * Real.rpow T η) *
            (32 * Real.rpow N (18 / 5 : ℝ) +
              2 * T * (16 * Real.rpow N (12 / 5 : ℝ))) / V ^ 4 := by
      have hterm18 :
          Real.rpow M η * Real.rpow M (18 / 5 : ℝ) ≤
            (Real.rpow 2 η * Real.rpow T η) *
              (32 * Real.rpow N (18 / 5 : ℝ)) := by
        have hM18' := hM18.trans
          (mul_le_mul_of_nonneg_right hpow2 (Real.rpow_nonneg hN _))
        have hq : 0 ≤ Real.rpow 2 η * Real.rpow T η :=
          mul_nonneg (Real.rpow_nonneg h2 η)
            (Real.rpow_nonneg hT.le η)
        have hbd : 0 ≤ 32 * Real.rpow N (18 / 5 : ℝ) :=
          mul_nonneg (by norm_num) (Real.rpow_nonneg hN _)
        have hfirst := mul_le_mul hMη' hM18'
          (Real.rpow_nonneg hM.le _)
          hq
        exact hfirst
      have hterm12 :
          Real.rpow M η * (2 * T * Real.rpow M (12 / 5 : ℝ)) ≤
            (Real.rpow 2 η * Real.rpow T η) *
              (2 * T * (16 * Real.rpow N (12 / 5 : ℝ))) := by
        have hM12' := hM12.trans
          (mul_le_mul_of_nonneg_right hpow12 (Real.rpow_nonneg hN _))
        have hq : 0 ≤ Real.rpow 2 η * Real.rpow T η :=
          mul_nonneg (Real.rpow_nonneg h2 η)
            (Real.rpow_nonneg hT.le η)
        have hbd : 0 ≤ 16 * Real.rpow N (12 / 5 : ℝ) :=
          mul_nonneg (by norm_num) (Real.rpow_nonneg hN _)
        have hbase := mul_le_mul hMη' hM12'
          (Real.rpow_nonneg hM.le _)
          hq
        have hthird := mul_le_mul_of_nonneg_right hbase h2T
        simpa [mul_assoc, mul_left_comm, mul_comm] using hthird
      have hnum :
          Real.rpow M η *
              (Real.rpow M (18 / 5 : ℝ) +
                2 * T * Real.rpow M (12 / 5 : ℝ)) ≤
            (Real.rpow 2 η * Real.rpow T η) *
              (32 * Real.rpow N (18 / 5 : ℝ) +
                2 * T * (16 * Real.rpow N (12 / 5 : ℝ))) := by
        convert add_le_add hterm18 hterm12 using 1 <;> ring
      exact div_le_div_of_nonneg_right hnum (pow_nonneg hV.le _)
    have hcoef :
        (Real.rpow 2 η * Real.rpow T η) *
            (32 * Real.rpow N (18 / 5 : ℝ) +
              2 * T * (16 * Real.rpow N (12 / 5 : ℝ))) / V ^ 4 =
          32 * Real.rpow 2 η * Real.rpow T η *
            (Real.rpow N (18 / 5 : ℝ) / V ^ 4 +
              T * Real.rpow N (12 / 5 : ℝ) / V ^ 4) := by ring
    exact hleft.trans_eq hcoef
  calc
    rawPiece C (5 * η / 12) T V M =
        48 * C * (Real.rpow M η *
          (Real.rpow M (18 / 5 : ℝ) +
            2 * T * Real.rpow M (12 / 5 : ℝ)) / V ^ 4) := by
      convert hraw using 1 <;> ring
    _ ≤ 48 * C * (32 * Real.rpow 2 η * Real.rpow T η *
          (Real.rpow N (18 / 5 : ℝ) / V ^ 4 +
            T * Real.rpow N (12 / 5 : ℝ) / V ^ 4)) := by
      exact mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = 1536 * C * Real.rpow 2 η * Real.rpow T η *
          (Real.rpow N (18 / 5 : ℝ) / V ^ 4 +
            T * Real.rpow N (12 / 5 : ℝ) / V ^ 4) := by ring

theorem criticalTwoPlateauConsumer
    {w : ℝ → ℝ} (hlocal : FixedWeightProp31 w) :
    ∀ η : ℝ, 0 < η →
      ∃ C : ℝ, 0 < C ∧
        ∀ (N : ℕ) (T V : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
          64 ≤ N → (N : ℝ) < T → 0 < V →
          4 * Real.rpow (N : ℝ) (7 / 10 : ℝ) ≤ V →
          V ≤ Real.rpow (N : ℝ) (8 / 10 : ℝ) →
          (∀ n, ‖a n‖ ≤ 1) → OneSeparated W →
          (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
          (∀ t ∈ W, V ≤ ‖dirichletPolynomial a N t‖) →
          (W.card : ℝ) ≤ C * Real.rpow T η *
            (Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 +
              T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4) := by
  intro η hη
  have hε : 0 < 5 * η / 12 := by positivity
  obtain ⟨C₀, hC₀, hconsumer⟩ :=
    twoPlateauTimeConsumer hlocal (5 * η / 12) hε
  let C : ℝ := 3072 * C₀ * Real.rpow 2 η
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro N T V a W hN hNT hV hVlow hVhigh ha hsep hheight hlarge
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
    have hTpos : 0 < T := hNpos.trans hNT
    have hT0 : 0 ≤ T := hTpos.le
    have htime := hconsumer N T V a W hN hT0 hV hVlow hVhigh ha hsep
      hheight hlarge
    let M₁ : ℝ := localN1 N
    let M₂ : ℝ := localN2 N
    have hM1pos : 0 < M₁ := by
      have : 1 ≤ localN1 N := by unfold localN1; omega
      dsimp [M₁]
      exact_mod_cast (show 0 < localN1 N by omega)
    have hM2pos : 0 < M₂ := by
      have : 1 ≤ localN2 N := by unfold localN2; omega
      dsimp [M₂]
      exact_mod_cast (show 0 < localN2 N by omega)
    have hM1N : M₁ ≤ 2 * (N : ℝ) := by
      dsimp [M₁]
      exact_mod_cast (localN1_scale (le_trans (by norm_num) hN)).2
    have hM2N : M₂ ≤ 2 * (N : ℝ) := by
      dsimp [M₂]
      exact_mod_cast (localN2_scale (le_trans (by norm_num) hN)).2
    have hM1T : M₁ ≤ 2 * T := by
      have hscale := localN1_scale (le_trans (by norm_num) hN)
      have hcast : M₁ ≤ 2 * (N : ℝ) := hM1N
      nlinarith
    have hM2T : M₂ ≤ 2 * T := by
      have hscale := localN2_scale (le_trans (by norm_num) hN)
      have hcast : M₂ ≤ 2 * (N : ℝ) := hM2N
      nlinarith
    have hp1 := rawPiece_le_target (C := C₀) hC₀.le hη hTpos hV
      hM1pos hM1N hM1T hN0
    have hp2 := rawPiece_le_target (C := C₀) hC₀.le hη hTpos hV
      hM2pos hM2N hM2T hN0
    have htime' : (W.card : ℝ) ≤ rawPiece C₀ (5 * η / 12) T V M₁ +
        rawPiece C₀ (5 * η / 12) T V M₂ := by
      simpa [rawPiece, M₁, M₂] using htime
    have hsum := add_le_add hp1 hp2
    dsimp [C]
    calc
      (W.card : ℝ) ≤ rawPiece C₀ (5 * η / 12) T V M₁ +
          rawPiece C₀ (5 * η / 12) T V M₂ := htime'
      _ ≤ 2 * (1536 * C₀ * Real.rpow 2 η * Real.rpow T η) *
          (Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 +
            T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4) := by
        exact hsum.trans_eq (by ring)
      _ = C * Real.rpow T η *
          (Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 +
            T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4) := by
        dsimp [C]
        ring

end
end GuthMaynardCriticalTwoPlateauConsumer

#print axioms GuthMaynardCriticalTwoPlateauConsumer.criticalTwoPlateauConsumer
