import RecenteredSampling
import CGLProofDAG

/-!
# Classical complements for the literal GM Theorem 11 interface

`RecenteredSampling.discreteDirichletMeanValue` is unconditional and gives
the exact elementary large-value count

`R ≤ C T^η (N² + T*N) / V²`.

This file records the two ranges where that count implies the published
three-term shape.  It does not claim the remaining range `N < T` and
`4*N^(7/10) < V`; that is the nonclassical large-value problem.
-/

namespace GuthMaynardClassicalComplement

open scoped BigOperators
open CGLProofDAG

noncomputable section

/-- The actual classical complement of the literal GM Theorem 11 target:
either `N ≥ T`, with arbitrary positive `V`, or the low-value range
`V ≤ 4*N^(7/10)`, with arbitrary `T`. -/
def GuthMaynardTheorem11ClassicalComplement : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T V : ℝ) (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 1 ≤ N → 0 < V →
        (∀ n, ‖b n‖ ≤ 1) →
        OneSeparated W →
        (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
        (∀ t ∈ W, V ≤ ‖dirichletPolynomial b N t‖) →
        (T ≤ (N : ℝ) ∨ V ≤ 4 * Real.rpow (N : ℝ) (7 / 10 : ℝ)) →
        (W.card : ℝ) ≤ C * Real.rpow T η *
          ((N : ℝ) ^ 2 / V ^ 2 +
            Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 +
            T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4)

/-- The unconditional recentered-sampling mean-value theorem supplies the
classical complement with the literal polynomial, coefficient, and spacing
interfaces unchanged. -/
theorem guthMaynardTheorem11ClassicalComplement :
    GuthMaynardTheorem11ClassicalComplement := by
  intro η hη
  obtain ⟨C₀, T₀, hC₀, hT₀, hmean⟩ :=
    DiscreteMeanValueSourceLeaf.discreteLargeValue_of_meanSquare
      (RecenteredSampling.discreteDirichletMeanSquare_of_hilbert
        MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert)
      η hη
  refine ⟨16 * C₀, T₀, by positivity, hT₀, ?_⟩
  intro T V N b W hT hN hV hb hsep hheight hlarge hbranch
  have hraw := hmean T V N b W hT hN hV hb hsep hheight hlarge
  have hT0 : 0 ≤ T := by linarith
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hV2 : 0 < V ^ 2 := sq_pos_of_pos hV
  have hV4 : 0 < V ^ 4 := pow_pos hV 4
  have hNpow : 0 ≤ Real.rpow (N : ℝ) (12 / 5 : ℝ) :=
    Real.rpow_nonneg hN0 _
  have hNpow18 : 0 ≤ Real.rpow (N : ℝ) (18 / 5 : ℝ) :=
    Real.rpow_nonneg hN0 _
  have hN2 : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
  have hterm1 : 0 ≤ (N : ℝ) ^ 2 / V ^ 2 :=
    div_nonneg hN2 hV2.le
  have hterm2 : 0 ≤ Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 :=
    div_nonneg hNpow18 hV4.le
  have hterm3 : 0 ≤ T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4 :=
    div_nonneg (mul_nonneg hT0 hNpow) hV4.le
  have hshape :
      ((N : ℝ) ^ 2 + T * (N : ℝ)) / V ^ 2 ≤
        16 * ((N : ℝ) ^ 2 / V ^ 2 +
          Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 +
          T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4) := by
    rcases hbranch with hNT | hVlow
    · have hTN : T * (N : ℝ) ≤ (N : ℝ) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hNT hN0]
      have hsum :
          ((N : ℝ) ^ 2 + T * (N : ℝ)) / V ^ 2 ≤
            2 * ((N : ℝ) ^ 2 / V ^ 2) := by
        rw [show 2 * ((N : ℝ) ^ 2 / V ^ 2) =
          (2 * (N : ℝ) ^ 2) / V ^ 2 by ring]
        apply (div_le_div_iff_of_pos_right hV2).2
        nlinarith [hTN]
      have hdom :
          2 * ((N : ℝ) ^ 2 / V ^ 2) ≤
            16 * ((N : ℝ) ^ 2 / V ^ 2 +
              Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 +
              T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4) := by
        nlinarith [hterm1, hterm2, hterm3]
      exact hsum.trans hdom
    · have hVsq : V ^ 2 ≤ 16 * Real.rpow (N : ℝ) (7 / 5 : ℝ) := by
        have hmul := mul_self_le_mul_self hV.le hVlow
        calc
          V ^ 2 = V * V := by ring
          _ ≤ (4 * Real.rpow (N : ℝ) (7 / 10 : ℝ)) *
              (4 * Real.rpow (N : ℝ) (7 / 10 : ℝ)) := hmul
          _ = 16 * (Real.rpow (N : ℝ) (7 / 10 : ℝ) *
              Real.rpow (N : ℝ) (7 / 10 : ℝ)) := by ring
          _ = 16 * Real.rpow (N : ℝ) (7 / 5 : ℝ) := by
            calc
              16 * (Real.rpow (N : ℝ) (7 / 10 : ℝ) *
                  Real.rpow (N : ℝ) (7 / 10 : ℝ)) =
                  16 * Real.rpow (N : ℝ) (7 / 10 + 7 / 10 : ℝ) := by
                    exact congrArg (fun x : ℝ => 16 * x)
                      (Real.rpow_add hNpos _ _).symm
              _ = 16 * Real.rpow (N : ℝ) (7 / 5 : ℝ) := by
                    congr 2
                    norm_num
      have hTNdom :
          T * (N : ℝ) / V ^ 2 ≤
            16 * (T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4) := by
        have hNpow72 :
            (N : ℝ) * V ^ 2 ≤
              16 * (N : ℝ) * Real.rpow (N : ℝ) (7 / 5 : ℝ) := by
          calc
            (N : ℝ) * V ^ 2 ≤
                (N : ℝ) * (16 * Real.rpow (N : ℝ) (7 / 5 : ℝ)) :=
              mul_le_mul_of_nonneg_left hVsq hN0
            _ = 16 * (N : ℝ) * Real.rpow (N : ℝ) (7 / 5 : ℝ) := by ring
        have hpowmul :
            (N : ℝ) * Real.rpow (N : ℝ) (7 / 5 : ℝ) =
              Real.rpow (N : ℝ) (12 / 5 : ℝ) := by
          calc
            (N : ℝ) * Real.rpow (N : ℝ) (7 / 5 : ℝ) =
                Real.rpow (N : ℝ) 1 * Real.rpow (N : ℝ) (7 / 5 : ℝ) := by
                  have hN1 : Real.rpow (N : ℝ) 1 = (N : ℝ) := by
                    norm_num [Real.rpow_natCast]
                  rw [hN1]
            _ = Real.rpow (N : ℝ) (1 + 7 / 5 : ℝ) :=
              (Real.rpow_add hNpos _ _).symm
            _ = Real.rpow (N : ℝ) (12 / 5 : ℝ) := by congr 1 <;> norm_num
        have hcore :
            T * (N : ℝ) * V ^ 2 ≤
              16 * T * Real.rpow (N : ℝ) (12 / 5 : ℝ) := by
          calc
            T * (N : ℝ) * V ^ 2 ≤
                T * (16 * (N : ℝ) * Real.rpow (N : ℝ) (7 / 5 : ℝ)) := by
                  simpa [mul_assoc, mul_left_comm, mul_comm] using
                    (mul_le_mul_of_nonneg_right hNpow72 hT0)
            _ = 16 * T * ((N : ℝ) * Real.rpow (N : ℝ) (7 / 5 : ℝ)) := by ring
            _ = 16 * T * Real.rpow (N : ℝ) (12 / 5 : ℝ) := by rw [hpowmul]
        calc
          T * (N : ℝ) / V ^ 2 ≤
              (16 * T * Real.rpow (N : ℝ) (12 / 5 : ℝ)) / V ^ 4 := by
                apply (div_le_div_iff₀ hV2 hV4).2
                calc
                  T * (N : ℝ) * V ^ 4 =
                      (T * (N : ℝ) * V ^ 2) * V ^ 2 := by ring
                  _ ≤ (16 * T * Real.rpow (N : ℝ) (12 / 5 : ℝ)) * V ^ 2 :=
                    mul_le_mul_of_nonneg_right hcore hV2.le
          _ = 16 * (T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4) := by
                field_simp [ne_of_gt hV]
      calc
        ((N : ℝ) ^ 2 + T * (N : ℝ)) / V ^ 2 =
            (N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) / V ^ 2 := by
              rw [add_div]
        _ ≤ (N : ℝ) ^ 2 / V ^ 2 +
            16 * (T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4) := by
              nlinarith [hTNdom]
        _ ≤ 16 * ((N : ℝ) ^ 2 / V ^ 2 +
          Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 +
          T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4) := by
            nlinarith [hterm1, hterm2]
  calc
    (W.card : ℝ) ≤ C₀ * Real.rpow T η *
        (((N : ℝ) ^ 2 + T * (N : ℝ)) / V ^ 2) := hraw
    _ ≤ C₀ * Real.rpow T η *
        (16 * ((N : ℝ) ^ 2 / V ^ 2 +
          Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 +
          T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4)) := by
      exact mul_le_mul_of_nonneg_left hshape
        (mul_nonneg hC₀.le (Real.rpow_nonneg hT0 η))
    _ = 16 * C₀ * Real.rpow T η *
        ((N : ℝ) ^ 2 / V ^ 2 +
          Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 +
          T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4) := by ring

end
end GuthMaynardClassicalComplement

#print axioms GuthMaynardClassicalComplement.guthMaynardTheorem11ClassicalComplement
