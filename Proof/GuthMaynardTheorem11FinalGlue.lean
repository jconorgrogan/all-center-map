import GuthMaynardClassicalComplement
import GuthMaynardGMGlobalHighActual
import GuthMaynardCriticalTwoPlateauConsumer
import GuthMaynardGMClassicalSmallN

namespace GuthMaynardTheorem11FinalGlue

open scoped BigOperators
open CGLProofDAG
open GuthMaynardClassicalComplement
open GuthMaynardGMGlobalHighActual
open GuthMaynardCriticalTwoPlateauConsumer
open GuthMaynardGMClassicalSmallN
open GuthMaynardSmoothedProp31Consumer

noncomputable section

/-- The four literal ranges cover the GM Theorem 11 interface once the
fixed-weight Proposition 3.1 premise is supplied. -/
theorem guthMaynardTheorem11_of_fixedWeightProp31
    {w : ℝ → ℝ} (hlocal : FixedWeightProp31 w) :
    CGLProofDAG.GuthMaynardTheorem11 := by
  intro η hη
  obtain ⟨Ccomp, Tcomp, hCcomp, hTcomp, hcomp⟩ :=
    guthMaynardTheorem11ClassicalComplement η hη
  obtain ⟨Chigh, Thigh, hChigh, hThigh, hhigh⟩ :=
    guthMaynard_high_range η hη
  obtain ⟨Ccrit, hCcrit, hcrit⟩ :=
    criticalTwoPlateauConsumer hlocal η hη
  let Csmall : ℝ := 2 * (64 : ℝ) ^ 2
  let Cfin : ℝ := Ccomp + Chigh + Ccrit + Csmall
  let Tfin : ℝ := max Tcomp Thigh
  have hCsmall : 0 < Csmall := by
    dsimp [Csmall]
    positivity
  have hCfin : 0 < Cfin := by
    dsimp [Cfin]
    positivity
  have hTfin : 2 ≤ Tfin := by
    dsimp [Tfin]
    exact le_max_of_le_left hTcomp
  refine ⟨Cfin, Tfin, hCfin, hTfin, ?_⟩
  intro T V N b W hT hN hV hb hsep hheight hlarge
  have hTcomp' : Tcomp ≤ T :=
    (le_max_left Tcomp Thigh).trans hT
  have hThigh' : Thigh ≤ T :=
    (le_max_right Tcomp Thigh).trans hT
  have hT1 : 1 ≤ T := by
    have : (2 : ℝ) ≤ T := hTfin.trans hT
    linarith
  have hT0 : 0 ≤ T := by linarith
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := hNreal.trans' (by norm_num)
  have hR : 0 ≤ Real.rpow T η := Real.rpow_nonneg hT0 _
  have hRone : 1 ≤ Real.rpow T η := Real.one_le_rpow hT1 hη.le
  let G : ℝ :=
    (N : ℝ) ^ 2 / V ^ 2 +
      Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 +
      T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4
  have hG : 0 ≤ G := by
    dsimp [G]
    have hV2 : 0 ≤ V ^ 2 := pow_nonneg hV.le _
    have hV4 : 0 ≤ V ^ 4 := pow_nonneg hV.le _
    have h1 : 0 ≤ (N : ℝ) ^ 2 / V ^ 2 :=
      div_nonneg (sq_nonneg _) hV2
    have h2 : 0 ≤ Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 :=
      div_nonneg (Real.rpow_nonneg hNnonneg _) hV4
    have h3 : 0 ≤ T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4 :=
      div_nonneg (mul_nonneg hT0 (Real.rpow_nonneg hNnonneg _)) hV4
    exact add_nonneg (add_nonneg h1 h2) h3
  have hCcomp_le : Ccomp ≤ Cfin := by
    dsimp [Cfin]
    linarith [hChigh, hCcrit, hCsmall]
  have hChigh_le : Chigh ≤ Cfin := by
    dsimp [Cfin]
    linarith [hCcomp, hCcrit, hCsmall]
  have hCcrit_le : Ccrit ≤ Cfin := by
    dsimp [Cfin]
    linarith [hCcomp, hChigh, hCsmall]
  have hCsmall_le : Csmall ≤ Cfin := by
    dsimp [Cfin]
    linarith [hCcomp, hChigh, hCcrit]
  have hbase_absorb {c : ℝ} (hc : c ≤ Cfin)
      (hbound : (W.card : ℝ) ≤ c * Real.rpow T η * G) :
      (W.card : ℝ) ≤ Cfin * Real.rpow T η * G := by
    exact hbound.trans (by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right hc hR
      · exact hG)
  have hsmall_absorb :
      (W.card : ℝ) ≤ Csmall * Real.rpow T η * G →
      (W.card : ℝ) ≤ Cfin * Real.rpow T η * G :=
    hbase_absorb hCsmall_le
  by_cases hNsmall : N < 64
  · have hNN₀ : (N : ℝ) ≤ (64 : ℕ) := by
      exact_mod_cast (Nat.le_of_lt_succ (show N < 65 by omega))
    have hsmall := smallN_largeValue_cardinality_rpow
      (N₀ := 64) (N := N) (T := T) (V := V) (b := b) (W := W)
      (by norm_num) hN hNN₀ hT1 hV hb hsep hheight hlarge
    have hthird :
        T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4 ≤ G := by
      dsimp [G]
      have hV4 : 0 ≤ V ^ 4 := pow_nonneg hV.le _
      have h1 : 0 ≤ (N : ℝ) ^ 2 / V ^ 2 :=
        div_nonneg (sq_nonneg _) (pow_nonneg hV.le _)
      have h2 : 0 ≤ Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 :=
        div_nonneg (Real.rpow_nonneg hNnonneg _) hV4
      calc
        T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4 ≤
            T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4 + 0 := by simp
        _ ≤ T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4 +
            ((N : ℝ) ^ 2 / V ^ 2 +
              Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4) :=
          by
            have hh := add_le_add_left (add_nonneg h1 h2)
              (T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4)
            simpa [add_assoc, add_comm, add_left_comm] using hh
        _ = (N : ℝ) ^ 2 / V ^ 2 +
            Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 +
              T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4 := by ring_nf
    have hsmall0 : 0 ≤ Csmall := le_of_lt hCsmall
    have hsmall' :
        (W.card : ℝ) ≤ Csmall *
          (T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4) := by
      convert hsmall using 1 <;> dsimp [Csmall] <;> norm_num <;> ring
    have hmain : (W.card : ℝ) ≤ Csmall * G :=
      hsmall'.trans (mul_le_mul_of_nonneg_left hthird hsmall0)
    have hmainR : (W.card : ℝ) ≤ Csmall * Real.rpow T η * G := by
      calc
        (W.card : ℝ) ≤ Csmall * G := hmain
        _ ≤ Csmall * Real.rpow T η * G := by
          have hcoef : Csmall ≤ Csmall * Real.rpow T η := by
            calc
              Csmall = Csmall * 1 := by ring
              _ ≤ Csmall * Real.rpow T η :=
                mul_le_mul_of_nonneg_left hRone hsmall0
          exact mul_le_mul_of_nonneg_right hcoef hG
    exact hsmall_absorb hmainR
  · have hN64 : 64 ≤ N := by omega
    by_cases hcompbranch : T ≤ (N : ℝ) ∨
        V ≤ 4 * Real.rpow (N : ℝ) (7 / 10 : ℝ)
    · have hraw := hcomp T V N b W hTcomp' hN hV hb hsep hheight hlarge
        hcompbranch
      have hbound : (W.card : ℝ) ≤ Ccomp * Real.rpow T η * G := by
        simpa [G] using hraw
      exact hbase_absorb hCcomp_le hbound
    · have hNT : (N : ℝ) < T := by
        have : ¬ T ≤ (N : ℝ) := by
          intro h
          exact hcompbranch (Or.inl h)
        exact lt_of_not_ge this
      have hVlow : 4 * Real.rpow (N : ℝ) (7 / 10 : ℝ) ≤ V := by
        have : ¬ V ≤ 4 * Real.rpow (N : ℝ) (7 / 10 : ℝ) := by
          intro h
          exact hcompbranch (Or.inr h)
        exact le_of_not_ge this
      by_cases hcritbranch : V ≤ Real.rpow (N : ℝ) (8 / 10 : ℝ)
      · have hraw := hcrit N T V b W hN64 hNT hV hVlow hcritbranch
          hb hsep hheight hlarge
        have hHG :
            Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 +
              T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4 ≤ G := by
          dsimp [G]
          have hfirst : 0 ≤ (N : ℝ) ^ 2 / V ^ 2 :=
            div_nonneg (sq_nonneg _) (pow_nonneg hV.le _)
          simpa [add_assoc, add_comm, add_left_comm] using
            (le_add_of_nonneg_left hfirst :
              Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 +
                T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4 ≤
                (N : ℝ) ^ 2 / V ^ 2 +
                  (Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 +
                    T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4))
        have hbound : (W.card : ℝ) ≤ Ccrit * Real.rpow T η * G := by
          calc
            (W.card : ℝ) ≤ Ccrit * Real.rpow T η *
                (Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 +
                  T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4) := hraw
            _ ≤ Ccrit * Real.rpow T η * G := by
              exact mul_le_mul_of_nonneg_left hHG
                (mul_nonneg hCcrit.le hR)
        exact hbase_absorb hCcrit_le hbound
      · have hhighbranch : Real.rpow (N : ℝ) (4 / 5 : ℝ) ≤ V := by
          have hcritbranch' : ¬ V ≤ Real.rpow (N : ℝ) (4 / 5 : ℝ) := by
            simpa only [show (4 / 5 : ℝ) = 8 / 10 by norm_num] using hcritbranch
          exact le_of_not_ge hcritbranch'
        have hraw := hhigh T V N b W hThigh' hN hV hhighbranch
          hb hsep hheight hlarge
        have hbound : (W.card : ℝ) ≤ Chigh * Real.rpow T η * G := by
          simpa [G] using hraw
        exact hbase_absorb hChigh_le hbound

end
end GuthMaynardTheorem11FinalGlue

#print axioms GuthMaynardTheorem11FinalGlue.guthMaynardTheorem11_of_fixedWeightProp31
