import CGLProofDAG
import JutilaGappedCollarSelectedP53Adapter

/-!
# Low-height charging for the principal selected collar

A one-separated ordinate set in `|t| ≤ H` has cardinality at most `2H+1`.
This is a finite packing lemma; it introduces no zero-density or contour
input, and retains the selected set's image-card hypothesis.
-/

namespace MAPJutilaPrincipalLowHeightCharge

open scoped BigOperators
open Complex Real
open CGLProofDAG
open MAPJutilaGappedCollarFiniteAggregation
open MAPJutilaGappedCollarSelectedP53Adapter

noncomputable section

/-- One-separated packing in a closed height window. -/
theorem oneSeparated_card_le_of_abs_le
    {W : Finset ℝ} {H : ℝ} (hH : 0 ≤ H)
    (hsep : OneSeparated W) (hW : ∀ t ∈ W, |t| ≤ H) :
    (W.card : ℝ) ≤ 2 * H + 1 := by
  classical
  rcases W.eq_empty_or_nonempty with hempty | hne
  · subst W
    have : (0 : ℝ) ≤ 2 * H + 1 := by linarith
    simpa using this
  · let tmin := W.min' hne
    have htmin : tmin ∈ W := W.min'_mem hne
    have hmin : ∀ t ∈ W, tmin ≤ t := fun t ht => W.min'_le t ht
    have hinj : Set.InjOn (fun t : ℝ => Int.floor (t - tmin)) (W : Set ℝ) := by
      intro t ht u hu hfloor
      by_contra htu
      have hsep' : 1 ≤ |t - u| := hsep t ht u hu htu
      have hx : t - tmin < (Int.floor (t - tmin) : ℝ) + 1 :=
        Int.lt_floor_add_one _
      have hy : (Int.floor (u - tmin) : ℝ) ≤ u - tmin := Int.floor_le _
      have hx' : u - tmin < (Int.floor (u - tmin) : ℝ) + 1 :=
        Int.lt_floor_add_one _
      have hy' : (Int.floor (t - tmin) : ℝ) ≤ t - tmin := Int.floor_le _
      have hfloor' : Int.floor (t - tmin) = Int.floor (u - tmin) := hfloor
      have htu1 : t - u < 1 := by
        have : t - tmin - (u - tmin) <
            (Int.floor (t - tmin) : ℝ) + 1 -
              (Int.floor (u - tmin) : ℝ) := by
          linarith
        rw [hfloor'] at this
        linarith
      have hut1 : u - t < 1 := by
        have : u - tmin - (t - tmin) <
            (Int.floor (u - tmin) : ℝ) + 1 -
              (Int.floor (t - tmin) : ℝ) := by
          linarith
        rw [hfloor'] at this
        linarith
      have : |t - u| < 1 := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
      linarith
    have himage :
        W.image (fun t : ℝ => Int.floor (t - tmin)) ⊆
          Finset.Icc (0 : ℤ) ⌊2 * H⌋ := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨t, ht, rfl⟩
      have ht0 : 0 ≤ t - tmin := sub_nonneg.mpr (hmin t ht)
      have htH : t - tmin ≤ 2 * H := by
        have htAbs := abs_le.mp (hW t ht)
        have hminAbs := abs_le.mp (hW tmin htmin)
        linarith
      have hfloor0 : 0 ≤ Int.floor (t - tmin) := Int.floor_nonneg.mpr ht0
      have hfloorHi : Int.floor (t - tmin) ≤ ⌊2 * H⌋ :=
        Int.floor_le_floor htH
      exact Finset.mem_Icc.mpr ⟨hfloor0, hfloorHi⟩
    have hcardEq :
        (W.image (fun t : ℝ => Int.floor (t - tmin))).card = W.card :=
      Finset.card_image_of_injOn hinj
    have hIcc :
        ((Finset.Icc (0 : ℤ) ⌊2 * H⌋).card : ℝ) ≤ 2 * H + 1 := by
      have hnn : (0 : ℤ) ≤ ⌊2 * H⌋ := Int.floor_nonneg.mpr (by linarith)
      have hnn1 : 0 ≤ ⌊2 * H⌋ + 1 := by linarith
      have hcard : (Finset.Icc (0 : ℤ) ⌊2 * H⌋).card =
          (⌊2 * H⌋ + 1 - 0).toNat := Int.card_Icc 0 ⌊2 * H⌋
      have hto : ((⌊2 * H⌋ + 1).toNat : ℝ) = (⌊2 * H⌋ : ℝ) + 1 := by
        exact_mod_cast (Int.toNat_of_nonneg hnn1)
      have hfloorLe : (⌊2 * H⌋ : ℝ) ≤ 2 * H := Int.floor_le _
      calc
        ((Finset.Icc (0 : ℤ) ⌊2 * H⌋).card : ℝ) =
            ((⌊2 * H⌋ + 1).toNat : ℝ) := by
          rw [hcard]
          simp
        _ = (⌊2 * H⌋ : ℝ) + 1 := hto
        _ ≤ 2 * H + 1 := by linarith
    have hle : (W.card : ℝ) ≤
        ((Finset.Icc (0 : ℤ) ⌊2 * H⌋).card : ℝ) := by
      rw [← hcardEq]
      exact_mod_cast Finset.card_le_card himage
    exact hle.trans hIcc

/-- Low-height selected zeros are charged by one-separation alone. -/
theorem lowHeight_selected_card_le
    {W : Finset ℂ} {H : ℝ} (hH : 0 ≤ H)
    (hsep : OneSeparated (W.image Complex.im))
    (hcard : (W.image Complex.im).card = W.card)
    (hW : ∀ rho ∈ W, |rho.im| ≤ H) :
    (W.card : ℝ) ≤ 2 * H + 1 := by
  have him : ∀ t ∈ W.image Complex.im, |t| ≤ H := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨rho, hrho, rfl⟩
    exact hW rho hrho
  have hbound := oneSeparated_card_le_of_abs_le hH hsep him
  simpa [hcard] using hbound

/-- Source-scale form used by the selected P53 low-height partition. -/
theorem lowHeight_source_card_le
    {W : Finset ℂ} {D : ℝ} (hD : Real.exp 1 ≤ D)
    (hsep : OneSeparated (W.image Complex.im))
    (hcard : (W.image Complex.im).card = W.card)
    (hW : ∀ rho ∈ W, |rho.im| ≤ 12 * Real.log D) :
    (W.card : ℝ) ≤ 24 * Real.log D + 1 := by
  have hlog : 0 ≤ Real.log D := by
    have h : 1 ≤ Real.log D := by
      have h' := Real.log_le_log (Real.exp_pos 1) hD
      simpa using h'
    exact zero_le_one.trans h
  have hH : 0 ≤ 12 * Real.log D := mul_nonneg (by norm_num) hlog
  have h := lowHeight_selected_card_le hH hsep hcard hW
  linarith

end

end MAPJutilaPrincipalLowHeightCharge

#print axioms MAPJutilaPrincipalLowHeightCharge.oneSeparated_card_le_of_abs_le
#print axioms MAPJutilaPrincipalLowHeightCharge.lowHeight_selected_card_le
#print axioms MAPJutilaPrincipalLowHeightCharge.lowHeight_source_card_le
