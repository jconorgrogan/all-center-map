import GuthMaynardS2ReflectionError
import GuthMaynardS2PowerLedger
import GuthMaynardS2CutoffGeometry
import GuthMaynardS2ShortGapMass
import GuthMaynardS2LiteralReduction

/-! # Sharp k=2 S2 normalization
The dyadic reflection error is replaced by `C_err(ell) 2^L / N`. Combined
with the existing cutoff and power ledgers, this produces the printed
Proposition 6.1 shape at `k = 2`:
`‖S2‖ ≤ C T^η (N^2 |W|^2 + T N |W|^(3/2) + N^2 T^(1/4) |W|^(13/8))`.
-/

namespace GuthMaynardS2SharpNormalization

open scoped BigOperators
open CGLProofDAG
open GuthMaynardEquation55Infinite
open GuthMaynardSectorFactorization
open GuthMaynardS2LiteralReduction
open GuthMaynardS2DyadicReflection
open GuthMaynardS2DyadicAssembly
open GuthMaynardS2PowerLedger
open GuthMaynardS2ShortGapMass
open GuthMaynardS2ReflectionError
open GuthMaynardS1Source GuthMaynardS1Tail
open GuthMaynardSectionThreeCutoffDerivativeBudget
open GuthMaynardHeathBrownInterface

noncomputable section

/-- Printed k=2 right-hand side of Guth--Maynard Proposition 6.1, before `C T^η`. -/
def sourceS2SharpShape (T : ℝ) (N : ℕ) (W : Finset ℝ) : ℝ :=
  (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 +
    T * (N : ℝ) * Real.rpow (W.card : ℝ) (3 / 2 : ℝ) +
    (N : ℝ) ^ 2 * Real.rpow T (1 / 4 : ℝ) *
      Real.rpow (W.card : ℝ) (13 / 8 : ℝ)

theorem sourceS2SharpShape_nonneg {T : ℝ} (hT : 0 ≤ T) (N : ℕ) (W : Finset ℝ) :
    0 ≤ sourceS2SharpShape T N W := by
  unfold sourceS2SharpShape
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hw : 0 ≤ (W.card : ℝ) := Nat.cast_nonneg _
  have h1 : 0 ≤ (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h2 : 0 ≤ T * (N : ℝ) * Real.rpow (W.card : ℝ) (3 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg hT hN) (Real.rpow_nonneg hw _)
  have h3 : 0 ≤ (N : ℝ) ^ 2 * Real.rpow T (1 / 4 : ℝ) *
      Real.rpow (W.card : ℝ) (13 / 8 : ℝ) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hT _))
      (Real.rpow_nonneg hw _)
  exact add_nonneg (add_nonneg h1 h2) h3

/-- Uniform Schur budget for the zero-frequency leg on a 1-separated set. -/
def sourceZeroLegConstant : ℝ :=
  lemma43DerivativeConstant 0 +
    s1VerticalConstant 2 * (2 * Real.pi) ^ 2 * 4

theorem sourceZeroLegConstant_nonneg : 0 ≤ sourceZeroLegConstant := by
  unfold sourceZeroLegConstant
  have h0 := lemma43DerivativeConstant_nonneg 0
  have hV := s1VerticalConstant_nonneg 2
  have hpi : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  exact add_nonneg h0 (mul_nonneg (mul_nonneg hV hpi) (by norm_num))

private theorem inv_sq_le_telescoping {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ) / n ^ 2 ≤ 1 / ((n : ℝ) - 1) - 1 / n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hden : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hfrac : (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) :=
    one_div_le_one_div_of_le (mul_pos hn0 hn1) hden
  have hid : (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) =
      1 / ((n : ℝ) - 1) - 1 / n := by
    field_simp [hn0.ne', hn1.ne']
    ring
  exact hfrac.trans_eq hid

private theorem sum_Icc_inv_sq_le (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, (1 : ℝ) / n ^ 2) ≤ 2 := by
  by_cases hM : M = 0
  · subst M; simp
  have hMpos : 1 ≤ M := Nat.pos_of_ne_zero hM
  have hinsert : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
    ext n
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  have h1 : 1 ∉ Finset.Icc 2 M := by
    simp [Finset.mem_Icc]
  have hshift :
      (∑ n ∈ Finset.Icc 2 M, (1 : ℝ) / ((n : ℝ) - 1)) =
        ∑ k ∈ Finset.Icc 1 (M - 1), (1 : ℝ) / k := by
    have hmap : Finset.Icc 2 M =
        (Finset.Icc 1 (M - 1)).map ⟨fun k => k + 1, add_left_injective 1⟩ := by
      ext n
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_Icc]
      constructor
      · intro ⟨h2, hle⟩
        refine ⟨n - 1, ⟨Nat.le_sub_of_add_le (by omega : 1 + 1 ≤ n),
          Nat.sub_le_sub_right hle 1⟩, Nat.sub_add_cancel (le_trans (by norm_num : 1 ≤ 2) h2)⟩
      · intro ⟨k, ⟨hk1, hkM⟩, hn⟩
        subst n
        exact ⟨Nat.succ_le_succ hk1, by
          have : k + 1 ≤ (M - 1) + 1 := Nat.succ_le_succ hkM
          simpa [Nat.sub_add_cancel hMpos] using this⟩
    rw [hmap, Finset.sum_map]
    refine Finset.sum_congr rfl fun k _hk => ?_
    simp [Function.Embedding.coeFn_mk, Nat.cast_succ]
  have hrest :
      (∑ n ∈ Finset.Icc 2 M, (1 : ℝ) / n) =
        (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / k) - 1 := by
    rw [hinsert, Finset.sum_insert h1]
    ring
  have htele :
      (∑ n ∈ Finset.Icc 2 M, (1 / ((n : ℝ) - 1) - 1 / n)) ≤ 1 := by
    rw [Finset.sum_sub_distrib, hshift, hrest]
    have hsub :
        (∑ k ∈ Finset.Icc 1 (M - 1), (1 : ℝ) / k) ≤
          ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        rcases Finset.mem_Icc.mp hk with ⟨hk1, hkM⟩
        exact Finset.mem_Icc.mpr ⟨hk1, le_trans hkM (Nat.sub_le M 1)⟩
      · intro _ _ _; positivity
    linarith
  calc
    (∑ n ∈ Finset.Icc 1 M, (1 : ℝ) / n ^ 2) =
        1 + ∑ n ∈ Finset.Icc 2 M, (1 : ℝ) / n ^ 2 := by
      rw [hinsert, Finset.sum_insert h1]; norm_num
    _ ≤ 1 + ∑ n ∈ Finset.Icc 2 M, (1 / ((n : ℝ) - 1) - 1 / n) :=
      add_le_add (le_refl (1 : ℝ))
        (Finset.sum_le_sum fun n hn =>
          inv_sq_le_telescoping (Finset.mem_Icc.mp hn).1)
    _ ≤ 1 + 1 := add_le_add (le_refl (1 : ℝ)) htele
    _ = 2 := by norm_num

private theorem sum_pos_inv_sq_le_two (s : Finset ℕ) (hs : ∀ n ∈ s, 0 < n) :
    (∑ n ∈ s, (1 : ℝ) / n ^ 2) ≤ 2 := by
  by_cases hne : s.Nonempty
  · let M := s.max' hne
    have hsub : s ⊆ Finset.Icc 1 M := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨hs n hn, Finset.le_max' s n hn⟩
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 M, (1 : ℝ) / n ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ 2 := sum_Icc_inv_sq_le M
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

private theorem oneSeparated_right_floor_inj
    {W : Finset ℝ} (hsep : OneSeparated W) {a : ℝ} :
    Set.InjOn (fun b : ℝ => Nat.floor (b - a))
      {b | b ∈ W ∧ a < b} := by
  intro b hb c hc heq
  have hbW : b ∈ W := hb.1
  have hcW : c ∈ W := hc.1
  have hba : 0 ≤ b - a := sub_nonneg.mpr hb.2.le
  have hca : 0 ≤ c - a := sub_nonneg.mpr hc.2.le
  have hfl : Nat.floor (b - a) = Nat.floor (c - a) := heq
  have hbl : (Nat.floor (b - a) : ℝ) ≤ b - a := Nat.floor_le hba
  have hcl : (Nat.floor (c - a) : ℝ) ≤ c - a := Nat.floor_le hca
  have hbu : b - a < (Nat.floor (b - a) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hcu : c - a < (Nat.floor (c - a) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hbc : |b - c| < 1 := by
    rw [hfl] at hbu hbl
    have h1 : b - c < 1 := by linarith
    have h2 : c - b < 1 := by linarith
    exact abs_lt.mpr ⟨by linarith, h1⟩
  by_contra hne
  exact (not_lt_of_ge (hsep b hbW c hcW hne)) hbc

private theorem oneSeparated_left_floor_inj
    {W : Finset ℝ} (hsep : OneSeparated W) {a : ℝ} :
    Set.InjOn (fun b : ℝ => Nat.floor (a - b))
      {b | b ∈ W ∧ b < a} := by
  intro b hb c hc heq
  have hbW : b ∈ W := hb.1
  have hcW : c ∈ W := hc.1
  have hab : 0 ≤ a - b := sub_nonneg.mpr hb.2.le
  have hac : 0 ≤ a - c := sub_nonneg.mpr hc.2.le
  have hfl : Nat.floor (a - b) = Nat.floor (a - c) := heq
  have hbl : (Nat.floor (a - b) : ℝ) ≤ a - b := Nat.floor_le hab
  have hcl : (Nat.floor (a - c) : ℝ) ≤ a - c := Nat.floor_le hac
  have hbu : a - b < (Nat.floor (a - b) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hcu : a - c < (Nat.floor (a - c) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hbc : |b - c| < 1 := by
    rw [hfl] at hbu hbl
    have h1 : b - c < 1 := by linarith
    have h2 : c - b < 1 := by linarith
    exact abs_lt.mpr ⟨by linarith, h1⟩
  by_contra hne
  exact (not_lt_of_ge (hsep b hbW c hcW hne)) hbc

/-- Inverse-square packing of a 1-separated row. -/
theorem oneSeparated_inv_sq_row
    {W : Finset ℝ} (hsep : OneSeparated W) {a : ℝ} (ha : a ∈ W) :
    (∑ b ∈ W, if b ≠ a then (1 : ℝ) / |b - a| ^ 2 else 0) ≤ 4 := by
  classical
  let sR := W.filter (fun b => a < b)
  let sL := W.filter (fun b => b < a)
  have hR : (∑ b ∈ sR, (1 : ℝ) / |b - a| ^ 2) ≤ 2 := by
    have himg : ∀ b ∈ sR, 0 < Nat.floor (b - a) := by
      intro b hb
      have hbW : b ∈ W := (Finset.mem_filter.mp hb).1
      have hlt : a < b := (Finset.mem_filter.mp hb).2
      have hge : (1 : ℝ) ≤ b - a := by
        have hsep' := hsep a ha b hbW (ne_of_lt hlt)
        rwa [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hlt.le)] at hsep'
      exact Nat.floor_pos.mpr hge
    have hinj : Set.InjOn (fun b : ℝ => Nat.floor (b - a)) (sR : Set ℝ) := by
      intro b hb c hc heq
      exact oneSeparated_right_floor_inj hsep
        ⟨(Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2⟩
        ⟨(Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2⟩ heq
    have hle : (∑ b ∈ sR, (1 : ℝ) / |b - a| ^ 2) ≤
        ∑ b ∈ sR, (1 : ℝ) / (Nat.floor (b - a) : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro b hb
      have hlt : a < b := (Finset.mem_filter.mp hb).2
      have hpos : 0 ≤ b - a := sub_nonneg.mpr hlt.le
      rw [abs_of_nonneg hpos]
      have hfl : (Nat.floor (b - a) : ℝ) ≤ b - a := Nat.floor_le hpos
      have hflpos : (0 : ℝ) < Nat.floor (b - a) := by exact_mod_cast himg b hb
      exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
        (pow_pos hflpos 2) (pow_le_pow_left₀ hflpos.le hfl 2)
    have himage :
        (∑ b ∈ sR, (1 : ℝ) / (Nat.floor (b - a) : ℝ) ^ 2) =
          ∑ n ∈ sR.image (fun b => Nat.floor (b - a)), (1 : ℝ) / (n : ℝ) ^ 2 := by
      exact (Finset.sum_image (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) hinj).symm
    have hpos : ∀ n ∈ sR.image (fun b => Nat.floor (b - a)), 0 < n := by
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨b, hb, rfl⟩
      exact himg b hb
    exact hle.trans (himage.trans_le (sum_pos_inv_sq_le_two _ hpos))
  have hL : (∑ b ∈ sL, (1 : ℝ) / |b - a| ^ 2) ≤ 2 := by
    have himg : ∀ b ∈ sL, 0 < Nat.floor (a - b) := by
      intro b hb
      have hbW : b ∈ W := (Finset.mem_filter.mp hb).1
      have hlt : b < a := (Finset.mem_filter.mp hb).2
      have hge : (1 : ℝ) ≤ a - b := by
        have hsep' := hsep a ha b hbW (ne_of_gt hlt)
        rwa [abs_of_nonneg (sub_nonneg.mpr hlt.le)] at hsep'
      exact Nat.floor_pos.mpr hge
    have hinj : Set.InjOn (fun b : ℝ => Nat.floor (a - b)) (sL : Set ℝ) := by
      intro b hb c hc heq
      exact oneSeparated_left_floor_inj hsep
        ⟨(Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2⟩
        ⟨(Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2⟩ heq
    have hle : (∑ b ∈ sL, (1 : ℝ) / |b - a| ^ 2) ≤
        ∑ b ∈ sL, (1 : ℝ) / (Nat.floor (a - b) : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro b hb
      have hlt : b < a := (Finset.mem_filter.mp hb).2
      have hpos : 0 ≤ a - b := sub_nonneg.mpr hlt.le
      rw [abs_sub_comm, abs_of_nonneg hpos]
      have hfl : (Nat.floor (a - b) : ℝ) ≤ a - b := Nat.floor_le hpos
      have hflpos : (0 : ℝ) < Nat.floor (a - b) := by exact_mod_cast himg b hb
      exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
        (pow_pos hflpos 2) (pow_le_pow_left₀ hflpos.le hfl 2)
    have himage :
        (∑ b ∈ sL, (1 : ℝ) / (Nat.floor (a - b) : ℝ) ^ 2) =
          ∑ n ∈ sL.image (fun b => Nat.floor (a - b)), (1 : ℝ) / (n : ℝ) ^ 2 := by
      exact (Finset.sum_image (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) hinj).symm
    have hpos : ∀ n ∈ sL.image (fun b => Nat.floor (a - b)), 0 < n := by
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨b, hb, rfl⟩
      exact himg b hb
    exact hle.trans (himage.trans_le (sum_pos_inv_sq_le_two _ hpos))
  have hdecomp :
      (∑ b ∈ W, if b ≠ a then (1 : ℝ) / |b - a| ^ 2 else 0) =
        (∑ b ∈ sR, (1 : ℝ) / |b - a| ^ 2) +
          ∑ b ∈ sL, (1 : ℝ) / |b - a| ^ 2 := by
    have hpoint : ∀ b ∈ W,
        (if b ≠ a then (1 : ℝ) / |b - a| ^ 2 else 0) =
          (if a < b then (1 : ℝ) / |b - a| ^ 2 else 0) +
            (if b < a then (1 : ℝ) / |b - a| ^ 2 else 0) := by
      intro b _hb
      rcases lt_trichotomy a b with hlt | heq | hgt
      · simp [hlt, hlt.ne', not_lt.mpr hlt.le]
      · simp [heq]
      · simp [hgt, hgt.ne, not_lt.mpr hgt.le]
    calc
      _ = ∑ b ∈ W, ((if a < b then (1 : ℝ) / |b - a| ^ 2 else 0) +
            (if b < a then (1 : ℝ) / |b - a| ^ 2 else 0)) :=
        Finset.sum_congr rfl hpoint
      _ = (∑ b ∈ W, if a < b then (1 : ℝ) / |b - a| ^ 2 else 0) +
            ∑ b ∈ W, if b < a then (1 : ℝ) / |b - a| ^ 2 else 0 :=
        Finset.sum_add_distrib
      _ = (∑ b ∈ sR, (1 : ℝ) / |b - a| ^ 2) +
            ∑ b ∈ sL, (1 : ℝ) / |b - a| ^ 2 := by
        simp only [sR, sL, Finset.sum_filter]
  linarith

theorem sourceHhat_zero_le (t : ℝ) :
    ‖sourceHhat t 0‖ ≤
      (if t = 0 then lemma43DerivativeConstant 0 else 0) +
        (if t ≠ 0 then
          s1VerticalConstant 2 * (2 * Real.pi) ^ 2 / |t| ^ 2 else 0) := by
  by_cases ht : t = 0
  · subst t
    simp
    exact norm_sourceHhat_le_fixed 0 0
  · simp [ht]
    have h := norm_sourceHhat_zero_le_div t 2 ht
    have h' : ‖sourceHhat t 0‖ ≤
        s1VerticalConstant 2 / |t / (2 * Real.pi)| ^ 2 := by
      simpa [s1VerticalConstant] using h
    have habs : |t| ≠ 0 := abs_ne_zero.mpr ht
    have hpi : 0 < 2 * Real.pi := by positivity
    have habsdiv : |t / (2 * Real.pi)| = |t| / (2 * Real.pi) := by
      rw [abs_div, abs_of_pos hpi]
    have hrewrite : s1VerticalConstant 2 / |t / (2 * Real.pi)| ^ 2 =
        s1VerticalConstant 2 * (2 * Real.pi) ^ 2 / t ^ 2 := by
      rw [habsdiv, div_pow, sq_abs]
      field_simp [habs, hpi.ne']
    simpa [sq_abs] using h'.trans_eq hrewrite

private theorem sourceHhat_zero_le_packed (a b : ℝ) :
    ‖sourceHhat (a - b) 0‖ ≤
      (if b = a then lemma43DerivativeConstant 0 else 0) +
        s1VerticalConstant 2 * (2 * Real.pi) ^ 2 *
          (if b ≠ a then (1 : ℝ) / |b - a| ^ 2 else 0) := by
  have h := sourceHhat_zero_le (a - b)
  have hrewrite :
      (if a - b = 0 then lemma43DerivativeConstant 0 else 0) +
        (if a - b ≠ 0 then
          s1VerticalConstant 2 * (2 * Real.pi) ^ 2 / |a - b| ^ 2 else 0) =
        (if b = a then lemma43DerivativeConstant 0 else 0) +
          s1VerticalConstant 2 * (2 * Real.pi) ^ 2 *
            (if b ≠ a then (1 : ℝ) / |b - a| ^ 2 else 0) := by
    by_cases hba : b = a
    · simp [hba]
    · have hne : a - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hba)
      simp [hba, hne, abs_sub_comm]
      ring
  exact h.trans_eq hrewrite

theorem sourceZeroFourier_row_le_oneSeparated
    {W : Finset ℝ} (hsep : OneSeparated W) {a : ℝ} (ha : a ∈ W) :
    (∑ b ∈ W, ‖sourceHhat (a - b) 0‖) ≤ sourceZeroLegConstant := by
  classical
  have hK : 0 ≤ s1VerticalConstant 2 * (2 * Real.pi) ^ 2 := by
    exact mul_nonneg (s1VerticalConstant_nonneg 2) (sq_nonneg _)
  have hsum : (∑ b ∈ W, ‖sourceHhat (a - b) 0‖) ≤
      lemma43DerivativeConstant 0 +
        s1VerticalConstant 2 * (2 * Real.pi) ^ 2 *
          ∑ b ∈ W, if b ≠ a then (1 : ℝ) / |b - a| ^ 2 else 0 := by
    calc
      _ ≤ ∑ b ∈ W,
            ((if b = a then lemma43DerivativeConstant 0 else 0) +
              s1VerticalConstant 2 * (2 * Real.pi) ^ 2 *
                (if b ≠ a then (1 : ℝ) / |b - a| ^ 2 else 0)) :=
        Finset.sum_le_sum fun b _ => sourceHhat_zero_le_packed a b
      _ = (∑ b ∈ W, if b = a then lemma43DerivativeConstant 0 else 0) +
            ∑ b ∈ W, s1VerticalConstant 2 * (2 * Real.pi) ^ 2 *
              (if b ≠ a then (1 : ℝ) / |b - a| ^ 2 else 0) :=
        Finset.sum_add_distrib
      _ = lemma43DerivativeConstant 0 +
            s1VerticalConstant 2 * (2 * Real.pi) ^ 2 *
              ∑ b ∈ W, if b ≠ a then (1 : ℝ) / |b - a| ^ 2 else 0 := by
        rw [Finset.sum_ite_eq_of_mem' W a (fun _ => lemma43DerivativeConstant 0) ha,
          ← Finset.mul_sum]
  have hpack := oneSeparated_inv_sq_row hsep ha
  have hpack0 : 0 ≤ (∑ b ∈ W, if b ≠ a then (1 : ℝ) / |b - a| ^ 2 else 0) :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
  calc
    _ ≤ _ := hsum
    _ ≤ lemma43DerivativeConstant 0 +
          s1VerticalConstant 2 * (2 * Real.pi) ^ 2 * 4 := by
      gcongr
    _ = sourceZeroLegConstant := by
      unfold sourceZeroLegConstant; ring

theorem sourceZeroFourier_col_le_oneSeparated
    {W : Finset ℝ} (hsep : OneSeparated W) {b : ℝ} (hb : b ∈ W) :
    (∑ a ∈ W, ‖sourceHhat (a - b) 0‖) ≤ sourceZeroLegConstant := by
  classical
  have hK : 0 ≤ s1VerticalConstant 2 * (2 * Real.pi) ^ 2 := by
    exact mul_nonneg (s1VerticalConstant_nonneg 2) (sq_nonneg _)
  have hsum : (∑ a ∈ W, ‖sourceHhat (a - b) 0‖) ≤
      lemma43DerivativeConstant 0 +
        s1VerticalConstant 2 * (2 * Real.pi) ^ 2 *
          ∑ a ∈ W, if a ≠ b then (1 : ℝ) / |a - b| ^ 2 else 0 := by
    calc
      _ ≤ ∑ a ∈ W,
            ((if a = b then lemma43DerivativeConstant 0 else 0) +
              s1VerticalConstant 2 * (2 * Real.pi) ^ 2 *
                (if a ≠ b then (1 : ℝ) / |a - b| ^ 2 else 0)) :=
        Finset.sum_le_sum fun a _ => by
          have h := sourceHhat_zero_le_packed a b
          by_cases hab : a = b
          · simpa [hab] using h
          · have hba : b ≠ a := Ne.symm hab
            simp [hba] at h
            have hsq : (b - a) ^ 2 = (a - b) ^ 2 := by ring
            rw [hsq] at h
            simpa [hab] using h
      _ = (∑ a ∈ W, if a = b then lemma43DerivativeConstant 0 else 0) +
            ∑ a ∈ W, s1VerticalConstant 2 * (2 * Real.pi) ^ 2 *
              (if a ≠ b then (1 : ℝ) / |a - b| ^ 2 else 0) :=
        Finset.sum_add_distrib
      _ = lemma43DerivativeConstant 0 +
            s1VerticalConstant 2 * (2 * Real.pi) ^ 2 *
              ∑ a ∈ W, if a ≠ b then (1 : ℝ) / |a - b| ^ 2 else 0 := by
        rw [Finset.sum_ite_eq_of_mem' W b (fun _ => lemma43DerivativeConstant 0) hb,
          ← Finset.mul_sum]
  have hpack := oneSeparated_inv_sq_row hsep hb
  have hpack0 : 0 ≤ (∑ a ∈ W, if a ≠ b then (1 : ℝ) / |a - b| ^ 2 else 0) :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
  calc
    _ ≤ _ := hsum
    _ ≤ lemma43DerivativeConstant 0 +
          s1VerticalConstant 2 * (2 * Real.pi) ^ 2 * 4 := by
      gcongr
    _ = sourceZeroLegConstant := by
      unfold sourceZeroLegConstant; ring

private theorem weighted_cycle_le_pairMoment
    {ι : Type*} [DecidableEq ι] (W : Finset ι)
    (A f : ι → ι → ℝ) {C : ℝ}
    (hA : ∀ a ∈ W, ∀ b ∈ W, 0 ≤ A a b)
    (hrow : ∀ a ∈ W, ∑ b ∈ W, A a b ≤ C)
    (hcol : ∀ b ∈ W, ∑ a ∈ W, A a b ≤ C) :
    (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, A a b * (f b c * f c a)) ≤
      C * ∑ a ∈ W, ∑ b ∈ W, f a b ^ 2 := by
  have hleft :
      (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, A a b * f b c ^ 2) ≤
        C * ∑ b ∈ W, ∑ c ∈ W, f b c ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c hc
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hcol b hb) (sq_nonneg _)
  have hright :
      (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, A a b * f c a ^ 2) ≤
        C * ∑ a ∈ W, ∑ c ∈ W, f c a ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c hc
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow a ha) (sq_nonneg _)
  rw [Finset.sum_comm (f := fun a c => f c a ^ 2)] at hright
  have hpoint :
      (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, 2 * (A a b * (f b c * f c a))) ≤
      ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
        (A a b * f b c ^ 2 + A a b * f c a ^ 2) := by
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    apply Finset.sum_le_sum
    intro c hc
    have h := mul_nonneg (hA a ha b hb) (sq_nonneg (f b c - f c a))
    nlinarith
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hpoint
  simp only [← Finset.mul_sum] at hleft hright ⊢
  linarith

private theorem norm_sum3_le {ι : Type*} [DecidableEq ι]
    (W : Finset ι) (f : ι → ι → ι → ℂ) :
    ‖∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, f a b c‖ ≤
      ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, ‖f a b c‖ := by
  calc
    _ ≤ ∑ a ∈ W, ‖∑ b ∈ W, ∑ c ∈ W, f a b c‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ W, ∑ b ∈ W, ‖∑ c ∈ W, f a b c‖ := by
      apply Finset.sum_le_sum
      intro a ha
      exact norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact norm_sum_le _ _

/-- `|W|^(3/2)` identity: `w * √w = w^(3/2)`.
Work in `HPow`/`^` rather than the explicit `Real.rpow` function, so
`rpow_one`/`rpow_add` match. `nth_rw 1` avoids rewriting the inner base of
`w^(1/2)`. -/
private theorem mul_sqrt_eq_rpow_three_halves {w : ℝ} (hw : 0 ≤ w) :
    w * Real.sqrt w = Real.rpow w (3 / 2 : ℝ) := by
  change w * Real.sqrt w = w ^ (3 / 2 : ℝ)
  rw [Real.sqrt_eq_rpow]
  by_cases hw0 : w = 0
  · simp [hw0]
  · have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    nth_rw 1 [← Real.rpow_one w]
    rw [← Real.rpow_add hwpos]
    norm_num

/-- `|W|^(13/8)` identity:
`w * √(w^(5/4) T^(1/2)) = w^(13/8) T^(1/4)`.
`Real.rpow_mul` is `x^(y*z) = (x^y)^z`, so the reverse lemma converts
`(x^y)^z` into `x^(y*z)`. Explicit `Real.rpow` is changed to `^` first. -/
private theorem mul_sqrt_mixed_eq_rpow_thirteen_eighths
    {T w : ℝ} (hT : 0 ≤ T) (hw : 0 ≤ w) :
    w * Real.sqrt (Real.rpow w (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ)) =
      Real.rpow w (13 / 8 : ℝ) * Real.rpow T (1 / 4 : ℝ) := by
  change w * Real.sqrt (w ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) =
    w ^ (13 / 8 : ℝ) * T ^ (1 / 4 : ℝ)
  by_cases hw0 : w = 0
  · rw [hw0]
    simp [Real.zero_rpow (by norm_num : (13 / 8 : ℝ) ≠ 0),
      Real.zero_rpow (by norm_num : (5 / 4 : ℝ) ≠ 0), Real.sqrt_zero]
  · have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    have hw5 : 0 ≤ w ^ (5 / 4 : ℝ) := Real.rpow_nonneg hw _
    rw [Real.sqrt_mul hw5, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hw (5 / 4 : ℝ) (1 / 2 : ℝ),
        ← Real.rpow_mul hT (1 / 2 : ℝ) (1 / 2 : ℝ)]
    have h1 : (5 / 4 : ℝ) * (1 / 2) = 5 / 8 := by norm_num
    have h2 : (1 / 2 : ℝ) * (1 / 2) = 1 / 4 := by norm_num
    rw [h1, h2, ← mul_assoc]
    nth_rw 1 [← Real.rpow_one w]
    rw [← Real.rpow_add hwpos]
    have h3 : (1 : ℝ) + 5 / 8 = 13 / 8 := by norm_num
    rw [h3]

theorem pairShape_le_three {T M w : ℝ} (hT : 0 ≤ T) (_hM : 0 ≤ M) (hw : 0 ≤ w) :
    pairShape T M w ≤
      w ^ 2 * M + Real.rpow w (3 / 2 : ℝ) * M ^ 2 +
        Real.rpow w (13 / 8 : ℝ) * Real.rpow T (1 / 4 : ℝ) * M := by
  have hsqrt := mul_sqrt_eq_rpow_three_halves hw
  have hthird := mul_sqrt_mixed_eq_rpow_thirteen_eighths hT hw
  unfold pairShape
  rw [hsqrt, hthird]

theorem sourceGapPoweredBudget_eq (C eta T : ℝ) (N : ℕ) (W : Finset ℝ)
    (U V R : ℝ) (J k ell : ℕ) :
    sourceGapPoweredBudget C eta T N W U V R J k ell =
      sourceCentralBudget C eta T W U R J +
        2 * (W.card : ℝ) ^ 2 * sourceReflectionError N U V R J k ell ^ 2 := by
  unfold sourceGapPoweredBudget sourceCentralBudget
  rfl

theorem contained_abs_le {W : Finset ℝ} {T : ℝ}
    (h : ContainedInIntervalOfLength W T) {t u : ℝ}
    (ht : t ∈ W) (hu : u ∈ W) : |t - u| ≤ T := by
  obtain ⟨x, hx⟩ := h
  have ht' := hx t ht
  have hu' := hx u hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The zero-frequency Schur factor is O(1) on a 1-separated set, matching
the paper's use of `ĥ_0(0) ≍ 1`. -/
theorem norm_sourceS2_le_oneSeparated_pairMoment
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) (hsep : OneSeparated W) :
    ‖sourceS2 N W‖ ≤
      3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
        sourceNonzeroFourierPairMoment N W := by
  rw [sourceS2_eq_three_nonzeroFourier_plane hN W, norm_mul]
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  rw [show ‖(3 : ℂ)‖ = (3 : ℝ) by norm_num]
  rw [mul_assoc (3 * (N : ℝ) ^ 3)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum3_le W _).trans
  simp only [norm_mul, mul_assoc]
  apply weighted_cycle_le_pairMoment W
    (fun a b => ‖sourceHhat (a - b) 0‖)
    (fun a b => ‖sourceNonzeroFourier N (a - b)‖)
  · intro a ha b hb; exact norm_nonneg _
  · intro a ha; exact sourceZeroFourier_row_le_oneSeparated hsep ha
  · intro b hb
    exact sourceZeroFourier_col_le_oneSeparated hsep hb

end
end GuthMaynardS2SharpNormalization

#print axioms GuthMaynardS2SharpNormalization.norm_sourceS2_le_oneSeparated_pairMoment
#print axioms GuthMaynardS2SharpNormalization.oneSeparated_inv_sq_row
#print axioms GuthMaynardS2SharpNormalization.sourceZeroFourier_row_le_oneSeparated
#print axioms GuthMaynardS2SharpNormalization.pairShape_le_three
