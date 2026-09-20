import GuthMaynardJutilaReflection2941

/-!
# Cardinality of the separated ordinate set in Lemma 29.10

A `T^delta`-separated subset of `(0,T]` has at most `2T` elements for
`T >= 2`.  The proof injects ceilings into `range (ceil T + 1)` and keeps the
strict endpoint arithmetic explicit.  This is used only to absorb the
pointwise AFE remainder after summing over pairs.
-/

namespace GuthMaynardTPowerCardinality

open GuthMaynardJutilaReflection2941

noncomputable section

/-- Equal ceilings force two positive reals to be less than one apart. -/
theorem abs_sub_lt_one_of_ceil_eq
    {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hceil : Nat.ceil t = Nat.ceil u) :
    |t - u| < 1 := by
  have htLe : t ≤ (Nat.ceil t : ℝ) := Nat.le_ceil t
  have huLe : u ≤ (Nat.ceil u : ℝ) := Nat.le_ceil u
  have htUpper : (Nat.ceil t : ℝ) < t + 1 := Nat.ceil_lt_add_one ht
  have huUpper : (Nat.ceil u : ℝ) < u + 1 := Nat.ceil_lt_add_one hu
  rw [hceil] at htLe htUpper
  rcases le_total t u with htu | hut
  · rw [abs_of_nonpos (sub_nonpos.mpr htu)]
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hut)]
    linarith

/-- The ceiling map is injective on a positive `T^delta`-separated set when
`T >= 1` and `delta >= 0`. -/
theorem ceil_injOn_of_TPowerSeparated
    {G : Finset ℝ} {T delta : ℝ}
    (hT : 1 ≤ T) (hdelta : 0 ≤ delta)
    (hsep : TPowerSeparated G T delta)
    (hheight : InOpenClosedZeroT G T) :
    Set.InjOn Nat.ceil (G : Set ℝ) := by
  intro t ht u hu hceil
  by_contra htu
  have hgap := hsep t ht u hu htu
  have hpow : 1 ≤ Real.rpow T delta := Real.one_le_rpow hT hdelta
  have hlt := abs_sub_lt_one_of_ceil_eq
    (hheight t ht).1.le (hheight u hu).1.le hceil
  exact (not_lt_of_ge (hpow.trans hgap)) hlt

/-- Exact finite cardinal bound used to sum the AFE remainder. -/
theorem card_cast_le_two_mul_T
    {G : Finset ℝ} {T delta : ℝ}
    (hT : 2 ≤ T) (hdelta : 0 ≤ delta)
    (hsep : TPowerSeparated G T delta)
    (hheight : InOpenClosedZeroT G T) :
    (G.card : ℝ) ≤ 2 * T := by
  let image : Finset ℕ := G.image Nat.ceil
  have hinj := ceil_injOn_of_TPowerSeparated
    (show 1 ≤ T by linarith) hdelta hsep hheight
  have hcardImage : image.card = G.card := by
    dsimp [image]
    exact Finset.card_image_iff.mpr (fun t ht u hu h => hinj ht hu h)
  have hsubset : image ⊆ Finset.range (Nat.ceil T + 1) := by
    intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.ceil_mono (hheight t ht).2)
  have hcardNat : G.card ≤ Nat.ceil T + 1 := by
    rw [← hcardImage]
    simpa using Finset.card_le_card hsubset
  have hcardReal : (G.card : ℝ) ≤ (Nat.ceil T : ℝ) + 1 := by
    exact_mod_cast hcardNat
  have hceil : (Nat.ceil T : ℝ) < T + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  linarith

end

end GuthMaynardTPowerCardinality

#print axioms GuthMaynardTPowerCardinality.abs_sub_lt_one_of_ceil_eq
#print axioms GuthMaynardTPowerCardinality.card_cast_le_two_mul_T
