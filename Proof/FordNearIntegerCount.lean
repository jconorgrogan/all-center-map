import GuthMaynardLemma118IntervalPacking

open scoped BigOperators

namespace FordNearIntegerCount

noncomputable section

/-- The literal finite set of bounded integer differences which lie within `δ`
of some integer after multiplication by `γ`. -/
def nearIntegerSet (K : ℕ) (gamma delta : ℝ) : Finset ℤ := by
  classical
  exact (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter fun d =>
    ∃ m : ℤ, |(d : ℝ) * gamma - m| < delta

private lemma card_cast_le_one_add_div_int
    (S : Finset ℤ) (a L sep : ℝ)
    (hsep : 0 < sep) (hL : 0 ≤ L)
    (hmem : ∀ d ∈ S, a ≤ (d : ℝ) * sep ∧ (d : ℝ) * sep ≤ a + L)
    (hgap : ∀ d ∈ S, ∀ e ∈ S, d ≠ e →
      sep ≤ |(d : ℝ) * sep - (e : ℝ) * sep|) :
    (S.card : ℝ) ≤ 1 + L / sep := by
  have hnat := GuthMaynardLemma118.card_le_natFloor_div_add_one_of_injective_map
    S (fun d : ℤ => (d : ℝ) * sep) a L sep hsep hL
    (by
      intro d hd e he hEq
      have hEq' : (d : ℝ) = (e : ℝ) := by
        apply (mul_right_cancel₀ (ne_of_gt hsep))
        simpa using hEq
      exact Int.cast_inj.mp hEq')
    hmem hgap
  have hnatR : (S.card : ℝ) ≤ (⌊L / sep⌋₊ : ℝ) + 1 := by
    exact_mod_cast hnat
  have hfloor : (⌊L / sep⌋₊ : ℝ) ≤ L / sep := by
    exact_mod_cast (Nat.floor_le (div_nonneg hL hsep.le))
  linarith

private lemma integer_gap
    {d e : ℤ} (hde : d ≠ e) :
    (1 : ℝ) ≤ |(d : ℝ) - (e : ℝ)| := by
  have hlt : d < e ∨ e < d := lt_or_gt_of_ne hde
  rcases hlt with hlt | hlt
  · have hcast : (d : ℝ) + 1 ≤ (e : ℝ) := by
      exact_mod_cast (show d + 1 ≤ e by omega)
    rw [abs_of_nonpos]
    · linarith
    · linarith
  · have hcast : (e : ℝ) + 1 ≤ (d : ℝ) := by
      exact_mod_cast (show e + 1 ≤ d by omega)
    rw [abs_of_nonneg]
    · linarith
    · linarith

private lemma fixed_card_bound
    (K : ℕ) {gamma delta m : ℝ}
    (hgamma : 0 < gamma) (hdelta : 0 < delta)
    (S : Finset ℤ)
    (hS : ∀ d ∈ S, d ∈ Finset.Icc (-(K : ℤ)) (K : ℤ))
    (hnear : ∀ d ∈ S, |(d : ℝ) * gamma - m| < delta) :
    (S.card : ℝ) ≤ 1 + 2 * delta / gamma := by
  apply card_cast_le_one_add_div_int S (m - delta) (2 * delta) gamma
    hgamma (by positivity)
  · intro d hd
    have h := abs_lt.mp (hnear d hd)
    constructor <;> linarith
  · intro d hd e he hde
    have hgap := integer_gap hde
    calc
      gamma ≤ gamma * |(d : ℝ) - (e : ℝ)| := by
        have := mul_le_mul_of_nonneg_left hgap hgamma.le
        nlinarith
      _ = |gamma| * |(d : ℝ) - (e : ℝ)| := by rw [abs_of_pos hgamma]
      _ = |gamma * ((d : ℝ) - (e : ℝ))| := by rw [abs_mul]
      _ = |(d : ℝ) * gamma - (e : ℝ) * gamma| := by congr 1 <;> ring

/-- Literal finite near-integer count.  The strict inequality in the predicate
is retained exactly. -/
theorem nearIntegerSet_card_le
    (K : ℕ) {gamma delta : ℝ}
    (hgamma : 0 < gamma) (hdelta : 0 < delta) :
    (nearIntegerSet K gamma delta).card ≤
      4 * (K : ℝ) * delta + 2 * (K : ℝ) * gamma +
        4 * delta / gamma + 2 := by
  classical
  by_cases hlarge : (1 : ℝ) / 2 ≤ delta
  · have htotal : (nearIntegerSet K gamma delta).card ≤ 2 * K + 1 := by
      rw [show (2 * K + 1 : ℕ) = (Finset.Icc (-(K : ℤ)) (K : ℤ)).card by
        rw [Int.card_Icc]
        have heq : (K : ℤ) + 1 - -(K : ℤ) = ((2 * K + 1 : ℕ) : ℤ) := by
          push_cast
          ring
        rw [heq]
        have h : (0 : ℤ) ≤ ((2 * K + 1 : ℕ) : ℤ) := by positivity
        have hn := Int.toNat_of_nonneg h
        exact_mod_cast hn]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    have htotalR : (nearIntegerSet K gamma delta).card ≤ (2 * K + 1 : ℕ) := htotal
    have hnonK : (0 : ℝ) ≤ (K : ℝ) := by positivity
    have hnonD : (0 : ℝ) ≤ delta := hdelta.le
    have hnonG : (0 : ℝ) ≤ gamma := hgamma.le
    have hdiv : (0 : ℝ) ≤ delta / gamma := div_nonneg hnonD hnonG
    have hkd : 2 * (K : ℝ) ≤ 4 * (K : ℝ) * delta := by
      have htmp := mul_nonneg hnonK (sub_nonneg.mpr hlarge)
      nlinarith
    have hkg : 0 ≤ (K : ℝ) * gamma := mul_nonneg hnonK hnonG
    have hR : ((nearIntegerSet K gamma delta).card : ℝ) ≤ (2 * (K : ℝ) + 1) := by
      exact_mod_cast htotal
    have hRHS : 2 * (K : ℝ) + 1 ≤
        4 * (K : ℝ) * delta + 2 * (K : ℝ) * gamma +
          4 * delta / gamma + 2 := by
      have hpos : 0 ≤ 2 * (K : ℝ) * gamma + 4 * delta / gamma + 1 := by
        positivity
      have hbase : 2 * (K : ℝ) + 1 ≤ 4 * (K : ℝ) * delta + 1 := by
        nlinarith [hkd]
      linarith [hbase, hpos]
    exact hR.trans hRHS
  · have hsmall : delta < (1 : ℝ) / 2 := lt_of_not_ge hlarge
    let S := nearIntegerSet K gamma delta
    let a : ℝ := -((K : ℝ) * gamma) - delta
    let b : ℝ := ((K : ℝ) * gamma) + delta
    let M : Finset ℝ :=
      ((Finset.Icc (Int.floor a) (Int.ceil b)).filter fun m : ℤ =>
        a < (m : ℝ) ∧ (m : ℝ) < b).image (fun m : ℤ => (m : ℝ))
    let D : ∀ m : M, Finset ℤ := fun m =>
      S.filter fun d => |(d : ℝ) * gamma - m.1| < delta
    have hSsub : S ⊆ M.attach.biUnion D := by
      intro d hd
      have hd' : d ∈ nearIntegerSet K gamma delta := hd
      change d ∈ ((Finset.Icc (-(K : ℤ)) (K : ℤ) : Finset ℤ).filter
          (fun d : ℤ => ∃ m : ℤ, |(d : ℝ) * gamma - m| < delta)) at hd'
      obtain ⟨m, hm⟩ := (Finset.mem_filter.mp hd').2
      have hK := Finset.mem_Icc.mp (Finset.mem_filter.mp hd').1
      have hdm : a < (m : ℝ) ∧ (m : ℝ) < b := by
        have habs := abs_lt.mp hm
        constructor
        · dsimp [a]
          have hdK : -(K : ℝ) ≤ (d : ℝ) := by
            exact_mod_cast hK.1
          have hmul := mul_le_mul_of_nonneg_right hdK hgamma.le
          linarith [hmul]
        · dsimp [b]
          have hdK : (d : ℝ) ≤ (K : ℝ) := by
            exact_mod_cast hK.2
          have hmul := mul_le_mul_of_nonneg_right hdK hgamma.le
          linarith [hmul]
      have hmfloor : Int.floor a ≤ m := by
        exact_mod_cast (Int.floor_lt.mpr hdm.1).le
      have hmceil : m ≤ Int.ceil b := by
        exact_mod_cast (Int.lt_ceil.mpr hdm.2).le
      have hmI : m ∈ Finset.Icc (Int.floor a) (Int.ceil b) := Finset.mem_Icc.mpr ⟨hmfloor, hmceil⟩
      have hmM : (m : ℝ) ∈ M := by
        apply Finset.mem_image.mpr
        exact ⟨m, Finset.mem_filter.mpr ⟨hmI, hdm⟩, rfl⟩
      let mm : M := ⟨(m : ℝ), hmM⟩
      have hdmS : d ∈ S := hd
      exact Finset.mem_biUnion.mpr ⟨mm, Finset.mem_attach M mm,
        (by change d ∈ S.filter (fun d : ℤ => |(d : ℝ) * gamma - mm.1| < delta)
            exact Finset.mem_filter.mpr ⟨hdmS, by simpa [mm] using hm⟩)⟩
    have hMmem : ∀ x ∈ M, a ≤ x ∧ x ≤ a + (b - a) := by
      intro x hx
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
      have hm' := (Finset.mem_filter.mp hm).2
      constructor
      · exact le_of_lt hm'.1
      · dsimp [a, b]
        linarith [le_of_lt hm'.2]
    have hMsep : ∀ x ∈ M, ∀ y ∈ M, x ≠ y →
        (1 : ℝ) ≤ |x - y| := by
      intro x hx y hy hxy
      obtain ⟨mx, hmx, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨my, hmy, rfl⟩ := Finset.mem_image.mp hy
      have hmxy : mx ≠ my := by
        intro h
        apply hxy
        simpa [h]
      simpa [sub_eq_add_neg] using integer_gap hmxy
    have hMcard : (M.card : ℝ) ≤ 1 + (b - a) := by
      have hL : 0 ≤ b - a := by
        dsimp [a, b]
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ K by positivity) hgamma.le, hdelta.le]
      exact GuthMaynardLemma118.card_cast_le_one_add_div M a (b - a) 1
        zero_lt_one hL hMmem hMsep |>.trans_eq (by ring)
    have hcardNat : S.card ≤ (M.attach.biUnion D).card := Finset.card_le_card hSsub
    have hsum : ((M.attach.biUnion D).card : ℝ) ≤
        (M.card : ℝ) * (1 + 2 * delta / gamma) := by
      have hbi := Finset.card_biUnion_le (s := M.attach) (t := D)
      have hsumNat : (M.attach.biUnion D).card ≤
          ∑ m ∈ M.attach, (D m).card := by simpa using hbi
      have hsumR : ((M.attach.biUnion D).card : ℝ) ≤
          ∑ m ∈ M.attach, ((D m).card : ℝ) := by exact_mod_cast hsumNat
      have hDreal : ∀ m : M, ((D m).card : ℝ) ≤ 1 + 2 * delta / gamma := by
        intro m
        apply fixed_card_bound K hgamma hdelta (D m)
        · intro d hd
          have hd' := (Finset.mem_filter.mp hd).1
          exact (Finset.mem_filter.mp (show d ∈ S from hd')).1
        · intro d hd
          exact (Finset.mem_filter.mp hd).2
      calc
        ((M.attach.biUnion D).card : ℝ) ≤
            ∑ m ∈ M.attach, ((D m).card : ℝ) := hsumR
        _ ≤ ∑ m ∈ M.attach, (1 + 2 * delta / gamma) :=
          Finset.sum_le_sum (fun m hm => hDreal m)
        _ = (M.card : ℝ) * (1 + 2 * delta / gamma) := by
          simp [Finset.card_attach, nsmul_eq_mul]
          ring
    have hcardR : (S.card : ℝ) ≤
        (1 + (b - a)) * (1 + 2 * delta / gamma) := by
      have hcardNatR : (S.card : ℝ) ≤ (M.attach.biUnion D).card := by exact_mod_cast hcardNat
      have hprod : (M.card : ℝ) * (1 + 2 * delta / gamma) ≤
          (1 + (b - a)) * (1 + 2 * delta / gamma) := by
        gcongr
      exact hcardNatR.trans (hsum.trans hprod)
    dsimp [S, a, b] at hcardR
    have hquad : 4 * delta * (delta / gamma) ≤ 2 * delta / gamma := by
      have hnon : 0 ≤ (1 - 2 * delta) * (delta / gamma) :=
        mul_nonneg (by linarith) (by positivity)
      calc
        4 * delta * (delta / gamma) = 2 * delta / gamma -
            2 * ((1 - 2 * delta) * (delta / gamma)) := by ring
        _ ≤ 2 * delta / gamma := by linarith
    have hmain :
        (1 + 2 * ((K : ℝ) * gamma) + 2 * delta) *
            (1 + 2 * delta / gamma) ≤
          4 * (K : ℝ) * delta + 2 * (K : ℝ) * gamma +
            4 * delta / gamma + 2 := by
      have hnon : 0 ≤ 1 - 2 * delta := by linarith
      have hexpand :
          (1 + 2 * ((K : ℝ) * gamma) + 2 * delta) *
              (1 + 2 * delta / gamma) =
            4 * (K : ℝ) * delta + 2 * (K : ℝ) * gamma +
              4 * delta * (delta / gamma) + 2 * delta +
              2 * delta / gamma + 1 := by
            field_simp [ne_of_gt hgamma]
            ring
      rw [hexpand]
      have htwo : 2 * delta ≤ 1 := by linarith
      have hsum : 4 * delta * (delta / gamma) + 2 * delta ≤
          2 * delta / gamma + 1 := by
        nlinarith [hquad, htwo]
      calc
        4 * (K : ℝ) * delta + 2 * (K : ℝ) * gamma +
            4 * delta * (delta / gamma) + 2 * delta +
            2 * delta / gamma + 1 ≤
          4 * (K : ℝ) * delta + 2 * (K : ℝ) * gamma +
            (2 * delta / gamma + 1) + (2 * delta / gamma + 1) := by
              nlinarith [hsum]
        _ = 4 * (K : ℝ) * delta + 2 * (K : ℝ) * gamma +
            4 * delta / gamma + 2 := by ring
    have hcardR' : (S.card : ℝ) ≤
        (1 + 2 * ((K : ℝ) * gamma) + 2 * delta) *
          (1 + 2 * delta / gamma) := by
      have hab : 1 + (b - a) =
          1 + 2 * ((K : ℝ) * gamma) + 2 * delta := by
        dsimp [a, b]
        ring
      rw [hab] at hcardR
      exact hcardR
    exact hcardR'.trans hmain

#print axioms FordNearIntegerCount.nearIntegerSet_card_le

end
end FordNearIntegerCount
