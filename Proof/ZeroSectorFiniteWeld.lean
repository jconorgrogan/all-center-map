import ZeroDeterminantSectorClosure

namespace MAPMixedMeanZeroClose

open ArithmeticFunction MixedMellinCert DeterminantCountWeld ShiuFoundation MAPMixedMean

noncomputable section

/-- Positive integers up to the literal quotient envelope. -/
def positiveRange (A : ℕ) : Finset ℕ := Finset.Icc 1 A

/-- All noncentral neighbors of `a` in `[1,A]` at distance at most `H`. -/
def neighborSet (A H a : ℕ) : Finset ℕ :=
  (positiveRange A).filter fun b => b ≠ a ∧ a.dist b ≤ H

 theorem neighborSet_subset_twoIntervals (A H a : ℕ) :
    neighborSet A H a ⊆ Finset.Ico (a - H) a ∪ Finset.Ioc a (a + H) := by
  intro b hb
  simp only [neighborSet, positiveRange, Finset.mem_filter, Finset.mem_Icc] at hb
  rcases hb with ⟨_, hbne, hdist⟩
  rcases lt_or_gt_of_ne hbne with hba | hab
  · apply Finset.mem_union_left
    simp only [Finset.mem_Ico]
    constructor
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba.le] at hdist
      omega
    · exact hba
  · apply Finset.mem_union_right
    simp only [Finset.mem_Ioc]
    constructor
    · exact hab
    · rw [Nat.dist_eq_sub_of_le hab.le] at hdist
      omega

 theorem card_neighborSet_le (A H a : ℕ) :
    (neighborSet A H a).card ≤ 2 * H := by
  calc
    (neighborSet A H a).card ≤
        (Finset.Ico (a - H) a ∪ Finset.Ioc a (a + H)).card :=
      Finset.card_le_card (neighborSet_subset_twoIntervals A H a)
    _ ≤ (Finset.Ico (a - H) a).card + (Finset.Ioc a (a + H)).card :=
      Finset.card_union_le _ _
    _ ≤ 2 * H := by simp; omega

/-- Ordered neighboring pairs in `[1,A]`; coprimality and dyadic filters can
only decrease this ambient set. -/
def symmetricNeighborPairs (A H : ℕ) : Finset (ℕ × ℕ) :=
  ((positiveRange A).product (positiveRange A)).filter fun p =>
    p.1 ≠ p.2 ∧ p.1.dist p.2 ≤ H

 theorem symmetricNeighborPairs_eq_biUnion (A H : ℕ) :
    symmetricNeighborPairs A H =
      (positiveRange A).biUnion fun a =>
        (neighborSet A H a).image fun b => (a, b) := by
  ext p
  constructor
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp'.1
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1, hp1, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨p.2, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hp2, hp'.2.1.symm, hp'.2.2⟩
  · intro hp
    obtain ⟨a, ha, hpa⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨b, hb, hpab⟩ := Finset.mem_image.mp hpa
    subst p
    have hb' := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨ha, hb'.1⟩, hb'.2.1.symm, hb'.2.2⟩

 theorem firstSquareMass_le (f : ℕ → ℕ) (A H : ℕ) :
    (∑ p ∈ symmetricNeighborPairs A H, f p.1 ^ 2) ≤
      2 * H * ∑ a ∈ positiveRange A, f a ^ 2 := by
  rw [symmetricNeighborPairs_eq_biUnion]
  calc
    (∑ p ∈ (positiveRange A).biUnion fun a =>
        (neighborSet A H a).image fun b => (a, b), f p.1 ^ 2) ≤
      ∑ a ∈ positiveRange A,
        ∑ p ∈ (neighborSet A H a).image (fun b => (a, b)), f p.1 ^ 2 := by
      induction positiveRange A using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          rw [Finset.biUnion_insert, Finset.sum_insert ha]
          calc
            (∑ p ∈ (neighborSet A H a).image (fun b => (a, b)) ∪
                s.biUnion fun a => (neighborSet A H a).image fun b => (a, b),
                f p.1 ^ 2) ≤
              (∑ p ∈ (neighborSet A H a).image (fun b => (a, b)), f p.1 ^ 2) +
                ∑ p ∈ s.biUnion fun a =>
                  (neighborSet A H a).image fun b => (a, b), f p.1 ^ 2 := by
                let left := (neighborSet A H a).image fun b => (a, b)
                let right := s.biUnion fun a =>
                  (neighborSet A H a).image fun b => (a, b)
                rw [show left ∪ right = left ∪ (right \ left) by
                  ext x; simp [left, right]]
                rw [Finset.sum_union (Finset.disjoint_sdiff)]
                exact Nat.add_le_add_left
                  (Finset.sum_le_sum_of_subset (Finset.sdiff_subset)) _
            _ ≤ (∑ p ∈ (neighborSet A H a).image (fun b => (a, b)), f p.1 ^ 2) +
                ∑ a ∈ s, ∑ p ∈ (neighborSet A H a).image (fun b => (a, b)),
                  f p.1 ^ 2 := Nat.add_le_add_left ih _
    _ = ∑ a ∈ positiveRange A, (neighborSet A H a).card * f a ^ 2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_image]
      · simp
      · intro x hx y hy hxy
        exact congrArg Prod.snd hxy
    _ ≤ ∑ a ∈ positiveRange A, (2 * H) * f a ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      exact Nat.mul_le_mul_right (f a ^ 2) (card_neighborSet_le A H a)
    _ = 2 * H * ∑ a ∈ positiveRange A, f a ^ 2 := by rw [Finset.mul_sum]

 theorem secondSquareMass_eq_firstSquareMass (f : ℕ → ℕ) (A H : ℕ) :
    (∑ p ∈ symmetricNeighborPairs A H, f p.2 ^ 2) =
      ∑ p ∈ symmetricNeighborPairs A H, f p.1 ^ 2 := by
  apply Finset.sum_equiv (Equiv.prodComm ℕ ℕ)
  · intro p
    constructor
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp'.1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hp2, hp1⟩, hp'.2.1.symm,
          by simpa [Nat.dist_comm] using hp'.2.2⟩
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp'.1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hp2, hp1⟩, hp'.2.1.symm,
          by simpa [Nat.dist_comm] using hp'.2.2⟩
  · intro p hp
    rfl

 theorem symmetricNeighbor_tauMass_le (k A H : ℕ) :
    (∑ p ∈ symmetricNeighborPairs A H, tauAF k p.1 * tauAF k p.2) ≤
      2 * H * zeroSecondMoment k A := by
  have htwo :
      2 * (∑ p ∈ symmetricNeighborPairs A H,
        tauAF k p.1 * tauAF k p.2) ≤
      2 * (2 * H * ∑ a ∈ positiveRange A, tauAF k a ^ 2) := by
    calc
      2 * (∑ p ∈ symmetricNeighborPairs A H,
          tauAF k p.1 * tauAF k p.2) =
          ∑ p ∈ symmetricNeighborPairs A H,
            2 * (tauAF k p.1 * tauAF k p.2) := by rw [Finset.mul_sum]
      _ ≤ ∑ p ∈ symmetricNeighborPairs A H,
          (tauAF k p.1 ^ 2 + tauAF k p.2 ^ 2) := by
        apply Finset.sum_le_sum
        intro p hp
        nlinarith [sq_nonneg ((tauAF k p.1 : ℤ) - tauAF k p.2)]
      _ = (∑ p ∈ symmetricNeighborPairs A H, tauAF k p.1 ^ 2) +
          ∑ p ∈ symmetricNeighborPairs A H, tauAF k p.2 ^ 2 := by
        rw [Finset.sum_add_distrib]
      _ = 2 * ∑ p ∈ symmetricNeighborPairs A H, tauAF k p.1 ^ 2 := by
        rw [secondSquareMass_eq_firstSquareMass]
        simp [two_mul]
      _ ≤ 2 * (2 * H * ∑ a ∈ positiveRange A, tauAF k a ^ 2) :=
        Nat.mul_le_mul_left 2 (firstSquareMass_le (tauAF k) A H)
  apply Nat.le_of_mul_le_mul_left htwo (by omega)

 theorem symmetricNeighbor_tauMass_cast_le_harmonic
    (k A H : ℕ) (hk : 1 ≤ k) :
    ((∑ p ∈ symmetricNeighborPairs A H,
      tauAF k p.1 * tauAF k p.2 : ℕ) : ℚ) ≤
      (2 * H * A : ℕ) * harmonic A ^ (k * k - 1) := by
  calc
    ((∑ p ∈ symmetricNeighborPairs A H,
      tauAF k p.1 * tauAF k p.2 : ℕ) : ℚ) ≤
      ((2 * H * zeroSecondMoment k A : ℕ) : ℚ) := by
        exact_mod_cast symmetricNeighbor_tauMass_le k A H
    _ = (2 * H : ℕ) * (zeroSecondMoment k A : ℚ) := by push_cast; ring
    _ ≤ (2 * H : ℕ) * ((A : ℚ) * harmonic A ^ (k * k - 1)) := by
      gcongr
      exact zeroSecondMoment_cast_le_harmonic k A hk
    _ = (2 * H * A : ℕ) * harmonic A ^ (k * k - 1) := by push_cast; ring


/-- Exact reduced short pairs for content `d`, preserving both dyadic collars
and the literal short-difference mask. -/
def reducedShortPairs (M K d : ℕ) : Finset (ℕ × ℕ) :=
  ((positiveRange ((2 * M) / d)).product
    (positiveRange ((2 * M) / d))).filter fun p =>
      d * p.1 ∈ dyadic M ∧ d * p.2 ∈ dyadic M ∧
      p.1 ≠ p.2 ∧ p.1.Coprime p.2 ∧ d * p.1.dist p.2 ≤ K

 theorem reducedShortPairs_subset_symmetric (M K d : ℕ) (hd : 0 < d) :
    reducedShortPairs M K d ⊆
      symmetricNeighborPairs ((2 * M) / d) (K / d) := by
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  rcases hp'.2 with ⟨_, _, hne, _, hdist⟩
  apply Finset.mem_filter.mpr
  refine ⟨hp'.1, hne, ?_⟩
  apply (Nat.le_div_iff_mul_le hd).2
  simpa [Nat.mul_comm] using hdist

 theorem reducedShortPairs_tauMass_cast_le
    (k M K d : ℕ) (hk : 1 ≤ k) (hd : 0 < d) :
    ((∑ p ∈ reducedShortPairs M K d,
      tauAF k p.1 * tauAF k p.2 : ℕ) : ℚ) ≤
      (2 * (K / d) * ((2 * M) / d) : ℕ) *
        harmonic ((2 * M) / d) ^ (k * k - 1) := by
  calc
    ((∑ p ∈ reducedShortPairs M K d,
      tauAF k p.1 * tauAF k p.2 : ℕ) : ℚ) ≤
      ((∑ p ∈ symmetricNeighborPairs ((2 * M) / d) (K / d),
        tauAF k p.1 * tauAF k p.2 : ℕ) : ℚ) := by
          exact_mod_cast Finset.sum_le_sum_of_subset
            (reducedShortPairs_subset_symmetric M K d hd)
    _ ≤ _ := symmetricNeighbor_tauMass_cast_le_harmonic
      k ((2 * M) / d) (K / d) hk


 theorem reducedShort_representation_unique
    {d e a b c f : ℕ} (hd : 0 < d) (he : 0 < e)
    (hab : a.Coprime b) (hcf : c.Coprime f)
    (h₁ : d * a = e * c) (h₂ : d * b = e * f) :
    d = e ∧ a = c ∧ b = f := by
  have hde : d = e := by
    calc
      d = (d * a).gcd (d * b) := by
        rw [Nat.gcd_mul_left, hab.gcd_eq_one, mul_one]
      _ = (e * c).gcd (e * f) := by rw [h₁, h₂]
      _ = e := by rw [Nat.gcd_mul_left, hcf.gcd_eq_one, mul_one]
  subst e
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hd h₁,
    Nat.eq_of_mul_eq_mul_left hd h₂⟩


/-- Union of all fixed reduced zero slices over the literal content and
neighbor ranges. -/
def reducedZeroSliceUnion (M N K Y : ℕ) : Finset LiteralTuple :=
  (Finset.Icc 1 K).biUnion fun d =>
    (reducedShortPairs M K d).biUnion fun p =>
      fixedZeroLiteralSlice M N K Y d p.1 p.2

 theorem zeroSector_eq_reducedZeroSliceUnion (M N K Y : ℕ) :
    zeroSector M N K Y = reducedZeroSliceUnion M N K Y := by
  classical
  ext t
  constructor
  · intro ht
    have ht' := Finset.mem_filter.mp ht
    have hlit := ht'.1
    have hdet := ht'.2
    have hlit' := Finset.mem_filter.mp hlit
    rcases hlit'.2 with ⟨hshortNe, hshortK, hdetY⟩
    obtain ⟨hshortBox, hlongBox⟩ := Finset.mem_product.mp hlit'.1
    obtain ⟨hm1, hm2⟩ := Finset.mem_product.mp hshortBox
    let m1 := t.1.1
    let m2 := t.1.2
    let d := m1.gcd m2
    let a := m1 / d
    let b := m2 / d
    have hm1bounds : M < m1 ∧ m1 ≤ 2 * M := by
      simpa only [m1, dyadic, Finset.mem_Ioc] using hm1
    have hm2bounds : M < m2 ∧ m2 ≤ 2 * M := by
      simpa only [m2, dyadic, Finset.mem_Ioc] using hm2
    have hm1pos : 0 < m1 := (Nat.zero_le M).trans_lt hm1bounds.1
    have hm2pos : 0 < m2 := (Nat.zero_le M).trans_lt hm2bounds.1
    have hd : 0 < d := by
      exact Nat.gcd_pos_of_pos_left m2 hm1pos
    have hda : d * a = m1 := by
      exact Nat.mul_div_cancel' (Nat.gcd_dvd_left m1 m2)
    have hdb : d * b = m2 := by
      exact Nat.mul_div_cancel' (Nat.gcd_dvd_right m1 m2)
    have ha : 0 < a := Nat.div_pos (Nat.gcd_le_left m2 hm1pos) hd
    have hb : 0 < b := Nat.div_pos (Nat.gcd_le_right m1 hm2pos) hd
    have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd hd
    have habne : a ≠ b := by
      intro heq
      apply hshortNe
      change m1 = m2
      rw [← hda, ← hdb, heq]
    have hdist : d * a.dist b ≤ K := by
      rw [← Nat.dist_mul_left, hda, hdb]
      exact hshortK
    have hdK : d ≤ K := by
      have hdistpos : 0 < a.dist b := Nat.dist_pos_of_ne habne
      exact (Nat.le_mul_of_pos_right d hdistpos).trans hdist
    have haRange : a ∈ positiveRange ((2 * M) / d) := by
      simp only [positiveRange, Finset.mem_Icc]
      constructor
      · exact ha
      · exact Nat.div_le_div_right hm1bounds.2
    have hbRange : b ∈ positiveRange ((2 * M) / d) := by
      simp only [positiveRange, Finset.mem_Icc]
      constructor
      · exact hb
      · exact Nat.div_le_div_right hm2bounds.2
    have hp : (a,b) ∈ reducedShortPairs M K d := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨haRange, hbRange⟩, ?_⟩
      exact ⟨by rw [hda]; exact hm1, by rw [hdb]; exact hm2,
        habne, hab, hdist⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨d, Finset.mem_Icc.mpr ⟨hd, hdK⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨(a,b), hp, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨hlit, ?_, hdet⟩
    change t.1 = (d * a, d * b)
    apply Prod.ext
    · exact hda.symm
    · exact hdb.symm
  · intro ht
    obtain ⟨d, hd, htd⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨p, hp, htp⟩ := Finset.mem_biUnion.mp htd
    have htp' := Finset.mem_filter.mp htp
    exact Finset.mem_filter.mpr ⟨htp'.1, htp'.2.2⟩


 theorem sum_biUnion_le_sum {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset κ) (t : κ → Finset ι) (f : ι → ℕ) :
    (∑ x ∈ s.biUnion t, f x) ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      let left := t a
      let right := s.biUnion t
      rw [show left ∪ right = left ∪ (right \ left) by
        ext x; simp [left, right]]
      rw [Finset.sum_union (Finset.disjoint_sdiff)]
      exact Nat.add_le_add_left
        ((Finset.sum_le_sum_of_subset Finset.sdiff_subset).trans ih) _

/-- The raw divisor weight in the paper's four-index count. -/
def literalTauMass (k : ℕ) (s : Finset LiteralTuple) : ℕ :=
  ∑ t ∈ s, tauAF k t.2.1 * tauAF k t.2.2

 theorem fixedZeroLiteralSlice_tauMass_eq_zeroFiber
    (k M N K Y d a b : ℕ) (hd : 0 < d)
    (hshortBox : (d * a, d * b) ∈ (dyadic M).product (dyadic M))
    (hshortNe : d * a ≠ d * b)
    (hshortK : (d * a).dist (d * b) ≤ K) :
    literalTauMass k (fixedZeroLiteralSlice M N K Y d a b) =
      fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂) (zeroFiber N a b) := by
  classical
  unfold literalTauMass fiberMass
  rw [← image_fixedZeroLiteralSlice_eq_zeroFiber
    M N K Y d a b hd hshortBox hshortNe hshortK]
  rw [Finset.sum_image fixedZeroLiteralSlice_snd_injOn]

 theorem fixedZeroLiteralSlice_tauMass_paper_normalized
    (k M N K Y d a b : ℕ) (hk : 1 ≤ k) (hM : 0 < M)
    (hd : 0 < d) (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b)
    (hshortBox : (d * a, d * b) ∈ (dyadic M).product (dyadic M))
    (hshortNe : d * a ≠ d * b)
    (hshortK : (d * a).dist (d * b) ≤ K) :
    (literalTauMass k (fixedZeroLiteralSlice M N K Y d a b) : ℚ) ≤
      ((tauAF k b * tauAF k a : ℕ) : ℚ) *
        (((2 * N * d : ℕ) : ℚ) / (M : ℚ)) *
          harmonic (2 * N) ^ (k * k - 1) := by
  rw [fixedZeroLiteralSlice_tauMass_eq_zeroFiber
    k M N K Y d a b hd hshortBox hshortNe hshortK]
  exact zeroFiber_tauMass_paper_normalized k M N d a b hk hM hd hab ha hb
    (Finset.mem_product.mp hshortBox).1


 theorem zeroSector_tauMass_le_tripleSum (k M N K Y : ℕ) :
    literalTauMass k (zeroSector M N K Y) ≤
      ∑ d ∈ Finset.Icc 1 K, ∑ p ∈ reducedShortPairs M K d,
        literalTauMass k (fixedZeroLiteralSlice M N K Y d p.1 p.2) := by
  rw [zeroSector_eq_reducedZeroSliceUnion]
  unfold reducedZeroSliceUnion literalTauMass
  calc
    (∑ t ∈ (Finset.Icc 1 K).biUnion fun d =>
        (reducedShortPairs M K d).biUnion fun p =>
          fixedZeroLiteralSlice M N K Y d p.1 p.2,
        tauAF k t.2.1 * tauAF k t.2.2) ≤
      ∑ d ∈ Finset.Icc 1 K,
        ∑ t ∈ (reducedShortPairs M K d).biUnion fun p =>
          fixedZeroLiteralSlice M N K Y d p.1 p.2,
          tauAF k t.2.1 * tauAF k t.2.2 :=
      sum_biUnion_le_sum _ _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 K, ∑ p ∈ reducedShortPairs M K d,
        ∑ t ∈ fixedZeroLiteralSlice M N K Y d p.1 p.2,
          tauAF k t.2.1 * tauAF k t.2.2 := by
      apply Finset.sum_le_sum
      intro d hd
      exact sum_biUnion_le_sum _ _ _

 theorem normalized_floor_product_le
    (M N K d : ℕ) (hM : 0 < M) :
    (((2 * N * d : ℕ) : ℚ) / (M : ℚ)) *
        (2 * (K / d) * ((2 * M) / d) : ℕ) ≤
      (8 * N * (K / d) : ℕ) := by
  have hAd : ((2 * M) / d) * d ≤ 2 * M := Nat.div_mul_le_self _ _
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by exact_mod_cast hM)).2
  norm_cast
  calc
    (2 * N * d) * (2 * (K / d) * ((2 * M) / d)) =
        4 * N * (K / d) * (((2 * M) / d) * d) := by ring
    _ ≤ 4 * N * (K / d) * (2 * M) :=
      Nat.mul_le_mul_left (4 * N * (K / d)) hAd
    _ = (8 * N * (K / d)) * M := by ring

 theorem fixedContent_zeroMass_cast_le
    (k M N K Y d : ℕ) (hk : 1 ≤ k) (hM : 0 < M) (hd : 0 < d) :
    ((∑ p ∈ reducedShortPairs M K d,
      literalTauMass k (fixedZeroLiteralSlice M N K Y d p.1 p.2) : ℕ) : ℚ) ≤
      (8 * N * (K / d) : ℕ) *
        harmonic (2 * N) ^ (k * k - 1) *
          harmonic (2 * M) ^ (k * k - 1) := by
  let X : ℚ := ((2 * N * d : ℕ) : ℚ) / (M : ℚ)
  let HN : ℚ := harmonic (2 * N) ^ (k * k - 1)
  let A : ℕ := (2 * M) / d
  let B : ℕ := K / d
  have hHM : harmonic A ^ (k * k - 1) ≤ harmonic (2 * M) ^ (k * k - 1) := by
    apply pow_le_pow_left₀
    · have hz := harmonic_mono (x := 0) (y := A) (Nat.zero_le A)
      simpa using hz
    · exact harmonic_mono (Nat.div_le_self (2 * M) d)
  have hHA0 : (0 : ℚ) ≤ harmonic A := by
    have hz := harmonic_mono (x := 0) (y := A) (Nat.zero_le A)
    simpa using hz
  have hHN0 : (0 : ℚ) ≤ HN := by
    dsimp [HN]
    exact pow_nonneg (by
      have hz := harmonic_mono (x := 0) (y := 2 * N) (Nat.zero_le (2 * N))
      simpa using hz) _
  have hHM0 : (0 : ℚ) ≤ harmonic (2 * M) ^ (k * k - 1) := by
    exact pow_nonneg (by
      have hz := harmonic_mono (x := 0) (y := 2 * M) (Nat.zero_le (2 * M))
      simpa using hz) _
  calc
    ((∑ p ∈ reducedShortPairs M K d,
      literalTauMass k (fixedZeroLiteralSlice M N K Y d p.1 p.2) : ℕ) : ℚ) =
      ∑ p ∈ reducedShortPairs M K d,
        (literalTauMass k (fixedZeroLiteralSlice M N K Y d p.1 p.2) : ℚ) := by
          push_cast; rfl
    _ ≤ ∑ p ∈ reducedShortPairs M K d,
        ((tauAF k p.2 * tauAF k p.1 : ℕ) : ℚ) * X * HN := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      obtain ⟨haRange, hbRange⟩ := Finset.mem_product.mp hp'.1
      rcases hp'.2 with ⟨hda, hdb, habne, hab, hdist⟩
      have haBounds : 1 ≤ p.1 ∧ p.1 ≤ A := by
        simpa only [A, positiveRange, Finset.mem_Icc] using haRange
      have hbBounds : 1 ≤ p.2 ∧ p.2 ≤ A := by
        simpa only [A, positiveRange, Finset.mem_Icc] using hbRange
      have ha : 0 < p.1 := haBounds.1
      have hb : 0 < p.2 := hbBounds.1
      have hshortBox : (d * p.1, d * p.2) ∈
          (dyadic M).product (dyadic M) := Finset.mem_product.mpr ⟨hda, hdb⟩
      have hshortNe : d * p.1 ≠ d * p.2 := by
        intro heq
        exact habne (Nat.eq_of_mul_eq_mul_left hd heq)
      have hshortK : (d * p.1).dist (d * p.2) ≤ K := by
        rw [Nat.dist_mul_left]
        exact hdist
      simpa [X, HN] using fixedZeroLiteralSlice_tauMass_paper_normalized
        k M N K Y d p.1 p.2 hk hM hd hab ha hb hshortBox hshortNe hshortK
    _ = X * HN *
        (∑ p ∈ reducedShortPairs M K d,
          (tauAF k p.2 * tauAF k p.1 : ℕ)) := by
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ X * HN *
        ((2 * B * A : ℕ) * harmonic A ^ (k * k - 1)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [A, B, mul_comm] using reducedShortPairs_tauMass_cast_le
          k M K d hk hd
      · positivity
    _ ≤ X * (2 * B * A : ℕ) * HN *
        harmonic (2 * M) ^ (k * k - 1) := by
      have hX : 0 ≤ X := by
        dsimp [X]
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hHN : 0 ≤ HN := hHN0
      calc
        X * HN * ((2 * B * A : ℕ) * harmonic A ^ (k * k - 1)) =
            (X * (2 * B * A : ℕ) * HN) * harmonic A ^ (k * k - 1) := by ring
        _ ≤ (X * (2 * B * A : ℕ) * HN) *
            harmonic (2 * M) ^ (k * k - 1) := by gcongr
    _ ≤ (8 * N * B : ℕ) * HN *
        harmonic (2 * M) ^ (k * k - 1) := by
      have hHN : 0 ≤ HN := hHN0
      have hHMnonneg : 0 ≤ harmonic (2 * M) ^ (k * k - 1) := hHM0
      apply mul_le_mul_of_nonneg_right _ hHMnonneg
      apply mul_le_mul_of_nonneg_right _ hHN
      simpa [X, A, B] using normalized_floor_product_le M N K d hM
    _ = _ := by rfl


 theorem sum_floor_div_cast_le_harmonic (K : ℕ) :
    ((∑ d ∈ Finset.Icc 1 K, K / d : ℕ) : ℚ) ≤
      (K : ℚ) * harmonic K := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := by simp only [Finset.mem_Icc] at hd; omega
  have hfloor : ((K / d : ℕ) : ℚ) ≤ (K : ℚ) / (d : ℚ) := by
    apply (le_div_iff₀ (by exact_mod_cast hdpos)).2
    norm_cast
    exact Nat.div_mul_le_self K d
  simpa [div_eq_mul_inv] using hfloor

/-- Complete paper-scale zero-determinant estimate.  It retains the exact
short dyadic collars and floor neighbors internally, and only at the endpoint
majorizes them by harmonic factors. -/
theorem zeroSector_tauMass_paper_bound
    (k M N K Y : ℕ) (hk : 1 ≤ k) (hM : 0 < M) :
    (literalTauMass k (zeroSector M N K Y) : ℚ) ≤
      (8 * N * K : ℕ) * harmonic K *
        harmonic (2 * N) ^ (k * k - 1) *
          harmonic (2 * M) ^ (k * k - 1) := by
  let HN : ℚ := harmonic (2 * N) ^ (k * k - 1)
  let HM : ℚ := harmonic (2 * M) ^ (k * k - 1)
  have hHN0 : 0 ≤ HN := by
    dsimp [HN]
    exact pow_nonneg (by
      have hz := harmonic_mono (x := 0) (y := 2 * N) (Nat.zero_le (2 * N))
      simpa using hz) _
  have hHM0 : 0 ≤ HM := by
    dsimp [HM]
    exact pow_nonneg (by
      have hz := harmonic_mono (x := 0) (y := 2 * M) (Nat.zero_le (2 * M))
      simpa using hz) _
  have hHK0 : (0 : ℚ) ≤ harmonic K := by
    have hz := harmonic_mono (x := 0) (y := K) (Nat.zero_le K)
    simpa using hz
  calc
    (literalTauMass k (zeroSector M N K Y) : ℚ) ≤
      ((∑ d ∈ Finset.Icc 1 K, ∑ p ∈ reducedShortPairs M K d,
        literalTauMass k (fixedZeroLiteralSlice M N K Y d p.1 p.2) : ℕ) : ℚ) := by
          exact_mod_cast zeroSector_tauMass_le_tripleSum k M N K Y
    _ = ∑ d ∈ Finset.Icc 1 K,
        ((∑ p ∈ reducedShortPairs M K d,
          literalTauMass k (fixedZeroLiteralSlice M N K Y d p.1 p.2) : ℕ) : ℚ) := by
      push_cast
      rfl
    _ ≤ ∑ d ∈ Finset.Icc 1 K,
        (8 * N * (K / d) : ℕ) * HN * HM := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hd : 0 < d := by simp only [Finset.mem_Icc] at hdmem; omega
      simpa [HN, HM] using fixedContent_zeroMass_cast_le
        k M N K Y d hk hM hd
    _ = ((8 * N : ℕ) : ℚ) * HN * HM *
        (∑ d ∈ Finset.Icc 1 K, K / d : ℕ) := by
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ ((8 * N : ℕ) : ℚ) * HN * HM * ((K : ℚ) * harmonic K) := by
      apply mul_le_mul_of_nonneg_left (sum_floor_div_cast_le_harmonic K)
      positivity
    _ = (8 * N * K : ℕ) * harmonic K * HN * HM := by
      push_cast
      ring
    _ = _ := by rfl

end

end MAPMixedMeanZeroClose

#print axioms MAPMixedMeanZeroClose.card_neighborSet_le
#print axioms MAPMixedMeanZeroClose.symmetricNeighbor_tauMass_cast_le_harmonic
#print axioms MAPMixedMeanZeroClose.reducedShortPairs_tauMass_cast_le
#print axioms MAPMixedMeanZeroClose.reducedShort_representation_unique
#print axioms MAPMixedMeanZeroClose.zeroSector_eq_reducedZeroSliceUnion
#print axioms MAPMixedMeanZeroClose.fixedContent_zeroMass_cast_le
#print axioms MAPMixedMeanZeroClose.sum_floor_div_cast_le_harmonic
#print axioms MAPMixedMeanZeroClose.zeroSector_tauMass_paper_bound
