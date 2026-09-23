import PostA5TypeIIFourthMoment

/-!
# Long-spacing finite assembly after Appendix A.5

This module generalizes the two-color unit-spacing extraction to the literal
`3B` thinning required before the Type-II shifts.  Floor bins are colored by
their residue modulo `ceil(3B+1)`.  One largest color class supplies one
representative per bin; the extra `+1` pays for the width of the floor bins.
-/

namespace PostA5LongSpacingAssembly

open scoped BigOperators
open PostA5CrowdingDeterministic
open DirichletZeros MAPAPZeroDensityCert

noncomputable section

def floorBinResidue (m : ℕ) (hm : 0 < m) (n : ℤ) : Fin m :=
  ⟨(n % (m : ℤ)).toNat, by
    apply (Int.toNat_lt (Int.emod_nonneg n (by exact_mod_cast hm.ne'))).2
    exact Int.emod_lt_of_pos n (by exact_mod_cast hm)⟩

theorem floorBin_gap_of_same_residue
    {m : ℕ} (hm : 0 < m) {n k : ℤ} (hnk : n ≠ k)
    (hres : floorBinResidue m hm n = floorBinResidue m hm k) :
    (m : ℝ) ≤ |(n : ℝ) - (k : ℝ)| := by
  have hnnonneg : 0 ≤ n % (m : ℤ) :=
    Int.emod_nonneg n (by exact_mod_cast hm.ne')
  have hknonneg : 0 ≤ k % (m : ℤ) :=
    Int.emod_nonneg k (by exact_mod_cast hm.ne')
  have hval := congrArg Fin.val hres
  have hmod : n % (m : ℤ) = k % (m : ℤ) := by
    calc
      n % (m : ℤ) = ((n % (m : ℤ)).toNat : ℤ) :=
        (Int.toNat_of_nonneg hnnonneg).symm
      _ = ((k % (m : ℤ)).toNat : ℤ) := by exact_mod_cast hval
      _ = k % (m : ℤ) := Int.toNat_of_nonneg hknonneg
  have hdvd : (m : ℤ) ∣ n - k := by
    apply (Int.dvd_iff_emod_eq_zero).2
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod)
  have hdvdNat : m ∣ (n - k).natAbs := by
    have := (Int.natAbs_dvd_natAbs).2 hdvd
    simpa using this
  have hdiffpos : 0 < (n - k).natAbs :=
    (Int.natAbs_pos.mpr (sub_ne_zero.mpr hnk))
  have hleNat : m ≤ (n - k).natAbs := Nat.le_of_dvd hdiffpos hdvdNat
  have hleReal : (m : ℝ) ≤ ((n - k).natAbs : ℝ) := by exact_mod_cast hleNat
  simpa [Nat.cast_natAbs, Int.cast_abs] using hleReal

/-- One residue class contains at least a `1/m` fraction of any finite set. -/
theorem exists_large_residue_fiber
    {α : Type*} [DecidableEq α] (Z : Finset α)
    {m : ℕ} (hm : 0 < m) (color : α → Fin m) :
    ∃ i : Fin m, ∃ S : Finset α,
      S = Z.filter (fun x => color x = i) ∧
      S ⊆ Z ∧ Z.card ≤ m * S.card := by
  classical
  let fiber : Fin m → Finset α := fun i => Z.filter (fun x => color x = i)
  have hcard : Z.card = ∑ i, (fiber i).card := by
    calc
      Z.card = ∑ x ∈ Z, 1 := by simp
      _ = ∑ i : Fin m, ∑ x ∈ Z with color x = i, 1 := by
        symm
        exact Finset.sum_fiberwise Z color (fun _ => 1)
      _ = ∑ i, (fiber i).card := by simp [fiber]
  have hsum :
      (∑ _i : Fin m, Z.card) ≤
        ∑ i : Fin m, m * (fiber i).card := by
    calc
      (∑ _i : Fin m, Z.card) = m * Z.card := by simp
      _ = m * ∑ i : Fin m, (fiber i).card := by rw [← hcard]
      _ ≤ ∑ i : Fin m, m * (fiber i).card := by
        rw [Finset.mul_sum]
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩ hsum
  refine ⟨i, fiber i, rfl, Finset.filter_subset _ _, hi⟩

/-- Long-separated representatives with the full local fiber loss visible.
If each unit floor bin contains at most `L` input points, the selected set
loses at most `m*L`. -/
theorem exists_floorBinRepresentatives_same_residue
    (Z : Finset ℂ) {m L : ℕ} (hm : 0 < m)
    (hcap : ∀ n ∈ occupiedFloorBins Z,
      (Z.filter fun rho => Int.floor rho.im = n).card ≤ L) :
    ∃ S : Finset ℂ,
      S ⊆ Z ∧
      (∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' →
        (m : ℝ) - 1 ≤ |rho.im - rho'.im|) ∧
      Z.card ≤ m * L * S.card := by
  classical
  let bins := occupiedFloorBins Z
  obtain ⟨i, chosen, hchosen, hchosenSub, hlarge⟩ :=
    exists_large_residue_fiber bins hm (floorBinResidue m hm)
  let S : Finset ℂ := chosen.image (floorBinRepresentative Z)
  have hchosenOcc : chosen ⊆ occupiedFloorBins Z := by
    simpa [hchosen, bins] using hchosenSub
  have hSsub : S ⊆ Z := by
    intro rho hrho
    change rho ∈ chosen.image (floorBinRepresentative Z) at hrho
    rw [Finset.mem_image] at hrho
    obtain ⟨n, hn, rfl⟩ := hrho
    exact (floorBinRepresentative_spec (hchosenOcc hn)).1
  have hScard : S.card = chosen.card := by
    unfold S
    apply Finset.card_image_iff.mpr
    intro n hn k hk heq
    have hnSpec := floorBinRepresentative_spec (hchosenOcc hn)
    have hkSpec := floorBinRepresentative_spec (hchosenOcc hk)
    rw [heq] at hnSpec
    exact hnSpec.2.symm.trans hkSpec.2
  have hgap : ∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' →
      (m : ℝ) - 1 ≤ |rho.im - rho'.im| := by
    intro rho hrho rho' hrho' hne
    change rho ∈ chosen.image (floorBinRepresentative Z) at hrho
    change rho' ∈ chosen.image (floorBinRepresentative Z) at hrho'
    rw [Finset.mem_image] at hrho hrho'
    obtain ⟨n, hn, rfl⟩ := hrho
    obtain ⟨k, hk, rfl⟩ := hrho'
    have hnSpec := floorBinRepresentative_spec (hchosenOcc hn)
    have hkSpec := floorBinRepresentative_spec (hchosenOcc hk)
    have hnk : n ≠ k := by
      intro h
      apply hne
      rw [h]
    have hnColor : floorBinResidue m hm n = i := by
      have hn' : n ∈ bins.filter (fun x => floorBinResidue m hm x = i) := by
        rw [← hchosen]
        exact hn
      exact (Finset.mem_filter.mp hn').2
    have hkColor : floorBinResidue m hm k = i := by
      have hk' : k ∈ bins.filter (fun x => floorBinResidue m hm x = i) := by
        rw [← hchosen]
        exact hk
      exact (Finset.mem_filter.mp hk').2
    have hbin := floorBin_gap_of_same_residue hm hnk (hnColor.trans hkColor.symm)
    let x : ℝ := (n : ℤ)
    let y : ℝ := (k : ℤ)
    have hxlo : x ≤ (floorBinRepresentative Z n).im := by
      dsimp [x]
      simpa only [hnSpec.2] using
        (Int.floor_le (floorBinRepresentative Z n).im)
    have hxhi : (floorBinRepresentative Z n).im < x + 1 := by
      dsimp [x]
      simpa only [hnSpec.2] using
        (Int.lt_floor_add_one (floorBinRepresentative Z n).im)
    have hylo : y ≤ (floorBinRepresentative Z k).im := by
      dsimp [y]
      simpa only [hkSpec.2] using
        (Int.floor_le (floorBinRepresentative Z k).im)
    have hyhi : (floorBinRepresentative Z k).im < y + 1 := by
      dsimp [y]
      simpa only [hkSpec.2] using
        (Int.lt_floor_add_one (floorBinRepresentative Z k).im)
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hmOne : (1 : ℝ) ≤ m := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm.ne')
    change (m : ℝ) ≤ |x - y| at hbin
    rcases le_total x y with hxy | hyx
    · rw [abs_of_nonpos (sub_nonpos.mpr hxy)] at hbin
      rw [abs_of_nonpos]
      · linarith
      · linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hyx)] at hbin
      rw [abs_of_nonneg]
      · linarith
      · linarith
  have hmaps : ∀ rho ∈ Z, Int.floor rho.im ∈ occupiedFloorBins Z := by
    intro rho hrho
    exact Finset.mem_image.mpr ⟨rho, hrho, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps (fun _ => 1)
  have hZbins : Z.card ≤ (occupiedFloorBins Z).card * L := by
    calc
      Z.card = ∑ rho ∈ Z, 1 := by simp
      _ = ∑ n ∈ occupiedFloorBins Z,
          ∑ rho ∈ Z with Int.floor rho.im = n, 1 := hfiber.symm
      _ ≤ ∑ _n ∈ occupiedFloorBins Z, L := by
        apply Finset.sum_le_sum
        intro n hn
        simpa using hcap n hn
      _ = (occupiedFloorBins Z).card * L := by simp
  refine ⟨S, hSsub, hgap, ?_⟩
  calc
    Z.card ≤ (occupiedFloorBins Z).card * L := hZbins
    _ ≤ (m * chosen.card) * L := by
      exact Nat.mul_le_mul_right L (by simpa [bins] using hlarge)
    _ = m * L * S.card := by rw [hScard]; ring

/-- Number of residue colors needed to make post-shift ordinates
one-separated at vertical cutoff `B`. -/
def longSpacingColorCount (B : ℝ) : ℕ := ⌈3 * B + 1⌉₊

theorem longSpacingColorCount_pos {B : ℝ} (hB : 0 ≤ B) :
    0 < longSpacingColorCount B := by
  unfold longSpacingColorCount
  have hceil : 3 * B + 1 ≤ (⌈3 * B + 1⌉₊ : ℝ) := Nat.le_ceil _
  by_contra h
  have hz : ⌈3 * B + 1⌉₊ = 0 := Nat.eq_zero_of_not_pos h
  rw [hz] at hceil
  norm_num at hceil
  linarith

/-- Literal `3B` thinning.  The loss is
`ceil(3B+1) * L`, hence polylogarithmic for `B=(log R)^2`. -/
theorem exists_threeBSeparated_representatives
    (Z : Finset ℂ) {B : ℝ} (hB : 0 ≤ B) {L : ℕ}
    (hcap : ∀ n ∈ occupiedFloorBins Z,
      (Z.filter fun rho => Int.floor rho.im = n).card ≤ L) :
    ∃ S : Finset ℂ,
      S ⊆ Z ∧
      (∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' →
        3 * B ≤ |rho.im - rho'.im|) ∧
      Z.card ≤ longSpacingColorCount B * L * S.card := by
  let m := longSpacingColorCount B
  have hm : 0 < m := longSpacingColorCount_pos hB
  obtain ⟨S, hS, hsep, hcard⟩ :=
    exists_floorBinRepresentatives_same_residue Z hm hcap
  refine ⟨S, hS, ?_, hcard⟩
  intro rho hrho rho' hrho' hne
  have hceil : 3 * B + 1 ≤ (m : ℝ) := by
    dsimp [m, longSpacingColorCount]
    exact Nat.le_ceil _
  exact hceil |> fun h => by linarith [hsep rho hrho rho' hrho' hne]

/-- The support cardinality in one floor bin is bounded by the certified
natural A.5 cap.  This is the exact distinct-zero/multiplicity conversion
needed by the long-spacing extraction. -/
theorem zeroSupport_floorBin_card_le_crowdingNatCap
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {sigma T : ℝ} (hsigma : 1 / 2 ≤ sigma) (hT : 0 ≤ T)
    {n : ℤ} (hn : n ∈ occupiedFloorBins (zeroSupport chi sigma T)) :
    ((zeroSupport chi sigma T).filter
      fun rho => Int.floor rho.im = n).card ≤
        certifiedA5CrowdingNatCap q T := by
  classical
  let Z := zeroSupport chi sigma T
  let F := Z.filter fun rho => Int.floor rho.im = n
  obtain ⟨rho0, hrho0, hfloor0⟩ := Finset.mem_image.mp hn
  have hcap := floor_closedUnitWindowCount_le_crowdingNatCap
    chi hchi hsigma hT hrho0
  rw [hfloor0] at hcap
  have hsub : F ⊆ MAPLocalZeroWindow.closedUnitWindowSupport chi sigma n := by
    intro rho hrho
    have hrhoZ : rho ∈ Z := (Finset.mem_filter.mp hrho).1
    have hfloor : Int.floor rho.im = n := (Finset.mem_filter.mp hrho).2
    have hlocal := mem_closedUnitWindowSupport_floor chi hrhoZ
    simpa [hfloor] using hlocal
  calc
    F.card = ∑ _rho ∈ F, 1 := by simp
    _ ≤ ∑ rho ∈ F,
        DirichletZeros.zeroMultiplicity chi sigma
          (MAPLocalZeroWindow.windowHeight n) rho := by
      apply Finset.sum_le_sum
      intro rho hrho
      have hrhoZ : rho ∈ Z := (Finset.mem_filter.mp hrho).1
      have hfloor : Int.floor rho.im = n := (Finset.mem_filter.mp hrho).2
      have hpos := MAPAPZeroDensityCert.zeroMultiplicity_pos_of_mem
        chi sigma T hrhoZ
      have heq := zeroMultiplicity_eq_floor_window chi hrhoZ
      rw [hfloor] at heq
      rw [← heq]
      omega
    _ ≤ ∑ rho ∈ MAPLocalZeroWindow.closedUnitWindowSupport chi sigma n,
        DirichletZeros.zeroMultiplicity chi sigma
          (MAPLocalZeroWindow.windowHeight n) rho :=
      Finset.sum_le_sum_of_subset hsub
    _ = MAPLocalZeroWindow.closedUnitWindowCount chi sigma n := rfl
    _ ≤ certifiedA5CrowdingNatCap q T := hcap

/-- Canonical long-spaced subset of the actual global zero support. -/
theorem exists_threeBSeparated_zeroSupport
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {sigma T B : ℝ} (hsigma : 1 / 2 ≤ sigma) (hT : 0 ≤ T)
    (hB : 0 ≤ B) :
    ∃ S : Finset ℂ,
      S ⊆ zeroSupport chi sigma T ∧
      (∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' →
        3 * B ≤ |rho.im - rho'.im|) ∧
      (zeroSupport chi sigma T).card ≤
        longSpacingColorCount B * certifiedA5CrowdingNatCap q T * S.card := by
  apply exists_threeBSeparated_representatives (zeroSupport chi sigma T) hB
  intro n hn
  exact zeroSupport_floorBin_card_le_crowdingNatCap
    chi hchi hsigma hT hn

/-- Natural-valued multiplicity bound, convenient for allocating the zero
mass exactly between the two detector fibers. -/
theorem dirichletZeroCount_le_crowdingNatCap_mul_supportCard
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {sigma T : ℝ} (hsigma : 1 / 2 ≤ sigma) (hT : 0 ≤ T) :
    dirichletZeroCount chi sigma T ≤
      certifiedA5CrowdingNatCap q T * (zeroSupport chi sigma T).card := by
  unfold dirichletZeroCount
  calc
    ∑ rho ∈ zeroSupport chi sigma T,
        zeroMultiplicity chi sigma T rho ≤
      ∑ _rho ∈ zeroSupport chi sigma T,
        certifiedA5CrowdingNatCap q T := by
      apply Finset.sum_le_sum
      intro rho hrho
      exact (zeroMultiplicity_le_floor_closedUnitWindowCount chi hrho).trans
        (floor_closedUnitWindowCount_le_crowdingNatCap
          chi hchi hsigma hT hrho)
    _ = certifiedA5CrowdingNatCap q T *
        (zeroSupport chi sigma T).card := by simp [mul_comm]

/-- Natural-valued weighted version of the `3B` extraction.  The square of
the A.5 natural cap is intentional: one factor bounds multiplicity and the
other bounds the number of distinct zeros in each unit bin. -/
theorem exists_threeBSeparated_zeroSupport_natWeighted
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {sigma T B : ℝ} (hsigma : 1 / 2 ≤ sigma) (hT : 0 ≤ T)
    (hB : 0 ≤ B) :
    ∃ S : Finset ℂ,
      S ⊆ zeroSupport chi sigma T ∧
      (∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' →
        3 * B ≤ |rho.im - rho'.im|) ∧
      dirichletZeroCount chi sigma T ≤
        (longSpacingColorCount B *
          certifiedA5CrowdingNatCap q T ^ 2) * S.card := by
  obtain ⟨S, hS, hsep, hsupport⟩ :=
    exists_threeBSeparated_zeroSupport chi hchi hsigma hT hB
  refine ⟨S, hS, hsep, ?_⟩
  have hcount := dirichletZeroCount_le_crowdingNatCap_mul_supportCard
    chi hchi hsigma hT
  calc
    dirichletZeroCount chi sigma T ≤
        certifiedA5CrowdingNatCap q T *
          (zeroSupport chi sigma T).card := hcount
    _ ≤ certifiedA5CrowdingNatCap q T *
        (longSpacingColorCount B * certifiedA5CrowdingNatCap q T * S.card) :=
      Nat.mul_le_mul_left _ hsupport
    _ = (longSpacingColorCount B *
          certifiedA5CrowdingNatCap q T ^ 2) * S.card := by ring

/-- Weighted MAP zero count controlled by the same explicit long-spaced
subset.  Both A.5 losses are visible: the real multiplicity envelope and the
natural unit-bin cap. -/
theorem exists_threeBSeparated_zeroSupport_weighted
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {sigma T B : ℝ} (hsigma : 1 / 2 ≤ sigma) (hT : 0 ≤ T)
    (hB : 0 ≤ B) :
    ∃ S : Finset ℂ,
      S ⊆ zeroSupport chi sigma T ∧
      (∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' →
        3 * B ≤ |rho.im - rho'.im|) ∧
      (DirichletZeros.dirichletZeroCount chi sigma T : ℝ) ≤
        certifiedA5CrowdingEnvelope q T *
          (longSpacingColorCount B * certifiedA5CrowdingNatCap q T) *
          S.card := by
  obtain ⟨S, hS, hsep, hcard⟩ :=
    exists_threeBSeparated_zeroSupport chi hchi hsigma hT hB
  refine ⟨S, hS, hsep, ?_⟩
  have hcount := dirichletZeroCount_le_crowdingEnvelope_mul_supportCard
    chi hchi hsigma hT
  have hcardR : ((zeroSupport chi sigma T).card : ℝ) ≤
      (longSpacingColorCount B * certifiedA5CrowdingNatCap q T : ℕ) *
        (S.card : ℝ) := by exact_mod_cast hcard
  have henvelope0 : 0 ≤ certifiedA5CrowdingEnvelope q T := by
    have hqone : (1 : ℝ) ≤ q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hscale : 1 ≤ (q : ℝ) * (T + 3) := by
      exact one_le_mul_of_one_le_of_one_le hqone (by linarith)
    unfold certifiedA5CrowdingEnvelope
    exact div_nonneg (by
      have h3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
      have h3200 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3200)
      have hs := Real.log_nonneg hscale
      linarith) (Real.log_nonneg (by norm_num))
  calc
    (DirichletZeros.dirichletZeroCount chi sigma T : ℝ) ≤
        certifiedA5CrowdingEnvelope q T *
          (zeroSupport chi sigma T).card := hcount
    _ ≤ certifiedA5CrowdingEnvelope q T *
        ((longSpacingColorCount B * certifiedA5CrowdingNatCap q T : ℕ) *
          (S.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hcardR (by
        exact henvelope0)
    _ = certifiedA5CrowdingEnvelope q T *
          (longSpacingColorCount B * certifiedA5CrowdingNatCap q T) *
          S.card := by push_cast; ring

end

end PostA5LongSpacingAssembly

#print axioms PostA5LongSpacingAssembly.floorBin_gap_of_same_residue
#print axioms PostA5LongSpacingAssembly.exists_large_residue_fiber
#print axioms PostA5LongSpacingAssembly.exists_floorBinRepresentatives_same_residue
#print axioms PostA5LongSpacingAssembly.exists_threeBSeparated_representatives
#print axioms PostA5LongSpacingAssembly.zeroSupport_floorBin_card_le_crowdingNatCap
#print axioms PostA5LongSpacingAssembly.exists_threeBSeparated_zeroSupport_natWeighted
#print axioms PostA5LongSpacingAssembly.exists_threeBSeparated_zeroSupport_weighted
