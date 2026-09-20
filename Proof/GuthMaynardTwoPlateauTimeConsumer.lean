import GuthMaynardSmoothedProp31Consumer
import GuthMaynardLargeValueIntervalSubdivision
import GuthMaynardLargeValueThinning

/-!
# Conditional two-plateau and time-bin consumer

This is the finite reduction that is needed before an analytic smoothed
Proposition 3.1 estimate can be used.  The source block is split into the two
literal plateaus, large values are assigned to one of the two pieces, and each
piece is thinned and subdivided into local time bins.  The fixed-weight
Proposition 3.1 witness is obtained before any of these parameters are
introduced, so its constant is uniform in both pieces and all translated
coefficients.

No global Theorem 1.1 claim is made here.
-/

namespace GuthMaynardTwoPlateauTimeConsumer

open scoped BigOperators
open CGLProofDAG
open GuthMaynardJutilaReflection2941
open GuthMaynardJutilaSpacingPartition
open GuthMaynardTwoPlateauSmoothingBridge
open GuthMaynardTwoPlateauThreshold
open GuthMaynardSmoothedProp31Consumer
open GuthMaynardLargeValueIntervalSubdivision
open GuthMaynardLargeValueThinning

noncomputable section

private theorem card_le_three_powerSpacing_mul_of_supported_local_bound
    (b : ℕ → ℂ) (M : ℕ) (W : Finset ℝ) {T delta V K : ℝ}
    (hT : 1 ≤ T) (hdelta : 0 ≤ delta)
    (hb : ∀ n, ‖b n‖ ≤ 1) (hsupp : supportedOnPlateau M b)
    (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T)
    (hlarge : ∀ t ∈ W, V ≤ ‖dirichletPolynomial b M t‖)
    (hK : 0 ≤ K)
    (hlocal : ∀ (a : ℕ → ℂ) (U : Finset ℝ),
      supportedOnPlateau M a →
      (∀ n, ‖a n‖ ≤ 1) → TPowerSeparated U T delta →
      (∀ u ∈ U, 0 ≤ u ∧ u ≤ T) →
      (∀ u ∈ U, V ≤ ‖dirichletPolynomial a M u‖) →
      (U.card : ℝ) ≤ K) :
    (W.card : ℝ) ≤ 3 * Real.rpow T delta * K := by
  have hcard := card_eq_sum_powerSpacingColorFiber hT hdelta hsep
  have hfiber : ∀ i : Fin (powerSpacingColorCount T delta),
      ((colorFiber (powerSpacingColor T delta) W i).card : ℝ) ≤ K := by
    intro i
    have hstrong := powerSpacingColorFiber_TPowerSeparated
      hsep (T := T) (delta := delta) i
    have hsub : colorFiber (powerSpacingColor T delta) W i ⊆ W :=
      Finset.filter_subset _ _
    have hheight' : ∀ u ∈ colorFiber (powerSpacingColor T delta) W i,
        0 ≤ u ∧ u ≤ T := fun u hu => hheight u (hsub hu)
    have hlarge' : ∀ u ∈ colorFiber (powerSpacingColor T delta) W i,
        V ≤ ‖dirichletPolynomial b M u‖ := fun u hu => hlarge u (hsub hu)
    exact hlocal b _ hsupp hb hstrong hheight' hlarge'
  have hsumle :
      ∑ i : Fin (powerSpacingColorCount T delta),
          ((colorFiber (powerSpacingColor T delta) W i).card : ℝ) ≤
        ∑ _i : Fin (powerSpacingColorCount T delta), K := by
    apply Finset.sum_le_sum
    intro i hi
    exact hfiber i
  have hW : (W.card : ℝ) =
      ∑ i : Fin (powerSpacingColorCount T delta),
        ((colorFiber (powerSpacingColor T delta) W i).card : ℝ) := by
    exact_mod_cast hcard
  rw [hW]
  calc
    _ ≤ ∑ _i : Fin (powerSpacingColorCount T delta), K := hsumle
    _ = (powerSpacingColorCount T delta : ℝ) * K := by simp
    _ ≤ 3 * Real.rpow T delta * K := by
      exact mul_le_mul_of_nonneg_right
        (powerSpacingColorCount_cast_le hT hdelta) hK

private theorem card_le_floor_intervals_mul_of_supported_local_bound
    (b : ℕ → ℂ) (M : ℕ) (W : Finset ℝ) {T L V K delta : ℝ}
    (hL : 0 < L) (hL1 : 1 ≤ L) (hdelta : 0 ≤ delta) (hT : 0 ≤ T)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T)
    (hb : ∀ n, ‖b n‖ ≤ 1) (hsupp : supportedOnPlateau M b)
    (hsep : OneSeparated W)
    (hlarge : ∀ t ∈ W, V ≤ ‖dirichletPolynomial b M t‖)
    (hK : 0 ≤ K)
    (hlocal : ∀ (a : ℕ → ℂ) (U : Finset ℝ),
      supportedOnPlateau M a →
      (∀ n, ‖a n‖ ≤ 1) → TPowerSeparated U L delta →
      (∀ u ∈ U, 0 ≤ u ∧ u ≤ L) →
      (∀ u ∈ U, V ≤ ‖dirichletPolynomial a M u‖) →
      (U.card : ℝ) ≤ K) :
    (W.card : ℝ) ≤ (⌊T / L⌋₊ + 1 : ℕ) * (3 * Real.rpow L delta * K) := by
  let J := Finset.range (⌊T / L⌋₊ + 1)
  have hcard : W.card =
      ∑ j ∈ J, (subdivisionFiber W L j).card := by
    simpa [J] using (card_eq_sum_subdivisionFiber hL hT hheight)
  have hfiber : ∀ j ∈ J,
      ((subdivisionFiber W L j).card : ℝ) ≤ 3 * Real.rpow L delta * K := by
    intro j hj
    let U := translatedSubdivisionFiber W L j
    let a' := forwardTranslatedCoefficient b ((j : ℝ) * L)
    have ha : ∀ n, ‖a' n‖ ≤ 1 := by
      intro n
      dsimp [a']
      rw [norm_forwardTranslatedCoefficient]
      exact hb n
    have hsupp' : supportedOnPlateau M a' := by
      intro n hn
      have hbn : b n ≠ 0 := by
        intro hzero
        apply hn
        simp [a', forwardTranslatedCoefficient, hzero]
      exact hsupp n hbn
    have hUsep : OneSeparated U := by
      dsimp [U]
      exact oneSeparated_translatedSubdivisionFiber hsep L j
    have hUheight : ∀ u ∈ U, 0 ≤ u ∧ u ≤ L := by
      intro u hu
      exact translatedSubdivisionFiber_mem_local_interval hL hT hheight hj hu
    have hUlarge : ∀ u ∈ U, V ≤ ‖dirichletPolynomial a' M u‖ := by
      intro u hu
      dsimp [a']
      rw [dirichletPolynomial_forwardTranslatedCoefficient]
      change u ∈ (subdivisionFiber W L j).image
          (fun t => t - (j : ℝ) * L) at hu
      rw [Finset.mem_image] at hu
      obtain ⟨t, ht, rfl⟩ := hu
      have hut : (t - (j : ℝ) * L) + (j : ℝ) * L = t := by ring
      rw [hut]
      exact hlarge t (Finset.mem_filter.mp ht).1
    have hU := card_le_three_powerSpacing_mul_of_supported_local_bound
      a' M U (T := L) (delta := delta) hL1 hdelta ha hsupp' hUsep hUheight hUlarge hK hlocal
    rw [← card_translatedSubdivisionFiber W L j]
    exact hU
  have hsumle :
      ∑ j ∈ J, ((subdivisionFiber W L j).card : ℝ) ≤
        ∑ _j ∈ J, (3 * Real.rpow L delta * K) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hfiber j hj
  have hW : (W.card : ℝ) =
      ∑ j ∈ J, ((subdivisionFiber W L j).card : ℝ) := by
    exact_mod_cast hcard
  rw [hW]
  exact hsumle.trans_eq (by simp [J])

private theorem card_le_two_ratio_mul_of_supported_local_bound
    (b : ℕ → ℂ) (M : ℕ) (W : Finset ℝ) {T L V K delta : ℝ}
    (hL : 0 < L) (hL1 : 1 ≤ L) (hdelta : 0 ≤ delta)
    (hT : 0 ≤ T) (hLT : L ≤ T)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T)
    (hb : ∀ n, ‖b n‖ ≤ 1) (hsupp : supportedOnPlateau M b)
    (hsep : OneSeparated W)
    (hlarge : ∀ t ∈ W, V ≤ ‖dirichletPolynomial b M t‖)
    (hK : 0 ≤ K)
    (hlocal : ∀ (a : ℕ → ℂ) (U : Finset ℝ),
      supportedOnPlateau M a →
      (∀ n, ‖a n‖ ≤ 1) → TPowerSeparated U L delta →
      (∀ u ∈ U, 0 ≤ u ∧ u ≤ L) →
      (∀ u ∈ U, V ≤ ‖dirichletPolynomial a M u‖) →
      (U.card : ℝ) ≤ K) :
    (W.card : ℝ) ≤ 2 * (T / L) * (3 * Real.rpow L delta * K) := by
  have hmain := card_le_floor_intervals_mul_of_supported_local_bound
    b M W hL hL1 hdelta hT hheight hb hsupp hsep hlarge hK hlocal
  have hfloor : (⌊T / L⌋₊ : ℝ) ≤ T / L := by
    apply Nat.floor_le
    exact div_nonneg hT hL.le
  have hratio : 1 ≤ T / L := (le_div_iff₀ hL).2 (by simpa using hLT)
  have hcount : ((⌊T / L⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * (T / L) := by
    push_cast
    linarith
  have hQ : 0 ≤ 3 * Real.rpow L delta * K := by
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hL.le delta)) hK
  have hmul := mul_le_mul_of_nonneg_right hcount hQ
  exact hmain.trans hmul

private theorem card_le_one_add_two_ratio_mul_of_supported_local_bound
    (b : ℕ → ℂ) (M : ℕ) (W : Finset ℝ) {T L V K delta : ℝ}
    (hL : 0 < L) (hL1 : 1 ≤ L) (hdelta : 0 ≤ delta) (hT : 0 ≤ T)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T)
    (hb : ∀ n, ‖b n‖ ≤ 1) (hsupp : supportedOnPlateau M b)
    (hsep : OneSeparated W)
    (hlarge : ∀ t ∈ W, V ≤ ‖dirichletPolynomial b M t‖)
    (hK : 0 ≤ K)
    (hlocal : ∀ (a : ℕ → ℂ) (U : Finset ℝ),
      supportedOnPlateau M a →
      (∀ n, ‖a n‖ ≤ 1) → TPowerSeparated U L delta →
      (∀ u ∈ U, 0 ≤ u ∧ u ≤ L) →
      (∀ u ∈ U, V ≤ ‖dirichletPolynomial a M u‖) →
      (U.card : ℝ) ≤ K) :
    (W.card : ℝ) ≤ (1 + 2 * (T / L)) * (3 * Real.rpow L delta * K) := by
  by_cases hTL : T ≤ L
  · have hheight' : ∀ t ∈ W, 0 ≤ t ∧ t ≤ L := by
      intro t ht
      exact ⟨(hheight t ht).1, (hheight t ht).2.trans hTL⟩
    have hlocal' := card_le_three_powerSpacing_mul_of_supported_local_bound
      b M W (T := L) (delta := delta) hL1 hdelta hb hsupp hsep hheight' hlarge hK hlocal
    have hfactor : 1 ≤ 1 + 2 * (T / L) := by
      have : 0 ≤ T / L := div_nonneg hT hL.le
      linarith
    have hQ : 0 ≤ 3 * Real.rpow L delta * K := by
      exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hL.le delta)) hK
    exact hlocal'.trans (by
      simpa using (mul_le_mul_of_nonneg_right hfactor hQ))
  · have hLT : L ≤ T := le_of_not_ge hTL
    have hmain := card_le_two_ratio_mul_of_supported_local_bound
      b M W hL hL1 hdelta hT hLT hheight hb hsupp hsep hlarge hK hlocal
    have hfactor : 2 * (T / L) ≤ 1 + 2 * (T / L) := by linarith
    have hQ : 0 ≤ 3 * Real.rpow L delta * K := by
      exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hL.le delta)) hK
    exact hmain.trans (mul_le_mul_of_nonneg_right hfactor hQ)

private theorem supported_firstPart {N : ℕ} (hN : 32 ≤ N)
    (a : ℕ → ℂ) : supportedOnPlateau (localN1 N) (firstPart a N) := by
  intro n hn
  by_contra hnot
  simp [firstPart, hnot] at hn

private theorem supported_secondPart {N : ℕ} (hN : 32 ≤ N)
    (a : ℕ → ℂ) : supportedOnPlateau (localN2 N) (secondPart a N) := by
  intro n hn
  by_contra hnot
  simp [secondPart, hnot] at hn

private theorem firstPart_norm_le {N : ℕ} {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ 1) : ∀ n, ‖firstPart a N n‖ ≤ 1 := by
  intro n
  by_cases hmem : n ∈ sourceBlock N ∧ n ∈ plateau (localN1 N)
  · simp only [firstPart, hmem, if_true]
    exact ha n
  · simp [firstPart, hmem]

private theorem secondPart_norm_le {N : ℕ} {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ 1) : ∀ n, ‖secondPart a N n‖ ≤ 1 := by
  intro n
  by_cases hmem : n ∈ sourceBlock N ∧ n ∉ plateau (localN1 N) ∧
      n ∈ plateau (localN2 N)
  · simp only [secondPart, hmem, if_true]
    exact ha n
  · simp [secondPart, hmem]

private theorem source_dirichlet_two_part_split {N : ℕ} (hN : 32 ≤ N)
    {a : ℕ → ℂ} {w : ℝ → ℝ} (hw : PlateauWeight w) (t : ℝ) :
    dirichletPolynomial a N t =
      dirichletPolynomial (firstPart a N) (localN1 N) t +
        dirichletPolynomial (secondPart a N) (localN2 N) t := by
  have hs := source_weighted_two_part_split hN (a := a) hw t
  have hfirst :
      (∑ n ∈ sourceBlock N,
        (w ((n : ℝ) / (localN1 N : ℝ)) : ℂ) * firstPart a N n *
          Complex.exp (Complex.I * (t * Real.log n))) =
        dirichletPolynomial (firstPart a N) (localN1 N) t := by
    have hplain :
        (∑ n ∈ sourceBlock N,
          firstPart a N n * Complex.exp (Complex.I * (t * Real.log n))) =
          dirichletPolynomial (firstPart a N) (localN1 N) t := by
      let s := sourceBlock N
      let u := Finset.Ioc (localN1 N) (2 * localN1 N)
      let q : ℕ → ℂ := fun n =>
        firstPart a N n * Complex.exp (Complex.I * (t * Real.log n))
      have hsu : s ⊆ s ∪ u := Finset.subset_union_left
      have hsumS : (∑ n ∈ s, q n) = ∑ n ∈ s ∪ u, q n := by
        apply Finset.sum_subset hsu
        intro n hn hns
        simp only [q]
        by_cases hzero : firstPart a N n = 0
        · simp [hzero]
        · have hmem : n ∈ sourceBlock N := by
            by_contra hnot
            apply hzero
            simp [firstPart, hnot]
          exact (hns hmem).elim
      have hus : u ⊆ s ∪ u := Finset.subset_union_right
      have hsumU : (∑ n ∈ u, q n) = ∑ n ∈ s ∪ u, q n := by
        apply Finset.sum_subset hus
        intro n hn hnu
        simp only [q]
        by_cases hzero : firstPart a N n = 0
        · simp [hzero]
        · have hmem := firstPart_mem_localBlock hN hzero
          exact (hnu hmem).elim
      dsimp [s, u, q] at hsumS hsumU ⊢
      exact hsumS.trans hsumU.symm
    calc
      _ = ∑ n ∈ sourceBlock N,
          firstPart a N n * Complex.exp (Complex.I * (t * Real.log n)) := by
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hzero : firstPart a N n = 0
        · simp [hzero]
        · rw [firstPart_weight_eq hN hw hzero]
      _ = _ := hplain
  have hsecond :
      (∑ n ∈ sourceBlock N,
        (w ((n : ℝ) / (localN2 N : ℝ)) : ℂ) * secondPart a N n *
          Complex.exp (Complex.I * (t * Real.log n))) =
        dirichletPolynomial (secondPart a N) (localN2 N) t := by
    have hplain :
        (∑ n ∈ sourceBlock N,
          secondPart a N n * Complex.exp (Complex.I * (t * Real.log n))) =
          dirichletPolynomial (secondPart a N) (localN2 N) t := by
      let s := sourceBlock N
      let u := Finset.Ioc (localN2 N) (2 * localN2 N)
      let q : ℕ → ℂ := fun n =>
        secondPart a N n * Complex.exp (Complex.I * (t * Real.log n))
      have hsu : s ⊆ s ∪ u := Finset.subset_union_left
      have hsumS : (∑ n ∈ s, q n) = ∑ n ∈ s ∪ u, q n := by
        apply Finset.sum_subset hsu
        intro n hn hns
        simp only [q]
        by_cases hzero : secondPart a N n = 0
        · simp [hzero]
        · have hmem : n ∈ sourceBlock N := by
            by_contra hnot
            apply hzero
            simp [secondPart, hnot]
          exact (hns hmem).elim
      have hus : u ⊆ s ∪ u := Finset.subset_union_right
      have hsumU : (∑ n ∈ u, q n) = ∑ n ∈ s ∪ u, q n := by
        apply Finset.sum_subset hus
        intro n hn hnu
        simp only [q]
        by_cases hzero : secondPart a N n = 0
        · simp [hzero]
        · have hmem := secondPart_mem_localBlock hN hzero
          exact (hnu hmem).elim
      dsimp [s, u, q] at hsumS hsumU ⊢
      exact hsumS.trans hsumU.symm
    calc
      _ = ∑ n ∈ sourceBlock N,
          secondPart a N n * Complex.exp (Complex.I * (t * Real.log n)) := by
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hzero : secondPart a N n = 0
        · simp [hzero]
        · rw [secondPart_weight_eq hN hw hzero]
      _ = _ := hplain
  calc
    dirichletPolynomial a N t =
        ∑ n ∈ sourceBlock N, a n * Complex.exp (Complex.I * (t * Real.log n)) := rfl
    _ = _ := hs
    _ = _ := by rw [hfirst, hsecond]

theorem twoPlateauTimeConsumer
    {w : ℝ → ℝ} (hlocal : FixedWeightProp31 w) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ (N : ℕ) (T V : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
          64 ≤ N → 0 ≤ T → 0 < V →
          4 * Real.rpow (N : ℝ) (7 / 10 : ℝ) ≤ V →
          V ≤ Real.rpow (N : ℝ) (8 / 10 : ℝ) →
          (∀ n, ‖a n‖ ≤ 1) → OneSeparated W →
          (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
          (∀ t ∈ W, V ≤ ‖dirichletPolynomial a N t‖) →
      (W.card : ℝ) ≤
        (1 + 2 * (T / Real.rpow (localN1 N : ℝ) (6 / 5 : ℝ))) *
            (3 * Real.rpow (Real.rpow (localN1 N : ℝ) (6 / 5 : ℝ)) ε *
              (C * Real.rpow (Real.rpow (localN1 N : ℝ) (6 / 5 : ℝ)) ε *
                (Real.rpow (localN1 N : ℝ) (6 / 5) *
                  Real.rpow (localN1 N : ℝ) (12 / 5) / (V / 2) ^ 4))) +
        (1 + 2 * (T / Real.rpow (localN2 N : ℝ) (6 / 5 : ℝ))) *
            (3 * Real.rpow (Real.rpow (localN2 N : ℝ) (6 / 5 : ℝ)) ε *
              (C * Real.rpow (Real.rpow (localN2 N : ℝ) (6 / 5 : ℝ)) ε *
                (Real.rpow (localN2 N : ℝ) (6 / 5) *
                  Real.rpow (localN2 N : ℝ) (12 / 5) / (V / 2) ^ 4))) := by
  intro ε hε
  rcases hlocal with ⟨hw, hprop⟩
  rcases hprop ε hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro N T V a W hN hT hV hVlow hVhigh ha hsep hheight hlarge
  have hN32 : 32 ≤ N := le_trans (by norm_num) hN
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (le_trans (by norm_num) hN)
  have hM1scale := localN1_scale hN32
  have hM2scale := localN2_scale hN32
  have hM1low : (N : ℝ) / 2 ≤ (localN1 N : ℝ) := by
    have hn : N ≤ 2 * localN1 N := by
      unfold localN1
      omega
    have hn' : (N : ℝ) ≤ 2 * (localN1 N : ℝ) := by
      exact_mod_cast hn
    linarith
  have hM1high : (localN1 N : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast hM1scale.2
  have hM2low : (N : ℝ) / 2 ≤ (localN2 N : ℝ) := by
    have hn : N ≤ 2 * localN2 N := by
      unfold localN2
      omega
    have hn' : (N : ℝ) ≤ 2 * (localN2 N : ℝ) := by
      exact_mod_cast hn
    linarith
  have hM2high : (localN2 N : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast hM2scale.2
  have hM132 : 32 ≤ localN1 N := by unfold localN1; omega
  have hM232 : 32 ≤ localN2 N := by unfold localN2; omega
  have hhalfV : 0 < V / 2 := by linarith
  have hthr1 := half_threshold_transfer hNreal
    hM1low hM1high
    hVlow hVhigh
  have hthr2 := half_threshold_transfer hNreal
    hM2low hM2high
    hVlow hVhigh
  let W₁ : Finset ℝ := W.filter (fun t =>
    V / 2 ≤ ‖dirichletPolynomial (firstPart a N) (localN1 N) t‖)
  let W₂ : Finset ℝ := W.filter (fun t =>
    V / 2 ≤ ‖dirichletPolynomial (secondPart a N) (localN2 N) t‖)
  have hcover : W ⊆ W₁ ∪ W₂ := by
    intro t ht
    have hsplit := largeValue_two_part_split
      (z₁ := dirichletPolynomial (firstPart a N) (localN1 N) t)
      (z₂ := dirichletPolynomial (secondPart a N) (localN2 N) t) hV
      (by
        rw [← source_dirichlet_two_part_split hN32 hw t]
        exact hlarge t ht)
    rcases hsplit with h1 | h2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht, h2⟩)
  have hcard : (W.card : ℝ) ≤ (W₁.card : ℝ) + (W₂.card : ℝ) := by
    have hc := Finset.card_le_card hcover
    have hu := Finset.card_union_le W₁ W₂
    exact_mod_cast (Nat.le_trans hc hu)
  have hsub1 : W₁ ⊆ W := Finset.filter_subset _ _
  have hsub2 : W₂ ⊆ W := Finset.filter_subset _ _
  have hsep1 : OneSeparated W₁ := fun x hx y hy hxy =>
    hsep x (hsub1 hx) y (hsub1 hy) hxy
  have hsep2 : OneSeparated W₂ := fun x hx y hy hxy =>
    hsep x (hsub2 hx) y (hsub2 hy) hxy
  have hheight1 : ∀ t ∈ W₁, 0 ≤ t ∧ t ≤ T := fun t ht =>
    hheight t (hsub1 ht)
  have hheight2 : ∀ t ∈ W₂, 0 ≤ t ∧ t ≤ T := fun t ht =>
    hheight t (hsub2 ht)
  let M₁ : ℝ := Real.rpow (localN1 N : ℝ) (6 / 5 : ℝ)
  let M₂ : ℝ := Real.rpow (localN2 N : ℝ) (6 / 5 : ℝ)
  have hM₁pos : 0 < M₁ := by dsimp [M₁]; positivity
  have hM₂pos : 0 < M₂ := by dsimp [M₂]; positivity
  have hM1base : 0 < (localN1 N : ℝ) := by positivity
  have hM2base : 0 < (localN2 N : ℝ) := by positivity
  have hM1base1 : 1 ≤ (localN1 N : ℝ) := by
    exact_mod_cast (show 1 ≤ localN1 N by omega)
  have hM2base1 : 1 ≤ (localN2 N : ℝ) := by
    exact_mod_cast (show 1 ≤ localN2 N by omega)
  have hM₁1 : 1 ≤ M₁ := by
    dsimp [M₁]
    exact Real.one_le_rpow hM1base1 (by norm_num)
  have hM₂1 : 1 ≤ M₂ := by
    dsimp [M₂]
    exact Real.one_le_rpow hM2base1 (by norm_num)
  have hK1 : 0 ≤ C * Real.rpow M₁ ε *
      (M₁ * Real.rpow (localN1 N : ℝ) (12 / 5) / (V / 2) ^ 4) := by
    have hden : 0 < (V / 2) ^ 4 := pow_pos hhalfV _
    exact mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hM₁pos.le _))
      (div_nonneg (mul_nonneg hM₁pos.le
        (Real.rpow_nonneg hM1base.le _)) hden.le)
  have hK2 : 0 ≤ C * Real.rpow M₂ ε *
      (M₂ * Real.rpow (localN2 N : ℝ) (12 / 5) / (V / 2) ^ 4) := by
    have hden : 0 < (V / 2) ^ 4 := pow_pos hhalfV _
    exact mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hM₂pos.le _))
      (div_nonneg (mul_nonneg hM₂pos.le
        (Real.rpow_nonneg hM2base.le _)) hden.le)
  have hpiece1 := card_le_one_add_two_ratio_mul_of_supported_local_bound
    (firstPart a N) (localN1 N) W₁ hM₁pos hM₁1 hε.le hT hheight1
    (firstPart_norm_le ha)
    (supported_firstPart hN32 a) hsep1
    (fun t ht => (Finset.mem_filter.mp ht).2) hK1
    (fun c U hcsupp hc hUsep hUheight hUlarge => by
      have hsmooth : ∀ u ∈ U, V / 2 ≤ ‖smoothedPolynomial w c
          (localN1 N) u‖ := by
        intro u hu
        rw [smoothed_eq_sharp_of_supported hw hM132 hcsupp]
        exact hUlarge u hu
      exact hbound (localN1 N) (V / 2) c U hM132 hhalfV hthr1.1 hthr1.2
        hc hcsupp hUsep hUheight hsmooth)
  have hpiece2 := card_le_one_add_two_ratio_mul_of_supported_local_bound
    (secondPart a N) (localN2 N) W₂ hM₂pos hM₂1 hε.le hT hheight2
    (secondPart_norm_le ha)
    (supported_secondPart hN32 a) hsep2
    (fun t ht => (Finset.mem_filter.mp ht).2) hK2
    (fun c U hcsupp hc hUsep hUheight hUlarge => by
      have hsmooth : ∀ u ∈ U, V / 2 ≤ ‖smoothedPolynomial w c
          (localN2 N) u‖ := by
        intro u hu
        rw [smoothed_eq_sharp_of_supported hw hM232 hcsupp]
        exact hUlarge u hu
      exact hbound (localN2 N) (V / 2) c U hM232 hhalfV hthr2.1 hthr2.2
        hc hcsupp hUsep hUheight hsmooth)
  exact hcard.trans (add_le_add hpiece1 hpiece2)

end
end GuthMaynardTwoPlateauTimeConsumer

#print axioms GuthMaynardTwoPlateauTimeConsumer.twoPlateauTimeConsumer
