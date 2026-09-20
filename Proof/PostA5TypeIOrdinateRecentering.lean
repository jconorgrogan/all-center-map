import PostA5RecenteredSourceSplit
import PostA5TypeIFourierAssembly

/-!
# Deterministic Type-I ordinate recentering

The Fourier extraction naturally produces a one-separated set in `[-T,T]`,
whereas the Guth--Maynard interface uses `[0,T]`.  Splitting by sign and
translating the negative half costs only a factor two in cardinality.  The
translation is absorbed exactly into unit-modulus coefficient phases.
-/

namespace PostA5TypeIOrdinateRecentering

open scoped BigOperators FourierTransform
open CGLProofDAG MAPAppendixA4PostA5SetAdapter SchwartzMap
open PostA5TypeIFourierAssembly

noncomputable section

/-- Coefficient modulation implementing translation of the ordinate by `c`. -/
def translatedCoefficient (b : ℕ → ℂ) (c : ℝ) (n : ℕ) : ℂ :=
  b n * Complex.exp
    ((((-c) * Real.log n : ℝ) : ℂ) * Complex.I)

theorem norm_translatedCoefficient
    (b : ℕ → ℂ) (c : ℝ) (n : ℕ) :
    ‖translatedCoefficient b c n‖ = ‖b n‖ := by
  unfold translatedCoefficient
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Exact phase identity: translating the sampling ordinate is the same as
modulating every coefficient by a unit complex phase. -/
theorem dirichletPolynomial_translatedCoefficient
    (b : ℕ → ℂ) (N : ℕ) (c t : ℝ) :
    dirichletPolynomial (translatedCoefficient b c) N (t + c) =
      dirichletPolynomial b N t := by
  unfold dirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  unfold translatedCoefficient
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

def nonnegativePart (W : Finset ℝ) : Finset ℝ :=
  W.filter fun t => 0 ≤ t

def nonpositivePart (W : Finset ℝ) : Finset ℝ :=
  W.filter fun t => t ≤ 0

theorem subset_nonpositive_union_nonnegative (W : Finset ℝ) :
    W ⊆ nonpositivePart W ∪ nonnegativePart W := by
  intro t ht
  rcases le_total t 0 with ht0 | h0t
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht, ht0⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht, h0t⟩)

theorem card_le_sign_parts (W : Finset ℝ) :
    W.card ≤ (nonpositivePart W).card + (nonnegativePart W).card := by
  exact (Finset.card_le_card (subset_nonpositive_union_nonnegative W)).trans
    (Finset.card_union_le _ _)

theorem oneSeparated_subset {W S : Finset ℝ}
    (hsep : OneSeparated W) (hS : S ⊆ W) :
    OneSeparated S := by
  intro t ht u hu htu
  exact hsep t (hS ht) u (hS hu) htu

theorem oneSeparated_image_add
    {W : Finset ℝ} (hsep : OneSeparated W) (c : ℝ) :
    OneSeparated (W.image fun t => t + c) := by
  intro t ht u hu htu
  rw [Finset.mem_image] at ht hu
  obtain ⟨x, hx, rfl⟩ := ht
  obtain ⟨y, hy, rfl⟩ := hu
  have hxy : x ≠ y := by
    intro h
    apply htu
    rw [h]
  simpa only [add_sub_add_right_eq_sub] using hsep x hx y hy hxy

theorem card_image_add (W : Finset ℝ) (c : ℝ) :
    (W.image fun t => t + c).card = W.card := by
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  linarith

/-- Coefficient-norm preserving form of the sign recentering. -/
theorem exists_nonnegative_recentered_largeValueSet_eq_norm
    (b : ℕ → ℂ) (N : ℕ) (W : Finset ℝ) {T V : ℝ}
    (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, |t| ≤ T)
    (hlarge : ∀ t ∈ W, V ≤ ‖dirichletPolynomial b N t‖) :
    ∃ (b' : ℕ → ℂ) (W' : Finset ℝ),
      (∀ n, ‖b' n‖ = ‖b n‖) ∧
      OneSeparated W' ∧
      (∀ t ∈ W', 0 ≤ t ∧ t ≤ T) ∧
      (∀ t ∈ W', V ≤ ‖dirichletPolynomial b' N t‖) ∧
      W.card ≤ 2 * W'.card := by
  classical
  let Wneg := nonpositivePart W
  let Wpos := nonnegativePart W
  have hcard : W.card ≤ Wneg.card + Wpos.card := by
    simpa [Wneg, Wpos] using card_le_sign_parts W
  by_cases hchoice : Wneg.card ≤ Wpos.card
  · refine ⟨b, Wpos, fun _ => rfl, ?_, ?_, ?_, ?_⟩
    · exact oneSeparated_subset hsep (Finset.filter_subset _ _)
    · intro t ht
      have htW : t ∈ W := (Finset.mem_filter.mp ht).1
      have h0t : 0 ≤ t := (Finset.mem_filter.mp ht).2
      exact ⟨h0t, (abs_le.mp (hheight t htW)).2⟩
    · intro t ht
      exact hlarge t (Finset.mem_filter.mp ht).1
    · omega
  · let b' := translatedCoefficient b T
    let W' := Wneg.image fun t => t + T
    refine ⟨b', W', ?_, ?_, ?_, ?_, ?_⟩
    · intro n
      exact norm_translatedCoefficient b T n
    · exact oneSeparated_image_add
        (oneSeparated_subset hsep (Finset.filter_subset _ _)) T
    · intro u hu
      change u ∈ Wneg.image (fun t => t + T) at hu
      rw [Finset.mem_image] at hu
      obtain ⟨t, ht, rfl⟩ := hu
      have htW : t ∈ W := (Finset.mem_filter.mp ht).1
      have ht0 : t ≤ 0 := (Finset.mem_filter.mp ht).2
      have htneg : -T ≤ t := (abs_le.mp (hheight t htW)).1
      constructor <;> linarith
    · intro u hu
      change u ∈ Wneg.image (fun t => t + T) at hu
      rw [Finset.mem_image] at hu
      obtain ⟨t, ht, rfl⟩ := hu
      rw [dirichletPolynomial_translatedCoefficient]
      exact hlarge t (Finset.mem_filter.mp ht).1
    · rw [show W'.card = Wneg.card by exact card_image_add Wneg T]
      omega

/-- Complete recentering adapter.  A symmetric one-separated large-value set
produces an actual `[0,T]` Guth--Maynard set, with unchanged coefficient
norms and only the literal two-color sign loss. -/
theorem exists_nonnegative_recentered_largeValueSet
    (b : ℕ → ℂ) (N : ℕ) (W : Finset ℝ) {T V : ℝ}
    (hb : ∀ n, ‖b n‖ ≤ 1)
    (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, |t| ≤ T)
    (hlarge : ∀ t ∈ W, V ≤ ‖dirichletPolynomial b N t‖) :
    ∃ (b' : ℕ → ℂ) (W' : Finset ℝ),
      (∀ n, ‖b' n‖ ≤ 1) ∧
      OneSeparated W' ∧
      (∀ t ∈ W', 0 ≤ t ∧ t ≤ T) ∧
      (∀ t ∈ W', V ≤ ‖dirichletPolynomial b' N t‖) ∧
      W.card ≤ 2 * W'.card := by
  classical
  let Wneg := nonpositivePart W
  let Wpos := nonnegativePart W
  have hcard : W.card ≤ Wneg.card + Wpos.card := by
    simpa [Wneg, Wpos] using card_le_sign_parts W
  by_cases hchoice : Wneg.card ≤ Wpos.card
  · refine ⟨b, Wpos, hb, ?_, ?_, ?_, ?_⟩
    · exact oneSeparated_subset hsep (Finset.filter_subset _ _)
    · intro t ht
      have htW : t ∈ W := (Finset.mem_filter.mp ht).1
      have h0t : 0 ≤ t := (Finset.mem_filter.mp ht).2
      exact ⟨h0t, (abs_le.mp (hheight t htW)).2⟩
    · intro t ht
      exact hlarge t (Finset.mem_filter.mp ht).1
    · omega
  · let b' := translatedCoefficient b T
    let W' := Wneg.image fun t => t + T
    refine ⟨b', W', ?_, ?_, ?_, ?_, ?_⟩
    · intro n
      simpa [b', norm_translatedCoefficient] using hb n
    · exact oneSeparated_image_add
        (oneSeparated_subset hsep (Finset.filter_subset _ _)) T
    · intro u hu
      change u ∈ Wneg.image (fun t => t + T) at hu
      rw [Finset.mem_image] at hu
      obtain ⟨t, ht, rfl⟩ := hu
      have htW : t ∈ W := (Finset.mem_filter.mp ht).1
      have ht0 : t ≤ 0 := (Finset.mem_filter.mp ht).2
      have htneg : -T ≤ t := (abs_le.mp (hheight t htW)).1
      constructor <;> linarith
    · intro u hu
      change u ∈ Wneg.image (fun t => t + T) at hu
      rw [Finset.mem_image] at hu
      obtain ⟨t, ht, rfl⟩ := hu
      rw [dirichletPolynomial_translatedCoefficient]
      exact hlarge t (Finset.mem_filter.mp ht).1
    · rw [show W'.card = Wneg.card by
          exact card_image_add Wneg T]
      omega

/-! ## Endpoint-collar bookkeeping -/

def endpointCollar (S : Finset ℂ) (T : ℝ) (C : ℕ) : Finset ℂ :=
  S.filter fun rho => T - C < |rho.im|

def endpointInterior (S : Finset ℂ) (T : ℝ) (C : ℕ) : Finset ℂ :=
  S.filter fun rho => |rho.im| + C ≤ T

theorem endpointInterior_union_endpointCollar
    (S : Finset ℂ) (T : ℝ) (C : ℕ) :
    endpointInterior S T C ∪ endpointCollar S T C = S := by
  classical
  ext rho
  simp only [endpointInterior, endpointCollar, Finset.mem_union,
    Finset.mem_filter]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hrho
    refine Or.elim (le_or_gt (|rho.im| + C) T)
      (fun h => Or.inl ⟨hrho, h⟩) (fun h => Or.inr ⟨hrho, by linarith⟩)

theorem disjoint_endpointInterior_endpointCollar
    (S : Finset ℂ) (T : ℝ) (C : ℕ) :
    Disjoint (endpointInterior S T C) (endpointCollar S T C) := by
  classical
  rw [Finset.disjoint_left]
  intro rho hinter hcollar
  have hi := (Finset.mem_filter.mp hinter).2
  have hc := (Finset.mem_filter.mp hcollar).2
  linarith

def endpointCollarFloorBins (T : ℝ) (C : ℕ) : Finset ℤ :=
  Finset.Icc (Int.floor (-T)) (Int.floor (-T + C)) ∪
    Finset.Icc (Int.floor (T - C)) (Int.floor T)

theorem card_endpointCollarFloorBins_le (T : ℝ) (C : ℕ) :
    (endpointCollarFloorBins T C).card ≤ 2 * (C + 1) := by
  have hleft :
      (Finset.Icc (Int.floor (-T)) (Int.floor (-T + C))).card = C + 1 := by
    rw [show (-T + (C : ℝ)) = -T + (C : ℤ) by norm_num]
    rw [Int.floor_add_intCast, Int.card_Icc]
    rw [show Int.floor (-T) + (C : ℤ) + 1 - Int.floor (-T) =
        (C : ℤ) + 1 by ring]
    simp
  have hright :
      (Finset.Icc (Int.floor (T - C)) (Int.floor T)).card = C + 1 := by
    rw [show T - (C : ℝ) = T - (C : ℤ) by norm_num]
    rw [Int.floor_sub_intCast, Int.card_Icc]
    rw [show Int.floor T + 1 - (Int.floor T - (C : ℤ)) =
        (C : ℤ) + 1 by ring]
    simp
  calc
    (endpointCollarFloorBins T C).card ≤
        (Finset.Icc (Int.floor (-T)) (Int.floor (-T + C))).card +
          (Finset.Icc (Int.floor (T - C)) (Int.floor T)).card :=
      Finset.card_union_le _ _
    _ = 2 * (C + 1) := by rw [hleft, hright]; omega

theorem floor_mem_endpointCollarFloorBins
    {rho : ℂ} {T : ℝ} {C : ℕ}
    (hheight : |rho.im| ≤ T) (hcollar : T - C < |rho.im|) :
    Int.floor rho.im ∈ endpointCollarFloorBins T C := by
  rcases le_total 0 rho.im with hnonneg | hnonpos
  · apply Finset.mem_union_right
    rw [Finset.mem_Icc]
    rw [abs_of_nonneg hnonneg] at hheight hcollar
    exact ⟨Int.floor_mono hcollar.le, Int.floor_mono hheight⟩
  · apply Finset.mem_union_left
    rw [Finset.mem_Icc]
    rw [abs_of_nonpos hnonpos] at hheight hcollar
    constructor
    · exact Int.floor_mono (by linarith)
    · exact Int.floor_mono (by linarith)

/-- An endpoint collar of integral width `C` occupies at most `2(C+1)`
unit floor bins.  Any natural-valued multiplicity is preserved exactly. -/
theorem sum_endpointCollar_weight_le
    (S : Finset ℂ) (weight : ℂ → ℕ) {T : ℝ} (C M : ℕ)
    (hheight : ∀ rho ∈ S, |rho.im| ≤ T)
    (hsource : ∀ m : ℤ,
      ∑ rho ∈ S with Int.floor rho.im = m, weight rho ≤ M) :
    ∑ rho ∈ endpointCollar S T C, weight rho ≤
      2 * (C + 1) * M := by
  classical
  let Z := endpointCollar S T C
  let bins := endpointCollarFloorBins T C
  have hmaps : ∀ rho ∈ Z, Int.floor rho.im ∈ bins := by
    intro rho hrho
    have hrho' := Finset.mem_filter.mp hrho
    exact floor_mem_endpointCollarFloorBins
      (hheight rho hrho'.1) hrho'.2
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps weight
  have hbin : ∀ m ∈ bins,
      ∑ rho ∈ Z with Int.floor rho.im = m, weight rho ≤ M := by
    intro m hm
    apply (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_).trans (hsource m)
    · intro rho hrho
      have hrho' := Finset.mem_filter.mp hrho
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hrho'.1).1, hrho'.2⟩
    · intro rho hrho hrhoNot
      exact Nat.zero_le _
  calc
    ∑ rho ∈ endpointCollar S T C, weight rho =
        ∑ m ∈ bins,
          ∑ rho ∈ Z with Int.floor rho.im = m, weight rho := by
      simpa [Z] using hfiber.symm
    _ ≤ ∑ _m ∈ bins, M := by
      apply Finset.sum_le_sum
      intro m hm
      exact hbin m hm
    _ = bins.card * M := by simp
    _ ≤ (2 * (C + 1)) * M := by
      exact Nat.mul_le_mul_right M (card_endpointCollarFloorBins_le T C)
    _ = 2 * (C + 1) * M := by ring

/-- The common-dyadic Fourier extraction followed by exact sign recentering.
The source points are assumed to lie outside the endpoint collar of width
`C`; hence every shifted ordinate lies in `[-T,T]`.  Multiplicity is retained
through the arbitrary natural weight, and recentering costs exactly one
additional factor two. -/
theorem exists_typeI_commonPolynomial_oneSeparated_recentered
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {U N : ℕ} (hU : 1 ≤ U) (Y sigma : ℝ)
    (j : Fin (detectorDyadicCount N))
    (S : Finset ℂ) (weight : ℂ → ℕ) {H A V T : ℝ} {C M : ℕ}
    (hC : 2 * Real.pi * H ≤ C)
    (hinterior : ∀ rho ∈ S, |rho.im| + C ≤ T)
    (hA : 0 < A) (hV : 0 < V)
    (hmass : ∀ rho ∈ S,
      (∫ xi in Set.Icc (-H) H,
        ‖((𝓕 (detectorRealPartCutoff (rho.re - sigma) (2 ^ (j : ℕ))) :
          𝓢(ℝ, ℂ)) xi)‖) ≤ A)
    (htail : ∀ rho ∈ S,
      (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
          ‖detectorCommonCoefficient
            chi U N Y sigma n‖) *
        (∫ xi in (Set.Icc (-H) H)ᶜ,
          ‖((𝓕 (detectorRealPartCutoff
            (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
          (V /
            (detectorDyadicCount N : ℝ)) / 2)
    (hblock : ∀ rho ∈ S,
      V ≤ detectorDyadicCount N *
        ‖arithmeticDetectorDyadicBlock
          chi U N rho Y j‖)
    (hsource : ∀ m : ℤ,
      ∑ rho ∈ S with Int.floor rho.im = m, weight rho ≤ M) :
    ∃ (b : ℕ → ℂ) (W : Finset ℝ),
      (∀ n, ‖b n‖ =
        ‖detectorCommonCoefficient
          chi U N Y sigma n‖) ∧
      OneSeparated W ∧
      (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) ∧
      (∀ t ∈ W,
        V / (4 * A *
            detectorDyadicCount N) ≤
          ‖dirichletPolynomial b (2 ^ (j : ℕ)) t‖) ∧
      ∑ rho ∈ S, weight rho ≤
        4 * (shiftedFloorWindowCount C * M) *
          W.card := by
  classical
  obtain ⟨xi, Wraw, hxi, hWsub, hWsep, hWlarge, hWweight⟩ :=
    exists_typeI_commonPolynomial_oneSeparated
      chi hU Y sigma j S weight hC hA hV hmass htail hblock hsource
  have hWheight : ∀ t ∈ Wraw, |t| ≤ T := by
    intro t ht
    obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp (hWsub ht)
    have hxlo : -H ≤ xi rho := (hxi rho hrho).1.1
    have hxhi : xi rho ≤ H := (hxi rho hrho).1.2
    have hxiAbs : |xi rho| ≤ H := (abs_le).2 ⟨hxlo, hxhi⟩
    have hshift : |2 * Real.pi * xi rho| ≤ C := by
      rw [abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos Real.pi_pos]
      exact (mul_le_mul_of_nonneg_left hxiAbs (by positivity)).trans hC
    calc
      |-rho.im + 2 * Real.pi * xi rho| ≤
          |rho.im| + |2 * Real.pi * xi rho| := by
        simpa [abs_neg] using abs_add_le (-rho.im) (2 * Real.pi * xi rho)
      _ ≤ |rho.im| + C := by gcongr
      _ ≤ T := hinterior rho hrho
  obtain ⟨b, W, hbnorm, hWsep', hWheight', hWlarge', hWcard⟩ :=
    exists_nonnegative_recentered_largeValueSet_eq_norm
      (detectorCommonCoefficient
        chi U N Y sigma) (2 ^ (j : ℕ)) Wraw hWsep hWheight hWlarge
  refine ⟨b, W, hbnorm, hWsep', hWheight', hWlarge', ?_⟩
  calc
    ∑ rho ∈ S, weight rho ≤
        2 * (shiftedFloorWindowCount C * M) *
          Wraw.card := hWweight
    _ ≤ 2 * (shiftedFloorWindowCount C * M) *
          (2 * W.card) := by gcongr
    _ = 4 * (shiftedFloorWindowCount C * M) *
          W.card := by ring

/-- Full deterministic endpoint-collar weld.  Fourier extraction is required
only on the interior points; the discarded multiplicity is bounded by the
literal `2(C+1)` occupied-bin count. -/
theorem exists_typeI_commonPolynomial_oneSeparated_recentered_with_collar
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {U N : ℕ} (hU : 1 ≤ U) (Y sigma : ℝ)
    (j : Fin (detectorDyadicCount N))
    (S : Finset ℂ) (weight : ℂ → ℕ) {H A V T : ℝ} {C M : ℕ}
    (hC : 2 * Real.pi * H ≤ C)
    (hheight : ∀ rho ∈ S, |rho.im| ≤ T)
    (hA : 0 < A) (hV : 0 < V)
    (hmass : ∀ rho ∈ endpointInterior S T C,
      (∫ xi in Set.Icc (-H) H,
        ‖((𝓕 (detectorRealPartCutoff (rho.re - sigma) (2 ^ (j : ℕ))) :
          𝓢(ℝ, ℂ)) xi)‖) ≤ A)
    (htail : ∀ rho ∈ endpointInterior S T C,
      (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
          ‖detectorCommonCoefficient chi U N Y sigma n‖) *
        (∫ xi in (Set.Icc (-H) H)ᶜ,
          ‖((𝓕 (detectorRealPartCutoff
            (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
          (V / (detectorDyadicCount N : ℝ)) / 2)
    (hblock : ∀ rho ∈ S,
      V ≤ detectorDyadicCount N *
        ‖arithmeticDetectorDyadicBlock chi U N rho Y j‖)
    (hsource : ∀ m : ℤ,
      ∑ rho ∈ S with Int.floor rho.im = m, weight rho ≤ M) :
    ∃ (b : ℕ → ℂ) (W : Finset ℝ),
      (∀ n, ‖b n‖ = ‖detectorCommonCoefficient chi U N Y sigma n‖) ∧
      OneSeparated W ∧
      (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) ∧
      (∀ t ∈ W,
        V / (4 * A * detectorDyadicCount N) ≤
          ‖dirichletPolynomial b (2 ^ (j : ℕ)) t‖) ∧
      ∑ rho ∈ S, weight rho ≤
        4 * (shiftedFloorWindowCount C * M) * W.card +
          2 * (C + 1) * M := by
  classical
  let Sint := endpointInterior S T C
  have hSintHeight : ∀ rho ∈ Sint, |rho.im| + C ≤ T := by
    intro rho hrho
    exact (Finset.mem_filter.mp hrho).2
  have hSintSource : ∀ m : ℤ,
      ∑ rho ∈ Sint with Int.floor rho.im = m, weight rho ≤ M := by
    intro m
    apply (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_).trans (hsource m)
    · intro rho hrho
      have hrho' := Finset.mem_filter.mp hrho
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hrho'.1).1, hrho'.2⟩
    · intro rho hrho hrhoNot
      exact Nat.zero_le _
  obtain ⟨b, W, hbnorm, hWsep, hWheight, hWlarge, hSintWeight⟩ :=
    exists_typeI_commonPolynomial_oneSeparated_recentered
      chi hU Y sigma j Sint weight hC hSintHeight hA hV hmass htail
        (fun rho hrho => hblock rho (Finset.filter_subset _ _ hrho))
        hSintSource
  refine ⟨b, W, hbnorm, hWsep, hWheight, hWlarge, ?_⟩
  have hcollar := sum_endpointCollar_weight_le S weight C M hheight hsource
  have hpartition :
      (∑ rho ∈ S, weight rho) =
        (∑ rho ∈ endpointInterior S T C, weight rho) +
          ∑ rho ∈ endpointCollar S T C, weight rho := by
    rw [← Finset.sum_union (disjoint_endpointInterior_endpointCollar S T C)]
    rw [endpointInterior_union_endpointCollar]
  rw [hpartition]
  exact Nat.add_le_add hSintWeight hcollar

end
end PostA5TypeIOrdinateRecentering

#print axioms PostA5TypeIOrdinateRecentering.norm_translatedCoefficient
#print axioms PostA5TypeIOrdinateRecentering.dirichletPolynomial_translatedCoefficient
#print axioms PostA5TypeIOrdinateRecentering.exists_nonnegative_recentered_largeValueSet
#print axioms PostA5TypeIOrdinateRecentering.sum_endpointCollar_weight_le
#print axioms PostA5TypeIOrdinateRecentering.exists_typeI_commonPolynomial_oneSeparated_recentered
#print axioms PostA5TypeIOrdinateRecentering.exists_typeI_commonPolynomial_oneSeparated_recentered_with_collar
