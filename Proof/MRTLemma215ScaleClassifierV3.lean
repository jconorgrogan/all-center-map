import MRTLemma215DynamicPreliminaryV3

/-!
# Exact scale classifier for dynamic HB components

The preliminary multinomial expansion produces a finite multiset of positive
dyadic shell lengths.  This module turns that multiset into the sorted scale
list used verbatim in MRT Lemma 2.15, chooses the largest small prefix, and
records the total Type-II/Type-`d_j`/vanishing trichotomy.  Analytic estimates
are not part of the classifier.
-/

namespace MRTLemma215ScaleClassifierV3

open scoped BigOperators
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215PreliminaryExpansion MRTLemma215DynamicPreliminaryV3
open MAPDynamicHBSourceV3

noncomputable section

/-- A unit choice contributes no positive shell; shell `j` has base `2^j`. -/
def activeShellScale {n : ℕ} : Option (Fin n) → Option ℝ
  | none => none
  | some j => some (2 ^ (j : ℕ) : ℝ)

def choiceScaleMultiset {n : ℕ} (c : Option (Fin n)) : Multiset ℝ :=
  match activeShellScale c with
  | none => 0
  | some x => {x}

def bagScaleMultiset {n k : ℕ} (bag : Sym (Option (Fin n)) k) :
    Multiset ℝ :=
  Multiset.filterMap activeShellScale (↑bag : Multiset (Option (Fin n)))

/-- The exact sorted scale list of one preliminary dynamic HB component. -/
def dynamicPreliminaryScaleList
    {X : ℝ} {K k : ℕ}
    (c : Option (Fin (sourceDyadicCount (hbFactorCutoff X))))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    List ℝ :=
  Multiset.sort
    (choiceScaleMultiset c + bagScaleMultiset zbag + bagScaleMultiset mbag)
    (· ≤ ·)

theorem activeShellScale_pos
    {n : ℕ} {c : Option (Fin n)} {x : ℝ}
    (h : activeShellScale c = some x) : 0 < x := by
  cases c with
  | none => simp [activeShellScale] at h
  | some j =>
      simp only [activeShellScale, Option.some.injEq] at h
      subst x
      positivity

theorem activeShellScale_one
    {n : ℕ} {c : Option (Fin n)} {x : ℝ}
    (h : activeShellScale c = some x) : 1 ≤ x := by
  cases c with
  | none => simp [activeShellScale] at h
  | some j =>
      simp only [activeShellScale, Option.some.injEq] at h
      subst x
      exact one_le_pow₀ (by norm_num)

/-- Every nonempty standard shell starts no later than its truncation point.
The lower bound excludes the degenerate zero coefficient shells that occur
only before the source's sufficiently-large-`X` threshold. -/
theorem sourceDyadicBase_le_cutoff
    {N : ℕ} (hN : 2 ≤ N) (j : Fin (sourceDyadicCount N)) :
    2 ^ (j : ℕ) ≤ N := by
  have hj : (j : ℕ) ≤ (N - 1).log2 := by
    have hjlt : (j : ℕ) < (N - 1).log2 + 1 := by
      simpa [sourceDyadicCount] using j.isLt
    omega
  have hsub : N - 1 ≠ 0 := by omega
  have hpow : 2 ^ (j : ℕ) ≤ N - 1 :=
    (Nat.le_log2 hsub).mp hj
  omega

/-- Every dynamic Möbius shell is literally at most `X^delta` for the live
order `kappa=2*ceil(1/delta)`.  This is the source fact used to exclude
Möbius coefficients from the large Type-`d_j` tail. -/
theorem dynamicMoebiusShellScale_le_rpow
    {X delta : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    (hcut : 2 ≤ ⌊dynamicHBCutoff X (hbOrder delta)⌋₊)
    (j : Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X (hbOrder delta)⌋₊)) :
    (2 ^ (j : ℕ) : ℝ) ≤ Real.rpow X delta := by
  have hbaseNat := sourceDyadicBase_le_cutoff hcut j
  have hbaseFloor : (2 ^ (j : ℕ) : ℝ) ≤
      (⌊dynamicHBCutoff X (hbOrder delta)⌋₊ : ℝ) := by
    exact_mod_cast hbaseNat
  have hcutNonneg : 0 ≤ dynamicHBCutoff X (hbOrder delta) :=
    Real.rpow_nonneg (by positivity) _
  have hfloorReal : (⌊dynamicHBCutoff X (hbOrder delta)⌋₊ : ℝ) ≤
      dynamicHBCutoff X (hbOrder delta) := Nat.floor_le hcutNonneg
  exact hbaseFloor.trans <| hfloorReal.trans <|
    dynamicHBCutoff_hbOrder_le_rpow hX hdelta

theorem bagScaleMultiset_pos
    {n k : ℕ} (bag : Sym (Option (Fin n)) k) {x : ℝ}
    (hx : x ∈ bagScaleMultiset bag) : 0 < x := by
  simp only [bagScaleMultiset, Multiset.mem_filterMap] at hx
  obtain ⟨c, hc, hcx⟩ := hx
  exact activeShellScale_pos hcx

theorem bagScaleMultiset_one
    {n k : ℕ} (bag : Sym (Option (Fin n)) k) {x : ℝ}
    (hx : x ∈ bagScaleMultiset bag) : 1 ≤ x := by
  simp only [bagScaleMultiset, Multiset.mem_filterMap] at hx
  obtain ⟨c, hc, hcx⟩ := hx
  exact activeShellScale_one hcx

theorem choiceScaleMultiset_pos
    {n : ℕ} (c : Option (Fin n)) {x : ℝ}
    (hx : x ∈ choiceScaleMultiset c) : 0 < x := by
  cases hc : activeShellScale c with
  | none => simp [choiceScaleMultiset, hc] at hx
  | some y =>
      simp only [choiceScaleMultiset, hc, Multiset.mem_singleton] at hx
      subst x
      exact activeShellScale_pos hc

theorem choiceScaleMultiset_one
    {n : ℕ} (c : Option (Fin n)) {x : ℝ}
    (hx : x ∈ choiceScaleMultiset c) : 1 ≤ x := by
  cases hc : activeShellScale c with
  | none => simp [choiceScaleMultiset, hc] at hx
  | some y =>
      simp only [choiceScaleMultiset, hc, Multiset.mem_singleton] at hx
      subst x
      exact activeShellScale_one hc

theorem dynamicPreliminaryScaleList_pos
    {X : ℝ} {K k : ℕ}
    (c : Option (Fin (sourceDyadicCount (hbFactorCutoff X))))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    {x : ℝ} (hx : x ∈ dynamicPreliminaryScaleList c zbag mbag) :
    0 < x := by
  have hx' : x ∈
      choiceScaleMultiset c + bagScaleMultiset zbag + bagScaleMultiset mbag := by
    rw [← Multiset.sort_eq
      (choiceScaleMultiset c + bagScaleMultiset zbag + bagScaleMultiset mbag)
      (· ≤ ·)]
    exact hx
  simp only [Multiset.mem_add] at hx'
  rcases hx' with hxcz | hxm
  · rcases hxcz with hxc | hxz
    · exact choiceScaleMultiset_pos c hxc
    · exact bagScaleMultiset_pos zbag hxz
  · exact bagScaleMultiset_pos mbag hxm

theorem dynamicPreliminaryScaleList_one
    {X : ℝ} {K k : ℕ}
    (c : Option (Fin (sourceDyadicCount (hbFactorCutoff X))))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    {x : ℝ} (hx : x ∈ dynamicPreliminaryScaleList c zbag mbag) :
    1 ≤ x := by
  have hx' : x ∈
      choiceScaleMultiset c + bagScaleMultiset zbag + bagScaleMultiset mbag := by
    rw [← Multiset.sort_eq
      (choiceScaleMultiset c + bagScaleMultiset zbag + bagScaleMultiset mbag)
      (· ≤ ·)]
    exact hx
  simp only [Multiset.mem_add] at hx'
  rcases hx' with hxcz | hxm
  · rcases hxcz with hxc | hxz
    · exact choiceScaleMultiset_one c hxc
    · exact bagScaleMultiset_one zbag hxz
  · exact bagScaleMultiset_one mbag hxm

theorem dynamicPreliminaryScaleList_pairwise
    {X : ℝ} {K k : ℕ}
    (c : Option (Fin (sourceDyadicCount (hbFactorCutoff X))))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    (dynamicPreliminaryScaleList c zbag mbag).Pairwise (· ≤ ·) := by
  exact Multiset.pairwise_sort _ _

theorem pow_length_le_prod
    {base : ℝ} {l : List ℝ} (hbase : 0 ≤ base)
    (hlower : ∀ x ∈ l, base ≤ x) :
    base ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : base ≤ a := hlower a (by simp)
      have hal : 0 ≤ a := hbase.trans ha
      have htail : ∀ x ∈ l, base ≤ x := by
        intro x hx
        exact hlower x (by simp [hx])
      have hi := ih htail
      have hlprod : 0 ≤ l.prod :=
        List.prod_nonneg (fun x hx => hbase.trans (htail x hx))
      simp only [List.length_cons, List.prod_cons, pow_succ]
      calc
        base ^ l.length * base ≤ l.prod * a :=
          mul_le_mul hi ha hbase hlprod
        _ = a * l.prod := by ring

theorem one_le_prod_of_one_le
    {l : List ℝ} (hlower : ∀ x ∈ l, 1 ≤ x) : 1 ≤ l.prod := by
  simpa using pow_length_le_prod (l := l) (base := 1) (by norm_num) hlower

theorem drop_scales_ge_head
    {scales : List ℝ} (hsorted : scales.Pairwise (· ≤ ·))
    {s : ℕ} (hs : s < scales.length) {x : ℝ}
    (hx : x ∈ scales.drop s) : scales[s] ≤ x := by
  have hsortedDrop : (scales.drop s).Pairwise (· ≤ ·) := hsorted.drop
  have hdecomp := List.drop_eq_getElem_cons hs
  have hsortedCons :
      (scales[s] :: scales.drop (s + 1)).Pairwise (· ≤ ·) := by
    rw [← hdecomp]
    exact hsortedDrop
  have hxCons : x ∈ scales[s] :: scales.drop (s + 1) := by
    rw [← hdecomp]
    exact hx
  simp only [List.mem_cons] at hxCons
  rcases hxCons with hxeq | hxrest
  · rw [hxeq]
  · exact (List.pairwise_cons.mp hsortedCons).1 x hxrest

/-- If at least `m` sorted tail factors remain, the full lower support product
strictly exceeds the `m`-th power of the first tail threshold. -/
theorem threshold_pow_lt_fullProduct
    {scales : List ℝ} {s m : ℕ} {threshold : ℝ}
    (hsorted : scales.Pairwise (· ≤ ·))
    (hone : ∀ x ∈ scales, 1 ≤ x)
    (hs : s < scales.length)
    (hthreshold : 1 ≤ threshold)
    (hfirst : threshold < scales[s])
    (hm : m ≤ scales.length - s) (hmone : 1 ≤ m) :
    threshold ^ m < scales.prod := by
  have hheadOne : 1 ≤ scales[s] := hone scales[s] (List.getElem_mem hs)
  have hpowStrict : threshold ^ m < scales[s] ^ m :=
    pow_lt_pow_left₀ hfirst (by linarith) (Nat.ne_of_gt hmone)
  have hpowMono : scales[s] ^ m ≤ scales[s] ^ (scales.drop s).length := by
    apply pow_le_pow_right₀ hheadOne
    simpa using hm
  have htailLower : ∀ x ∈ scales.drop s, scales[s] ≤ x := by
    intro x hx
    exact drop_scales_ge_head hsorted hs hx
  have htailProd : scales[s] ^ (scales.drop s).length ≤
      (scales.drop s).prod :=
    pow_length_le_prod (by linarith) htailLower
  have htailPos : 0 ≤ (scales.drop s).prod := by
    exact List.prod_nonneg (fun x hx =>
      ((by norm_num : (0 : ℝ) ≤ 1).trans
        (hone x (List.mem_of_mem_drop hx))))
  have hprefixOne : 1 ≤ (scales.take s).prod := by
    apply one_le_prod_of_one_le
    intro x hx
    exact hone x (List.mem_of_mem_take hx)
  have htail : threshold ^ m < (scales.drop s).prod :=
    hpowStrict.trans_le (hpowMono.trans htailProd)
  calc
    threshold ^ m < (scales.drop s).prod := htail
    _ = 1 * (scales.drop s).prod := by ring
    _ ≤ (scales.take s).prod * (scales.drop s).prod :=
      mul_le_mul_of_nonneg_right hprefixOne htailPos
    _ = scales.prod := List.prod_take_mul_prod_drop scales s

/-- The source threshold `2*X^(1/m)` has `m`-th power at least `2X`. -/
theorem two_mul_rpow_inv_pow_ge_two_mul
    {X : ℝ} {m : ℕ} (hX : 0 ≤ X) (hm : 1 ≤ m) :
    2 * X ≤ (2 * Real.rpow X ((m : ℝ)⁻¹)) ^ m := by
  have hm0 : m ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hm)
  rw [mul_pow]
  have hroot : (Real.rpow X ((m : ℝ)⁻¹)) ^ m = X := by
    change (X ^ ((m : ℝ)⁻¹)) ^ m = X
    exact Real.rpow_inv_natCast_pow hX hm0
  rw [hroot]
  have htwo : (2 : ℝ) ≤ 2 ^ m := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm
  exact mul_le_mul_of_nonneg_right htwo hX

/-- The `j≥m` outcome is incompatible with a component whose lower support
product is at most `2X`; this is the exact vanishing alternative of MRT 2.15. -/
theorem tail_count_lt_of_fullProduct_le_twoX
    {scales : List ℝ} {s m : ℕ} {X : ℝ}
    (hsorted : scales.Pairwise (· ≤ ·))
    (hone : ∀ x ∈ scales, 1 ≤ x)
    (hs : s < scales.length) (hX : 2 ≤ X) (hmone : 1 ≤ m)
    (hfirst : 2 * Real.rpow X ((m : ℝ)⁻¹) < scales[s])
    (hfull : scales.prod ≤ 2 * X) :
    scales.length - s < m := by
  by_contra h
  have hm : m ≤ scales.length - s := le_of_not_gt h
  have hthresholdOne : (1 : ℝ) ≤
      2 * Real.rpow X ((m : ℝ)⁻¹) := by
    have hroot : 1 ≤ Real.rpow X ((m : ℝ)⁻¹) :=
      Real.one_le_rpow (by linarith) (by positivity)
    linarith
  have hlarge := threshold_pow_lt_fullProduct hsorted hone hs
    hthresholdOne hfirst hm hmone
  have htwo := two_mul_rpow_inv_pow_ge_two_mul
    (X := X) (m := m) (by linarith) hmone
  exact (not_lt_of_ge (hfull.trans htwo)) hlarge

/-- Product of the first `s` sorted scales. -/
def scalePrefixProduct (scales : List ℝ) (s : ℕ) : ℝ :=
  (scales.take s).prod

/-- Largest prefix whose product is at most the prescribed small scale. -/
def largestSmallPrefix (scales : List ℝ) (smallScale : ℝ) : ℕ :=
  Nat.findGreatest
    (fun s => scalePrefixProduct scales s ≤ smallScale) scales.length

theorem largestSmallPrefix_le_length (scales : List ℝ) (smallScale : ℝ) :
    largestSmallPrefix scales smallScale ≤ scales.length :=
  Nat.findGreatest_le _

theorem largestSmallPrefix_spec
    {scales : List ℝ} {smallScale : ℝ} (hsmall : 1 ≤ smallScale) :
    scalePrefixProduct scales (largestSmallPrefix scales smallScale) ≤
      smallScale := by
  unfold largestSmallPrefix
  exact Nat.findGreatest_spec
    (P := fun s => scalePrefixProduct scales s ≤ smallScale)
    (m := 0) (n := scales.length) (Nat.zero_le _)
    (by simpa [scalePrefixProduct] using hsmall)

theorem largestSmallPrefix_succ_not_small
    {scales : List ℝ} {smallScale : ℝ}
    (hs : largestSmallPrefix scales smallScale < scales.length) :
    ¬ scalePrefixProduct scales
        (largestSmallPrefix scales smallScale + 1) ≤ smallScale := by
  exact Nat.findGreatest_is_greatest
    (show largestSmallPrefix scales smallScale <
      largestSmallPrefix scales smallScale + 1 by omega)
    (by omega)

theorem scalePrefixProduct_succ
    (scales : List ℝ) {s : ℕ} (hs : s < scales.length) :
    scalePrefixProduct scales (s + 1) =
      scalePrefixProduct scales s * scales[s] := by
  exact List.prod_take_succ scales s hs

/-- In the non-Type-II case the first large factor is genuinely above the
tail threshold.  This is the exact inequality behind the paper's display
`N_{s+1}>2X^(1/m)`. -/
theorem firstLargeScale_gt
    {scales : List ℝ} {smallScale H₀ tailThreshold : ℝ}
    (hpos : ∀ x ∈ scales, 0 < x)
    (hsmall : 1 ≤ smallScale)
    (hgeom : smallScale * tailThreshold ≤ 2 * H₀)
    (hs : largestSmallPrefix scales smallScale < scales.length)
    (hnotII : 2 * H₀ < scalePrefixProduct scales
      (largestSmallPrefix scales smallScale + 1)) :
    tailThreshold < scales[largestSmallPrefix scales smallScale] := by
  let s := largestSmallPrefix scales smallScale
  have hprefix : scalePrefixProduct scales s ≤ smallScale := by
    simpa [s] using
      (largestSmallPrefix_spec (scales := scales) hsmall)
  have hprefixNonneg : 0 ≤ scalePrefixProduct scales s := by
    unfold scalePrefixProduct
    exact List.prod_nonneg (fun x hx =>
      (hpos x (List.mem_of_mem_take hx)).le)
  have hfactorPos : 0 < scales[s] :=
    hpos scales[s] (List.getElem_mem hs)
  by_contra htail
  have hfactor : scales[s] ≤ tailThreshold := le_of_not_gt htail
  have htailNonneg : 0 ≤ tailThreshold := hfactorPos.le.trans hfactor
  have hprod : scalePrefixProduct scales s * scales[s] ≤
      smallScale * tailThreshold := by
    calc
      scalePrefixProduct scales s * scales[s] ≤
          smallScale * scales[s] :=
        mul_le_mul_of_nonneg_right hprefix hfactorPos.le
      _ ≤ smallScale * tailThreshold :=
        mul_le_mul_of_nonneg_left hfactor
          ((by norm_num : (0 : ℝ) ≤ 1).trans hsmall)
  rw [scalePrefixProduct_succ scales hs] at hnotII
  exact (not_lt_of_ge (hprod.trans hgeom)) hnotII

/-- Total scale outcome. `vanishing` covers both an all-small component and
the `j≥m` product-support alternative in MRT Lemma 2.15. -/
inductive MRTScaleOutcome (m : ℕ) where
  | typeII
  | typeD (j : Fin m)
  | vanishing
deriving DecidableEq

def classifyScaleList (m : ℕ) (scales : List ℝ)
    (smallScale H₀ : ℝ) : MRTScaleOutcome m :=
  let s := largestSmallPrefix scales smallScale
  if hs : s < scales.length then
    if scalePrefixProduct scales (s + 1) ≤ 2 * H₀ then
      .typeII
    else if hj : scales.length - s < m then
      .typeD ⟨scales.length - s, hj⟩
    else .vanishing
  else .vanishing

theorem classifyScaleList_typeII
    {m : ℕ} {scales : List ℝ} {smallScale H₀ : ℝ}
    (hs : largestSmallPrefix scales smallScale < scales.length)
    (hII : scalePrefixProduct scales
      (largestSmallPrefix scales smallScale + 1) ≤ 2 * H₀) :
    classifyScaleList m scales smallScale H₀ = .typeII := by
  simp [classifyScaleList, hs, hII]

theorem classifyScaleList_typeD
    {m : ℕ} {scales : List ℝ} {smallScale H₀ : ℝ}
    (hs : largestSmallPrefix scales smallScale < scales.length)
    (hnotII : ¬ scalePrefixProduct scales
      (largestSmallPrefix scales smallScale + 1) ≤ 2 * H₀)
    (hj : scales.length - largestSmallPrefix scales smallScale < m) :
    classifyScaleList m scales smallScale H₀ =
      .typeD ⟨scales.length - largestSmallPrefix scales smallScale, hj⟩ := by
  simp [classifyScaleList, hs, hnotII, hj]

theorem classifyScaleList_vanishing_of_allSmall
    {m : ℕ} {scales : List ℝ} {smallScale H₀ : ℝ}
    (hs : ¬ largestSmallPrefix scales smallScale < scales.length) :
    classifyScaleList m scales smallScale H₀ = .vanishing := by
  simp [classifyScaleList, hs]

theorem classifyScaleList_vanishing_of_largeTail
    {m : ℕ} {scales : List ℝ} {smallScale H₀ : ℝ}
    (hs : largestSmallPrefix scales smallScale < scales.length)
    (hnotII : ¬ scalePrefixProduct scales
      (largestSmallPrefix scales smallScale + 1) ≤ 2 * H₀)
    (htail : ¬ scales.length - largestSmallPrefix scales smallScale < m) :
    classifyScaleList m scales smallScale H₀ = .vanishing := by
  simp [classifyScaleList, hs, hnotII, htail]

end
end MRTLemma215ScaleClassifierV3

#print axioms MRTLemma215ScaleClassifierV3.dynamicPreliminaryScaleList_pos
#print axioms MRTLemma215ScaleClassifierV3.largestSmallPrefix_spec
#print axioms MRTLemma215ScaleClassifierV3.firstLargeScale_gt
#print axioms MRTLemma215ScaleClassifierV3.classifyScaleList_typeD
#print axioms MRTLemma215ScaleClassifierV3.classifyScaleList_vanishing_of_largeTail
