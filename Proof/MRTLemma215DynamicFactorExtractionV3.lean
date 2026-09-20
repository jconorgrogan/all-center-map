import MRTLemma215DynamicSupportV3

/-!
# Literal active-factor extraction from dynamic HB components

Unit choices in the multinomial `Sym` bags are removed without losing
multiplicity.  Every remaining choice becomes a concrete
`NatDyadicFactor`.  The main generic theorem proves that the resulting list
has exactly the same Dirichlet convolution as the original multiset product.
-/

namespace MRTLemma215DynamicFactorExtractionV3

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215PreliminaryExpansion MRTLemma215DynamicPreliminaryV3
open MRTLemma215DynamicSupportV3

noncomputable section

def optionFactor {n : ℕ} (factor : Fin n → NatDyadicFactor) :
    Option (Fin n) → Option NatDyadicFactor
  | none => none
  | some j => some (factor j)

def optionFactorCoeff {n : ℕ} (factor : Fin n → NatDyadicFactor) :
    Option (Fin n) → ArithmeticFunction ℂ
  | none => 1
  | some j => (factor j).coeff

def multisetRepresentative {α : Type*} (s : Multiset α) : List α :=
  Quotient.out s

theorem coe_multisetRepresentative {α : Type*} (s : Multiset α) :
    (↑(multisetRepresentative s) : Multiset α) = s := by
  exact Quotient.out_eq s

/-- Canonical multiplicity-preserving list of the active factors of a bag. -/
def bagFactorList {n k : ℕ} (factor : Fin n → NatDyadicFactor)
    (bag : Sym (Option (Fin n)) k) : List NatDyadicFactor :=
  (multisetRepresentative (↑bag : Multiset (Option (Fin n)))).filterMap
    (optionFactor factor)

theorem factorConvolution_append
    (l₁ l₂ : List NatDyadicFactor) :
    factorConvolution (l₁ ++ l₂) =
      factorConvolution l₁ * factorConvolution l₂ := by
  induction l₁ with
  | nil => simp [factorConvolution]
  | cons f l ih =>
      simp only [List.cons_append, factorConvolution, ih]
      ring

private theorem factorConvolution_filterMap_option
    {n : ℕ} (factor : Fin n → NatDyadicFactor)
    (l : List (Option (Fin n))) :
    factorConvolution (l.filterMap (optionFactor factor)) =
      (l.map (optionFactorCoeff factor)).prod := by
  induction l with
  | nil => simp [factorConvolution]
  | cons c l ih =>
      cases c with
      | none =>
          rw [List.filterMap_cons_none (by rfl)]
          simpa only [List.map_cons, optionFactorCoeff, List.prod_cons,
            one_mul] using ih
      | some j =>
          rw [List.filterMap_cons_some (by rfl)]
          simpa only [factorConvolution, List.map_cons, optionFactorCoeff,
            List.prod_cons] using congrArg (fun F => (factor j).coeff * F) ih

/-- Removing unit choices preserves the exact multiset convolution product. -/
theorem factorConvolution_bagFactorList
    {n k : ℕ} (factor : Fin n → NatDyadicFactor)
    (bag : Sym (Option (Fin n)) k) :
    factorConvolution (bagFactorList factor bag) =
      (Multiset.map (optionFactorCoeff factor)
        (↑bag : Multiset (Option (Fin n)))).prod := by
  unfold bagFactorList
  rw [factorConvolution_filterMap_option]
  let l := multisetRepresentative (↑bag : Multiset (Option (Fin n)))
  have hsort : (↑l : Multiset (Option (Fin n))) =
      (↑bag : Multiset (Option (Fin n))) := by
    exact coe_multisetRepresentative _
  have hmap := congrArg
    (fun s : Multiset (Option (Fin n)) =>
      (s.map (optionFactorCoeff factor)).prod) hsort
  simpa [l, Multiset.map_coe, Multiset.prod_coe] using hmap

theorem coe_realLengths_bagFactorList
    {n k : ℕ} (factor : Fin n → NatDyadicFactor)
    (bag : Sym (Option (Fin n)) k) :
    (↑((bagFactorList factor bag).map
        (fun f => (f.length : ℝ))) : Multiset ℝ) =
      Multiset.filterMap
        (fun c => Option.map (fun j => ((factor j).length : ℝ)) c)
        (↑bag : Multiset (Option (Fin n))) := by
  unfold bagFactorList
  rw [← Multiset.map_coe, ← Multiset.filterMap_coe,
    Multiset.map_filterMap, coe_multisetRepresentative]
  congr 1
  funext c
  cases c <;> rfl

def dynamicLogFactor (X : ℝ)
    (j : Fin (sourceDyadicCount (hbFactorCutoff X))) : NatDyadicFactor where
  length := 2 ^ (j : ℕ)
  coeff := hbLogShell X j
  support := sourceDyadicArithmetic_supported _ _ j

def dynamicZetaFactor (X : ℝ)
    (j : Fin (sourceDyadicCount (hbFactorCutoff X))) : NatDyadicFactor where
  length := 2 ^ (j : ℕ)
  coeff := hbZetaShell X j
  support := sourceDyadicArithmetic_supported _ _ j

def dynamicMoebiusFactor (X : ℝ) (K : ℕ)
    (j : Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊)) :
    NatDyadicFactor where
  length := 2 ^ (j : ℕ)
  coeff := dynamicHBMoebiusShell X K j
  support := sourceDyadicArithmetic_supported _ _ j

theorem optionFactorCoeff_dynamicZeta
    (X : ℝ)
    (c : Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) :
    optionFactorCoeff (dynamicZetaFactor X) c =
      shellChoice 1 (hbZetaShell X) c := by
  cases c <;> rfl

theorem optionFactorCoeff_dynamicMoebius
    (X : ℝ) (K : ℕ)
    (c : Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) :
    optionFactorCoeff (dynamicMoebiusFactor X K) c =
      shellChoice 1 (dynamicHBMoebiusShell X K) c := by
  cases c <;> rfl

theorem realLengths_zetaBag_eq_scaleMultiset
    {X : ℝ} {k : ℕ}
    (bag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k) :
    (↑((bagFactorList (dynamicZetaFactor X) bag).map
        (fun f => (f.length : ℝ))) : Multiset ℝ) =
      MRTLemma215ScaleClassifierV3.bagScaleMultiset bag := by
  rw [coe_realLengths_bagFactorList]
  unfold MRTLemma215ScaleClassifierV3.bagScaleMultiset
  congr 1
  funext c
  cases c <;> simp [dynamicZetaFactor,
    MRTLemma215ScaleClassifierV3.activeShellScale]

theorem realLengths_moebiusBag_eq_scaleMultiset
    {X : ℝ} {K k : ℕ}
    (bag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) k) :
    (↑((bagFactorList (dynamicMoebiusFactor X K) bag).map
        (fun f => (f.length : ℝ))) : Multiset ℝ) =
      MRTLemma215ScaleClassifierV3.bagScaleMultiset bag := by
  rw [coe_realLengths_bagFactorList]
  unfold MRTLemma215ScaleClassifierV3.bagScaleMultiset
  congr 1
  funext c
  cases c <;> simp [dynamicMoebiusFactor,
    MRTLemma215ScaleClassifierV3.activeShellScale]

theorem factorConvolution_zetaBag
    {X : ℝ} {k : ℕ}
    (bag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k) :
    factorConvolution (bagFactorList (dynamicZetaFactor X) bag) =
      (Multiset.map (shellChoice 1 (hbZetaShell X))
        (↑bag : Multiset
          (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))))).prod := by
  rw [factorConvolution_bagFactorList]
  rw [show optionFactorCoeff (dynamicZetaFactor X) =
      shellChoice 1 (hbZetaShell X) by
    funext c
    exact optionFactorCoeff_dynamicZeta X c]

theorem factorConvolution_moebiusBag
    {X : ℝ} {K k : ℕ}
    (bag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) k) :
    factorConvolution (bagFactorList (dynamicMoebiusFactor X K) bag) =
      (Multiset.map (shellChoice 1 (dynamicHBMoebiusShell X K))
        (↑bag : Multiset
          (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))))).prod := by
  rw [factorConvolution_bagFactorList]
  rw [show optionFactorCoeff (dynamicMoebiusFactor X K) =
      shellChoice 1 (dynamicHBMoebiusShell X K) by
    funext c
    exact optionFactorCoeff_dynamicMoebius X K c]

def dynamicZetaBagProduct
    {X : ℝ} {k : ℕ}
    (bag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k) :
    ArithmeticFunction ℂ :=
  (Multiset.map (shellChoice 1 (hbZetaShell X))
    (↑bag : Multiset
      (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))))).prod

def dynamicMoebiusBagProduct
    {X : ℝ} {K k : ℕ}
    (bag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) k) :
    ArithmeticFunction ℂ :=
  (Multiset.map (shellChoice 1 (dynamicHBMoebiusShell X K))
    (↑bag : Multiset
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))))).prod

/-- The active factor list of one component with a nonzero log choice. -/
def dynamicComponentFactorList
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    List NatDyadicFactor :=
  dynamicLogFactor X logIndex ::
    (bagFactorList (dynamicZetaFactor X) zbag ++
      bagFactorList (dynamicMoebiusFactor X K) mbag)

theorem dynamicComponent_realLengths_eq_scaleMultiset
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    (↑((dynamicComponentFactorList logIndex zbag mbag).map
        (fun f => (f.length : ℝ))) : Multiset ℝ) =
      MRTLemma215ScaleClassifierV3.choiceScaleMultiset (some logIndex) +
        MRTLemma215ScaleClassifierV3.bagScaleMultiset zbag +
        MRTLemma215ScaleClassifierV3.bagScaleMultiset mbag := by
  let A := (bagFactorList (dynamicZetaFactor X) zbag).map
    (fun f => (f.length : ℝ))
  let B := (bagFactorList (dynamicMoebiusFactor X K) mbag).map
    (fun f => (f.length : ℝ))
  have hz : (↑A : Multiset ℝ) =
      MRTLemma215ScaleClassifierV3.bagScaleMultiset zbag := by
    exact realLengths_zetaBag_eq_scaleMultiset zbag
  have hm : (↑B : Multiset ℝ) =
      MRTLemma215ScaleClassifierV3.bagScaleMultiset mbag := by
    exact realLengths_moebiusBag_eq_scaleMultiset mbag
  have htail : (↑(A ++ B) : Multiset ℝ) =
      MRTLemma215ScaleClassifierV3.bagScaleMultiset zbag +
        MRTLemma215ScaleClassifierV3.bagScaleMultiset mbag := by
    change (↑A : Multiset ℝ) + (↑B : Multiset ℝ) = _
    rw [hz, hm]
  dsimp only [A, B] at htail
  unfold dynamicComponentFactorList dynamicLogFactor
  simp only [List.map_cons, List.map_append]
  unfold MRTLemma215ScaleClassifierV3.choiceScaleMultiset
    MRTLemma215ScaleClassifierV3.activeShellScale
  have hc := congrArg (fun s : Multiset ℝ =>
    (2 ^ (logIndex : ℕ) : ℝ) ::ₘ s) htail
  simpa [A, B] using hc

theorem dynamicComponent_scaleList_prod_eq_lowerProduct
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    (MRTLemma215ScaleClassifierV3.dynamicPreliminaryScaleList
        (some logIndex) zbag mbag).prod =
      (factorLowerProduct
        (dynamicComponentFactorList logIndex zbag mbag) : ℝ) := by
  have hsort := Multiset.sort_eq
    (MRTLemma215ScaleClassifierV3.choiceScaleMultiset (some logIndex) +
      MRTLemma215ScaleClassifierV3.bagScaleMultiset zbag +
      MRTLemma215ScaleClassifierV3.bagScaleMultiset mbag) (· ≤ ·)
  have hlengths := dynamicComponent_realLengths_eq_scaleMultiset
    logIndex zbag mbag
  have hmulti :
      (↑(MRTLemma215ScaleClassifierV3.dynamicPreliminaryScaleList
        (some logIndex) zbag mbag) : Multiset ℝ) =
        ↑((dynamicComponentFactorList logIndex zbag mbag).map
          (fun f => (f.length : ℝ))) := hsort.trans hlengths.symm
  have hprod := congrArg (fun s : Multiset ℝ => s.prod) hmulti
  change
    (MRTLemma215ScaleClassifierV3.dynamicPreliminaryScaleList
      (some logIndex) zbag mbag).prod =
      ((dynamicComponentFactorList logIndex zbag mbag).map
        (fun f => (f.length : ℝ))).prod at hprod
  rw [hprod]
  simp [factorLowerProduct, Function.comp_def]

/-- The exact arithmetic-function component before the scalar multinomial
coefficients are absorbed into the first factor. -/
theorem factorConvolution_dynamicComponentFactorList
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    factorConvolution (dynamicComponentFactorList logIndex zbag mbag) =
      hbLogShell X logIndex *
        dynamicZetaBagProduct zbag * dynamicMoebiusBagProduct mbag := by
  unfold dynamicComponentFactorList dynamicLogFactor
  simp only [factorConvolution, factorConvolution_append]
  rw [factorConvolution_zetaBag, factorConvolution_moebiusBag]
  unfold dynamicZetaBagProduct dynamicMoebiusBagProduct
  ring

/-- One indexed summand of the flattened preliminary expansion. -/
def dynamicPreliminaryComponent
    {X : ℝ} {K k : ℕ}
    (c : Option (Fin (sourceDyadicCount (hbFactorCutoff X))))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    ArithmeticFunction ℂ :=
  dynamicComplexHBScalar K k *
    (shellChoice (hbLogUnit X) (hbLogShell X) c *
      shellPowerTerm (hbZetaUnit X) (hbZetaShell X) k zbag *
      shellPowerTerm (dynamicHBMoebiusUnit X K)
        (dynamicHBMoebiusShell X K) (k + 1) mbag)

def dynamicComponentScalar
    {X : ℝ} {K k : ℕ}
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    ArithmeticFunction ℂ :=
  dynamicComplexHBScalar K k *
    (((↑zbag : Multiset
      (Option (Fin (sourceDyadicCount (hbFactorCutoff X))))).countPerms :
        ArithmeticFunction ℂ) *
      ((↑mbag : Multiset
        (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊)))).countPerms :
          ArithmeticFunction ℂ))

/-- The signed binomial coefficient is an honest scalar arithmetic
function, hence is supported only at `1`. -/
theorem dynamicComplexHBScalar_eq_smul_one (K k : ℕ) :
    dynamicComplexHBScalar K k =
      (((-1 : ℂ) ^ k * (K.choose (k + 1) : ℂ)) •
        (1 : ArithmeticFunction ℂ)) := by
  have hinner :
      ((-1 : ArithmeticFunction ℝ) ^ k *
          (K.choose (k + 1) : ArithmeticFunction ℝ)) =
        algebraMap ℝ (ArithmeticFunction ℝ)
          ((-1 : ℝ) ^ k * (K.choose (k + 1) : ℝ)) := by
    rw [map_mul, map_pow]
    congr <;> norm_num
  rw [dynamicComplexHBScalar, hinner,
    Algebra.algebraMap_eq_smul_one]
  ext n
  by_cases hn : n = 1 <;>
    simp [complexifyArithmetic, ArithmeticFunction.one_apply, hn]

theorem natCastArithmetic_eq_smul_one (a : ℕ) :
    (a : ArithmeticFunction ℂ) =
      (a : ℂ) • (1 : ArithmeticFunction ℂ) := by
  have hinner : (a : ArithmeticFunction ℂ) =
      algebraMap ℂ (ArithmeticFunction ℂ) (a : ℂ) := by
    norm_num
  exact hinner.trans (Algebra.algebraMap_eq_smul_one (a : ℂ))

/-- All multinomial and HB signs live at the Dirichlet-convolution unit;
they therefore do not enlarge either endpoint of the active factor support. -/
theorem dynamicComponentScalar_eq_smul_one
    {X : ℝ} {K k : ℕ}
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    dynamicComponentScalar zbag mbag =
      ((((-1 : ℂ) ^ k * (K.choose (k + 1) : ℂ)) *
          ((↑zbag : Multiset
            (Option (Fin (sourceDyadicCount (hbFactorCutoff X))))).countPerms : ℂ) *
          ((↑mbag : Multiset
            (Option (Fin (sourceDyadicCount
              ⌊dynamicHBCutoff X K⌋₊)))).countPerms : ℂ)) •
        (1 : ArithmeticFunction ℂ)) := by
  rw [dynamicComponentScalar, dynamicComplexHBScalar_eq_smul_one,
    natCastArithmetic_eq_smul_one, natCastArithmetic_eq_smul_one]
  ext n
  by_cases hn : n = 1
  · subst n
    simp
    ring
  · simp [hn]

theorem dynamicComponentScalar_apply_ne_one
    {X : ℝ} {K k : ℕ}
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    {n : ℕ} (hn : n ≠ 1) :
    dynamicComponentScalar zbag mbag n = 0 := by
  rw [dynamicComponentScalar_eq_smul_one]
  simp [hn]

theorem dynamicPreliminaryComponent_none
    {X : ℝ} {K k : ℕ}
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    dynamicPreliminaryComponent (X := X) (K := K) none zbag mbag = 0 := by
  unfold dynamicPreliminaryComponent
  rw [hbLogUnit_eq_zero]
  simp [shellChoice]

/-- Every nonzero-log preliminary component is exactly its scalar
multinomial coefficient times the convolution of the extracted active
dyadic factors. -/
theorem dynamicPreliminaryComponent_some_eq_factorConvolution
    {X : ℝ} (hX : 1 ≤ X) {K k : ℕ} (hK : 1 ≤ K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    dynamicPreliminaryComponent (some logIndex) zbag mbag =
      dynamicComponentScalar zbag mbag *
        factorConvolution (dynamicComponentFactorList logIndex zbag mbag) := by
  unfold dynamicPreliminaryComponent dynamicComponentScalar shellPowerTerm
  rw [hbZetaUnit_eq_one hX, dynamicHBMoebiusUnit_eq_one hX hK]
  simp only [shellChoice]
  rw [factorConvolution_dynamicComponentFactorList]
  unfold dynamicZetaBagProduct dynamicMoebiusBagProduct
  simp only [shellChoice]
  ring

/-- The full preliminary branch after deleting the identically zero log-unit
choice and replacing every surviving component by its literal factor list. -/
def dynamicFactorizedPreliminarySum
    (X : ℝ) (K k : ℕ) : ArithmeticFunction ℂ :=
  ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)),
    ∑ zbag ∈ (Finset.univ : Finset
        (Option (Fin (sourceDyadicCount (hbFactorCutoff X))))).sym k,
      ∑ mbag ∈ (Finset.univ : Finset
          (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊)))).sym
            (k + 1),
        dynamicComponentScalar zbag mbag *
          factorConvolution
            (dynamicComponentFactorList logIndex zbag mbag)

theorem dynamicPreliminaryHBShellComponentSum_eq_factorized
    {X : ℝ} (hX : 1 ≤ X) {K : ℕ} (hK : 1 ≤ K) (k : ℕ) :
    dynamicPreliminaryHBShellComponentSum X K k =
      dynamicFactorizedPreliminarySum X K k := by
  change
    (∑ c : Option (Fin (sourceDyadicCount (hbFactorCutoff X))),
      ∑ zbag ∈ (Finset.univ : Finset
          (Option (Fin (sourceDyadicCount (hbFactorCutoff X))))).sym k,
        ∑ mbag ∈ (Finset.univ : Finset
            (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊)))).sym
              (k + 1),
          dynamicPreliminaryComponent c zbag mbag) =
      dynamicFactorizedPreliminarySum X K k
  rw [Fintype.sum_option]
  have hnone :
      (∑ zbag ∈ (Finset.univ : Finset
          (Option (Fin (sourceDyadicCount (hbFactorCutoff X))))).sym k,
        ∑ mbag ∈ (Finset.univ : Finset
            (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊)))).sym
              (k + 1),
          dynamicPreliminaryComponent none zbag mbag) = 0 := by
    apply Finset.sum_eq_zero
    intro zbag hzbag
    apply Finset.sum_eq_zero
    intro mbag hmbag
    exact dynamicPreliminaryComponent_none zbag mbag
  rw [hnone, zero_add]
  unfold dynamicFactorizedPreliminarySum
  apply Finset.sum_congr rfl
  intro logIndex hlogIndex
  apply Finset.sum_congr rfl
  intro zbag hzbag
  apply Finset.sum_congr rfl
  intro mbag hmbag
  exact dynamicPreliminaryComponent_some_eq_factorConvolution
    hX hK logIndex zbag mbag

def maskedDynamicFactorizedPreliminarySum
    (X : ℝ) (K k n : ℕ) : ℂ :=
  if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then
    dynamicFactorizedPreliminarySum X K k n else 0

/-- Each dynamic raw HB branch now has an exact finite factor-list expansion.
This is the direct source input to the scale classifier. -/
theorem dynamicHBBranchCoeff_eq_maskedFactorizedPreliminarySum
    {X : ℝ} (hX : 1 ≤ X) {K : ℕ} (hK : 1 ≤ K)
    (branch : Fin K) (n : ℕ) :
    dynamicHBBranchCoeff X K branch n =
      maskedDynamicFactorizedPreliminarySum X K branch n := by
  rw [dynamicHBBranchCoeff_eq_maskedPreliminaryComponentSum
    (le_trans (by norm_num) hX)]
  unfold maskedDynamicPreliminaryHBShellComponentSum
    maskedDynamicFactorizedPreliminarySum
  rw [dynamicPreliminaryHBShellComponentSum_eq_factorized hX hK]

/-- A component with at least `m` factors in the non-Type-II tail vanishes
identically after the `(X,2X]` mask.  This is the fully connected `j≥m`
alternative: exact Sym component, exact scale classifier, and exact Dirichlet
support are all present in one statement. -/
theorem maskedDynamicPreliminaryComponent_eq_zero_of_largeTail
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K k m : ℕ} (hK : 1 ≤ K) (hmone : 1 ≤ m)
    (hgeom : Real.rpow X delta *
        (2 * Real.rpow X ((m : ℝ)⁻¹)) ≤ 2 * H₀)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (hs : MRTLemma215ScaleClassifierV3.largestSmallPrefix
        (MRTLemma215ScaleClassifierV3.dynamicPreliminaryScaleList
          (some logIndex) zbag mbag) (Real.rpow X delta) <
      (MRTLemma215ScaleClassifierV3.dynamicPreliminaryScaleList
        (some logIndex) zbag mbag).length)
    (hnotII : 2 * H₀ <
      MRTLemma215ScaleClassifierV3.scalePrefixProduct
        (MRTLemma215ScaleClassifierV3.dynamicPreliminaryScaleList
          (some logIndex) zbag mbag)
        (MRTLemma215ScaleClassifierV3.largestSmallPrefix
          (MRTLemma215ScaleClassifierV3.dynamicPreliminaryScaleList
            (some logIndex) zbag mbag) (Real.rpow X delta) + 1))
    (htail : m ≤
      (MRTLemma215ScaleClassifierV3.dynamicPreliminaryScaleList
          (some logIndex) zbag mbag).length -
        MRTLemma215ScaleClassifierV3.largestSmallPrefix
          (MRTLemma215ScaleClassifierV3.dynamicPreliminaryScaleList
            (some logIndex) zbag mbag) (Real.rpow X delta))
    (n : ℕ) :
    (if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then
      dynamicPreliminaryComponent (some logIndex) zbag mbag n else 0) = 0 := by
  let scales := MRTLemma215ScaleClassifierV3.dynamicPreliminaryScaleList
    (some logIndex) zbag mbag
  let s := MRTLemma215ScaleClassifierV3.largestSmallPrefix scales
    (Real.rpow X delta)
  have hsmall : 1 ≤ Real.rpow X delta :=
    Real.one_le_rpow (by linarith) hdelta.le
  have hpos : ∀ x ∈ scales, 0 < x := by
    intro x hx
    exact MRTLemma215ScaleClassifierV3.dynamicPreliminaryScaleList_pos
      (some logIndex) zbag mbag hx
  have hone : ∀ x ∈ scales, 1 ≤ x := by
    intro x hx
    exact MRTLemma215ScaleClassifierV3.dynamicPreliminaryScaleList_one
      (some logIndex) zbag mbag hx
  have hsorted : scales.Pairwise (· ≤ ·) :=
    MRTLemma215ScaleClassifierV3.dynamicPreliminaryScaleList_pairwise
      (some logIndex) zbag mbag
  have hs' : s < scales.length := by simpa [s, scales] using hs
  have hnotII' : 2 * H₀ <
      MRTLemma215ScaleClassifierV3.scalePrefixProduct scales (s + 1) := by
    simpa [s, scales] using hnotII
  have htail' : m ≤ scales.length - s := by simpa [s, scales] using htail
  have hfirst : 2 * Real.rpow X ((m : ℝ)⁻¹) < scales[s] :=
    MRTLemma215ScaleClassifierV3.firstLargeScale_gt hpos hsmall hgeom
      hs' hnotII'
  have hlarge := MRTLemma215ScaleClassifierV3.threshold_pow_lt_fullProduct
    hsorted hone hs' (by
      have hroot : 1 ≤ Real.rpow X ((m : ℝ)⁻¹) :=
        Real.one_le_rpow (by linarith) (by positivity)
      linarith) hfirst htail' hmone
  have htwo := MRTLemma215ScaleClassifierV3.two_mul_rpow_inv_pow_ge_two_mul
    (X := X) (m := m) (by linarith) hmone
  have hprodScales : 2 * X < scales.prod := htwo.trans_lt hlarge
  have hscaleEq := dynamicComponent_scaleList_prod_eq_lowerProduct
    logIndex zbag mbag
  have hprodFactors : 2 * X <
      (factorLowerProduct
        (dynamicComponentFactorList logIndex zbag mbag) : ℝ) := by
    simpa [scales] using hprodScales.trans_le hscaleEq.le
  have hcomponent :=
    congrArg (fun F : ArithmeticFunction ℂ => F n)
      (dynamicPreliminaryComponent_some_eq_factorConvolution
        (by linarith : 1 ≤ X) hK logIndex zbag mbag)
  change dynamicPreliminaryComponent (some logIndex) zbag mbag n =
    (dynamicComponentScalar zbag mbag *
      factorConvolution
        (dynamicComponentFactorList logIndex zbag mbag)) n at hcomponent
  rw [hcomponent]
  simpa [dynamicComponentFactorList] using
    (masked_scalar_mul_factorConvolution_eq_zero_of_twoX_lt
      (X := X) (by linarith)
      (dynamicComponentScalar zbag mbag)
      (dynamicLogFactor X logIndex)
      (bagFactorList (dynamicZetaFactor X) zbag ++
        bagFactorList (dynamicMoebiusFactor X K) mbag)
      hprodFactors n)

/-- The other vanishing alternative in MRT Lemma 2.15.  If the maximal
`X^delta` prefix contains every active shell, then the literal upper support
is still below `X` once `X` exceeds the displayed finite dyadic dilation.
Unlike the paper's `X` sufficiently large notation, the exact size condition
is kept as a hypothesis here. -/
theorem maskedDynamicPreliminaryComponent_eq_zero_of_allSmall
    {X delta : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K k : ℕ} (hK : 1 ≤ K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (hsize : (2 : ℝ) ^
        (dynamicComponentFactorList logIndex zbag mbag).length *
          Real.rpow X delta ≤ X)
    (hall : ¬ MRTLemma215ScaleClassifierV3.largestSmallPrefix
        (MRTLemma215ScaleClassifierV3.dynamicPreliminaryScaleList
          (some logIndex) zbag mbag) (Real.rpow X delta) <
      (MRTLemma215ScaleClassifierV3.dynamicPreliminaryScaleList
        (some logIndex) zbag mbag).length)
    (n : ℕ) :
    (if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then
      dynamicPreliminaryComponent (some logIndex) zbag mbag n else 0) = 0 := by
  let scales := MRTLemma215ScaleClassifierV3.dynamicPreliminaryScaleList
    (some logIndex) zbag mbag
  let factors := dynamicComponentFactorList logIndex zbag mbag
  let s := MRTLemma215ScaleClassifierV3.largestSmallPrefix scales
    (Real.rpow X delta)
  have hsmall : 1 ≤ Real.rpow X delta :=
    Real.one_le_rpow (by linarith) hdelta.le
  have hsLe : s ≤ scales.length :=
    MRTLemma215ScaleClassifierV3.largestSmallPrefix_le_length _ _
  have hlenLe : scales.length ≤ s := by
    have := le_of_not_gt hall
    simpa [s, scales] using this
  have hsEq : s = scales.length := le_antisymm hsLe hlenLe
  have hprefix := MRTLemma215ScaleClassifierV3.largestSmallPrefix_spec
    (scales := scales) hsmall
  change MRTLemma215ScaleClassifierV3.scalePrefixProduct scales s ≤
    Real.rpow X delta at hprefix
  have hscales : scales.prod ≤ Real.rpow X delta := by
    rw [hsEq] at hprefix
    simpa [MRTLemma215ScaleClassifierV3.scalePrefixProduct] using hprefix
  have hscaleEq := dynamicComponent_scaleList_prod_eq_lowerProduct
    logIndex zbag mbag
  have hlower : (factorLowerProduct factors : ℝ) ≤ Real.rpow X delta := by
    rw [← hscaleEq]
    simpa [scales, factors] using hscales
  have hupper : (factorUpperProduct factors : ℝ) ≤ X := by
    calc
      (factorUpperProduct factors : ℝ) =
          (2 : ℝ) ^ factors.length * (factorLowerProduct factors : ℝ) := by
        rw [factorUpperProduct_eq_pow_mul_lowerProduct]
        norm_num
      _ ≤ (2 : ℝ) ^ factors.length * Real.rpow X delta :=
        mul_le_mul_of_nonneg_left hlower (by positivity)
      _ ≤ X := by simpa [factors] using hsize
  by_cases hn : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊
  · rw [if_pos hn]
    have hnReal : X < (n : ℝ) :=
      (Nat.floor_lt (by linarith : 0 ≤ X)).mp (Finset.mem_Ioc.mp hn).1
    have hupperReal : (factorUpperProduct factors : ℝ) < n :=
      hupper.trans_lt hnReal
    have hupperNat : factorUpperProduct factors < n := by
      exact_mod_cast hupperReal
    have hzero : factorConvolution factors n = 0 := by
      exact factorConvolution_zero_of_upperProduct_lt
        (dynamicLogFactor X logIndex)
        (bagFactorList (dynamicZetaFactor X) zbag ++
          bagFactorList (dynamicMoebiusFactor X K) mbag)
        (by simpa [factors, dynamicComponentFactorList] using hupperNat)
    have hcomponent :=
      congrArg (fun F : ArithmeticFunction ℂ => F n)
        (dynamicPreliminaryComponent_some_eq_factorConvolution
          (by linarith : 1 ≤ X) hK logIndex zbag mbag)
    change dynamicPreliminaryComponent (some logIndex) zbag mbag n =
      (dynamicComponentScalar zbag mbag * factorConvolution factors) n at hcomponent
    rw [hcomponent, dynamicComponentScalar_eq_smul_one]
    simpa [hzero]
  · rw [if_neg hn]

end
end MRTLemma215DynamicFactorExtractionV3

#print axioms MRTLemma215DynamicFactorExtractionV3.factorConvolution_bagFactorList
#print axioms MRTLemma215DynamicFactorExtractionV3.factorConvolution_dynamicComponentFactorList
#print axioms MRTLemma215DynamicFactorExtractionV3.dynamicPreliminaryComponent_some_eq_factorConvolution
#print axioms MRTLemma215DynamicFactorExtractionV3.dynamicPreliminaryHBShellComponentSum_eq_factorized
#print axioms MRTLemma215DynamicFactorExtractionV3.dynamicHBBranchCoeff_eq_maskedFactorizedPreliminarySum
#print axioms MRTLemma215DynamicFactorExtractionV3.maskedDynamicPreliminaryComponent_eq_zero_of_largeTail
#print axioms MRTLemma215DynamicFactorExtractionV3.maskedDynamicPreliminaryComponent_eq_zero_of_allSmall
