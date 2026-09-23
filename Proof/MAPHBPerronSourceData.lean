import MAPFarSourceWeldScaffold
import MAPHeathBrownFiniteIdentity
import MRTProposition51Source
import MRTCorollary25Certified
import MRTCorollary25TypeD1IntegratedWeld
import MRTProposition61TypeD1Factorization
import MRTSourceBaseApertureOuterCutoffWeld

/-!
# Literal Heath--Brown/Perron source data for the MAP far branch

This file starts from the exact eight-term Heath--Brown identity and constructs
its literal signed, masked branch family.  It proves that the MAP Mangoldt
coefficient, the source critical-line polynomial, and the `q₀ = 1` source
component are controlled by those eight branches.  The `q₀ > 1` contribution
is retained as the literal small-remainder mass from Lemma 2.16; it is not
silently folded into a cell error.

The finite-height Perron theorem used after dyadic packetization is already
certified by `MAPMRTCorollary25Certified.mrtCorollary25_certified`.  The final
section isolates the first missing source theorem: construction of concrete
padded dyadic cells for the branch masses defined here.  No
`LiteralPaddedSourceCertificate` is assumed.
-/

namespace MAPHBPerronSourceData

open scoped BigOperators ArithmeticFunction
open MeasureTheory
open MAPHeathBrownFiniteIdentity
open MAPMRTCorollary25Instantiation
open MAPMRTCorollary53Source
open MAPFarSourceWeldScaffold
open MAPMRTProposition51Source
open MixedMeanFrontend DeterminantCountWeld
open MAPMRTCorollary25
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTProposition61TypeD1Factorization
open MAPMRTCorollary25TypeD1IntegratedWeld
open MAPMRTCorollary25Minkowski
open MAPFarAnnulusSourceToModel

noncomputable section

/-- The literal real cutoff `(2X)^(1/8)` in the eight-term Heath--Brown
identity used by the source decomposition. -/
def hbCutoff (X : ℝ) : ℝ :=
  Real.rpow (2 * X) ((8 : ℝ)⁻¹)

/-- The signed `j=k+1` summand in the published Heath--Brown identity.  The
sign and binomial coefficient stay inside the coefficient. -/
def hbSignedTerm (X : ℝ) (k n : ℕ) : ℂ :=
  ((((-1 : ArithmeticFunction ℝ) ^ k *
      ((8).choose (k + 1) : ArithmeticFunction ℝ)) *
    (ArithmeticFunction.log *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k *
      realTruncatedMoebius (hbCutoff X) ^ (k + 1))) n : ℂ)

/-- The source support mask `(X,2X]`, applied after the signed convolution
coefficient has been formed. -/
def maskedHBSignedTerm (X : ℝ) (k n : ℕ) : ℂ :=
  if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then hbSignedTerm X k n else 0

/-- Fixed bookkeeping enumeration of eight coefficient slots.  This does not
identify the raw `k`-th Heath--Brown summand with the published Type-`d k`
classification: that classification occurs only after dyadic packetization. -/
def cutoffBranchIndex : CutoffBranch → Fin 8
  | .typeD1 => 0
  | .typeD2 => 1
  | .typeD3 => 2
  | .typeD4 => 3
  | .typeD5 => 4
  | .typeD6 => 5
  | .typeD7 => 6
  | .typeII => 7

/-- Inverse bookkeeping enumeration. -/
def cutoffBranchOfIndex : Fin 8 → CutoffBranch
  | ⟨0, _⟩ => .typeD1
  | ⟨1, _⟩ => .typeD2
  | ⟨2, _⟩ => .typeD3
  | ⟨3, _⟩ => .typeD4
  | ⟨4, _⟩ => .typeD5
  | ⟨5, _⟩ => .typeD6
  | ⟨6, _⟩ => .typeD7
  | ⟨7, _⟩ => .typeII

@[simp] theorem cutoffBranchOfIndex_index (branch : CutoffBranch) :
    cutoffBranchOfIndex (cutoffBranchIndex branch) = branch := by
  cases branch <;> rfl

@[simp] theorem cutoffBranchIndex_ofIndex (k : Fin 8) :
    cutoffBranchIndex (cutoffBranchOfIndex k) = k := by
  fin_cases k <;> rfl

/-- The bookkeeping branch/index equivalence.  A later packetization theorem
must still certify the published Type labels of the emitted dyadic packets. -/
def cutoffBranchEquivFin : CutoffBranch ≃ Fin 8 where
  toFun := cutoffBranchIndex
  invFun := cutoffBranchOfIndex
  left_inv := cutoffBranchOfIndex_index
  right_inv := cutoffBranchIndex_ofIndex

/-- The literal signed, masked coefficient attached to one source branch. -/
def hbBranchCoeff (X : ℝ) (branch : CutoffBranch) (n : ℕ) : ℂ :=
  maskedHBSignedTerm X (cutoffBranchIndex branch) n

private theorem hbCutoff_pow_eight {X : ℝ} (hX : 0 ≤ X) :
    hbCutoff X ^ 8 = 2 * X := by
  unfold hbCutoff
  have hbase : 0 ≤ 2 * X := by positivity
  simpa using (Real.rpow_inv_natCast_pow hbase (by norm_num : (8 : ℕ) ≠ 0))

/-- Exact coefficient identity on the source interval, at the literal
`(2X)^(1/8)` cutoff. -/
theorem sum_hbSignedTerm_eq_vonMangoldt
    {X : ℝ} (hX : 0 ≤ X) {n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊) :
    (∑ k : Fin 8, hbSignedTerm X k n) =
      (ArithmeticFunction.vonMangoldt n : ℂ) := by
  have hnFloor : n ≤ ⌊2 * X⌋₊ := (Finset.mem_Ioc.mp hn).2
  have htwoX : 0 ≤ 2 * X := by positivity
  have hnReal : (n : ℝ) ≤ 2 * X := by
    have : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by exact_mod_cast hnFloor
    exact this.trans (Nat.floor_le htwoX)
  have hcutoffNonneg : 0 ≤ hbCutoff X := Real.rpow_nonneg (by positivity) _
  have hpow : (n : ℝ) ≤ hbCutoff X ^ 8 := by
    rw [hbCutoff_pow_eight hX]
    exact hnReal
  have hid := heathBrownPublishedRealSum_apply
    (Y := hbCutoff X) (K := 8) (n := n) (by norm_num) hcutoffNonneg hpow
  rw [← hid]
  rw [show (∑ k : Fin 8, hbSignedTerm X k n) =
      ∑ k ∈ Finset.range 8, hbSignedTerm X k n by
    exact Fin.sum_univ_eq_sum_range (fun k ↦ hbSignedTerm X k n) 8]
  unfold heathBrownPublishedRealSum hbSignedTerm
  rw [← Complex.ofReal_sum]
  congr 1

/-- The source coefficient is exactly the sum of its eight signed, masked HB
branches. -/
theorem mapMangoldtCoeff_eq_sum_hbBranchCoeff
    {X : ℝ} (hX : 0 ≤ X) (n : ℕ) :
    mapMangoldtCoeff X n =
      ∑ branch : CutoffBranch, hbBranchCoeff X branch n := by
  classical
  by_cases hn : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊
  · rw [mapMangoldtCoeff, if_pos hn]
    have hsum := sum_hbSignedTerm_eq_vonMangoldt hX hn
    rw [← hsum]
    exact (Fintype.sum_equiv cutoffBranchEquivFin
      (fun branch ↦ hbBranchCoeff X branch n)
      (fun k ↦ hbSignedTerm X k n)
      (fun branch ↦ by
        simp [hbBranchCoeff, maskedHBSignedTerm, hn,
          cutoffBranchEquivFin])).symm
  · simp [mapMangoldtCoeff, hbBranchCoeff, maskedHBSignedTerm, hn]

/-- Linearity of the literal source Dirichlet polynomial over a finite
coefficient family. -/
theorem criticalDirichletPolynomial_finset_sum
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (X : ℝ) (q₀ q₁ : ℕ)
    (f : ι → ℕ → ℂ) (chi : DirichletCharacter ℂ q₁) (t : ℝ) :
    criticalDirichletPolynomial X q₀ q₁
        (fun n ↦ ∑ i ∈ S, f i n) chi t =
      ∑ i ∈ S, criticalDirichletPolynomial X q₀ q₁ (f i) chi t := by
  classical
  unfold criticalDirichletPolynomial
  calc
    (∑ n ∈ Finset.Icc 1 ⌊2 * X⌋₊,
        (∑ i ∈ S, f i (q₀ * n)) * chi n *
          (Real.sqrt n : ℂ)⁻¹ * MixedMeanFrontend.mellinPhase n t) =
        ∑ n ∈ Finset.Icc 1 ⌊2 * X⌋₊, ∑ i ∈ S,
          f i (q₀ * n) * chi n * (Real.sqrt n : ℂ)⁻¹ *
            MixedMeanFrontend.mellinPhase n t := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    _ = ∑ i ∈ S, ∑ n ∈ Finset.Icc 1 ⌊2 * X⌋₊,
          f i (q₀ * n) * chi n * (Real.sqrt n : ℂ)⁻¹ *
            MixedMeanFrontend.mellinPhase n t := by
      rw [Finset.sum_comm]
    _ = _ := rfl

/-- The `q₀=1` source polynomial is exactly the sum of the eight signed HB
branch polynomials. -/
theorem criticalDirichletPolynomial_map_eq_sum_hb
    {X : ℝ} (hX : 0 ≤ X) (q₁ : ℕ)
    (chi : DirichletCharacter ℂ q₁) (t : ℝ) :
    criticalDirichletPolynomial X 1 q₁ (mapMangoldtCoeff X) chi t =
      ∑ branch : CutoffBranch,
        criticalDirichletPolynomial X 1 q₁ (hbBranchCoeff X branch) chi t := by
  rw [show mapMangoldtCoeff X = fun n ↦
      ∑ branch : CutoffBranch, hbBranchCoeff X branch n by
    funext n
    exact mapMangoldtCoeff_eq_sum_hbBranchCoeff hX n]
  simpa using criticalDirichletPolynomial_finset_sum
    (Finset.univ : Finset CutoffBranch) X 1 q₁
    (fun branch ↦ hbBranchCoeff X branch) chi t

/-! ## Finite-source Cauchy constructors -/

/-- A source character window of a finite coefficient sum is bounded by the
sum of the individual windows. Both the character sum and moving interval
remain literal. -/
theorem characterWindow_finset_sum_le
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    {X H beta t : ℝ} {q₀ q₁ : ℕ} (f : ι → ℕ → ℂ)
    (hH : 0 ≤ H) :
    characterWindow X q₀ q₁ (fun n ↦ ∑ i ∈ S, f i n) beta H t ≤
      ∑ i ∈ S, characterWindow X q₀ q₁ (f i) beta H t := by
  classical
  have horder : t - |beta| * H ≤ t + |beta| * H := by
    have : 0 ≤ |beta| * H := mul_nonneg (abs_nonneg _) hH
    linarith
  unfold characterWindow
  calc
    (∑ chi : DirichletCharacter ℂ q₁,
        ∫ t' in (t - |beta| * H)..(t + |beta| * H),
          ‖criticalDirichletPolynomial X q₀ q₁
            (fun n ↦ ∑ i ∈ S, f i n) chi t'‖) ≤
        ∑ chi : DirichletCharacter ℂ q₁,
          ∫ t' in (t - |beta| * H)..(t + |beta| * H),
            ∑ i ∈ S,
              ‖criticalDirichletPolynomial X q₀ q₁ (f i) chi t'‖ := by
      apply Finset.sum_le_sum
      intro chi hchi
      apply intervalIntegral.integral_mono_on horder
      · exact (continuous_norm_criticalDirichletPolynomial X q₀ q₁
          (fun n ↦ ∑ i ∈ S, f i n) chi).intervalIntegrable _ _
      · exact (continuous_finsetSum S fun i hi ↦
          continuous_norm_criticalDirichletPolynomial X q₀ q₁
            (f i) chi).intervalIntegrable _ _
      · intro t' ht'
        rw [criticalDirichletPolynomial_finset_sum S X q₀ q₁ f chi t']
        exact norm_sum_le S _
    _ = ∑ chi : DirichletCharacter ℂ q₁, ∑ i ∈ S,
          ∫ t' in (t - |beta| * H)..(t + |beta| * H),
            ‖criticalDirichletPolynomial X q₀ q₁ (f i) chi t'‖ := by
      apply Finset.sum_congr rfl
      intro chi hchi
      rw [intervalIntegral.integral_finsetSum]
      intro i hi
      exact (continuous_norm_criticalDirichletPolynomial X q₀ q₁
        (f i) chi).intervalIntegrable _ _
    _ = ∑ i ∈ S, ∑ chi : DirichletCharacter ℂ q₁,
          ∫ t' in (t - |beta| * H)..(t + |beta| * H),
            ‖criticalDirichletPolynomial X q₀ q₁ (f i) chi t'‖ := by
      rw [Finset.sum_comm]
    _ = _ := rfl

/-- Squaring the preceding finite branch sum costs exactly the branch count.
This is the only Cauchy loss in the exact HB source constructor. -/
theorem characterWindow_finset_sum_sq_le
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    {X H beta t : ℝ} {q₀ q₁ : ℕ} (f : ι → ℕ → ℂ)
    (hH : 0 ≤ H) :
    characterWindow X q₀ q₁ (fun n ↦ ∑ i ∈ S, f i n) beta H t ^ 2 ≤
      (S.card : ℝ) *
        ∑ i ∈ S, characterWindow X q₀ q₁ (f i) beta H t ^ 2 := by
  let W := characterWindow X q₀ q₁
    (fun n ↦ ∑ i ∈ S, f i n) beta H t
  let B : ι → ℝ := fun i ↦ characterWindow X q₀ q₁ (f i) beta H t
  have hW0 : 0 ≤ W := characterWindow_nonneg
    (mul_nonneg (abs_nonneg _) hH)
  have hwindow : W ≤ ∑ i ∈ S, B i :=
    characterWindow_finset_sum_le S f hH
  have hpow : W ^ 2 ≤ (∑ i ∈ S, B i) ^ 2 :=
    pow_le_pow_left₀ hW0 hwindow 2
  have hcauchy : (∑ i ∈ S, B i) ^ 2 ≤
      (S.card : ℝ) * ∑ i ∈ S, B i ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  exact hpow.trans hcauchy

/-- Componentwise form of the finite-source Cauchy constructor, with the
negative and positive outer intervals kept separate. -/
theorem componentIntegral_finset_sum_le
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    {X H beta eta : ℝ} {q₀ q₁ : ℕ} (f : ι → ℕ → ℂ)
    (hX : 0 ≤ X) (hH : 0 ≤ H) (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (component : OuterComponent) :
    componentIntegral X H q₀ q₁ (fun n ↦ ∑ i ∈ S, f i n)
        beta eta component ≤
      (S.card : ℝ) * ∑ i ∈ S,
        componentIntegral X H q₀ q₁ (f i) beta eta component := by
  let e := componentEndpoints X beta eta component
  have he : e.1 ≤ e.2 := componentEndpoints_mono hX heta hetaOne component
  have hleft : Continuous (fun t : ℝ ↦
      characterWindow X q₀ q₁ (fun n ↦ ∑ i ∈ S, f i n) beta H t ^ 2) :=
    (continuous_characterWindow X H q₀ q₁
      (fun n ↦ ∑ i ∈ S, f i n) beta).pow 2
  have hright : Continuous (fun t : ℝ ↦
      (S.card : ℝ) *
        ∑ i ∈ S, characterWindow X q₀ q₁ (f i) beta H t ^ 2) := by
    apply continuous_const.mul
    exact continuous_finsetSum S fun i hi ↦
      (continuous_characterWindow X H q₀ q₁ (f i) beta).pow 2
  unfold componentIntegral
  dsimp only
  calc
    (∫ t in e.1..e.2,
        characterWindow X q₀ q₁ (fun n ↦ ∑ i ∈ S, f i n)
          beta H t ^ 2) ≤
        ∫ t in e.1..e.2, (S.card : ℝ) *
          ∑ i ∈ S, characterWindow X q₀ q₁ (f i) beta H t ^ 2 := by
      apply intervalIntegral.integral_mono_on he
      · exact hleft.intervalIntegrable _ _
      · exact hright.intervalIntegrable _ _
      · intro t ht
        exact characterWindow_finset_sum_sq_le S f hH
    _ = (S.card : ℝ) * ∫ t in e.1..e.2,
          ∑ i ∈ S, characterWindow X q₀ q₁ (f i) beta H t ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
    _ = (S.card : ℝ) * ∑ i ∈ S,
          ∫ t in e.1..e.2,
            characterWindow X q₀ q₁ (f i) beta H t ^ 2 := by
      congr 1
      rw [intervalIntegral.integral_finsetSum]
      intro i hi
      exact (continuous_characterWindow X H q₀ q₁ (f i) beta).pow 2
        |>.intervalIntegrable _ _
    _ = _ := rfl

/-- Exact `q₀=1` component bound for the masked eight-term HB expansion. -/
theorem componentIntegral_map_le_hbBranches
    {X H beta eta : ℝ} (hX : 0 ≤ X) (hH : 0 ≤ H)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (q₁ : ℕ)
    (component : OuterComponent) :
    componentIntegral X H 1 q₁ (mapMangoldtCoeff X) beta eta component ≤
      8 * ∑ branch : CutoffBranch,
        componentIntegral X H 1 q₁ (hbBranchCoeff X branch)
          beta eta component := by
  rw [show mapMangoldtCoeff X = fun n ↦
      ∑ branch : CutoffBranch, hbBranchCoeff X branch n by
    funext n
    exact mapMangoldtCoeff_eq_sum_hbBranchCoeff hX n]
  have hcard : Fintype.card CutoffBranch = 8 := by decide
  simpa [hcard] using componentIntegral_finset_sum_le
    (Finset.univ : Finset CutoffBranch)
    (fun branch ↦ hbBranchCoeff X branch)
    hX hH heta hetaOne component

/-- Literal `q₀>1` small-remainder mass.  Only positive first factors are
included, and every exact source component stays visible. -/
def smallRemainderMass
    (p : Corollary53Input) (component : OuterComponent) : ℝ :=
  ∑ z ∈ (modulusFactorizations p.q).filter (fun z ↦ 1 < z.1),
    componentIntegral p.X p.H z.1 z.2 p.f p.beta p.eta component

/-- The branch masses emitted by the exact HB split before Perron cutoff
removal and dyadic packetization. -/
def hbSourceMass
    (p : Corollary53Input) (component : OuterComponent) : FarSourceBranch → ℝ
  | .cutoff branch =>
      8 * componentIntegral p.X p.H 1 p.q
        (hbBranchCoeff p.X branch) p.beta p.eta component
  | .smallRemainder => smallRemainderMass p component
  | .badEulerFactor => 0

/-- No decomposition error is charged by the exact HB identity. -/
def hbDecompositionError (_p : Corollary53Input) (_component : OuterComponent) : ℝ := 0

/-- Positivity of one literal signed outer component; the orientation is
certified from `0<eta≤1`. -/
theorem componentIntegral_nonneg_of_admissibleGeometry
    {X H beta eta : ℝ} {q₀ q₁ : ℕ} {f : ℕ → ℂ}
    (hX : 0 ≤ X) (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (component : OuterComponent) :
    0 ≤ componentIntegral X H q₀ q₁ f beta eta component := by
  unfold componentIntegral
  apply intervalIntegral.integral_nonneg
    (componentEndpoints_mono hX heta hetaOne component)
  intro t ht
  exact sq_nonneg _

theorem smallRemainderMass_nonneg
    {p : Corollary53Input} (hX : 0 ≤ p.X)
    (heta : 0 < p.eta) (hetaOne : p.eta ≤ 1)
    (component : OuterComponent) :
    0 ≤ smallRemainderMass p component := by
  unfold smallRemainderMass
  exact Finset.sum_nonneg fun z hz ↦
    componentIntegral_nonneg_of_admissibleGeometry hX heta hetaOne component

theorem hbSourceMass_nonneg
    {p : Corollary53Input} (hX : 0 ≤ p.X)
    (heta : 0 < p.eta) (hetaOne : p.eta ≤ 1)
    (component : OuterComponent) (branch : FarSourceBranch) :
    0 ≤ hbSourceMass p component branch := by
  cases branch with
  | cutoff branch =>
      unfold hbSourceMass
      exact mul_nonneg (by norm_num)
        (componentIntegral_nonneg_of_admissibleGeometry
          hX heta hetaOne component)
  | smallRemainder =>
      exact smallRemainderMass_nonneg hX heta hetaOne component
  | badEulerFactor =>
      simp [hbSourceMass]

/-- The exact eight-term HB source family constructs the formerly abstract
`SourceBranchDecomposition`. For `q₀=1` it uses the signed HB identity and one
eight-term Cauchy loss. For `q₀>1` it retains the literal prime-power small
remainder component. No mass is assigned to a bad Euler factor in the
Mangoldt specialization. -/
theorem sourceBranchDecomposition_hb
    {p : Corollary53Input}
    (hp : Corollary53Admissible 1 1 p)
    (hf : p.f = mapMangoldtCoeff p.X) :
    SourceBranchDecomposition p (hbDecompositionError p) (hbSourceMass p) := by
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.1
  have hX : 0 ≤ p.X := hH.trans hp.2.1
  have heta : 0 < p.eta := hp.2.2.2.2.1
  have hetaOne : p.eta ≤ 1 := hp.2.2.2.2.2.1
  intro q₀ q₁ hfac hq₀ hq₁ component
  by_cases hq₀one : q₀ = 1
  · subst q₀
    have hq₁eq : q₁ = p.q := by simpa using hfac
    subst q₁
    rw [hf]
    have hmain := componentIntegral_map_le_hbBranches
      (beta := p.beta) hX hH heta hetaOne p.q component
    calc
      componentIntegral p.X p.H 1 p.q (mapMangoldtCoeff p.X)
          p.beta p.eta component ≤
          8 * ∑ branch : CutoffBranch,
            componentIntegral p.X p.H 1 p.q
              (hbBranchCoeff p.X branch) p.beta p.eta component := hmain
      _ = ∑ branch : CutoffBranch,
          hbSourceMass p component (.cutoff branch) := by
        simp only [hbSourceMass, Finset.mul_sum]
      _ ≤ ∑ branch : FarSourceBranch, hbSourceMass p component branch := by
        rw [sum_farSourceBranch_eq]
        have hsmall := smallRemainderMass_nonneg hX heta hetaOne component
        simp only [hbSourceMass]
        linarith
      _ = hbDecompositionError p component +
          ∑ branch : FarSourceBranch, hbSourceMass p component branch := by
        simp [hbDecompositionError]

  · have hq₀gt : 1 < q₀ := lt_of_le_of_ne hq₀ (Ne.symm hq₀one)
    have hq₀le : q₀ ≤ p.q := by nlinarith
    have hq₁le : q₁ ≤ p.q := by nlinarith
    have hz : (q₀, q₁) ∈
        (modulusFactorizations p.q).filter (fun z ↦ 1 < z.1) := by
      simp [modulusFactorizations, hq₀, hq₁, hq₀le, hq₁le, hfac, hq₀gt]
    have hterm : componentIntegral p.X p.H q₀ q₁ p.f
        p.beta p.eta component ≤ smallRemainderMass p component := by
      unfold smallRemainderMass
      have hsingle := Finset.single_le_sum
        (s := (modulusFactorizations p.q).filter (fun z ↦ 1 < z.1))
        (f := fun z ↦ componentIntegral p.X p.H z.1 z.2 p.f
          p.beta p.eta component)
        (fun z hz' ↦ componentIntegral_nonneg_of_admissibleGeometry
          hX heta hetaOne component) hz
      simpa using hsingle
    calc
      componentIntegral p.X p.H q₀ q₁ p.f p.beta p.eta component ≤
          smallRemainderMass p component := hterm
      _ ≤ ∑ branch : FarSourceBranch, hbSourceMass p component branch := by
        rw [sum_farSourceBranch_eq]
        have hcut : 0 ≤ ∑ branch : CutoffBranch,
            hbSourceMass p component (.cutoff branch) :=
          Finset.sum_nonneg fun branch hbranch ↦
            hbSourceMass_nonneg hX heta hetaOne component _
        have hcut' : 0 ≤ ∑ branch : CutoffBranch,
            8 * componentIntegral p.X p.H 1 p.q
              (hbBranchCoeff p.X branch) p.beta p.eta component := by
          simpa only [hbSourceMass] using hcut
        simp only [hbSourceMass]
        linarith
      _ = hbDecompositionError p component +
          ∑ branch : FarSourceBranch, hbSourceMass p component branch := by
        simp [hbDecompositionError]

/-! ## Exact base-aperture outer-cutoff insertion -/

/-- The HB/Perron source constructor consumes the actual MAP aperture with no
lower-collar charge. Thus every cell error constructed below is a genuine
Corollary 2.5 truncation remainder; none of the source mass is hidden in an
`X/2` three-cell collar budget. -/
theorem hbPerron_outerCutoff_exact_at_baseAperture
    {epsilon X beta t : ℝ} {cutoff outer : ℝ → ℝ} {g : ℝ → ℂ}
    (hX : 4 ≤ X)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1)
    (hNoOuter : Integrable (fun x : ℝ ↦ g x *
      MAPMRTProposition51HardBranch.sourceStationaryPacket
        X (MAPAllCenterApertureTransfer.baseAperture epsilon X) x beta t cutoff (fun _ ↦ 1)))
    (hOuter : Integrable (fun x : ℝ ↦ g x *
      MAPMRTProposition51HardBranch.sourceStationaryPacket
        X (MAPAllCenterApertureTransfer.baseAperture epsilon X) x beta t cutoff outer)) :
    (∫ x : ℝ, g x *
      MAPMRTProposition51HardBranch.sourceStationaryPacket
        X (MAPAllCenterApertureTransfer.baseAperture epsilon X) x beta t cutoff (fun _ ↦ 1)) =
      ∫ x : ℝ, g x *
        MAPMRTProposition51HardBranch.sourceStationaryPacket
          X (MAPAllCenterApertureTransfer.baseAperture epsilon X) x beta t cutoff outer :=
  MAPMRTSourceBaseApertureOuterCutoffWeld.integral_mul_packet_withoutOuter_eq_outer_baseAperture
      hX hgSupport hcutoffSupport houterOne hNoOuter hOuter

/-! ## Certified Perron-to-padded-cell adapter

The lemmas in this section close the analytic part of one dyadic packet.
Natural dyadic support is converted to the real support convention of
Corollary 2.5, the actual character family is zero-padded into `Fin q`, and
the certified Perron multiplier is absorbed into the long coefficient.  Only
the displayed cutoff remainder enters `cellError`.
-/

def SupportedNatDyadic (M : ℕ) (f : ℕ → ℂ) : Prop :=
  ∀ n, n ∉ dyadic M → f n = 0

theorem supportedDyadic_coe_of_supportedNatDyadic
    {M : ℕ} {f : ℕ → ℂ} (hf : SupportedNatDyadic M f) :
    SupportedDyadic (M : ℝ) f := by
  intro n hn
  apply hf n
  simp only [dyadic, Finset.mem_Ioc]
  intro h
  apply hn
  exact ⟨by exact_mod_cast h.1.le, by exact_mod_cast h.2⟩

theorem halfLineDirichletPolynomial_eq_longFactor
    {M : ℕ} (hM : 1 ≤ M) {phase f : ℕ → ℂ}
    (hf : SupportedNatDyadic M f) (t : ℝ) :
    halfLineDirichletPolynomial (M : ℝ) 2 (characterTwist phase f) t =
      longFactor M
        (MixedMeanMajorantWeld.invSqrtCoeff (characterTwist phase f)) t := by
  unfold halfLineDirichletPolynomial longFactor dirichletPoly
  have hceil : Nat.ceil (2 * (M : ℝ)) = 2 * M := by
    rw [show 2 * (M : ℝ) = ((2 * M : ℕ) : ℝ) by norm_num]
    exact Nat.ceil_natCast _
  rw [hceil]
  let S := Finset.Icc 1 (2 * M)
  let D := dyadic M
  have hDS : D ⊆ S := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, hn'.2⟩
  rw [← Finset.sum_subset hDS]
  · apply Finset.sum_congr rfl
    intro n hn
    unfold MixedMeanMajorantWeld.invSqrtCoeff characterTwist
    rw [show (Real.sqrt n : ℂ) = (Real.sqrt (n : ℝ) : ℂ) by norm_num]
  · intro n hnS hnD
    unfold characterTwist
    rw [hf n hnD]
    simp

theorem paddedCharacterTwist_eq_zero_of_not_mem
    {q₁ q : ℕ} [NeZero q₁] (hq₁q : q₁ ≤ q)
    (f : ℕ → ℂ) (j : Fin q)
    (hj : j ∉ Finset.univ.map (actualCharacterEmbedding q₁ q hq₁q)) :
    paddedCharacterTwist q₁ q hq₁q f j = 0 := by
  funext n
  unfold paddedCharacterTwist zeroPadFamily
  exact zeroPad_eq_zero_of_not_mem
    (actualCharacterEmbedding q₁ q hq₁q)
    (fun chi ↦ chi n * f n) j hj

theorem typeD1FullNorm_eq_natFactors
    {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    {alpha beta : ℕ → ℂ}
    (halpha : SupportedNatDyadic N alpha)
    (hbeta : SupportedNatDyadic M beta)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    typeD1FullNorm (N : ℝ) (M : ℝ)
        (fun chi n ↦ chi n) alpha beta chi t =
      ‖longFactor N
          (MixedMeanMajorantWeld.invSqrtCoeff
            (characterTwist (fun n ↦ chi n) alpha)) t‖ *
        ‖shortFactor M
          (MixedMeanMajorantWeld.invSqrtCoeff
            (characterTwist (fun n ↦ chi n) beta)) t‖ := by
  unfold typeD1FullNorm
  rw [norm_halfLineDirichletPolynomial_convolution_eq_mul
    (by exact_mod_cast hN) (by exact_mod_cast hM)
    (fun m n ↦ by simp)
    (supportedDyadic_coe_of_supportedNatDyadic halpha)
    (supportedDyadic_coe_of_supportedNatDyadic hbeta)]
  have hlong := congrArg norm
    (halfLineDirichletPolynomial_eq_longFactor
      (phase := fun n ↦ chi n) hN halpha t)
  have hshort := congrArg norm
    (halfLineDirichletPolynomial_eq_longFactor
      (phase := fun n ↦ chi n) hM hbeta t)
  rw [hlong, hshort]
  rfl

theorem integral_characterMovingMass_typeD1FullNorm_eq_literalFactoredCell
    {q N M : ℕ} [NeZero q] (hN : 1 ≤ N) (hM : 1 ≤ M)
    {alpha beta : ℕ → ℂ}
    (halpha : SupportedNatDyadic N alpha)
    (hbeta : SupportedNatDyadic M beta)
    (a b U : ℝ) :
    (∫ t in a..b,
      (characterMovingMass
        (typeD1FullNorm (N : ℝ) (M : ℝ)
          (fun chi : DirichletCharacter ℂ q ↦ fun n ↦ chi n)
          alpha beta) U t) ^ 2) =
      literalFactoredTypeDCell q M N
        (paddedCharacterTwist q q le_rfl beta)
        (paddedCharacterTwist q q le_rfl alpha) a b U := by
  unfold literalFactoredTypeDCell characterMovingMass
  apply intervalIntegral.integral_congr
  intro t ht
  change
    (∑ chi : DirichletCharacter ℂ q,
      movingIntegral
        (typeD1FullNorm (N : ℝ) (M : ℝ)
          (fun chi : DirichletCharacter ℂ q ↦ fun n ↦ chi n)
          alpha beta chi) U t) ^ 2 =
      (∑ j : Fin q,
        ∫ s in (t - U)..(t + U),
          ‖longFactor N
            (MixedMeanMajorantWeld.invSqrtCoeff
              (paddedCharacterTwist q q le_rfl alpha j)) s‖ *
          ‖shortFactor M
            (MixedMeanMajorantWeld.invSqrtCoeff
              (paddedCharacterTwist q q le_rfl beta j)) s‖) ^ 2
  let e := actualCharacterEmbedding q q (le_refl q)
  let I : DirichletCharacter ℂ q → ℝ := fun chi ↦
    ∫ s in (t - U)..(t + U),
      ‖longFactor N
        (MixedMeanMajorantWeld.invSqrtCoeff
          (characterTwist (fun n ↦ chi n) alpha)) s‖ *
      ‖shortFactor M
        (MixedMeanMajorantWeld.invSqrtCoeff
          (characterTwist (fun n ↦ chi n) beta)) s‖
  let J : Fin q → ℝ := fun j ↦
    ∫ s in (t - U)..(t + U),
      ‖longFactor N
        (MixedMeanMajorantWeld.invSqrtCoeff
          (paddedCharacterTwist q q le_rfl alpha j)) s‖ *
      ‖shortFactor M
        (MixedMeanMajorantWeld.invSqrtCoeff
          (paddedCharacterTwist q q le_rfl beta j)) s‖
  have hleft : (∑ chi : DirichletCharacter ℂ q,
      movingIntegral
        (typeD1FullNorm (N : ℝ) (M : ℝ)
          (fun chi : DirichletCharacter ℂ q ↦ fun n ↦ chi n)
          alpha beta chi) U t) = ∑ chi, I chi := by
    apply Finset.sum_congr rfl
    intro chi hchi
    unfold movingIntegral I
    apply intervalIntegral.integral_congr
    intro s hs
    exact typeD1FullNorm_eq_natFactors hN hM halpha hbeta chi s
  rw [hleft]
  congr 1
  change (∑ chi, I chi) = ∑ j, J j
  rw [← Finset.sum_subset
    (s₁ := Finset.univ.map e) (s₂ := Finset.univ)
    (by intro j hj; simp)]
  · rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro chi hchi
    change I chi = J (e chi)
    unfold I J e
    have ha :
        paddedCharacterTwist q q (le_refl q) alpha
            (actualCharacterEmbedding q q (le_refl q) chi) =
          characterTwist (fun n ↦ chi n) alpha := by
      funext n
      exact paddedCharacterTwist_on_actual q q (le_refl q) alpha chi n
    have hb :
        paddedCharacterTwist q q (le_refl q) beta
            (actualCharacterEmbedding q q (le_refl q) chi) =
          characterTwist (fun n ↦ chi n) beta := by
      funext n
      exact paddedCharacterTwist_on_actual q q (le_refl q) beta chi n
    rw [ha, hb]
  · intro j hj hjnot
    change J j = 0
    have ha0 := paddedCharacterTwist_eq_zero_of_not_mem
      (q₁ := q) (q := q) (le_refl q) alpha j hjnot
    have hb0 := paddedCharacterTwist_eq_zero_of_not_mem
      (q₁ := q) (q := q) (le_refl q) beta j hjnot
    unfold J
    rw [ha0, hb0]
    simp [MixedMeanMajorantWeld.invSqrtCoeff, longFactor, shortFactor,
      dirichletPoly]

def scaleCoeffFamily {q : ℕ} (c : ℝ) (g : Fin q → ℕ → ℂ) :
    Fin q → ℕ → ℂ :=
  fun chi n ↦ (c : ℂ) * g chi n

theorem longFactor_invSqrt_scaleCoeffFamily
    {q N : ℕ} (c : ℝ) (g : Fin q → ℕ → ℂ)
    (chi : Fin q) (t : ℝ) :
    longFactor N
        (MixedMeanMajorantWeld.invSqrtCoeff
          (scaleCoeffFamily c g chi)) t =
      (c : ℂ) * longFactor N
        (MixedMeanMajorantWeld.invSqrtCoeff (g chi)) t := by
  unfold longFactor dirichletPoly MixedMeanMajorantWeld.invSqrtCoeff
    scaleCoeffFamily
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem literalFactoredTypeDCell_scale_long
    {q M N : ℕ} {c a b U : ℝ} (hc : 0 ≤ c)
    (beta g : Fin q → ℕ → ℂ) :
    literalFactoredTypeDCell q M N beta (scaleCoeffFamily c g) a b U =
      c ^ 2 * literalFactoredTypeDCell q M N beta g a b U := by
  unfold literalFactoredTypeDCell
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have hsum :
      (∑ chi : Fin q,
        ∫ s in (t - U)..(t + U),
          ‖longFactor N
              (MixedMeanMajorantWeld.invSqrtCoeff
                (scaleCoeffFamily c g chi)) s‖ *
            ‖shortFactor M
              (MixedMeanMajorantWeld.invSqrtCoeff (beta chi)) s‖) =
        c * ∑ chi : Fin q,
          ∫ s in (t - U)..(t + U),
            ‖longFactor N
                (MixedMeanMajorantWeld.invSqrtCoeff (g chi)) s‖ *
              ‖shortFactor M
                (MixedMeanMajorantWeld.invSqrtCoeff (beta chi)) s‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chi hchi
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    change
      ‖longFactor N
          (MixedMeanMajorantWeld.invSqrtCoeff
            (scaleCoeffFamily c g chi)) s‖ *
          ‖shortFactor M
            (MixedMeanMajorantWeld.invSqrtCoeff (beta chi)) s‖ =
        c * (‖longFactor N
            (MixedMeanMajorantWeld.invSqrtCoeff (g chi)) s‖ *
          ‖shortFactor M
            (MixedMeanMajorantWeld.invSqrtCoeff (beta chi)) s‖)
    rw [longFactor_invSqrt_scaleCoeffFamily]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    ring
  change
    (∑ chi : Fin q,
      ∫ s in (t - U)..(t + U),
        ‖longFactor N
            (MixedMeanMajorantWeld.invSqrtCoeff
              (scaleCoeffFamily c g chi)) s‖ *
          ‖shortFactor M
            (MixedMeanMajorantWeld.invSqrtCoeff (beta chi)) s‖) ^ 2 =
      c ^ 2 * (∑ chi : Fin q,
        ∫ s in (t - U)..(t + U),
          ‖longFactor N
              (MixedMeanMajorantWeld.invSqrtCoeff (g chi)) s‖ *
            ‖shortFactor M
              (MixedMeanMajorantWeld.invSqrtCoeff (beta chi)) s‖) ^ 2
  rw [hsum]
  ring

def perronCellScale (K T : ℝ) : ℝ :=
  Real.sqrt 2 * K * (∫ u in (-T)..T, perronWeight u)

def perronCellError
    (q : ℕ) (N M T B U a b K : ℝ) : ℝ :=
  2 * K ^ 2 * (b - a) *
    (2 * U * q *
      (B * Real.sqrt (N * M) * Real.log (2 + T) / T)) ^ 2

theorem literalTypeD1_component95_to_paddedCell
    {q N M : ℕ} [NeZero q]
    {T X1 X2 B U a b : ℝ}
    {alpha beta : ℕ → ℂ}
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hT : 1 ≤ T) (hB : 0 ≤ B) (hU : 0 ≤ U) (hab : a ≤ b)
    (halpha : SupportedNatDyadic N alpha)
    (hbeta : SupportedNatDyadic M beta)
    (hcoeff : ∀ n, ‖literalDirichletConvolution alpha beta n‖ ≤ B) :
    ∃ K : ℝ, 0 < K ∧
      (∫ t in a..b,
        (characterMovingMass
          (typeD1ClippedNorm (N : ℝ) (M : ℝ) X1 X2
            (fun chi : DirichletCharacter ℂ q ↦ fun n ↦ chi n)
            alpha beta) U t) ^ 2) ≤
        perronCellError q N M T B U a b K +
          literalFactoredTypeDCell q M N
            (paddedCharacterTwist q q le_rfl beta)
            (scaleCoeffFamily (perronCellScale K T)
              (paddedCharacterTwist q q le_rfl alpha))
            (a - T) (b + T) U := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNM : (1 : ℝ) ≤ (N : ℝ) * (M : ℝ) := by
    exact_mod_cast Nat.mul_le_mul hN hM
  obtain ⟨K, hK, htransfer⟩ :=
    literalTypeD1_component95_cutoff_transfer
      (N := (N : ℝ)) (M := (M : ℝ)) (T := T)
      (X1 := X1) (X2 := X2) (B := B) (U := U) (a := a) (b := b)
      hNr hMr hNM hT hB hU hab
      (supportedDyadic_coe_of_supportedNatDyadic halpha)
      (supportedDyadic_coe_of_supportedNatDyadic hbeta)
      (fun (chi : DirichletCharacter ℂ q) n ↦
        DirichletCharacter.norm_le_one chi n) hcoeff
  refine ⟨K, hK, ?_⟩
  let W : ℝ := ∫ u in (-T)..T, perronWeight u
  let E : ℝ :=
    2 * U * (Fintype.card (DirichletCharacter ℂ q) : ℝ) *
      (B * Real.sqrt ((N : ℝ) * (M : ℝ)) * Real.log (2 + T) / T)
  let Ep : ℝ :=
    2 * U * q *
      (B * Real.sqrt ((N : ℝ) * (M : ℝ)) * Real.log (2 + T) / T)
  have hcard : (Fintype.card (DirichletCharacter ℂ q) : ℝ) ≤ q := by
    exact_mod_cast card_dirichletCharacters_le_modulus q
  have hbase :
      0 ≤ B * Real.sqrt ((N : ℝ) * (M : ℝ)) *
        Real.log (2 + T) / T := by
    have hlog : 0 ≤ Real.log (2 + T) :=
      Real.log_nonneg (by linarith)
    positivity
  have hE : 0 ≤ E := by
    unfold E
    positivity
  have hEp : 0 ≤ Ep := by
    unfold Ep
    positivity
  have hEEp : E ≤ Ep := by
    unfold E Ep
    gcongr
  have hW : 0 ≤ W := by
    unfold W
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun u hu ↦ (perronWeight_pos u).le)
  have hc : 0 ≤ perronCellScale K T := by
    unfold perronCellScale
    have hW' : 0 ≤ ∫ u in (-T)..T, perronWeight u := by simpa [W] using hW
    positivity
  have hfull :=
    integral_characterMovingMass_typeD1FullNorm_eq_literalFactoredCell
      (q := q) (N := N) (M := M)
      hN hM halpha hbeta (a - T) (b + T) U
  have hscale :=
    literalFactoredTypeDCell_scale_long hc
      (paddedCharacterTwist q q le_rfl beta)
      (paddedCharacterTwist q q le_rfl alpha)
      (q := q) (M := M) (N := N) (a := a - T) (b := b + T) (U := U)
  have hsqrt : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num
  have hscaleSq : perronCellScale K T ^ 2 = 2 * K ^ 2 * W ^ 2 := by
    unfold perronCellScale
    change
      (Real.sqrt 2 * K * (∫ u in (-T)..T, perronWeight u)) ^ 2 =
        2 * K ^ 2 * (∫ u in (-T)..T, perronWeight u) ^ 2
    nlinarith
  rw [hfull] at htransfer
  rw [hscale]
  unfold perronCellError
  change _ ≤ 2 * K ^ 2 * (b - a) * Ep ^ 2 +
    perronCellScale K T ^ 2 *
      literalFactoredTypeDCell q M N
        (paddedCharacterTwist q q le_rfl beta)
        (paddedCharacterTwist q q le_rfl alpha) (a - T) (b + T) U
  rw [hscaleSq]
  have herr : E ^ 2 ≤ Ep ^ 2 := by nlinarith
  calc
    _ ≤ 2 * K ^ 2 *
        (W ^ 2 *
          literalFactoredTypeDCell q M N
            (paddedCharacterTwist q q le_rfl beta)
            (paddedCharacterTwist q q le_rfl alpha)
            (a - T) (b + T) U +
          (b - a) * E ^ 2) := by
      simpa [W, E] using htransfer
    _ ≤ 2 * K ^ 2 *
        (W ^ 2 *
          literalFactoredTypeDCell q M N
            (paddedCharacterTwist q q le_rfl beta)
            (paddedCharacterTwist q q le_rfl alpha)
            (a - T) (b + T) U +
          (b - a) * Ep ^ 2) := by
      gcongr
    _ = _ := by ring

/-! ## Concrete projection into `LiteralPaddedSourceData` -/

/-- The remaining dyadic arrays after the signed HB family has been fixed.
The ambient character index is definitionally `Fin p.q`, so no character mass
can disappear during padding. The Perron height stays branchwise data and
determines the translated outer interval exactly. -/
structure HBPerronDyadicCells (p : Corollary53Input) where
  cellError : OuterComponent → CutoffBranch → ℝ
  blockCount : OuterComponent → CutoffBranch → ℕ
  shortLength : OuterComponent → CutoffBranch → ℕ
  longLength : (component : OuterComponent) →
    (branch : CutoffBranch) → Fin (blockCount component branch) → ℕ
  betaCoeff : (component : OuterComponent) → (branch : CutoffBranch) →
    Fin p.q → ℕ → ℂ
  longCoeff : (component : OuterComponent) → (branch : CutoffBranch) →
    Fin (blockCount component branch) → Fin p.q → ℕ → ℂ
  perronHeight : OuterComponent → CutoffBranch → ℝ
  perronHeight_nonneg : ∀ component branch,
    0 ≤ perronHeight component branch

/-- Left endpoint after the exact Corollary 2.5 translation. -/
def translatedLeft (p : Corollary53Input) (cells : HBPerronDyadicCells p)
    (component : OuterComponent) (branch : CutoffBranch) : ℝ :=
  (componentEndpoints p.X p.beta p.eta component).1 -
    cells.perronHeight component branch

/-- Right endpoint after the exact Corollary 2.5 translation. -/
def translatedRight (p : Corollary53Input) (cells : HBPerronDyadicCells p)
    (component : OuterComponent) (branch : CutoffBranch) : ℝ :=
  (componentEndpoints p.X p.beta p.eta component).2 +
    cells.perronHeight component branch

/-- The literal packet width `U=|beta|H`; no rescaling is performed in the
source-data projection. -/
def literalPacketWidth (p : Corollary53Input)
    (_component : OuterComponent) (_branch : CutoffBranch) : ℝ :=
  stationaryWidth p.beta p.H

/-- Concrete projection of signed HB/Perron arrays into the public certificate
record. In particular, `decompositionError`, `sourceMass`, the ambient modulus,
translated endpoints, and packet width are no longer caller-selectable. -/
def toLiteralPaddedSourceData
    (p : Corollary53Input) (cells : HBPerronDyadicCells p) :
    LiteralPaddedSourceData p where
  decompositionError := hbDecompositionError p
  sourceMass := hbSourceMass p
  cellError := cells.cellError
  blockCount := cells.blockCount
  q := fun _component _branch ↦ p.q
  shortLength := cells.shortLength
  longLength := cells.longLength
  beta := cells.betaCoeff
  g := cells.longCoeff
  a := translatedLeft p cells
  b := translatedRight p cells
  U := literalPacketWidth p

/-- The first missing source constructor after the exact HB identity and the
certified Perron/Corollary 2.5 theorem. It must dyadically packetize the actual
signed HB branch masses into the displayed padded cells. This proposition
retains the source mask, branch label, component sign, Perron translation,
ambient modulus, and literal width; it is strictly upstream of the expanded
global budget. -/
def HBPerronDyadicPacketization
    (p : Corollary53Input) (cells : HBPerronDyadicCells p) : Prop :=
  ∀ component,
    SourceToPaddedDyadicCells
      (fun branch ↦ hbSourceMass p component (.cutoff branch))
      (cells.cellError component) (cells.blockCount component)
      (fun _branch ↦ p.q) (cells.shortLength component)
      (cells.longLength component) (cells.betaCoeff component)
      (cells.longCoeff component) (translatedLeft p cells component)
      (translatedRight p cells component) (literalPacketWidth p component)

/-! ## Literal HB dyadic classification and certified packet constructor -/

/-- One exact family of HB dyadic packets.  The final field is the finite
algebraic/dyadic classification theorem: it must be proved from the signed HB
coefficient identity, support masks, and finite Cauchy.  It is deliberately
stated before Perron removal, character padding, or the mixed-mean estimate. -/
structure HBPerronPacketFamily (p : Corollary53Input) where
  blockCount : OuterComponent → CutoffBranch → ℕ
  shortLength : OuterComponent → CutoffBranch → ℕ
  longLength : (component : OuterComponent) →
    (branch : CutoffBranch) → Fin (blockCount component branch) → ℕ
  shortCoeff : OuterComponent → CutoffBranch → ℕ → ℂ
  longCoeff : (component : OuterComponent) →
    (branch : CutoffBranch) → Fin (blockCount component branch) → ℕ → ℂ
  perronHeight : OuterComponent → CutoffBranch → ℝ
  coefficientBound : (component : OuterComponent) →
    (branch : CutoffBranch) → Fin (blockCount component branch) → ℝ
  shortLength_one : ∀ component branch, 1 ≤ shortLength component branch
  longLength_one : ∀ component branch i, 1 ≤ longLength component branch i
  perronHeight_one : ∀ component branch, 1 ≤ perronHeight component branch
  coefficientBound_nonneg : ∀ component branch i,
    0 ≤ coefficientBound component branch i
  shortSupport : ∀ component branch,
    SupportedNatDyadic (shortLength component branch)
      (shortCoeff component branch)
  longSupport : ∀ component branch i,
    SupportedNatDyadic (longLength component branch i)
      (longCoeff component branch i)
  convolutionBound : ∀ component branch i n,
    ‖literalDirichletConvolution
      (longCoeff component branch i) (shortCoeff component branch) n‖ ≤
        coefficientBound component branch i
  sourceBound : ∀ component branch,
    hbSourceMass p component (.cutoff branch) ≤
      ∑ i : Fin (blockCount component branch),
        ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
          (componentEndpoints p.X p.beta p.eta component).2,
          (characterMovingMass
            (typeD1ClippedNorm
              (longLength component branch i : ℝ)
              (shortLength component branch : ℝ) p.X (2 * p.X)
              (fun chi : DirichletCharacter ℂ p.q ↦ fun n ↦ chi n)
              (longCoeff component branch i) (shortCoeff component branch))
            (stationaryWidth p.beta p.H) t) ^ 2

private def certifiedPacketTransfer
    {p : Corollary53Input} [NeZero p.q] (hq : 1 ≤ p.q)
    (hp : Corollary53Admissible 1 1 p)
    (packets : HBPerronPacketFamily p)
    (component : OuterComponent) (branch : CutoffBranch)
    (i : Fin (packets.blockCount component branch)) :
    ∃ K : ℝ, 0 < K ∧
      (∫ t in (componentEndpoints p.X p.beta p.eta component).1..
          (componentEndpoints p.X p.beta p.eta component).2,
        (characterMovingMass
          (typeD1ClippedNorm
            (packets.longLength component branch i : ℝ)
            (packets.shortLength component branch : ℝ) p.X (2 * p.X)
            (fun chi : DirichletCharacter ℂ p.q ↦ fun n ↦ chi n)
            (packets.longCoeff component branch i)
            (packets.shortCoeff component branch))
          (stationaryWidth p.beta p.H) t) ^ 2) ≤
        perronCellError p.q
          (packets.longLength component branch i)
          (packets.shortLength component branch)
          (packets.perronHeight component branch)
          (packets.coefficientBound component branch i)
          (stationaryWidth p.beta p.H)
          (componentEndpoints p.X p.beta p.eta component).1
          (componentEndpoints p.X p.beta p.eta component).2 K +
        literalFactoredTypeDCell p.q
          (packets.shortLength component branch)
          (packets.longLength component branch i)
          (paddedCharacterTwist p.q p.q le_rfl
            (packets.shortCoeff component branch))
          (scaleCoeffFamily
            (perronCellScale K (packets.perronHeight component branch))
            (paddedCharacterTwist p.q p.q le_rfl
              (packets.longCoeff component branch i)))
          ((componentEndpoints p.X p.beta p.eta component).1 -
            packets.perronHeight component branch)
          ((componentEndpoints p.X p.beta p.eta component).2 +
            packets.perronHeight component branch)
          (stationaryWidth p.beta p.H) := by
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.1
  have hX : 0 ≤ p.X := hH.trans hp.2.1
  have heta : 0 < p.eta := hp.2.2.2.2.1
  have hetaOne : p.eta ≤ 1 := hp.2.2.2.2.2.1
  exact literalTypeD1_component95_to_paddedCell
    (packets.longLength_one component branch i)
    (packets.shortLength_one component branch)
    (packets.perronHeight_one component branch)
    (packets.coefficientBound_nonneg component branch i)
    (by unfold stationaryWidth; positivity)
    (componentEndpoints_mono hX heta hetaOne component)
    (packets.longSupport component branch i)
    (packets.shortSupport component branch)
    (packets.convolutionBound component branch i)

/-- The certified Corollary 2.5 constant chosen for one literal packet. -/
def certifiedPacketK
    {p : Corollary53Input} [NeZero p.q] (hq : 1 ≤ p.q)
    (hp : Corollary53Admissible 1 1 p)
    (packets : HBPerronPacketFamily p)
    (component : OuterComponent) (branch : CutoffBranch)
    (i : Fin (packets.blockCount component branch)) : ℝ :=
  Classical.choose (certifiedPacketTransfer hq hp packets component branch i)

theorem certifiedPacketK_pos
    {p : Corollary53Input} [NeZero p.q] (hq : 1 ≤ p.q)
    (hp : Corollary53Admissible 1 1 p)
    (packets : HBPerronPacketFamily p)
    (component : OuterComponent) (branch : CutoffBranch)
    (i : Fin (packets.blockCount component branch)) :
    0 < certifiedPacketK hq hp packets component branch i :=
  (Classical.choose_spec
    (certifiedPacketTransfer hq hp packets component branch i)).1

theorem certifiedPacketK_transfer
    {p : Corollary53Input} [NeZero p.q] (hq : 1 ≤ p.q)
    (hp : Corollary53Admissible 1 1 p)
    (packets : HBPerronPacketFamily p)
    (component : OuterComponent) (branch : CutoffBranch)
    (i : Fin (packets.blockCount component branch)) :
    (∫ t in (componentEndpoints p.X p.beta p.eta component).1..
        (componentEndpoints p.X p.beta p.eta component).2,
      (characterMovingMass
        (typeD1ClippedNorm
          (packets.longLength component branch i : ℝ)
          (packets.shortLength component branch : ℝ) p.X (2 * p.X)
          (fun chi : DirichletCharacter ℂ p.q ↦ fun n ↦ chi n)
          (packets.longCoeff component branch i)
          (packets.shortCoeff component branch))
        (stationaryWidth p.beta p.H) t) ^ 2) ≤
      perronCellError p.q
        (packets.longLength component branch i)
        (packets.shortLength component branch)
        (packets.perronHeight component branch)
        (packets.coefficientBound component branch i)
        (stationaryWidth p.beta p.H)
        (componentEndpoints p.X p.beta p.eta component).1
        (componentEndpoints p.X p.beta p.eta component).2
        (certifiedPacketK hq hp packets component branch i) +
      literalFactoredTypeDCell p.q
        (packets.shortLength component branch)
        (packets.longLength component branch i)
        (paddedCharacterTwist p.q p.q le_rfl
          (packets.shortCoeff component branch))
        (scaleCoeffFamily
          (perronCellScale
            (certifiedPacketK hq hp packets component branch i)
            (packets.perronHeight component branch))
          (paddedCharacterTwist p.q p.q le_rfl
            (packets.longCoeff component branch i)))
        ((componentEndpoints p.X p.beta p.eta component).1 -
          packets.perronHeight component branch)
        ((componentEndpoints p.X p.beta p.eta component).2 +
          packets.perronHeight component branch)
        (stationaryWidth p.beta p.H) :=
  (Classical.choose_spec
    (certifiedPacketTransfer hq hp packets component branch i)).2

/-- Concrete padded arrays emitted from a literal HB packet family. -/
def cellsOfPacketFamily
    {p : Corollary53Input} [NeZero p.q] (hq : 1 ≤ p.q)
    (hp : Corollary53Admissible 1 1 p)
    (packets : HBPerronPacketFamily p) : HBPerronDyadicCells p := by
  exact
    { cellError := fun component branch ↦
        ∑ i : Fin (packets.blockCount component branch),
          perronCellError p.q
            (packets.longLength component branch i)
            (packets.shortLength component branch)
            (packets.perronHeight component branch)
            (packets.coefficientBound component branch i)
            (stationaryWidth p.beta p.H)
            (componentEndpoints p.X p.beta p.eta component).1
            (componentEndpoints p.X p.beta p.eta component).2
            (certifiedPacketK hq hp packets component branch i)
      blockCount := packets.blockCount
      shortLength := packets.shortLength
      longLength := packets.longLength
      betaCoeff := fun component branch ↦
        paddedCharacterTwist p.q p.q le_rfl
          (packets.shortCoeff component branch)
      longCoeff := fun component branch i ↦
        scaleCoeffFamily
          (perronCellScale
            (certifiedPacketK hq hp packets component branch i)
            (packets.perronHeight component branch))
          (paddedCharacterTwist p.q p.q le_rfl
            (packets.longCoeff component branch i))
      perronHeight := packets.perronHeight
      perronHeight_nonneg := fun component branch ↦
        (by norm_num : (0 : ℝ) ≤ 1).trans
          (packets.perronHeight_one component branch) }

/-- Certified Corollary 2.5, dyadic support, exact character padding, and the
translated Perron intervals inhabit the public packetization contract. -/
theorem HBPerronDyadicPacketization_of_packetFamily
    {p : Corollary53Input} [NeZero p.q]
    (hp : Corollary53Admissible 1 1 p)
    (packets : HBPerronPacketFamily p) :
    HBPerronDyadicPacketization p
      (cellsOfPacketFamily hp.2.2.1 hp packets) := by
  let hq : 1 ≤ p.q := hp.2.2.1
  intro component branch
  calc
    hbSourceMass p component (.cutoff branch) ≤
        ∑ i : Fin (packets.blockCount component branch),
          ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
            (componentEndpoints p.X p.beta p.eta component).2,
            (characterMovingMass
              (typeD1ClippedNorm
                (packets.longLength component branch i : ℝ)
                (packets.shortLength component branch : ℝ) p.X (2 * p.X)
                (fun chi : DirichletCharacter ℂ p.q ↦ fun n ↦ chi n)
                (packets.longCoeff component branch i)
                (packets.shortCoeff component branch))
              (stationaryWidth p.beta p.H) t) ^ 2 :=
      packets.sourceBound component branch
    _ ≤ ∑ i : Fin (packets.blockCount component branch),
        (perronCellError p.q
          (packets.longLength component branch i)
          (packets.shortLength component branch)
          (packets.perronHeight component branch)
          (packets.coefficientBound component branch i)
          (stationaryWidth p.beta p.H)
          (componentEndpoints p.X p.beta p.eta component).1
          (componentEndpoints p.X p.beta p.eta component).2
          (certifiedPacketK hq hp packets component branch i) +
        literalFactoredTypeDCell p.q
          (packets.shortLength component branch)
          (packets.longLength component branch i)
          (paddedCharacterTwist p.q p.q le_rfl
            (packets.shortCoeff component branch))
          (scaleCoeffFamily
            (perronCellScale
              (certifiedPacketK hq hp packets component branch i)
              (packets.perronHeight component branch))
            (paddedCharacterTwist p.q p.q le_rfl
              (packets.longCoeff component branch i)))
          ((componentEndpoints p.X p.beta p.eta component).1 -
            packets.perronHeight component branch)
          ((componentEndpoints p.X p.beta p.eta component).2 +
            packets.perronHeight component branch)
          (stationaryWidth p.beta p.H)) := by
      exact Finset.sum_le_sum fun i hi ↦
        certifiedPacketK_transfer hq hp packets component branch i
    _ = (cellsOfPacketFamily hq hp packets).cellError component branch +
        ∑ i : Fin ((cellsOfPacketFamily hq hp packets).blockCount component branch),
          literalFactoredTypeDCell p.q
            ((cellsOfPacketFamily hq hp packets).shortLength component branch)
            ((cellsOfPacketFamily hq hp packets).longLength component branch i)
            ((cellsOfPacketFamily hq hp packets).betaCoeff component branch)
            ((cellsOfPacketFamily hq hp packets).longCoeff component branch i)
            (translatedLeft p (cellsOfPacketFamily hq hp packets)
              component branch)
            (translatedRight p (cellsOfPacketFamily hq hp packets)
              component branch)
            (literalPacketWidth p component branch) := by
      rw [Finset.sum_add_distrib]
      simp only [cellsOfPacketFamily, translatedLeft, translatedRight,
        literalPacketWidth]
      congr 1

theorem translatedLeft_le_translatedRight
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    (cells : HBPerronDyadicCells p) (component : OuterComponent)
    (branch : CutoffBranch) :
    translatedLeft p cells component branch ≤
      translatedRight p cells component branch := by
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.1
  have hX : 0 ≤ p.X := hH.trans hp.2.1
  have heta : 0 < p.eta := hp.2.2.2.2.1
  have hetaOne : p.eta ≤ 1 := hp.2.2.2.2.2.1
  have hend := componentEndpoints_mono (beta := p.beta)
    hX heta hetaOne component
  have hT := cells.perronHeight_nonneg component branch
  unfold translatedLeft translatedRight
  linarith

theorem literalPacketWidth_nonneg
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    (component : OuterComponent) (branch : CutoffBranch) :
    0 ≤ literalPacketWidth p component branch := by
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.1
  unfold literalPacketWidth stationaryWidth
  positivity

/-- Certificate constructor from concrete HB/Perron arrays. The only remaining
premises are their exact dyadic packetization theorem and the fully expanded
budget for those same arrays; certificate existence itself is never assumed. -/
def literalPaddedSourceCertificate_of_hbPerron
    {p : Corollary53Input} {budget : ℝ}
    (hp : Corollary53Admissible 1 1 p)
    (hf : p.f = mapMangoldtCoeff p.X)
    (cells : HBPerronDyadicCells p)
    (hpacket : HBPerronDyadicPacketization p cells)
    (hbudget : expandedPaddedSourceRHS p
      (toLiteralPaddedSourceData p cells) ≤ budget) :
    LiteralPaddedSourceCertificate p budget where
  data := toLiteralPaddedSourceData p cells
  sourceDecomposition := sourceBranchDecomposition_hb hp hf
  paddedCells := hpacket
  intervalOrder := translatedLeft_le_translatedRight hp cells
  widthNonneg := literalPacketWidth_nonneg hp
  expandedBudget := hbudget

/-- Pointwise source-data obligation consumed by the uniform far-budget
quantifiers. Unlike certificate existence, this proposition exposes the
concrete HB/Perron cell arrays, their packetization proof, and their expanded
normalized budget. -/
def HBPerronExpandedBudgetLeaf
    (p : Corollary53Input) (cells : HBPerronDyadicCells p)
    (budget : ℝ) : Prop :=
  expandedPaddedSourceRHS p (toLiteralPaddedSourceData p cells) ≤ budget

/-- The shared BHP/MRT expanded-budget leaf, specialized to the concrete
cells constructed above.  This is intentionally only an alias for the public
expanded expression: no parallel Lemma 2.11 or fourth-moment interface is
introduced here. -/
def HBPerronPacketExpandedBudgetLeaf
    {p : Corollary53Input} [NeZero p.q]
    (hp : Corollary53Admissible 1 1 p)
    (packets : HBPerronPacketFamily p) (budget : ℝ) : Prop :=
  HBPerronExpandedBudgetLeaf p
    (cellsOfPacketFamily hp.2.2.1 hp packets) budget

/-- Complete literal source certificate from the exact HB decomposition,
certified Perron packetization, and the one shared expanded-budget leaf. -/
def literalPaddedSourceCertificate_of_hbPacketFamily
    {p : Corollary53Input} [NeZero p.q] {budget : ℝ}
    (hp : Corollary53Admissible 1 1 p)
    (hf : p.f = mapMangoldtCoeff p.X)
    (packets : HBPerronPacketFamily p)
    (hbudget : HBPerronPacketExpandedBudgetLeaf hp packets budget) :
    LiteralPaddedSourceCertificate p budget :=
  literalPaddedSourceCertificate_of_hbPerron hp hf
    (cellsOfPacketFamily hp.2.2.1 hp packets)
    (HBPerronDyadicPacketization_of_packetFamily hp packets)
    hbudget

def HBPerronExpandedCellBudget
    (p : Corollary53Input) (budget : ℝ) : Prop :=
  ∃ cells : HBPerronDyadicCells p,
    HBPerronDyadicPacketization p cells ∧
      HBPerronExpandedBudgetLeaf p cells budget

theorem nonempty_literalPaddedSourceCertificate_of_hbPerronBudget
    {p : Corollary53Input} {budget : ℝ}
    (hp : Corollary53Admissible 1 1 p)
    (hf : p.f = mapMangoldtCoeff p.X)
    (hsource : HBPerronExpandedCellBudget p budget) :
    Nonempty (LiteralPaddedSourceCertificate p budget) := by
  obtain ⟨cells, hpacket, hbudget⟩ := hsource
  exact ⟨literalPaddedSourceCertificate_of_hbPerron
    hp hf cells hpacket hbudget⟩

end
end MAPHBPerronSourceData

#print axioms MAPHBPerronSourceData.sum_hbSignedTerm_eq_vonMangoldt
#print axioms MAPHBPerronSourceData.mapMangoldtCoeff_eq_sum_hbBranchCoeff
#print axioms MAPHBPerronSourceData.criticalDirichletPolynomial_map_eq_sum_hb
#print axioms MAPHBPerronSourceData.sourceBranchDecomposition_hb
#print axioms MAPHBPerronSourceData.hbPerron_outerCutoff_exact_at_baseAperture
#print axioms MAPHBPerronSourceData.literalTypeD1_component95_to_paddedCell
#print axioms MAPHBPerronSourceData.HBPerronDyadicPacketization_of_packetFamily
#print axioms MAPHBPerronSourceData.literalPaddedSourceCertificate_of_hbPerron
#print axioms MAPHBPerronSourceData.literalPaddedSourceCertificate_of_hbPacketFamily
