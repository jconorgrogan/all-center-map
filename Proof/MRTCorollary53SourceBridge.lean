import MRTCorollary25MAPInstantiation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import AllCenterNearFarTransfer

/-!
# Literal MRT Corollary 5.3 source layer for the MAP far annulus

This file separates three logically different objects.

* `MRTCorollary53` is a source-faithful **proposition naming an imported
  published input**.  This module does not prove or assert it.  Every theorem
  using Corollary 5.3 keeps an explicit `hMRT : MRTCorollary53 ...` premise.
  The proposition retains the actual exponential sum,
  `D[f](1/2+it,χ,q₀)`, both components of region (69), the supremum over
  `q=q₀q₁`, and the ordinary error.
* `SourceBranchDecomposition` is the later Heath--Brown source decomposition
  of each component of the actual Corollary 5.3 integral.  It is deliberately
  not a far-annulus conclusion.
* The remaining theorems prove finite factorization, actual-character padding,
  fixed outer-length geometry, and the weld to the existing
  `SourceToPaddedDyadicCells` contract.

The published theorem is MRT, *Correlations of the von Mangoldt and divisor
functions II*, Corollary 5.3, PDF page 53, with the region `I` from (69).
The MAP paper cites this result as an external input; it does not reproduce
its proof.  A full certification of MRT itself must start from Proposition 5.1
and prove the Lemma 2.9/Cauchy deduction rather than postulating this `Prop`.
-/

namespace MAPMRTCorollary53Source

open scoped BigOperators ArithmeticFunction
open MeasureTheory
open MAPMRTCorollary25Instantiation
open MAPFarAnnulusSourceToModel
open MAPFarAnnulusMRT
open PrimePairEndpoints MAPAllCenterApertureTransfer
open MAPAllCenterNearFarTransfer
open MAPMajorArcWeld

noncomputable section

/-! ## The literal source functions -/

/-- The paper's additive phase `e(x)=exp(2πix)`. -/
def additivePhase (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * x * Complex.I)

/-- `S_f(α)=∑_{X<n≤2X} f(n)e(nα)`. -/
def exponentialSum (X : ℝ) (f : ℕ → ℂ) (alpha : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    f n * fourier (n : ℤ) (alpha : UnitAddCircle)

/-- The source Dirichlet polynomial
`D[f](1/2+it,χ,q₀)=∑ f(q₀n)χ(n)/n^(1/2+it)`.
The finite range is exact for a function supported on `(X,2X]` when `q₀≥1`. -/
def criticalDirichletPolynomial
    (X : ℝ) (q₀ q₁ : ℕ) (f : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q₁) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊2 * X⌋₊,
    f (q₀ * n) * chi n * (Real.sqrt n : ℂ)⁻¹ *
      MixedMeanFrontend.mellinPhase n t

/-- Lower endpoint `η|β|X` of the positive component of MRT region (69). -/
def outerLower (X : ℝ) (beta eta : ℝ) : ℝ :=
  eta * |beta| * X

/-- Upper endpoint `|β|X/η` of the positive component of MRT region (69). -/
def outerUpper (X : ℝ) (beta eta : ℝ) : ℝ :=
  |beta| * X / eta

/-- The two connected components of `I={t:η|β|X≤|t|≤|β|X/η}`. -/
inductive OuterComponent where
  | negative
  | positive
  deriving DecidableEq, Fintype, Repr

/-- Oriented endpoints of one component of MRT region (69). -/
def componentEndpoints (X : ℝ) (beta eta : ℝ) :
    OuterComponent → ℝ × ℝ
  | .negative => (-outerUpper X beta eta, -outerLower X beta eta)
  | .positive => (outerLower X beta eta, outerUpper X beta eta)

/-- The inner character/window sum in the literal `I(q₀,q₁)`. -/
def characterWindow
    (X : ℝ) (q₀ q₁ : ℕ) (f : ℕ → ℂ) (beta H t : ℝ) : ℝ :=
  ∑ chi : DirichletCharacter ℂ q₁,
    ∫ t' in (t - |beta| * H)..(t + |beta| * H),
      ‖criticalDirichletPolynomial X q₀ q₁ f chi t'‖

/-- One connected component of the actual source integral. -/
def componentIntegral
    (X H : ℝ) (q₀ q₁ : ℕ) (f : ℕ → ℂ) (beta eta : ℝ)
    (component : OuterComponent) : ℝ :=
  let endpoints := componentEndpoints X beta eta component
  ∫ t in endpoints.1..endpoints.2,
    characterWindow X q₀ q₁ f beta H t ^ 2

/-- The exact `I(q₀,q₁)` in MAP equation (3.3), written as the sum over the
two components of the source region (69). -/
def sourceI
    (X H : ℝ) (q₀ q₁ : ℕ) (f : ℕ → ℂ) (beta eta : ℝ) : ℝ :=
  ∑ component : OuterComponent,
    componentIntegral X H q₀ q₁ f beta eta component

/-! ## Factorizations and the literal ordinary term -/

/-- All positive ordered factorizations `q=q₀q₁`. -/
def modulusFactorizations (q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 q).product (Finset.Icc 1 q)).filter
    (fun z ↦ z.1 * z.2 = q)

theorem modulusFactorizations_nonempty {q : ℕ} (hq : 1 ≤ q) :
    (modulusFactorizations q).Nonempty := by
  refine ⟨(1, q), ?_⟩
  simp [modulusFactorizations, hq]

/-- The literal finite supremum in Corollary 5.3. -/
def factorizationSup
    (X H : ℝ) (q : ℕ) (f : ℕ → ℂ) (beta eta : ℝ) (hq : 1 ≤ q) : ℝ :=
  (modulusFactorizations q).sup' (modulusFactorizations_nonempty hq)
    (fun z ↦ sourceI X H z.1 z.2 f beta eta)

theorem sourceI_le_factorizationSup
    {X H : ℝ} {q q₀ q₁ : ℕ} {f : ℕ → ℂ} {beta eta : ℝ}
    (hq : 1 ≤ q) (hqfac : q₀ * q₁ = q) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) :
    sourceI X H q₀ q₁ f beta eta ≤
      factorizationSup X H q f beta eta hq := by
  have hmem : (q₀, q₁) ∈ modulusFactorizations q := by
    have hq₀q : q₀ ≤ q := by nlinarith
    have hq₁q : q₁ ≤ q := by nlinarith
    simp [modulusFactorizations, hqfac, hq₀, hq₁, hq₀q, hq₁q]
  unfold factorizationSup
  exact Finset.le_sup'
    (fun z : ℕ × ℕ ↦ sourceI X H z.1 z.2 f beta eta) hmem

/-- The sliding short-interval `L¹` square in the ordinary source term. -/
def ordinarySlidingMass (X H : ℝ) (f : ℕ → ℂ) : ℝ :=
  ∫ x : ℝ,
    (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
      if x ≤ n ∧ (n : ℝ) ≤ x + H then ‖f n‖ else 0) ^ 2

/-- The ordinary error in published Corollary 5.3:
`((η+1/(|β|H))²/H²) ∫_ℝ (∑_{x≤n≤x+H}|f(n)|)² dx`.
There is no factor of `q` in this term. -/
def ordinaryError (X H : ℝ) (f : ℕ → ℂ) (beta eta : ℝ) : ℝ :=
  (eta + 1 / (|beta| * H)) ^ 2 / H ^ 2 * ordinarySlidingMass X H f

/-- The exact source main term, before `U=|β|H` is substituted. -/
def divisorCount (q : ℕ) : ℕ := q.divisors.card

def stationaryMainTerm
    (X H : ℝ) (q : ℕ) (f : ℕ → ℂ) (beta eta : ℝ) (hq : 1 ≤ q) : ℝ :=
  (divisorCount q : ℝ) ^ 4 /
      (|beta| ^ 2 * H ^ 2 * q) *
    factorizationSup X H q f beta eta hq

/-- Data in the first assertion of published MRT Corollary 5.3. -/
structure Corollary53Input where
  X : ℝ
  H : ℝ
  q : ℕ
  a : ℕ
  beta : ℝ
  eta : ℝ
  f : ℕ → ℂ

/-- The paper's hypotheses, with the two Vinogradov relations made explicit
as fixed admissibility constants. -/
def Corollary53Admissible (cBetaEta cEta : ℝ)
    (p : Corollary53Input) : Prop :=
  1 ≤ p.H ∧ p.H ≤ p.X ∧ 1 ≤ p.q ∧ p.a.Coprime p.q ∧
  0 < p.eta ∧ p.eta ≤ 1 ∧
  |p.beta| ≤ cBetaEta * p.eta ∧ p.eta ≤ cEta ∧
  p.beta ≠ 0 ∧
  (∀ n : ℕ,
    ¬(p.X < (n : ℝ) ∧ (n : ℝ) ≤ 2 * p.X) → p.f n = 0)

/-- The left side of Corollary 5.3. -/
def sourceEnergy (p : Corollary53Input) : ℝ :=
  ∫ theta in (p.beta - 1 / p.H)..(p.beta + 1 / p.H),
    ‖exponentialSum p.X p.f (p.a / p.q + theta)‖ ^ 2

/-- Source-faithful imported analytic theorem.  This is a uniform
Vinogradov estimate for the published expression, not the MAP far conclusion.
The constant may depend only on the two fixed constants hidden in
`|β| ≪ η ≪ 1`. -/
def MRTCorollary53 (cBetaEta cEta : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (p : Corollary53Input)
    (hp : Corollary53Admissible cBetaEta cEta p),
    sourceEnergy p ≤ C *
      (stationaryMainTerm p.X p.H p.q p.f p.beta p.eta
          hp.2.2.1 +
        ordinaryError p.X p.H p.f p.beta p.eta)

/-! ## MAP specialization and exact `U` normalization -/

/-- The literal coefficient `Λ 1_(X,2X]`. -/
def mapMangoldtCoeff (X : ℝ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then
    (ArithmeticFunction.vonMangoldt n : ℂ)
  else 0

theorem mapMangoldtCoeff_supported (X : ℝ) (n : ℕ)
    (hX : 0 ≤ X)
    (hn : ¬(X < (n : ℝ) ∧ (n : ℝ) ≤ 2 * X)) :
    mapMangoldtCoeff X n = 0 := by
  rw [mapMangoldtCoeff]
  split_ifs with hmem
  · have hbox := Finset.mem_Ioc.mp hmem
    have hlower : X < (n : ℝ) := (Nat.floor_lt hX).mp hbox.1
    have htwoX : 0 ≤ 2 * X := by positivity
    have hupper : (n : ℝ) ≤ 2 * X := by
      have hnFloor : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by exact_mod_cast hbox.2
      exact hnFloor.trans (Nat.floor_le htwoX)
    exact (hn ⟨hlower, hupper⟩).elim
  · simp

/-- The MAP source polynomial is literally the public prime polynomial on a
real lift of the circle.  No integer-`X` restriction is present. -/
theorem exponentialSum_mapMangoldtCoeff_eq_primeExponentialSum
    (X alpha : ℝ) :
    exponentialSum X (mapMangoldtCoeff X) alpha =
      primeExponentialSum X (alpha : UnitAddCircle) := by
  unfold exponentialSum primeExponentialSum
  apply Finset.sum_congr rfl
  intro n hn
  simp [mapMangoldtCoeff, hn]

/-- The literal MAP specialization `f=Λ 1_(X,2X]` of the published input. -/
def mapCorollary53Input
    (X H : ℝ) (q a : ℕ) (beta eta : ℝ) : Corollary53Input where
  X := X
  H := H
  q := q
  a := a
  beta := beta
  eta := eta
  f := mapMangoldtCoeff X

theorem mapCorollary53Input_admissible
    {cBetaEta cEta beta eta X H : ℝ} {q a : ℕ}
    (hH : 1 ≤ H) (hHX : H ≤ X) (hq : 1 ≤ q) (haq : a.Coprime q)
    (heta : 0 < eta) (hetaUnit : eta ≤ 1)
    (hbetaEta : |beta| ≤ cBetaEta * eta)
    (hetaCap : eta ≤ cEta) (hbeta : beta ≠ 0) :
    Corollary53Admissible cBetaEta cEta
      (mapCorollary53Input X H q a beta eta) := by
  refine ⟨hH, hHX, hq, haq, heta, hetaUnit, hbetaEta, hetaCap, hbeta, ?_⟩
  intro n hn
  exact mapMangoldtCoeff_supported X n
    ((le_trans zero_le_one hH).trans hHX) hn

/-- `U=|β|H`, exactly as in the published source and MAP equation (3.3). -/
def stationaryWidth (beta H : ℝ) : ℝ := |beta| * H

theorem stationary_denominator_eq_U
    (beta H : ℝ) (q : ℕ) :
    |beta| ^ 2 * H ^ 2 * q =
      q * stationaryWidth beta H ^ 2 := by
  simp only [stationaryWidth]
  ring

/-- The source main term is exactly the MAP denominator `qU²`. -/
theorem stationaryMainTerm_eq_U
    (X H : ℝ) (q : ℕ) (f : ℕ → ℂ) (beta eta : ℝ) (hq : 1 ≤ q) :
    stationaryMainTerm X H q f beta eta hq =
      (divisorCount q : ℝ) ^ 4 /
          (q * stationaryWidth beta H ^ 2) *
        factorizationSup X H q f beta eta hq := by
  unfold stationaryMainTerm
  rw [stationary_denominator_eq_U]

theorem ordinaryError_eq_U
    {X H : ℝ} {f : ℕ → ℂ} {beta eta U : ℝ}
    (hU : U = stationaryWidth beta H) :
    ordinaryError X H f beta eta =
      (eta + 1 / U) ^ 2 / H ^ 2 * ordinarySlidingMass X H f := by
  rw [ordinaryError, hU, stationaryWidth]

/-! ## Actual Dirichlet-character embedding and exact zero padding -/

theorem card_dirichletCharacters_le_modulus (q : ℕ) [NeZero q] :
    Fintype.card (DirichletCharacter ℂ q) ≤ q := by
  rw [← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  exact Nat.totient_le q

/-- Canonical (choice-based) injection of all characters modulo `q₁` into
`Fin q`, valid for every source factorization because `q₁≤q`. -/
def actualCharacterEmbedding (q₁ q : ℕ) [NeZero q₁] (hq₁q : q₁ ≤ q) :
    DirichletCharacter ℂ q₁ ↪ Fin q :=
  (Fintype.equivFin (DirichletCharacter ℂ q₁)).toEmbedding.trans
    (Fin.castLEEmb ((card_dirichletCharacters_le_modulus q₁).trans hq₁q))

/-- Complex-valued padding of the actual real character-window mass. -/
def paddedCharacterWindow
    (X H : ℝ) (q₀ q₁ q : ℕ) [NeZero q₁] (hq₁q : q₁ ≤ q)
    (f : ℕ → ℂ) (beta t : ℝ) (j : Fin q) : ℂ :=
  zeroPad (actualCharacterEmbedding q₁ q hq₁q)
    (fun chi ↦ ((∫ t' in (t - |beta| * H)..(t + |beta| * H),
      ‖criticalDirichletPolynomial X q₀ q₁ f chi t'‖ : ℝ) : ℂ)) j

/-- Padding along the actual character embedding preserves the inner sum in
`I(q₀,q₁)` exactly. -/
theorem sum_paddedCharacterWindow_eq_characterWindow
    (X H : ℝ) (q₀ q₁ q : ℕ) [NeZero q₁] (hq₁q : q₁ ≤ q)
    (f : ℕ → ℂ) (beta t : ℝ) :
    (∑ j : Fin q,
      (paddedCharacterWindow X H q₀ q₁ q hq₁q f beta t j).re) =
      characterWindow X q₀ q₁ f beta H t := by
  simpa [paddedCharacterWindow, characterWindow] using
    sum_transform_zeroPad (actualCharacterEmbedding q₁ q hq₁q)
      (fun chi ↦ ((∫ t' in (t - |beta| * H)..(t + |beta| * H),
        ‖criticalDirichletPolynomial X q₀ q₁ f chi t'‖ : ℝ) : ℂ))
      Complex.re (by simp)

/-- Actual characters, multiplied by any source coefficient, padded into the
ambient `Fin q` family consumed downstream. -/
def paddedCharacterTwist
    (q₁ q : ℕ) [NeZero q₁] (hq₁q : q₁ ≤ q)
    (coeff : ℕ → ℂ) : Fin q → ℕ → ℂ :=
  zeroPadFamily (actualCharacterEmbedding q₁ q hq₁q)
    (fun chi n ↦ chi n * coeff n)

theorem paddedCharacterTwist_on_actual
    (q₁ q : ℕ) [NeZero q₁] (hq₁q : q₁ ≤ q)
    (coeff : ℕ → ℂ) (chi : DirichletCharacter ℂ q₁) (n : ℕ) :
    paddedCharacterTwist q₁ q hq₁q coeff
        (actualCharacterEmbedding q₁ q hq₁q chi) n =
      chi n * coeff n := by
  exact zeroPadFamily_apply_embedding
    (actualCharacterEmbedding q₁ q hq₁q)
      (fun chi n ↦ chi n * coeff n) chi n

/-! ## Fixed outer-length constant after the Fubini enlargement -/

def mapOuterLower (Q : ℝ) (lambda X : ℝ) : ℝ :=
  lambda * X / Real.sqrt Q

def mapOuterUpper (Q : ℝ) (lambda X : ℝ) : ℝ :=
  Real.sqrt Q * lambda * X

/-- The exact interval length consumed by the downstream mixed mean after the
source component is enlarged by `2U`. -/
def mapPaddedOuterLength (Q lambda X H : ℝ) : ℝ :=
  (mapOuterUpper Q lambda X - mapOuterLower Q lambda X) +
    2 * (lambda * H)

/-- A fixed honest constant for the enlarged outer interval.  The paper writes
`T ≪ Q^(1/2)|λ|X`; the compiled constant here is `3`. -/
theorem mapPaddedOuterLength_le_three
    {Q lambda X H : ℝ} (hQ : 1 ≤ Q) (hlambda : 0 ≤ lambda)
    (hX : 0 ≤ X) (hHX : H ≤ X) :
    mapPaddedOuterLength Q lambda X H ≤
      3 * Real.sqrt Q * lambda * X := by
  have hsqrt : 1 ≤ Real.sqrt Q := by
    have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ
    nlinarith [Real.sq_sqrt hQ0, Real.sqrt_nonneg Q]
  have hlower : 0 ≤ mapOuterLower Q lambda X := by
    unfold mapOuterLower
    positivity
  have hfirst :
      mapOuterUpper Q lambda X - mapOuterLower Q lambda X ≤
        mapOuterUpper Q lambda X := sub_le_self _ hlower
  have hsecond : 2 * (lambda * H) ≤
      2 * (Real.sqrt Q * lambda * X) := by
    have : lambda * H ≤ Real.sqrt Q * lambda * X := by
      calc
        lambda * H ≤ lambda * X := mul_le_mul_of_nonneg_left hHX hlambda
        _ ≤ Real.sqrt Q * (lambda * X) :=
          le_mul_of_one_le_left (mul_nonneg hlambda hX) hsqrt
        _ = Real.sqrt Q * lambda * X := by ring
    linarith
  calc
    mapPaddedOuterLength Q lambda X H ≤
        mapOuterUpper Q lambda X + 2 * (lambda * H) :=
      add_le_add hfirst le_rfl
    _ ≤ mapOuterUpper Q lambda X +
        2 * (Real.sqrt Q * lambda * X) := add_le_add le_rfl hsecond
    _ = 3 * Real.sqrt Q * lambda * X := by
      unfold mapOuterUpper
      ring

/-- The downstream (3.7) envelope with the honest outer-length constant `3`.
The shared connector currently hard-codes constant `1`; this version is the
literal one compatible with the proved Fubini enlargement. -/
def paperFarEnvelopeThree (Q R H H₀ K₀ : ℝ) : ℝ :=
  3 / Real.sqrt Q + K₀ * Q / H₀ + K₀ * Q / R +
    3 * (Q * Real.sqrt Q) / H

theorem first_cell_term_le_three
    {q Q lambda T X : ℝ}
    (hq : 0 ≤ q) (hQ : 0 < Q) (hX : 0 < X)
    (hT : T ≤ 3 * Real.sqrt Q * lambda * X)
    (hDirichlet : q * lambda ≤ 1 / Q) :
    q * T / X ≤ 3 / Real.sqrt Q := by
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  rw [div_le_iff₀ hX]
  calc
    q * T ≤ q * (3 * Real.sqrt Q * lambda * X) :=
      mul_le_mul_of_nonneg_left hT hq
    _ = 3 * Real.sqrt Q * (q * lambda) * X := by ring
    _ ≤ 3 * Real.sqrt Q * (1 / Q) * X := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hDirichlet (by positivity)) hX.le
    _ = (3 / Real.sqrt Q) * X := by
      have hsq : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ.le
      field_simp [ne_of_gt hsqrt, ne_of_gt hQ]
      nlinarith

theorem fourth_cell_term_le_three
    {q Q lambda T U H X : ℝ}
    (hq : 0 ≤ q) (hqQ : q ≤ Q)
    (hlambda : 0 < lambda) (hH : 0 < H) (hX : 0 < X)
    (hU : U = lambda * H)
    (hT : T ≤ 3 * Real.sqrt Q * lambda * X) :
    q * T / (U * X) ≤ 3 * (Q * Real.sqrt Q) / H := by
  have hUpos : 0 < U := by rw [hU]; positivity
  rw [div_le_div_iff₀ (mul_pos hUpos hX) hH]
  calc
    q * T * H ≤ q * (3 * Real.sqrt Q * lambda * X) * H :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hT hq) hH.le
    _ = 3 * (q * Real.sqrt Q) * (lambda * H * X) := by ring
    _ ≤ 3 * (Q * Real.sqrt Q) * (lambda * H * X) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hqQ (Real.sqrt_nonneg Q))
          (by norm_num)) (by positivity)
    _ = 3 * (Q * Real.sqrt Q) * (U * X) := by rw [hU]

theorem paperCellTerms_le_paperFarEnvelopeThree
    {q Q lambda M N T U R H H₀ X K₀ : ℝ}
    (hq : 0 ≤ q) (hqQ : q ≤ Q) (hQ : 0 < Q)
    (hlambda : 0 < lambda) (hM : 0 < M) (hN : 0 ≤ N)
    (hU : U = lambda * H) (hH : 0 < H)
    (hR : 0 < R) (hRU : R ≤ U)
    (hH₀ : 0 < H₀) (hH₀M : H₀ ≤ M)
    (hX : 0 < X) (hK₀ : 0 ≤ K₀)
    (hT : T ≤ 3 * Real.sqrt Q * lambda * X)
    (hDirichlet : q * lambda ≤ 1 / Q)
    (hprod : M * N ≤ K₀ * X) :
    paperCellTerms q M N T U X ≤
      paperFarEnvelopeThree Q R H H₀ K₀ := by
  have h1 := first_cell_term_le_three hq hQ hX hT hDirichlet
  have h2 := second_cell_term_le hq hqQ hM hH₀ hH₀M hN hX hK₀ hprod
  have h3 := third_cell_term_le hq hqQ hM.le hN
    (by rw [hU]; positivity) hR hRU hX hK₀ hprod
  have h4 := fourth_cell_term_le_three hq hqQ hlambda hH hX hU hT
  unfold paperCellTerms paperFarEnvelopeThree
  linarith

theorem outerLower_eta_eq_mapOuterLower
    (Q beta X : ℝ) :
    outerLower X beta (1 / Real.sqrt Q) =
      mapOuterLower Q |beta| X := by
  unfold outerLower mapOuterLower
  ring

theorem outerUpper_eta_eq_mapOuterUpper
    {Q : ℝ} (hQ : 0 < Q) (beta X : ℝ) :
    outerUpper X beta (1 / Real.sqrt Q) =
      mapOuterUpper Q |beta| X := by
  have hsqrt : Real.sqrt Q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hQ)
  unfold outerUpper mapOuterUpper
  field_simp

/-! ## Honest source-branch bridge -/

/-- A uniform source decomposition of the actual `I(q₀,q₁)` components.
This is the still-research-level Heath--Brown/Perron input: every source
factorization is bounded componentwise by an explicit ordinary decomposition
error plus the enumerated source branches.  No normalized MAP conclusion occurs
in this proposition. -/
def SourceBranchDecomposition
    (p : Corollary53Input)
    (decompositionError : OuterComponent → ℝ)
    (sourceMass : OuterComponent → FarSourceBranch → ℝ) : Prop :=
  ∀ q₀ q₁, q₀ * q₁ = p.q → 1 ≤ q₀ → 1 ≤ q₁ →
    ∀ component : OuterComponent,
      componentIntegral p.X p.H q₀ q₁ p.f p.beta p.eta component ≤
        decompositionError component +
          ∑ branch : FarSourceBranch, sourceMass component branch

/-- Explicit equivalence separating cutoff-bearing branches from the two
direct source errors. -/
def farSourceBranchEquiv :
    FarSourceBranch ≃ Sum CutoffBranch (Fin 2) where
  toFun
    | .cutoff branch => .inl branch
    | .smallRemainder => .inr 0
    | .badEulerFactor => .inr 1
  invFun
    | .inl branch => .cutoff branch
    | .inr i => if i = 0 then .smallRemainder else .badEulerFactor
  left_inv x := by cases x <;> simp
  right_inv x := by
    cases x with
    | inl branch => simp
    | inr i => fin_cases i <;> simp

theorem sum_farSourceBranch_eq
    (mass : FarSourceBranch → ℝ) :
    (∑ branch : FarSourceBranch, mass branch) =
      (∑ branch : CutoffBranch, mass (.cutoff branch)) +
        mass .smallRemainder + mass .badEulerFactor := by
  calc
    (∑ branch : FarSourceBranch, mass branch) =
        ∑ z : Sum CutoffBranch (Fin 2),
          mass (farSourceBranchEquiv.symm z) :=
      Fintype.sum_equiv farSourceBranchEquiv _ _
        (fun x ↦ congrArg mass (farSourceBranchEquiv.symm_apply_apply x).symm)
    _ = (∑ branch : CutoffBranch, mass (.cutoff branch)) +
        ∑ i : Fin 2,
          mass (if i = 0 then .smallRemainder else .badEulerFactor) := by
      rw [Fintype.sum_sum_type]
      rfl
    _ = _ := by rw [Fin.sum_univ_two]; simp; ring

def nonCellSourceTotal
    (decompositionError : OuterComponent → ℝ)
    (sourceMass : OuterComponent → FarSourceBranch → ℝ) : ℝ :=
  ∑ component : OuterComponent,
    (decompositionError component +
      sourceMass component .smallRemainder +
      sourceMass component .badEulerFactor)

def cutoffSourceTotal
    (sourceMass : OuterComponent → FarSourceBranch → ℝ) : ℝ :=
  ∑ component : OuterComponent, ∑ branch : CutoffBranch,
    sourceMass component (.cutoff branch)

/-- The source decomposition controls the literal factorization supremum. -/
theorem factorizationSup_le_sourceBranches
    {p : Corollary53Input} {hq : 1 ≤ p.q}
    {decompositionError : OuterComponent → ℝ}
    {sourceMass : OuterComponent → FarSourceBranch → ℝ}
    (hsource : SourceBranchDecomposition p decompositionError sourceMass) :
    factorizationSup p.X p.H p.q p.f p.beta p.eta hq ≤
      ∑ component : OuterComponent,
        (decompositionError component +
          ∑ branch : FarSourceBranch, sourceMass component branch) := by
  apply (Finset.sup'_le_iff _ _).2
  intro z hz
  simp only [sourceI]
  apply Finset.sum_le_sum
  intro component hcomponent
  have hz' := (Finset.mem_filter.mp hz)
  have hbox := Finset.mem_product.mp hz'.1
  exact hsource z.1 z.2 hz'.2
    (Finset.mem_Icc.mp hbox.1).1 (Finset.mem_Icc.mp hbox.2).1 component

theorem factorizationSup_le_nonCell_add_cutoff
    {p : Corollary53Input} {hq : 1 ≤ p.q}
    {decompositionError : OuterComponent → ℝ}
    {sourceMass : OuterComponent → FarSourceBranch → ℝ}
    (hsource : SourceBranchDecomposition p decompositionError sourceMass) :
    factorizationSup p.X p.H p.q p.f p.beta p.eta hq ≤
      nonCellSourceTotal decompositionError sourceMass +
        cutoffSourceTotal sourceMass := by
  calc
    factorizationSup p.X p.H p.q p.f p.beta p.eta hq ≤
        ∑ component : OuterComponent,
          (decompositionError component +
            ∑ branch : FarSourceBranch, sourceMass component branch) :=
      factorizationSup_le_sourceBranches hsource
    _ = ∑ component : OuterComponent,
        ((decompositionError component +
            sourceMass component .smallRemainder +
            sourceMass component .badEulerFactor) +
          ∑ branch : CutoffBranch,
            sourceMass component (.cutoff branch)) := by
      apply Finset.sum_congr rfl
      intro component hcomponent
      rw [sum_farSourceBranch_eq]
      ring
    _ = nonCellSourceTotal decompositionError sourceMass +
        cutoffSourceTotal sourceMass := by
      rw [Finset.sum_add_distrib]
      rfl

/-- For each sign component, the existing local padded-cell proposition turns
all cutoff-bearing source branches into the certified mixed-mass majorants. -/
theorem cutoffSourceMass_le_paddedMixedMass
    {sourceMass : OuterComponent → FarSourceBranch → ℝ}
    {cellError : OuterComponent → CutoffBranch → ℝ}
    {blockCount q shortLength : OuterComponent → CutoffBranch → ℕ}
    {longLength : (component : OuterComponent) →
      (branch : CutoffBranch) → Fin (blockCount component branch) → ℕ}
    {beta : (component : OuterComponent) → (branch : CutoffBranch) →
      Fin (q component branch) → ℕ → ℂ}
    {g : (component : OuterComponent) → (branch : CutoffBranch) →
      Fin (blockCount component branch) → Fin (q component branch) → ℕ → ℂ}
    {a b U : OuterComponent → CutoffBranch → ℝ}
    (hcells : ∀ component,
      SourceToPaddedDyadicCells
        (fun branch ↦ sourceMass component (.cutoff branch))
        (cellError component) (blockCount component) (q component)
        (shortLength component) (longLength component) (beta component)
        (g component) (a component) (b component) (U component))
    (hab : ∀ component branch, a component branch ≤ b component branch)
    (hU : ∀ component branch, 0 ≤ U component branch) :
    (∑ component : OuterComponent, ∑ branch : CutoffBranch,
      sourceMass component (.cutoff branch)) ≤
      ∑ component : OuterComponent, ∑ branch : CutoffBranch,
        (cellError component branch +
          2 * blockwiseCharacterPairMixedMass
            (M := shortLength component branch)
            (longLength component branch) (beta component branch)
            (g component branch)
            ((a component branch + b component branch) / 2)
            ((b component branch - a component branch) +
              2 * U component branch) (U component branch)) := by
  apply Finset.sum_le_sum
  intro component hcomponent
  exact sourceToPaddedDyadicCells_implies_mixedMassMajorant
    (hcells component) (hab component) (hU component)

/-- The literal source supremum is now welded to the two direct source errors
and the padded mixed-mass cells.  The only assumptions are the source-level
Heath--Brown decomposition and its local `SourceToPaddedDyadicCells` output. -/
theorem factorizationSup_le_paddedCells
    {p : Corollary53Input} {hq : 1 ≤ p.q}
    {decompositionError : OuterComponent → ℝ}
    {sourceMass : OuterComponent → FarSourceBranch → ℝ}
    {cellError : OuterComponent → CutoffBranch → ℝ}
    {blockCount q shortLength : OuterComponent → CutoffBranch → ℕ}
    {longLength : (component : OuterComponent) →
      (branch : CutoffBranch) → Fin (blockCount component branch) → ℕ}
    {beta : (component : OuterComponent) → (branch : CutoffBranch) →
      Fin (q component branch) → ℕ → ℂ}
    {g : (component : OuterComponent) → (branch : CutoffBranch) →
      Fin (blockCount component branch) → Fin (q component branch) → ℕ → ℂ}
    {a b U : OuterComponent → CutoffBranch → ℝ}
    (hsource : SourceBranchDecomposition p decompositionError sourceMass)
    (hcells : ∀ component,
      SourceToPaddedDyadicCells
        (fun branch ↦ sourceMass component (.cutoff branch))
        (cellError component) (blockCount component) (q component)
        (shortLength component) (longLength component) (beta component)
        (g component) (a component) (b component) (U component))
    (hab : ∀ component branch, a component branch ≤ b component branch)
    (hU : ∀ component branch, 0 ≤ U component branch) :
    factorizationSup p.X p.H p.q p.f p.beta p.eta hq ≤
      nonCellSourceTotal decompositionError sourceMass +
      ∑ component : OuterComponent, ∑ branch : CutoffBranch,
        (cellError component branch +
          2 * blockwiseCharacterPairMixedMass
            (M := shortLength component branch)
            (longLength component branch) (beta component branch)
            (g component branch)
            ((a component branch + b component branch) / 2)
            ((b component branch - a component branch) +
              2 * U component branch) (U component branch)) := by
  calc
    factorizationSup p.X p.H p.q p.f p.beta p.eta hq ≤
        nonCellSourceTotal decompositionError sourceMass +
          cutoffSourceTotal sourceMass :=
      factorizationSup_le_nonCell_add_cutoff hsource
    _ ≤ nonCellSourceTotal decompositionError sourceMass +
        ∑ component : OuterComponent, ∑ branch : CutoffBranch,
          (cellError component branch +
            2 * blockwiseCharacterPairMixedMass
              (M := shortLength component branch)
              (longLength component branch) (beta component branch)
              (g component branch)
              ((a component branch + b component branch) / 2)
              ((b component branch - a component branch) +
                2 * U component branch) (U component branch)) := by
      apply add_le_add le_rfl
      exact cutoffSourceMass_le_paddedMixedMass hcells hab hU

/-- Apply published Corollary 5.3 and replace only its literal factorization
supremum by a proved source envelope.  The result still displays the exact
`d₂(q)^4/(qU²)` prefactor and the ordinary source error. -/
theorem corollary53_to_sourceEnvelope
    {cBetaEta cEta envelope : ℝ} {p : Corollary53Input}
    (hMRT : MRTCorollary53 cBetaEta cEta)
    (hp : Corollary53Admissible cBetaEta cEta p)
    (henvelope : factorizationSup p.X p.H p.q p.f p.beta p.eta hp.2.2.1 ≤
      envelope) :
    ∃ C : ℝ, 0 < C ∧
      sourceEnergy p ≤ C *
        ((divisorCount p.q : ℝ) ^ 4 /
            (p.q * stationaryWidth p.beta p.H ^ 2) * envelope +
          ordinaryError p.X p.H p.f p.beta p.eta) := by
  obtain ⟨C, hC, hbound⟩ := hMRT
  refine ⟨C, hC, (hbound p hp).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hC)
  apply add_le_add _ le_rfl
  rw [stationaryMainTerm_eq_U]
  apply mul_le_mul_of_nonneg_left henvelope
  positivity

/-! ## Direct promotion target for `CanonicalNearFarEstimates` -/

/-- Exact far conjunct of `CanonicalNearFarEstimates`, kept separate so the
source chain can be promoted without assuming the near Gallagher conjunct. -/
def CanonicalFarAnnulusEstimate : Prop :=
  ∀ A epsilon : ℝ, 0 < A → 0 < epsilon →
    ∃ B D Cc : ℕ, ∃ C X₀ : ℝ,
      0 < C ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        1 ≤ Real.log X ∧
        ∀ center : UnitAddCircle,
          center ∉ innerRationalCollars epsilon X B Cc →
          (∫ alpha in centeredArc (baseAperture epsilon X) center,
              ‖primeExponentialSum X alpha‖ ^ 2
                ∂AddCircle.haarAddCircle) ≤
            C * X * Real.rpow (Real.log X) (-A)

/-- The first MAP-specific source theorem still needed after importing
published Corollary 5.3.

For every canonical far center it produces the actual reduced rational lift,
signed `β`, the source input `Λ1_(X,2X]`, the Dirichlet bound and far threshold,
the real-line/circle domination, and a bound for the *literal* Corollary 5.3
right side.  Thus it is upstream of the desired far estimate and cannot be
satisfied merely by passing that estimate back as a premise.

`factorizationSup_le_paddedCells` and `sourceRHS_le_of_paddedCells` below give
the intended construction of the final RHS bound from
`SourceToPaddedDyadicCells`. -/
def MAPFarSourceReduction (cBetaEta cEta : ℝ) : Prop :=
  ∀ A epsilon : ℝ, 0 < A → 0 < epsilon →
    ∃ B D Cc : ℕ, ∃ Cred X₀ : ℝ,
      0 < Cred ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        1 ≤ Real.log X ∧
        ∀ center : UnitAddCircle,
          center ∉ innerRationalCollars epsilon X B Cc →
          ∃ q a : ℕ, ∃ beta : ℝ,
            let Q := (Real.log X) ^ B
            let H := baseAperture epsilon X
            let eta := 1 / Real.sqrt Q
            let p := mapCorollary53Input X H q a beta eta
            1 ≤ q ∧ (q : ℝ) ≤ Q ∧ a < q ∧ a.Coprime q ∧
            center = rationalCenter q a + (beta : UnitAddCircle) ∧
            |beta| ≤ 1 / ((q : ℝ) * Q) ∧
            2 * (Real.log X) ^ Cc < stationaryWidth beta H ∧
            ∃ hp : Corollary53Admissible cBetaEta cEta p,
              (∫ alpha in centeredArc H center,
                  ‖primeExponentialSum X alpha‖ ^ 2
                    ∂AddCircle.haarAddCircle) ≤ sourceEnergy p ∧
              stationaryMainTerm p.X p.H p.q p.f p.beta p.eta
                  hp.2.2.1 +
                  ordinaryError p.X p.H p.f p.beta p.eta ≤
                Cred * X * Real.rpow (Real.log X) (-A)

/-- Published Corollary 5.3 plus the precise MAP source reduction proves the
literal far conjunct consumed by `CanonicalNearFarEstimates`. -/
theorem canonicalFarAnnulusEstimate_of_source
    {cBetaEta cEta : ℝ}
    (hMRT : MRTCorollary53 cBetaEta cEta)
    (hsource : MAPFarSourceReduction cBetaEta cEta) :
    CanonicalFarAnnulusEstimate := by
  obtain ⟨Cmrt, hCmrt, hcor⟩ := hMRT
  intro A epsilon hA hepsilon
  obtain ⟨B, D, Cc, Cred, X₀, hCred, hX₀, hred⟩ :=
    hsource A epsilon hA hepsilon
  refine ⟨B, D, Cc, Cmrt * Cred, X₀, mul_pos hCmrt hCred, hX₀, ?_⟩
  intro X hXX₀
  obtain ⟨hlog, hfar⟩ := hred X hXX₀
  refine ⟨hlog, ?_⟩
  intro center hcenter
  obtain ⟨q, a, beta, hq, hqQ, ha, hacop, hcenterEq, hbeta,
      hfarWidth, hp, hcircle, hRHS⟩ := hfar center hcenter
  let Q := (Real.log X) ^ B
  let H := baseAperture epsilon X
  let eta := 1 / Real.sqrt Q
  let p := mapCorollary53Input X H q a beta eta
  have hcorP : sourceEnergy p ≤ Cmrt *
      (stationaryMainTerm p.X p.H p.q p.f p.beta p.eta hq +
        ordinaryError p.X p.H p.f p.beta p.eta) := hcor p hp
  calc
    (∫ alpha in centeredArc (baseAperture epsilon X) center,
        ‖primeExponentialSum X alpha‖ ^ 2
          ∂AddCircle.haarAddCircle) ≤ sourceEnergy p := hcircle
    _ ≤ Cmrt *
        (stationaryMainTerm p.X p.H p.q p.f p.beta p.eta hq +
          ordinaryError p.X p.H p.f p.beta p.eta) := hcorP
    _ ≤ Cmrt * (Cred * X * Real.rpow (Real.log X) (-A)) :=
      mul_le_mul_of_nonneg_left hRHS hCmrt.le
    _ = (Cmrt * Cred) * X * Real.rpow (Real.log X) (-A) := by ring

/-- A local budget theorem: the already-compiled source decomposition and
`SourceToPaddedDyadicCells` bridge suffice to bound the literal Corollary 5.3
RHS.  This is the construction step intended inside `MAPFarSourceReduction`. -/
theorem sourceRHS_le_of_paddedCells
    {p : Corollary53Input} {hq : 1 ≤ p.q}
    {decompositionError : OuterComponent → ℝ}
    {sourceMass : OuterComponent → FarSourceBranch → ℝ}
    {cellError : OuterComponent → CutoffBranch → ℝ}
    {blockCount q shortLength : OuterComponent → CutoffBranch → ℕ}
    {longLength : (component : OuterComponent) →
      (branch : CutoffBranch) → Fin (blockCount component branch) → ℕ}
    {beta : (component : OuterComponent) → (branch : CutoffBranch) →
      Fin (q component branch) → ℕ → ℂ}
    {g : (component : OuterComponent) → (branch : CutoffBranch) →
      Fin (blockCount component branch) → Fin (q component branch) → ℕ → ℂ}
    {a b U : OuterComponent → CutoffBranch → ℝ}
    {budget : ℝ}
    (hsource : SourceBranchDecomposition p decompositionError sourceMass)
    (hcells : ∀ component,
      SourceToPaddedDyadicCells
        (fun branch ↦ sourceMass component (.cutoff branch))
        (cellError component) (blockCount component) (q component)
        (shortLength component) (longLength component) (beta component)
        (g component) (a component) (b component) (U component))
    (hab : ∀ component branch, a component branch ≤ b component branch)
    (hU : ∀ component branch, 0 ≤ U component branch)
    (hbudget :
      (divisorCount p.q : ℝ) ^ 4 /
          (p.q * stationaryWidth p.beta p.H ^ 2) *
        (nonCellSourceTotal decompositionError sourceMass +
          ∑ component : OuterComponent, ∑ branch : CutoffBranch,
            (cellError component branch +
              2 * blockwiseCharacterPairMixedMass
                (M := shortLength component branch)
                (longLength component branch) (beta component branch)
                (g component branch)
                ((a component branch + b component branch) / 2)
                ((b component branch - a component branch) +
                  2 * U component branch) (U component branch))) +
          ordinaryError p.X p.H p.f p.beta p.eta ≤ budget) :
    stationaryMainTerm p.X p.H p.q p.f p.beta p.eta hq +
        ordinaryError p.X p.H p.f p.beta p.eta ≤ budget := by
  rw [stationaryMainTerm_eq_U]
  apply le_trans _ hbudget
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left
    (factorizationSup_le_paddedCells hsource hcells hab hU)
  positivity

end
end MAPMRTCorollary53Source

#print axioms MAPMRTCorollary53Source.modulusFactorizations_nonempty
#print axioms MAPMRTCorollary53Source.sourceI_le_factorizationSup
#print axioms MAPMRTCorollary53Source.exponentialSum_mapMangoldtCoeff_eq_primeExponentialSum
#print axioms MAPMRTCorollary53Source.stationaryMainTerm_eq_U
#print axioms MAPMRTCorollary53Source.sum_paddedCharacterWindow_eq_characterWindow
#print axioms MAPMRTCorollary53Source.paddedCharacterTwist_on_actual
#print axioms MAPMRTCorollary53Source.mapPaddedOuterLength_le_three
#print axioms MAPMRTCorollary53Source.paperCellTerms_le_paperFarEnvelopeThree
#print axioms MAPMRTCorollary53Source.factorizationSup_le_sourceBranches
#print axioms MAPMRTCorollary53Source.cutoffSourceMass_le_paddedMixedMass
#print axioms MAPMRTCorollary53Source.factorizationSup_le_paddedCells
#print axioms MAPMRTCorollary53Source.corollary53_to_sourceEnvelope
#print axioms MAPMRTCorollary53Source.canonicalFarAnnulusEstimate_of_source
#print axioms MAPMRTCorollary53Source.sourceRHS_le_of_paddedCells
