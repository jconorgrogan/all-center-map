import MRTLemma29Proof

/-!
# Corrected downstream integration of MRT Lemma 2.9

This module threads the source-faithful support premise through the complete
Proposition 5.1 to Corollary 5.3 half-range chain.  The rejected finite
`MRTLemma29` proposition is never consumed.
-/

namespace MAPMRTProposition51Supported

open scoped BigOperators
open MeasureTheory
open MAPMRTCorollary53Source
open MAPFarAnnulusSourceToModel
open MAPAllCenterApertureTransfer
open PrimePairEndpoints MAPAllCenterNearFarTransfer
open MAPMRTProposition51Source MAPMRTLemma29Corrected MAPMRTLemma29Proof

noncomputable section

theorem lemma29_window_bound
    (hL29 : MRTLemma29Supported) {X H beta t : ℝ} {q a : ℕ} {f : ℕ → ℂ}
    (hH : 0 ≤ H) (hq : 1 ≤ q) (haq : a.Coprime q)
    (hsupport : ∀ n : ℕ, ⌊2 * X⌋₊ < n → f n = 0) :
    untwistedWindow X H (additiveTwist q a f) beta t ≤
      (divisorCount q : ℝ) / Real.sqrt q *
        ∑ z ∈ modulusFactorizations q,
          characterWindow X z.1 z.2 f beta H t := by
  have hU : 0 ≤ |beta| * H := mul_nonneg (abs_nonneg _) hH
  have hpoint := fun t' ↦
    lemma29_specialize_to_source_supported hL29 (X := X) (q := q) (a := a)
      (f := f) (t := t') hq haq hsupport
  have hleft : Continuous (fun t' : ℝ ↦
      ‖finiteCriticalPolynomial ⌊2 * X⌋₊ (additiveTwist q a f) t'‖) :=
    continuous_norm_finiteCriticalPolynomial _ _
  have hright : Continuous (fun t' : ℝ ↦
      (divisorCount q : ℝ) / Real.sqrt q *
        ∑ z ∈ modulusFactorizations q,
          ∑ chi : DirichletCharacter ℂ z.2,
            ‖criticalDirichletPolynomial X z.1 z.2 f chi t'‖) := by
    apply continuous_const.mul
    apply continuous_finset_sum
    intro z hz
    apply continuous_finset_sum
    intro chi hchi
    exact continuous_norm_criticalDirichletPolynomial X z.1 z.2 f chi
  unfold untwistedWindow
  calc
    (∫ t' in (t - |beta| * H)..(t + |beta| * H),
        ‖finiteCriticalPolynomial ⌊2 * X⌋₊ (additiveTwist q a f) t'‖) ≤
        ∫ t' in (t - |beta| * H)..(t + |beta| * H),
          (divisorCount q : ℝ) / Real.sqrt q *
            ∑ z ∈ modulusFactorizations q,
              ∑ chi : DirichletCharacter ℂ z.2,
                ‖criticalDirichletPolynomial X z.1 z.2 f chi t'‖ := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact hleft.intervalIntegrable _ _
      · exact hright.intervalIntegrable _ _
      · intro t' ht'
        exact hpoint t'
    _ = (divisorCount q : ℝ) / Real.sqrt q *
        ∑ z ∈ modulusFactorizations q,
          characterWindow X z.1 z.2 f beta H t := by
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_finset_sum]
      · apply congrArg
        apply Finset.sum_congr rfl
        intro z hz
        unfold characterWindow
        rw [intervalIntegral.integral_finsetSum]
        intro chi hchi
        exact (continuous_norm_criticalDirichletPolynomial
          X z.1 z.2 f chi).intervalIntegrable _ _
      · intro z hz
        exact (continuous_finset_sum _ fun chi _ ↦
          continuous_norm_criticalDirichletPolynomial
            X z.1 z.2 f chi).intervalIntegrable _ _

/-- The exact coefficient after squaring Lemma 2.9 and applying Cauchy only
over the factorization variable. -/
def lemma29CauchyCoefficient (q : ℕ) : ℝ :=
  ((divisorCount q : ℝ) / Real.sqrt q) ^ 2 * divisorCount q

theorem lemma29CauchyCoefficient_eq
    {q : ℕ} (hq : 1 ≤ q) :
    lemma29CauchyCoefficient q = (divisorCount q : ℝ) ^ 3 / q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hsqrt : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq0)
  have hsquare : Real.sqrt (q : ℝ) ^ 2 = q := Real.sq_sqrt hq0.le
  unfold lemma29CauchyCoefficient
  rw [div_pow, hsquare]
  ring

theorem lemma29_window_sq_bound
    (hL29 : MRTLemma29Supported) {X H beta t : ℝ} {q a : ℕ} {f : ℕ → ℂ}
    (hH : 0 ≤ H) (hq : 1 ≤ q) (haq : a.Coprime q)
    (hsupport : ∀ n : ℕ, ⌊2 * X⌋₊ < n → f n = 0) :
    untwistedWindow X H (additiveTwist q a f) beta t ^ 2 ≤
      lemma29CauchyCoefficient q *
        ∑ z ∈ modulusFactorizations q,
          characterWindow X z.1 z.2 f beta H t ^ 2 := by
  let W : ℝ := untwistedWindow X H (additiveTwist q a f) beta t
  let B : ℕ × ℕ → ℝ := fun z ↦
    characterWindow X z.1 z.2 f beta H t
  let c : ℝ := (divisorCount q : ℝ) / Real.sqrt q
  have hW0 : 0 ≤ W := untwistedWindow_nonneg hH
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  have hB0 : ∀ z ∈ modulusFactorizations q, 0 ≤ B z := by
    intro z hz
    exact characterWindow_nonneg (mul_nonneg (abs_nonneg _) hH)
  have hsum0 : 0 ≤ ∑ z ∈ modulusFactorizations q, B z :=
    Finset.sum_nonneg fun z hz ↦ hB0 z hz
  have hwindow : W ≤ c * ∑ z ∈ modulusFactorizations q, B z :=
    lemma29_window_bound hL29 hH hq haq hsupport
  have hpow : W ^ 2 ≤ (c * ∑ z ∈ modulusFactorizations q, B z) ^ 2 :=
    pow_le_pow_left₀ hW0 hwindow 2
  have hcauchy :
      (∑ z ∈ modulusFactorizations q, B z) ^ 2 ≤
        ((modulusFactorizations q).card : ℝ) *
          ∑ z ∈ modulusFactorizations q, B z ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hcard : ((modulusFactorizations q).card : ℝ) ≤ divisorCount q := by
    exact_mod_cast card_modulusFactorizations_le_divisorCount hq
  have hsumsq0 : 0 ≤ ∑ z ∈ modulusFactorizations q, B z ^ 2 :=
    Finset.sum_nonneg fun z hz ↦ sq_nonneg _
  calc
    W ^ 2 ≤ (c * ∑ z ∈ modulusFactorizations q, B z) ^ 2 := hpow
    _ = c ^ 2 * (∑ z ∈ modulusFactorizations q, B z) ^ 2 := by ring
    _ ≤ c ^ 2 * (((modulusFactorizations q).card : ℝ) *
          ∑ z ∈ modulusFactorizations q, B z ^ 2) := by
      exact mul_le_mul_of_nonneg_left hcauchy (sq_nonneg c)
    _ ≤ c ^ 2 * ((divisorCount q : ℝ) *
          ∑ z ∈ modulusFactorizations q, B z ^ 2) := by
      gcongr
    _ = lemma29CauchyCoefficient q *
          ∑ z ∈ modulusFactorizations q, B z ^ 2 := by
      unfold lemma29CauchyCoefficient c
      ring

theorem lemma29_componentIntegral_bound
    (hL29 : MRTLemma29Supported) {X H beta eta : ℝ} {q a : ℕ} {f : ℕ → ℂ}
    (hX : 0 ≤ X) (hH : 0 ≤ H) (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (hq : 1 ≤ q) (haq : a.Coprime q)
    (hsupport : ∀ n : ℕ, ⌊2 * X⌋₊ < n → f n = 0)
    (component : OuterComponent) :
    untwistedComponentIntegral X H (additiveTwist q a f) beta eta component ≤
      lemma29CauchyCoefficient q *
        ∑ z ∈ modulusFactorizations q,
          componentIntegral X H z.1 z.2 f beta eta component := by
  let e := componentEndpoints X beta eta component
  have he : e.1 ≤ e.2 := componentEndpoints_mono hX heta hetaOne component
  have hleft : Continuous (fun t : ℝ ↦
      untwistedWindow X H (additiveTwist q a f) beta t ^ 2) :=
    (continuous_untwistedWindow X H (additiveTwist q a f) beta).pow 2
  have hright : Continuous (fun t : ℝ ↦
      lemma29CauchyCoefficient q *
        ∑ z ∈ modulusFactorizations q,
          characterWindow X z.1 z.2 f beta H t ^ 2) := by
    apply continuous_const.mul
    apply continuous_finset_sum
    intro z hz
    exact (continuous_characterWindow X H z.1 z.2 f beta).pow 2
  unfold untwistedComponentIntegral componentIntegral
  dsimp only
  calc
    (∫ t in e.1..e.2,
        untwistedWindow X H (additiveTwist q a f) beta t ^ 2) ≤
        ∫ t in e.1..e.2,
          lemma29CauchyCoefficient q *
            ∑ z ∈ modulusFactorizations q,
              characterWindow X z.1 z.2 f beta H t ^ 2 := by
      apply intervalIntegral.integral_mono_on he
      · exact hleft.intervalIntegrable _ _
      · exact hright.intervalIntegrable _ _
      · intro t ht
        exact lemma29_window_sq_bound hL29 hH hq haq hsupport
    _ = lemma29CauchyCoefficient q *
        ∑ z ∈ modulusFactorizations q,
          (∫ t in e.1..e.2,
            characterWindow X z.1 z.2 f beta H t ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_finset_sum]
      intro z hz
      exact (continuous_characterWindow X H z.1 z.2 f beta).pow 2
        |>.intervalIntegrable _ _

theorem lemma29_proposition51I_bound
    (hL29 : MRTLemma29Supported) {X H beta eta : ℝ} {q a : ℕ} {f : ℕ → ℂ}
    (hX : 0 ≤ X) (hH : 0 ≤ H) (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (hq : 1 ≤ q) (haq : a.Coprime q)
    (hsupport : ∀ n : ℕ, ⌊2 * X⌋₊ < n → f n = 0) :
    proposition51I X H (additiveTwist q a f) beta eta ≤
      lemma29CauchyCoefficient q *
        ∑ z ∈ modulusFactorizations q,
          sourceI X H z.1 z.2 f beta eta := by
  unfold proposition51I sourceI
  calc
    (∑ component : OuterComponent,
        untwistedComponentIntegral X H (additiveTwist q a f)
          beta eta component) ≤
        ∑ component : OuterComponent,
          lemma29CauchyCoefficient q *
            ∑ z ∈ modulusFactorizations q,
              componentIntegral X H z.1 z.2 f beta eta component := by
      apply Finset.sum_le_sum
      intro component hcomponent
      exact lemma29_componentIntegral_bound hL29 hX hH heta hetaOne hq haq
        hsupport component
    _ = lemma29CauchyCoefficient q *
        ∑ z ∈ modulusFactorizations q,
          ∑ component : OuterComponent,
            componentIntegral X H z.1 z.2 f beta eta component := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]

theorem factorization_sum_sourceI_le_sup
    {X H beta eta : ℝ} {q : ℕ} {f : ℕ → ℂ}
    (hX : 0 ≤ X) (hH : 0 ≤ H) (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (hq : 1 ≤ q) :
    (∑ z ∈ modulusFactorizations q,
        sourceI X H z.1 z.2 f beta eta) ≤
      (divisorCount q : ℝ) * factorizationSup X H q f beta eta hq := by
  have hterm : ∀ z ∈ modulusFactorizations q,
      sourceI X H z.1 z.2 f beta eta ≤
        factorizationSup X H q f beta eta hq := by
    intro z hz
    have hmem := Finset.mem_filter.mp hz
    have hprod := Finset.mem_product.mp hmem.1
    exact sourceI_le_factorizationSup hq hmem.2
      (Finset.mem_Icc.mp hprod.1).1 (Finset.mem_Icc.mp hprod.2).1
  have hsum := Finset.sum_le_card_nsmul
    (modulusFactorizations q)
    (fun z ↦ sourceI X H z.1 z.2 f beta eta)
    (factorizationSup X H q f beta eta hq) hterm
  have hsup0 : 0 ≤ factorizationSup X H q f beta eta hq := by
    obtain ⟨z, hz⟩ := modulusFactorizations_nonempty hq
    exact (sourceI_nonneg hX hH heta hetaOne).trans
      (sourceI_le_factorizationSup hq (Finset.mem_filter.mp hz).2
        (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1).1
        (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).2).1)
  have hcard : ((modulusFactorizations q).card : ℝ) ≤ divisorCount q := by
    exact_mod_cast card_modulusFactorizations_le_divisorCount hq
  calc
    (∑ z ∈ modulusFactorizations q,
        sourceI X H z.1 z.2 f beta eta) ≤
        ((modulusFactorizations q).card : ℝ) *
          factorizationSup X H q f beta eta hq := by
      simpa [nsmul_eq_mul] using hsum
    _ ≤ (divisorCount q : ℝ) *
          factorizationSup X H q f beta eta hq := by
      exact mul_le_mul_of_nonneg_right hcard hsup0

theorem lemma29_proposition51I_le_factorizationSup
    (hL29 : MRTLemma29Supported) {X H beta eta : ℝ} {q a : ℕ} {f : ℕ → ℂ}
    (hX : 0 ≤ X) (hH : 0 ≤ H) (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (hq : 1 ≤ q) (haq : a.Coprime q)
    (hsupport : ∀ n : ℕ, ⌊2 * X⌋₊ < n → f n = 0) :
    proposition51I X H (additiveTwist q a f) beta eta ≤
      (divisorCount q : ℝ) ^ 4 / q *
        factorizationSup X H q f beta eta hq := by
  have hfirst := lemma29_proposition51I_bound hL29
    (X := X) (H := H) (beta := beta) (eta := eta)
    (q := q) (a := a) (f := f) hX hH heta hetaOne hq haq hsupport
  have hsecond := factorization_sum_sourceI_le_sup
    (X := X) (H := H) (beta := beta) (eta := eta)
    (q := q) (f := f) hX hH heta hetaOne hq
  have hcoef0 : 0 ≤ lemma29CauchyCoefficient q := by
    unfold lemma29CauchyCoefficient
    positivity
  calc
    proposition51I X H (additiveTwist q a f) beta eta ≤
        lemma29CauchyCoefficient q *
          ∑ z ∈ modulusFactorizations q,
            sourceI X H z.1 z.2 f beta eta := hfirst
    _ ≤ lemma29CauchyCoefficient q *
        ((divisorCount q : ℝ) *
          factorizationSup X H q f beta eta hq) :=
      mul_le_mul_of_nonneg_left hsecond hcoef0
    _ = (divisorCount q : ℝ) ^ 4 / q *
        factorizationSup X H q f beta eta hq := by
      rw [lemma29CauchyCoefficient_eq hq]
      ring

/-! ## The direct Corollary 5.3 deduction on Proposition 5.1's range -/

def twistedProposition51Input (p : Corollary53Input) : Proposition51Input where
  X := p.X
  H := p.H
  beta := p.beta
  eta := p.eta
  f := additiveTwist p.q p.a p.f

theorem twistedProposition51Input_admissible
    {cBetaEta cEta : ℝ} {p : Corollary53Input}
    (hp : Corollary53Admissible cBetaEta cEta p)
    (hHalf : p.H ≤ p.X / 2) :
    Proposition51Admissible cBetaEta cEta (twistedProposition51Input p) := by
  rcases hp with
    ⟨hH, hHX, hq, haq, heta, hetaOne, hbetaEta, hetaCap, hbeta, hsupport⟩
  refine ⟨hH, hHalf, heta, hetaOne, hbetaEta, hetaCap, hbeta, ?_⟩
  intro n hn
  exact additiveTwist_eq_zero_of_eq_zero (hsupport n hn)

theorem proposition51Energy_twisted_eq_sourceEnergy (p : Corollary53Input) :
    proposition51Energy (twistedProposition51Input p) = sourceEnergy p := by
  unfold proposition51Energy twistedProposition51Input sourceEnergy
  simp only
  apply intervalIntegral.integral_congr
  intro theta htheta
  change ‖exponentialSum p.X (additiveTwist p.q p.a p.f) theta‖ ^ 2 =
    ‖exponentialSum p.X p.f ((p.a : ℝ) / p.q + theta)‖ ^ 2
  rw [exponentialSum_additiveTwist]

theorem ordinarySlidingMass_additiveTwist
    (X H : ℝ) (q a : ℕ) (f : ℕ → ℂ) :
    ordinarySlidingMass X H (additiveTwist q a f) =
      ordinarySlidingMass X H f := by
  unfold ordinarySlidingMass
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp [norm_additiveTwist]

theorem ordinaryError_additiveTwist
    (X H beta eta : ℝ) (q a : ℕ) (f : ℕ → ℂ) :
    ordinaryError X H (additiveTwist q a f) beta eta =
      ordinaryError X H f beta eta := by
  unfold ordinaryError
  rw [ordinarySlidingMass_additiveTwist]

theorem proposition51_main_le_stationaryMain
    (hL29 : MRTLemma29Supported) {p : Corollary53Input}
    (hp : Corollary53Admissible cBetaEta cEta p) :
    1 / (|p.beta| ^ 2 * p.H ^ 2) *
        proposition51I p.X p.H (additiveTwist p.q p.a p.f)
          p.beta p.eta ≤
      stationaryMainTerm p.X p.H p.q p.f p.beta p.eta hp.2.2.1 := by
  rcases hp with
    ⟨hH, hHX, hq, haq, heta, hetaOne, hbetaEta, hetaCap, hbeta, hsupport⟩
  have hX : 0 ≤ p.X := by linarith
  have hcutoff : ∀ n : ℕ, ⌊2 * p.X⌋₊ < n → p.f n = 0 :=
    cutoff_support_of_dyadic_support hX hsupport
  have hI := lemma29_proposition51I_le_factorizationSup hL29
    (X := p.X) (H := p.H) (beta := p.beta) (eta := p.eta)
    (q := p.q) (a := p.a) (f := p.f)
    hX (by linarith) heta hetaOne hq haq hcutoff
  have hscale : 0 ≤ 1 / (|p.beta| ^ 2 * p.H ^ 2) := by positivity
  calc
    1 / (|p.beta| ^ 2 * p.H ^ 2) *
        proposition51I p.X p.H (additiveTwist p.q p.a p.f)
          p.beta p.eta ≤
      1 / (|p.beta| ^ 2 * p.H ^ 2) *
        ((divisorCount p.q : ℝ) ^ 4 / p.q *
          factorizationSup p.X p.H p.q p.f p.beta p.eta hq) :=
      mul_le_mul_of_nonneg_left hI hscale
    _ = stationaryMainTerm p.X p.H p.q p.f p.beta p.eta hq := by
      unfold stationaryMainTerm
      ring

/-- Corollary 5.3(i) restricted to the literal range of Proposition 5.1.
This is the largest conclusion obtained by the printed one-line proof without
an additional endpoint-range argument. -/
def MRTCorollary53HalfRange (cBetaEta cEta : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (p : Corollary53Input)
    (hp : Corollary53Admissible cBetaEta cEta p)
    (hHalf : p.H ≤ p.X / 2),
    sourceEnergy p ≤ C *
      (stationaryMainTerm p.X p.H p.q p.f p.beta p.eta hp.2.2.1 +
        ordinaryError p.X p.H p.f p.beta p.eta)

theorem corollary53_halfRange_of_proposition51_lemma29
    (hP51 : MRTProposition51 cBetaEta cEta) :
    MRTCorollary53HalfRange cBetaEta cEta := by
  let hL29 : MRTLemma29Supported := mrtLemma29Supported_proof
  obtain ⟨C, hC, hP51bound⟩ := hP51
  refine ⟨C, hC, ?_⟩
  intro p hp hHalf
  have hp51 := twistedProposition51Input_admissible hp hHalf
  have hbound := hP51bound (twistedProposition51Input p) hp51
  rw [proposition51Energy_twisted_eq_sourceEnergy] at hbound
  simp only [twistedProposition51Input] at hbound
  rw [ordinaryError_additiveTwist] at hbound
  have hmain := proposition51_main_le_stationaryMain hL29 hp
  have hinside :
      1 / (|p.beta| ^ 2 * p.H ^ 2) *
          proposition51I p.X p.H (additiveTwist p.q p.a p.f)
            p.beta p.eta +
        ordinaryError p.X p.H p.f p.beta p.eta ≤
      stationaryMainTerm p.X p.H p.q p.f p.beta p.eta hp.2.2.1 +
        ordinaryError p.X p.H p.f p.beta p.eta :=
    add_le_add hmain le_rfl
  exact hbound.trans (mul_le_mul_of_nonneg_left hinside hC.le)

/-! ## MAP-specific promotion without the unused endpoint range -/

/-- The MAP base aperture is already in Proposition 5.1's literal half-range
for every `X ≥ 1`.  No asymptotic slack is needed: the exponent is at most
`2/15+1/1200 < 1`, and the definition contains the factor `1/2`. -/
theorem baseAperture_le_half_of_one_le
    {epsilon X : ℝ} (hX : 1 ≤ X) :
    baseAperture epsilon X ≤ X / 2 := by
  have hreserve : apertureReserve epsilon ≤ 1 / 1200 := by
    unfold apertureReserve
    exact min_le_right _ _
  have hexponent : 2 / 15 + apertureReserve epsilon ≤ 1 := by
    linarith
  have hpow : Real.rpow X (2 / 15 + apertureReserve epsilon) ≤ X := by
    simpa using Real.rpow_le_rpow_of_exponent_le hX hexponent
  unfold baseAperture
  nlinarith

/-- The already-promoted MAP source reduction consumes only inputs whose
`H` is the base aperture.  Thus the compiled half-range Corollary 5.3 is
sufficient for the exact far conjunct; no theorem about `X/2 < H ≤ X` enters
the MAP endpoint DAG. -/
theorem canonicalFarAnnulusEstimate_of_halfRange_source
    {cBetaEta cEta : ℝ}
    (hMRT : MRTCorollary53HalfRange cBetaEta cEta)
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
  have hXone : 1 ≤ X := by linarith
  have hHalf : p.H ≤ p.X / 2 := by
    change baseAperture epsilon X ≤ X / 2
    exact baseAperture_le_half_of_one_le hXone
  have hcorP : sourceEnergy p ≤ Cmrt *
      (stationaryMainTerm p.X p.H p.q p.f p.beta p.eta hq +
        ordinaryError p.X p.H p.f p.beta p.eta) := hcor p hp hHalf
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

/-- Direct MAP promotion from Proposition 5.1 and the existing MAP source
reduction.  The corrected Lemma 2.9 is proved internally by the half-range
constructor; the two still-open analytic premises remain visible here. -/
theorem canonicalFarAnnulusEstimate_of_proposition51_lemma29_source
    {cBetaEta cEta : ℝ}
    (hP51 : MRTProposition51 cBetaEta cEta)
    (hsource : MAPFarSourceReduction cBetaEta cEta) :
    CanonicalFarAnnulusEstimate :=
  canonicalFarAnnulusEstimate_of_halfRange_source
    (corollary53_halfRange_of_proposition51_lemma29 hP51) hsource


end
end MAPMRTProposition51Supported
