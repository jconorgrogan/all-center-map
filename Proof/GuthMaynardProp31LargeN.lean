import GuthMaynardProp31TraceCardinality
import GuthMaynardS1Proposition51Endpoint
import GuthMaynardS1MassBridge
import GuthMaynardS2SharpConsumer
import GuthMaynardS3EnergyInserted
import GuthMaynardProp31PolynomialBridge
import GuthMaynardProp31SeamMonomials
import GuthMaynardS3ProfileScaleGrowth

open scoped BigOperators Real
open CGLProofDAG GuthMaynardHeathBrownInterface
open GuthMaynardS3LiteralLemma82 GuthMaynardEquation55Infinite
open GuthMaynardSmoothedProp31Consumer GuthMaynardSectionFourTrace
open GuthMaynardProp31PolynomialBridge GuthMaynardS2SharpNormalization

noncomputable section
set_option maxHeartbeats 1000000
namespace GuthMaynardProp31LargeN

/-- Uniform large-N Prop.3.1 with all literal source estimates supplied. -/
theorem exists_actual_prop31_largeN_bound (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 256 ≤ N0 ∧
      ∀ (N : ℕ) (W : Finset ℝ) (T sigma : ℝ) (b : ℕ → ℂ),
        N0 ≤ N → T = (N : ℝ) ^ (6 / 5 : ℝ) →
        (7 / 10 : ℝ) ≤ sigma → sigma ≤ (8 / 10 : ℝ) →
        W.Nonempty → TEtaSeparated W T eps →
        ContainedInIntervalOfLength W T →
        (∀ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ≤ 1) →
        supportedOnPlateau N b →
        (∀ t ∈ W, (N : ℝ) ^ sigma ≤ ‖dirichletPolynomial b N t‖) →
        (W.card : ℝ) ≤ C * T ^ eps * (N : ℝ) ^ (18 / 5 - 4 * sigma : ℝ) := by
  let delta : ℝ := min (eps / 10) (1 / 2)
  have hd : 0 < delta := lt_min (by positivity) (by norm_num)
  have hde : delta ≤ eps := by
    have := min_le_left (eps / 10) (1 / 2 : ℝ)
    dsimp [delta]
    linarith
  have hdh : delta ≤ 1 / 2 := min_le_right _ _
  obtain ⟨Ct, hCt, httrace⟩ :=
    GuthMaynardProp31TraceCardinality.exists_actual_trace_cardinality_bound delta hd
  obtain ⟨C1, T1, hC1, hT1, hS1⟩ :=
    GuthMaynardS1Proposition51Endpoint.source_proposition5_1 hd hdh
  obtain ⟨C2, T2, hC2, hT2, hS2⟩ :=
    GuthMaynardS2SharpConsumer.norm_sourceS2_le_sharp hd
  obtain ⟨C3, hC3, N3, hN3, hS3⟩ :=
    GuthMaynardS3EnergyInserted.exists_actual_prop11_2_bound hd
  let N0 : ℕ := max 256 (max N3 (max (Nat.ceil T1 + 1) (Nat.ceil T2 + 1)))
  let G : ℝ := 2 + C2 + C3
  let F : ℝ := Ct * G + 1
  have hG : 0 < G := by dsimp [G]; positivity
  have hF : 1 ≤ F := by dsimp [F]; nlinarith
  refine ⟨8 * F, by positivity, N0, by dsimp [N0]; omega, ?_⟩
  intro N W T sigma b hN0 hTdef hslo hshi hW hsep hcontained hb hsupp hlarge
  have hN256 : 256 ≤ N := by dsimp [N0] at hN0; omega
  have hNnat : 1 ≤ N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNnat
  have hNp : 0 < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hTone : 1 ≤ T := by rw [hTdef]; exact Real.one_le_rpow hN1 (by norm_num)
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  have hNT : (N : ℝ) ≤ T := by
    rw [hTdef]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (1 : ℝ) ≤ 6 / 5)
  have hTN2 : T ≤ (N : ℝ)^2 := by
    rw [hTdef]
    exact (Real.rpow_le_rpow_of_exponent_le hN1
      (by norm_num : (6 / 5 : ℝ) ≤ 2)).trans_eq (Real.rpow_natCast (N : ℝ) 2)
  have hN3le : N3 ≤ N := by dsimp [N0] at hN0; omega
  have hceil1 : Nat.ceil T1 + 1 ≤ N := by dsimp [N0] at hN0; omega
  have hceil2 : Nat.ceil T2 + 1 ≤ N := by dsimp [N0] at hN0; omega
  have hT1cut : T1 ≤ T := by
    have hc := Nat.le_ceil T1
    have hn : (Nat.ceil T1 : ℝ) + 1 ≤ N := by exact_mod_cast hceil1
    linarith
  have hT2cut : T2 ≤ T := by
    have hc := Nat.le_ceil T2
    have hn : (Nat.ceil T2 : ℝ) + 1 ≤ N := by exact_mod_cast hceil2
    linarith
  have hsepD : TEtaSeparated W T delta := by
    intro t ht u hu htu
    exact (Real.rpow_le_rpow_of_exponent_le hTone hde).trans (hsep t ht u hu htu)
  have hOne : OneSeparated W := by
    intro t ht u hu htu
    exact (Real.one_le_rpow hTone heps.le).trans (hsep t ht u hu htu)
  have hRle := GuthMaynardS3ProfileScaleGrowth.card_le_two_time_of_separation
    hTone heps.le hsep hcontained
  have hdiam : ∀ t ∈ W, ∀ u ∈ W, |t-u| ≤ T := by
    obtain ⟨x, hx⟩ := hcontained
    intro t ht u hu
    obtain ⟨htl, hth⟩ := hx t ht
    obtain ⟨hul, huh⟩ := hx u hu
    rw [abs_le]
    constructor <;> linarith
  have hS1raw := hS1 N W hNnat (by simpa [hTdef] using hT1cut)
    (by simpa [hTdef] using hRle) (by simpa [hTdef] using hsepD) (by simpa [hTdef] using hdiam)
  have hS1norm : ‖sourceS1 N W‖ ≤ 1 := by
    have hh := (GuthMaynardS1MassBridge.norm_sourceS1_le_sourceS1TotalContribution
      (show 0 < N by omega) W).trans hS1raw
    have hp : T ^ (-10 : ℝ) ≤ 1 := by
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_le hTone (by norm_num : (-10 : ℝ) ≤ 0)
    exact hh.trans (by simpa [hTdef] using hp)
  have hS2raw := hS2 T N W hT2cut hNnat hTdef hOne hcontained
  have hS3raw := hS3 N W T sigma b hN3le hTdef hW hsepD hcontained hb hlarge
  have hDNlarge : ∀ t : SourceRow W, (N : ℝ) ^ sigma ≤ ‖sourceDN b N t‖ := by
    intro t
    rw [sourceDN_eq_dirichletPolynomial (by omega) hsupp]
    exact hlarge t t.property
  have htrace := httrace N W T b ((N : ℝ)^sigma)
    hNnat hTone hTN2 hRle hW (by positivity) hsepD hb hDNlarge
  let R : ℝ := W.card
  let A : ℝ := sourceS2SharpShape T N W
  let B : ℝ := T^2 * R^(3 / 2 : ℝ) + T * R * (N : ℝ)^(3 - 2*sigma : ℝ) +
    T^(9 / 8 : ℝ) * R^(29 / 16 : ℝ) * (N : ℝ)^(3 / 2 - sigma : ℝ) +
    T * R^2 * (N : ℝ)^(3 / 2 - sigma : ℝ)
  let M : ℝ := (N : ℝ)^3 + A + B
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  have hA0 : 0 ≤ A := sourceS2SharpShape_nonneg hTp.le N W
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hNM : (N : ℝ)^3 ≤ M := by dsimp [M]; linarith
  have hAM : A ≤ M := by
    have hn : 0 ≤ (N : ℝ)^3 := by positivity
    dsimp [M]
    linarith
  have hBM : B ≤ M := by
    have hn : 0 ≤ (N : ℝ)^3 := by positivity
    dsimp [M]
    linarith
  have hNcube : 1 ≤ (N : ℝ)^3 := one_le_pow₀ hN1
  have hMone : 1 ≤ M := hNcube.trans hNM
  have hTd : 1 ≤ T^delta := Real.one_le_rpow hTone hd.le
  have hMT : M ≤ T^delta * M := by nlinarith
  have hsum : (N : ℝ)^3 + ‖sourceS1 N W‖ + ‖sourceS2 N W‖ + ‖sourceS3 N W‖ ≤
      G * T^delta * M := by
    have hs2 : ‖sourceS2 N W‖ ≤ C2 * T^delta * M :=
      hS2raw.trans (mul_le_mul_of_nonneg_left hAM (by positivity))
    have hs3 : ‖sourceS3 N W‖ ≤ C3 * T^delta * M :=
      hS3raw.trans (mul_le_mul_of_nonneg_left hBM (by positivity))
    have hs1 : ‖sourceS1 N W‖ ≤ T^delta * M := hS1norm.trans (hMone.trans hMT)
    have hn : (N : ℝ)^3 ≤ T^delta * M := hNM.trans hMT
    dsimp [G]
    nlinarith
  have hscale : (N : ℝ)^(6*sigma-3 : ℝ) * (N : ℝ)^3 = ((N : ℝ)^sigma)^6 := by
    calc
      _ = (N : ℝ)^(6*sigma-3 : ℝ) * (N : ℝ)^(3 : ℝ) :=
        congrArg (fun z : ℝ => (N : ℝ)^(6*sigma-3 : ℝ) * z)
          (Real.rpow_natCast (N : ℝ) 3).symm
      _ = (N : ℝ)^((6*sigma-3)+3 : ℝ) := (Real.rpow_add hNp _ _).symm
      _ = (N : ℝ)^(sigma * (6 : ℕ) : ℝ) := by congr 1; push_cast; ring
      _ = _ := Real.rpow_mul_natCast hNp.le sigma 6
  have htraceNorm : R^3 * (N : ℝ)^(6*sigma-3 : ℝ) ≤
      Ct * ((N : ℝ)^3 + ‖sourceS1 N W‖ + ‖sourceS2 N W‖ + ‖sourceS3 N W‖) := by
    apply le_of_mul_le_mul_right _ (pow_pos hNp 3)
    calc
      _ = R^3 * ((N : ℝ)^sigma)^6 := by rw [mul_assoc, hscale]
      _ ≤ Ct * (N : ℝ)^3 *
          ((N : ℝ)^3 + ‖sourceS1 N W‖ + ‖sourceS2 N W‖ + ‖sourceS3 N W‖) := htrace
      _ = _ := by ring
  have hMsum : M = ∑ i : Fin 8,
      (N : ℝ)^(GuthMaynardProp31DirectAbsorption.a sigma i) *
      R^(GuthMaynardProp31DirectAbsorption.b i) := by
    have hh := GuthMaynardProp31SeamMonomials.seam_monomial_identity
      (R := R) (σ := sigma) hNp hTdef
    change (N : ℝ)^(3 : ℝ) +
      ((N : ℝ)^(2 : ℝ) * R^(2 : ℝ) + T * (N : ℝ) * R^(3 / 2 : ℝ) +
        (N : ℝ)^(2 : ℝ) * T^(1 / 4 : ℝ) * R^(13 / 8 : ℝ)) +
      (T^(2 : ℝ) * R^(3 / 2 : ℝ) + T * R * (N : ℝ)^(3 - 2*sigma : ℝ) +
        T^(9 / 8 : ℝ) * R^(29 / 16 : ℝ) * (N : ℝ)^(3 / 2 - sigma : ℝ) +
        T * R^(2 : ℝ) * (N : ℝ)^(3 / 2 - sigma : ℝ)) =
      ∑ i : Fin 8, (N : ℝ)^(GuthMaynardProp31DirectAbsorption.a sigma i) *
        R^(GuthMaynardProp31DirectAbsorption.b i) at hh
    have hn3 : (N : ℝ)^(3 : ℝ) = (N : ℝ)^3 := Real.rpow_natCast (N : ℝ) 3
    have hn2 : (N : ℝ)^(2 : ℝ) = (N : ℝ)^2 := Real.rpow_natCast (N : ℝ) 2
    have hr2 : R^(2 : ℝ) = R^2 := Real.rpow_natCast R 2
    have ht2 : T^(2 : ℝ) = T^2 := Real.rpow_natCast T 2
    rw [hn3, hn2, hr2, ht2] at hh
    exact hh
  have hTdE : T^delta ≤ T^eps := Real.rpow_le_rpow_of_exponent_le hTone hde
  have hprem : R^3 * (N : ℝ)^(6*sigma-3 : ℝ) ≤
      (F * T^eps) * ∑ i : Fin 8,
        (N : ℝ)^(GuthMaynardProp31DirectAbsorption.a sigma i) *
          R^(GuthMaynardProp31DirectAbsorption.b i) := by
    rw [← hMsum]
    calc
      _ ≤ Ct * (G * T^delta * M) := htraceNorm.trans
        (mul_le_mul_of_nonneg_left hsum hCt.le)
      _ = (Ct * G) * T^delta * M := by ring
      _ ≤ F * T^eps * M := by
        apply mul_le_mul_of_nonneg_right _ hM0
        exact mul_le_mul (by dsimp [F]; linarith) hTdE (by positivity) (by positivity)
  have hFeps : 1 ≤ F*T^eps := by
    have hh := Real.one_le_rpow hTone heps.le
    nlinarith
  have hresult := GuthMaynardProp31DirectAbsorption.prop31_direct_absorption hslo
    (by convert hshi using 1 <;> norm_num) hN1 hR0 hFeps hprem
  simpa only [R, GuthMaynardProp31DirectAbsorption.q, mul_assoc] using hresult

end GuthMaynardProp31LargeN
#print axioms GuthMaynardProp31LargeN.exists_actual_prop31_largeN_bound
