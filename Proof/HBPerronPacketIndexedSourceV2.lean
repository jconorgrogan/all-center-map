import MAPHBPerronSourceData
import MAPPacketIndexedFarSourceV2

/-!
# Packet-indexed HB/Perron source constructor

Each literal dyadic packet has its own short factor.  The sole finite source
datum is an exact identity of the corresponding critical-line polynomials.
This file proves the character-window Cauchy loss, absorbs the outer eight-term
HB loss by coefficient scaling, and emits the packet-indexed V2 cells.
-/

namespace HBPerronPacketIndexedSourceV2

set_option maxHeartbeats 1200000

open scoped BigOperators
open MeasureTheory
open MixedMeanFrontend DeterminantCountWeld
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary25TypeD1IntegratedWeld
open MAPMRTCorollary25Minkowski
open MAPMRTCorollary53Source
open MAPMRTProposition51Source
open MAPHBPerronSourceData
open MAPPacketIndexedFarSourceV2

noncomputable section

/-- The source-faithful low branches of MRT Lemmas 2.15--2.16.  They are
kept separate so their published second/fourth-moment budgets cannot be
silently replaced by the high-packet mixed-mean estimate. -/
inductive HBRemainderKind where
  | typeII
  | typeD1
  | typeD2
  | unitScale
  | smallTerm
deriving DecidableEq

instance : Fintype HBRemainderKind where
  elems := {.typeII, .typeD1, .typeD2, .unitScale, .smallTerm}
  complete := by
    intro kind
    cases kind <;> simp

def scaleNatCoefficient (c : ℝ) (f : ℕ → ℂ) : ℕ → ℂ :=
  fun n => (c : ℂ) * f n

theorem scaleNatCoefficient_supported
    {M : ℕ} {c : ℝ} {f : ℕ → ℂ}
    (hf : SupportedNatDyadic M f) :
    SupportedNatDyadic M (scaleNatCoefficient c f) := by
  intro n hn
  unfold scaleNatCoefficient
  rw [hf n hn]
  simp

theorem literalDirichletConvolution_scale_left
    (c : ℝ) (alpha beta : ℕ → ℂ) (n : ℕ) :
    literalDirichletConvolution (scaleNatCoefficient c alpha) beta n =
      (c : ℂ) * literalDirichletConvolution alpha beta n := by
  unfold literalDirichletConvolution scaleNatCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem typeD1ClippedNorm_scale_left
    {q N M : ℕ} {X1 X2 c t : ℝ} {alpha beta : ℕ → ℂ}
    (hc : 0 ≤ c) (chi : DirichletCharacter ℂ q) :
    typeD1ClippedNorm (N : ℝ) (M : ℝ) X1 X2
        (fun chi : DirichletCharacter ℂ q => fun n => chi n)
        (scaleNatCoefficient c alpha) beta chi t =
      c * typeD1ClippedNorm (N : ℝ) (M : ℝ) X1 X2
        (fun chi : DirichletCharacter ℂ q => fun n => chi n)
        alpha beta chi t := by
  unfold typeD1ClippedNorm halfLineDirichletPolynomial
  have hpoly :
      (∑ n ∈ Finset.Icc 1 (Nat.ceil (4 * ((N : ℝ) * M))),
        intervalCutoff X1 X2
            (characterTwist (fun n => chi n)
              (literalDirichletConvolution
                (scaleNatCoefficient c alpha) beta)) n /
          (Real.sqrt (n : ℝ) : ℂ) * mellinPhase n t) =
        (c : ℂ) *
          ∑ n ∈ Finset.Icc 1 (Nat.ceil (4 * ((N : ℝ) * M))),
            intervalCutoff X1 X2
                (characterTwist (fun n => chi n)
                  (literalDirichletConvolution alpha beta)) n /
              (Real.sqrt (n : ℝ) : ℂ) * mellinPhase n t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    unfold intervalCutoff characterTwist
    split_ifs
    · rw [literalDirichletConvolution_scale_left]
      ring
    · ring
  rw [hpoly, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]

theorem characterMovingMass_scale_left
    {q N M : ℕ} {X1 X2 c U t : ℝ} {alpha beta : ℕ → ℂ}
    (hc : 0 ≤ c) :
    characterMovingMass
        (typeD1ClippedNorm (N : ℝ) (M : ℝ) X1 X2
          (fun chi : DirichletCharacter ℂ q => fun n => chi n)
          (scaleNatCoefficient c alpha) beta) U t =
      c * characterMovingMass
        (typeD1ClippedNorm (N : ℝ) (M : ℝ) X1 X2
          (fun chi : DirichletCharacter ℂ q => fun n => chi n)
          alpha beta) U t := by
  unfold characterMovingMass movingIntegral
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro chi hchi
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  exact typeD1ClippedNorm_scale_left hc chi

/-- Literal packetwise HB classification at the exact critical polynomial
consumed by the far branch.  It is an equality, not a bound or a reformulation
of the final source estimate. -/
structure HBDyadicPolynomialClassification (p : Corollary53Input) where
  blockCount : CutoffBranch → ℕ
  remainderCoeff : CutoffBranch → HBRemainderKind → ℕ → ℂ
  shortLength : (branch : CutoffBranch) → Fin (blockCount branch) → ℕ
  longLength : (branch : CutoffBranch) → Fin (blockCount branch) → ℕ
  shortCoeff : (branch : CutoffBranch) →
    Fin (blockCount branch) → ℕ → ℂ
  longCoeff : (branch : CutoffBranch) →
    Fin (blockCount branch) → ℕ → ℂ
  perronHeight : (branch : CutoffBranch) →
    Fin (blockCount branch) → ℝ
  coefficientBound : (branch : CutoffBranch) →
    Fin (blockCount branch) → ℝ
  shortLength_one : ∀ branch i, 1 ≤ shortLength branch i
  longLength_one : ∀ branch i, 1 ≤ longLength branch i
  perronHeight_one : ∀ branch i, 1 ≤ perronHeight branch i
  coefficientBound_nonneg : ∀ branch i, 0 ≤ coefficientBound branch i
  shortSupport : ∀ branch i,
    SupportedNatDyadic (shortLength branch i) (shortCoeff branch i)
  longSupport : ∀ branch i,
    SupportedNatDyadic (longLength branch i) (longCoeff branch i)
  convolutionBound : ∀ branch i n,
    ‖literalDirichletConvolution
      (longCoeff branch i) (shortCoeff branch i) n‖ ≤
        coefficientBound branch i
  polynomialIdentity : ∀ branch (chi : DirichletCharacter ℂ p.q) t,
    criticalDirichletPolynomial p.X 1 p.q (hbBranchCoeff p.X branch) chi t =
      criticalDirichletPolynomial p.X 1 p.q
        (fun n => ∑ kind : HBRemainderKind, remainderCoeff branch kind n) chi t +
        ∑ i : Fin (blockCount branch),
          halfLineDirichletPolynomial
            ((longLength branch i : ℝ) * shortLength branch i) 4
            (intervalCutoff p.X (2 * p.X)
              (characterTwist (fun n => chi n)
                (literalDirichletConvolution
                  (longCoeff branch i) (shortCoeff branch i)))) t

def packetScale (data : HBDyadicPolynomialClassification p)
    (branch : CutoffBranch) : ℝ :=
  Real.sqrt (16 * data.blockCount branch)

theorem packetScale_nonneg (data : HBDyadicPolynomialClassification p)
    (branch : CutoffBranch) : 0 ≤ packetScale data branch := by
  unfold packetScale
  positivity

theorem packetScale_sq (data : HBDyadicPolynomialClassification p)
    (branch : CutoffBranch) :
    packetScale data branch ^ 2 = 16 * data.blockCount branch := by
  unfold packetScale
  rw [Real.sq_sqrt]
  positivity

def scaledLongCoeff (data : HBDyadicPolynomialClassification p)
    (branch : CutoffBranch) (i : Fin (data.blockCount branch)) : ℕ → ℂ :=
  scaleNatCoefficient (packetScale data branch) (data.longCoeff branch i)

def scaledCoefficientBound (data : HBDyadicPolynomialClassification p)
    (branch : CutoffBranch) (i : Fin (data.blockCount branch)) : ℝ :=
  packetScale data branch * data.coefficientBound branch i

def combinedRemainderCoeff (data : HBDyadicPolynomialClassification p)
    (branch : CutoffBranch) : ℕ → ℂ :=
  fun n => ∑ kind : HBRemainderKind, data.remainderCoeff branch kind n

/-- The literal low-type/small-term mass left outside the high packet family.
It remains visible in the expanded budget and is the consumer of the MRT
second/fourth-moment inputs. -/
def remainderSourceMass (p : Corollary53Input)
    (data : HBDyadicPolynomialClassification p)
    (component : OuterComponent) (branch : CutoffBranch) : ℝ :=
  ∑ kind : HBRemainderKind,
    80 * componentIntegral p.X p.H 1 p.q (data.remainderCoeff branch kind)
      p.beta p.eta component

theorem combinedRemainderMass_le_remainderSourceMass
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    (data : HBDyadicPolynomialClassification p)
    (component : OuterComponent) (branch : CutoffBranch) :
    16 * componentIntegral p.X p.H 1 p.q
        (combinedRemainderCoeff data branch) p.beta p.eta component ≤
      remainderSourceMass p data component branch := by
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.1
  have hX : 0 ≤ p.X := hH.trans hp.2.1
  have hraw := componentIntegral_finset_sum_le
    (Finset.univ : Finset HBRemainderKind)
    (fun kind => data.remainderCoeff branch kind)
    (beta := p.beta) (q₀ := 1) (q₁ := p.q)
    hX hH hp.2.2.2.2.1 hp.2.2.2.2.2.1 component
  unfold combinedRemainderCoeff remainderSourceMass
  have hcardNat : (Finset.univ : Finset HBRemainderKind).card = 5 := by
    decide
  have hcard : ((Finset.univ : Finset HBRemainderKind).card : ℝ) = 5 := by
    exact_mod_cast hcardNat
  rw [hcard] at hraw
  calc
    16 * componentIntegral p.X p.H 1 p.q
        (fun n => ∑ kind : HBRemainderKind, data.remainderCoeff branch kind n)
        p.beta p.eta component ≤
      16 * (5 * ∑ kind : HBRemainderKind,
        componentIntegral p.X p.H 1 p.q (data.remainderCoeff branch kind)
          p.beta p.eta component) := by gcongr
    _ = ∑ kind : HBRemainderKind,
        80 * componentIntegral p.X p.H 1 p.q (data.remainderCoeff branch kind)
          p.beta p.eta component := by
      rw [show 16 * (5 * ∑ kind : HBRemainderKind,
          componentIntegral p.X p.H 1 p.q (data.remainderCoeff branch kind)
            p.beta p.eta component) =
        (∑ kind : HBRemainderKind,
          componentIntegral p.X p.H 1 p.q (data.remainderCoeff branch kind)
            p.beta p.eta component) * 80 by ring]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro kind hkind
      ring

theorem characterWindow_hb_le_remainder_add_packetMovingMass
    {p : Corollary53Input} (hH : 0 ≤ p.H)
    (data : HBDyadicPolynomialClassification p)
    (branch : CutoffBranch) (t : ℝ) :
    characterWindow p.X 1 p.q (hbBranchCoeff p.X branch)
        p.beta p.H t ≤
      characterWindow p.X 1 p.q (combinedRemainderCoeff data branch)
          p.beta p.H t +
        ∑ i : Fin (data.blockCount branch),
          characterMovingMass
            (typeD1ClippedNorm
              (data.longLength branch i : ℝ)
              (data.shortLength branch i : ℝ) p.X (2 * p.X)
              (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
              (data.longCoeff branch i) (data.shortCoeff branch i))
            (stationaryWidth p.beta p.H) t := by
  have hU : 0 ≤ stationaryWidth p.beta p.H := by
    unfold stationaryWidth
    positivity
  have horder : t - stationaryWidth p.beta p.H ≤
      t + stationaryWidth p.beta p.H := by linarith
  unfold characterWindow characterMovingMass movingIntegral stationaryWidth
  calc
    (∑ chi : DirichletCharacter ℂ p.q,
      ∫ s in (t - |p.beta| * p.H)..(t + |p.beta| * p.H),
        ‖criticalDirichletPolynomial p.X 1 p.q
          (hbBranchCoeff p.X branch) chi s‖) ≤
      ∑ chi : DirichletCharacter ℂ p.q,
        ∫ s in (t - |p.beta| * p.H)..(t + |p.beta| * p.H),
          ‖criticalDirichletPolynomial p.X 1 p.q
              (combinedRemainderCoeff data branch) chi s‖ +
            ∑ i : Fin (data.blockCount branch),
              typeD1ClippedNorm
                (data.longLength branch i : ℝ)
                (data.shortLength branch i : ℝ) p.X (2 * p.X)
                (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
                (data.longCoeff branch i) (data.shortCoeff branch i) chi s := by
        apply Finset.sum_le_sum
        intro chi hchi
        apply intervalIntegral.integral_mono_on horder
        · exact (continuous_norm_criticalDirichletPolynomial p.X 1 p.q
            (hbBranchCoeff p.X branch) chi).intervalIntegrable _ _
        · exact ((continuous_norm_criticalDirichletPolynomial p.X 1 p.q
              (combinedRemainderCoeff data branch) chi).add
            (continuous_finsetSum Finset.univ fun i hi =>
              continuous_typeD1ClippedNorm
                (data.longLength branch i : ℝ)
                (data.shortLength branch i : ℝ) p.X (2 * p.X)
                (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
                (data.longCoeff branch i) (data.shortCoeff branch i) chi))
            |>.intervalIntegrable _ _
        · intro s hs
          rw [data.polynomialIdentity branch chi s]
          unfold combinedRemainderCoeff
          apply (norm_add_le _ _).trans
          gcongr
          simpa [typeD1ClippedNorm] using
            (norm_sum_le (Finset.univ : Finset (Fin (data.blockCount branch)))
              (fun i => halfLineDirichletPolynomial
                ((data.longLength branch i : ℝ) * data.shortLength branch i) 4
                (intervalCutoff p.X (2 * p.X)
                  (characterTwist (fun n => chi n)
                    (literalDirichletConvolution
                      (data.longCoeff branch i) (data.shortCoeff branch i)))) s))
    _ = ∑ chi : DirichletCharacter ℂ p.q,
        ((∫ s in (t - |p.beta| * p.H)..(t + |p.beta| * p.H),
            ‖criticalDirichletPolynomial p.X 1 p.q
              (combinedRemainderCoeff data branch) chi s‖) +
          ∑ i : Fin (data.blockCount branch),
            ∫ s in (t - |p.beta| * p.H)..(t + |p.beta| * p.H),
              typeD1ClippedNorm
                (data.longLength branch i : ℝ)
                (data.shortLength branch i : ℝ) p.X (2 * p.X)
                (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
                (data.longCoeff branch i) (data.shortCoeff branch i) chi s) := by
      apply Finset.sum_congr rfl
      intro chi hchi
      rw [intervalIntegral.integral_add]
      · congr 1
        rw [intervalIntegral.integral_finsetSum]
        intro i hi
        exact (continuous_typeD1ClippedNorm
          (data.longLength branch i : ℝ)
          (data.shortLength branch i : ℝ) p.X (2 * p.X)
          (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
          (data.longCoeff branch i) (data.shortCoeff branch i) chi)
          |>.intervalIntegrable _ _
      · exact (continuous_norm_criticalDirichletPolynomial p.X 1 p.q
          (combinedRemainderCoeff data branch) chi).intervalIntegrable _ _
      · exact (continuous_finsetSum Finset.univ fun i hi =>
          continuous_typeD1ClippedNorm
            (data.longLength branch i : ℝ)
            (data.shortLength branch i : ℝ) p.X (2 * p.X)
            (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
            (data.longCoeff branch i) (data.shortCoeff branch i) chi)
          |>.intervalIntegrable _ _
    _ = (∑ chi : DirichletCharacter ℂ p.q,
          ∫ s in (t - |p.beta| * p.H)..(t + |p.beta| * p.H),
            ‖criticalDirichletPolynomial p.X 1 p.q
              (combinedRemainderCoeff data branch) chi s‖) +
        ∑ chi : DirichletCharacter ℂ p.q,
          ∑ i : Fin (data.blockCount branch),
            ∫ s in (t - |p.beta| * p.H)..(t + |p.beta| * p.H),
              typeD1ClippedNorm
                (data.longLength branch i : ℝ)
                (data.shortLength branch i : ℝ) p.X (2 * p.X)
                (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
                (data.longCoeff branch i) (data.shortCoeff branch i) chi s := by
      rw [Finset.sum_add_distrib]
    _ = (∑ chi : DirichletCharacter ℂ p.q,
          ∫ s in (t - |p.beta| * p.H)..(t + |p.beta| * p.H),
            ‖criticalDirichletPolynomial p.X 1 p.q
              (combinedRemainderCoeff data branch) chi s‖) +
        ∑ i : Fin (data.blockCount branch),
          ∑ chi : DirichletCharacter ℂ p.q,
            ∫ s in (t - |p.beta| * p.H)..(t + |p.beta| * p.H),
              typeD1ClippedNorm
                (data.longLength branch i : ℝ)
                (data.shortLength branch i : ℝ) p.X (2 * p.X)
                (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
                (data.longCoeff branch i) (data.shortCoeff branch i) chi s := by
      congr 1
      rw [Finset.sum_comm]
    _ = _ := rfl

theorem hbSourceMass_le_packetIndexedScaled
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    (data : HBDyadicPolynomialClassification p)
    (component : OuterComponent) (branch : CutoffBranch) :
    hbSourceMass p component (.cutoff branch) ≤
      remainderSourceMass p data component branch +
        ∑ i : Fin (data.blockCount branch),
          ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
            (componentEndpoints p.X p.beta p.eta component).2,
            (characterMovingMass
              (typeD1ClippedNorm
                (data.longLength branch i : ℝ)
                (data.shortLength branch i : ℝ) p.X (2 * p.X)
                (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
                (scaledLongCoeff data branch i) (data.shortCoeff branch i))
              (stationaryWidth p.beta p.H) t) ^ 2 := by
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.1
  have hX : 0 ≤ p.X := hH.trans hp.2.1
  have heta : 0 < p.eta := hp.2.2.2.2.1
  have hetaOne : p.eta ≤ 1 := hp.2.2.2.2.2.1
  have hend := componentEndpoints_mono (beta := p.beta)
    hX heta hetaOne component
  let W : ℝ → ℝ := fun t => characterWindow p.X 1 p.q
    (hbBranchCoeff p.X branch) p.beta p.H t
  let R : ℝ → ℝ := fun t => characterWindow p.X 1 p.q
    (combinedRemainderCoeff data branch) p.beta p.H t
  let P : Fin (data.blockCount branch) → ℝ → ℝ := fun i t =>
    characterMovingMass
      (typeD1ClippedNorm
        (data.longLength branch i : ℝ) (data.shortLength branch i : ℝ)
        p.X (2 * p.X)
        (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
        (data.longCoeff branch i) (data.shortCoeff branch i))
      (stationaryWidth p.beta p.H) t
  have hpoint : ∀ t, W t ^ 2 ≤ 2 * R t ^ 2 +
      2 * (data.blockCount branch : ℝ) * ∑ i, P i t ^ 2 := by
    intro t
    have hW0 : 0 ≤ W t := characterWindow_nonneg
      (mul_nonneg (abs_nonneg _) hH)
    have hle : W t ≤ R t + ∑ i, P i t :=
      characterWindow_hb_le_remainder_add_packetMovingMass hH data branch t
    have hcauchy : (∑ i : Fin (data.blockCount branch), P i t) ^ 2 ≤
        (data.blockCount branch : ℝ) * ∑ i, P i t ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin (data.blockCount branch))))
        (f := fun i => P i t))
    have hsq : W t ^ 2 ≤ (R t + ∑ i, P i t) ^ 2 :=
      pow_le_pow_left₀ hW0 hle 2
    have htwo : (R t + ∑ i, P i t) ^ 2 ≤
        2 * R t ^ 2 + 2 * (∑ i, P i t) ^ 2 := by
      nlinarith [sq_nonneg (R t - ∑ i, P i t)]
    have hmul : 2 * (∑ i, P i t) ^ 2 ≤
        2 * ((data.blockCount branch : ℝ) * ∑ i, P i t ^ 2) :=
      mul_le_mul_of_nonneg_left hcauchy (by norm_num)
    exact hsq.trans (htwo.trans (by
      have := add_le_add_left hmul (2 * R t ^ 2)
      simpa [mul_assoc] using this))
  have hintegral :
      componentIntegral p.X p.H 1 p.q (hbBranchCoeff p.X branch)
          p.beta p.eta component ≤
        2 * componentIntegral p.X p.H 1 p.q (combinedRemainderCoeff data branch)
            p.beta p.eta component +
          2 * (data.blockCount branch : ℝ) * ∑ i,
            ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
              (componentEndpoints p.X p.beta p.eta component).2, P i t ^ 2 := by
    unfold componentIntegral
    change
      (∫ t in (componentEndpoints p.X p.beta p.eta component).1..
        (componentEndpoints p.X p.beta p.eta component).2, W t ^ 2) ≤
      2 * componentIntegral p.X p.H 1 p.q (combinedRemainderCoeff data branch)
          p.beta p.eta component +
        2 * (data.blockCount branch : ℝ) * ∑ i,
          ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
            (componentEndpoints p.X p.beta p.eta component).2, P i t ^ 2
    calc
      (∫ t in (componentEndpoints p.X p.beta p.eta component).1..
          (componentEndpoints p.X p.beta p.eta component).2,
          characterWindow p.X 1 p.q (hbBranchCoeff p.X branch)
            p.beta p.H t ^ 2) ≤
        ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
          (componentEndpoints p.X p.beta p.eta component).2,
          2 * R t ^ 2 + 2 * (data.blockCount branch : ℝ) *
            ∑ i, P i t ^ 2 := by
        apply intervalIntegral.integral_mono_on hend
        · exact (continuous_characterWindow p.X p.H 1 p.q
            (hbBranchCoeff p.X branch) p.beta).pow 2 |>.intervalIntegrable _ _
        · apply Continuous.intervalIntegrable
          apply Continuous.add
          · exact continuous_const.mul
              ((continuous_characterWindow p.X p.H 1 p.q
                (combinedRemainderCoeff data branch) p.beta).pow 2)
          · apply Continuous.mul
            · fun_prop
            · exact continuous_finsetSum Finset.univ fun i hi => by
                unfold P
                exact (continuous_characterMovingMass
                  (fun chi => continuous_typeD1ClippedNorm
                    (data.longLength branch i : ℝ)
                    (data.shortLength branch i : ℝ) p.X (2 * p.X)
                    (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
                    (data.longCoeff branch i) (data.shortCoeff branch i) chi)
                  (stationaryWidth p.beta p.H)).pow 2
        · intro t ht
          exact hpoint t
      _ = 2 * (∫ t in (componentEndpoints p.X p.beta p.eta component).1..
            (componentEndpoints p.X p.beta p.eta component).2, R t ^ 2) +
          2 * (data.blockCount branch : ℝ) *
            (∫ t in (componentEndpoints p.X p.beta p.eta component).1..
              (componentEndpoints p.X p.beta p.eta component).2,
              ∑ i, P i t ^ 2) := by
        have hRint : IntervalIntegrable (fun t => 2 * R t ^ 2) volume
            (componentEndpoints p.X p.beta p.eta component).1
            (componentEndpoints p.X p.beta p.eta component).2 := by
          exact (continuous_const.mul
            ((continuous_characterWindow p.X p.H 1 p.q
              (combinedRemainderCoeff data branch) p.beta).pow 2)).intervalIntegrable _ _
        have hPint : IntervalIntegrable
            (fun t => 2 * (data.blockCount branch : ℝ) * ∑ i, P i t ^ 2)
            volume (componentEndpoints p.X p.beta p.eta component).1
            (componentEndpoints p.X p.beta p.eta component).2 := by
          apply Continuous.intervalIntegrable
          apply Continuous.mul
          · fun_prop
          · exact continuous_finsetSum Finset.univ fun i hi => by
              unfold P
              exact (continuous_characterMovingMass
                (fun chi => continuous_typeD1ClippedNorm
                  (data.longLength branch i : ℝ)
                  (data.shortLength branch i : ℝ) p.X (2 * p.X)
                  (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
                  (data.longCoeff branch i) (data.shortCoeff branch i) chi)
                (stationaryWidth p.beta p.H)).pow 2
        rw [intervalIntegral.integral_add hRint hPint,
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
      _ = 2 * componentIntegral p.X p.H 1 p.q
            (combinedRemainderCoeff data branch) p.beta p.eta component +
          2 * (data.blockCount branch : ℝ) * ∑ i,
            ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
              (componentEndpoints p.X p.beta p.eta component).2, P i t ^ 2 := by
        unfold componentIntegral
        congr 1
        rw [intervalIntegral.integral_finsetSum]
        intro i hi
        unfold P
        exact (continuous_characterMovingMass
          (fun chi => continuous_typeD1ClippedNorm
            (data.longLength branch i : ℝ)
            (data.shortLength branch i : ℝ) p.X (2 * p.X)
            (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
            (data.longCoeff branch i) (data.shortCoeff branch i) chi)
          (stationaryWidth p.beta p.H)).pow 2 |>.intervalIntegrable _ _
  unfold hbSourceMass
  calc
    8 * componentIntegral p.X p.H 1 p.q (hbBranchCoeff p.X branch)
        p.beta p.eta component ≤
      8 * (2 * componentIntegral p.X p.H 1 p.q
          (combinedRemainderCoeff data branch) p.beta p.eta component +
        2 * (data.blockCount branch : ℝ) * ∑ i,
          ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
            (componentEndpoints p.X p.beta p.eta component).2, P i t ^ 2) := by
      gcongr
    _ = 16 * componentIntegral p.X p.H 1 p.q
          (combinedRemainderCoeff data branch) p.beta p.eta component +
      ∑ i : Fin (data.blockCount branch),
        ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
          (componentEndpoints p.X p.beta p.eta component).2,
          (characterMovingMass
            (typeD1ClippedNorm
              (data.longLength branch i : ℝ)
              (data.shortLength branch i : ℝ) p.X (2 * p.X)
              (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
              (scaledLongCoeff data branch i) (data.shortCoeff branch i))
            (stationaryWidth p.beta p.H) t) ^ 2 := by
      rw [show 8 * (2 * componentIntegral p.X p.H 1 p.q
          (combinedRemainderCoeff data branch) p.beta p.eta component +
          2 * (data.blockCount branch : ℝ) * ∑ i,
          ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
            (componentEndpoints p.X p.beta p.eta component).2, P i t ^ 2) =
        16 * componentIntegral p.X p.H 1 p.q
            (combinedRemainderCoeff data branch) p.beta p.eta component +
          (16 * data.blockCount branch) * ∑ i,
          ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
            (componentEndpoints p.X p.beta p.eta component).2, P i t ^ 2 by ring]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      change
        16 * (data.blockCount branch : ℝ) * P i t ^ 2 =
          characterMovingMass
            (typeD1ClippedNorm
              (data.longLength branch i : ℝ)
              (data.shortLength branch i : ℝ) p.X (2 * p.X)
              (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
              (scaleNatCoefficient (packetScale data branch)
                (data.longCoeff branch i)) (data.shortCoeff branch i))
            (stationaryWidth p.beta p.H) t ^ 2
      rw [characterMovingMass_scale_left (packetScale_nonneg data branch)]
      rw [mul_pow, packetScale_sq]
    _ ≤ remainderSourceMass p data component branch +
      ∑ i : Fin (data.blockCount branch),
        ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
          (componentEndpoints p.X p.beta p.eta component).2,
          (characterMovingMass
            (typeD1ClippedNorm
              (data.longLength branch i : ℝ)
              (data.shortLength branch i : ℝ) p.X (2 * p.X)
              (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
              (scaledLongCoeff data branch i) (data.shortCoeff branch i))
            (stationaryWidth p.beta p.H) t) ^ 2 :=
      add_le_add (combinedRemainderMass_le_remainderSourceMass hp data
        component branch) le_rfl

/-- Exact packet-indexed HB family with `sourceBound` now a theorem of the
classification rather than a caller premise. -/
structure HBPerronPacketFamilyV2 (p : Corollary53Input) where
  blockCount : OuterComponent → CutoffBranch → ℕ
  sourceError : OuterComponent → CutoffBranch → ℝ
  shortLength : (component : OuterComponent) → (branch : CutoffBranch) →
    Fin (blockCount component branch) → ℕ
  longLength : (component : OuterComponent) → (branch : CutoffBranch) →
    Fin (blockCount component branch) → ℕ
  shortCoeff : (component : OuterComponent) → (branch : CutoffBranch) →
    Fin (blockCount component branch) → ℕ → ℂ
  longCoeff : (component : OuterComponent) → (branch : CutoffBranch) →
    Fin (blockCount component branch) → ℕ → ℂ
  perronHeight : (component : OuterComponent) → (branch : CutoffBranch) →
    Fin (blockCount component branch) → ℝ
  coefficientBound : (component : OuterComponent) → (branch : CutoffBranch) →
    Fin (blockCount component branch) → ℝ
  shortLength_one : ∀ component branch i, 1 ≤ shortLength component branch i
  longLength_one : ∀ component branch i, 1 ≤ longLength component branch i
  perronHeight_one : ∀ component branch i, 1 ≤ perronHeight component branch i
  coefficientBound_nonneg : ∀ component branch i,
    0 ≤ coefficientBound component branch i
  shortSupport : ∀ component branch i,
    SupportedNatDyadic (shortLength component branch i)
      (shortCoeff component branch i)
  longSupport : ∀ component branch i,
    SupportedNatDyadic (longLength component branch i)
      (longCoeff component branch i)
  convolutionBound : ∀ component branch i n,
    ‖literalDirichletConvolution
      (longCoeff component branch i) (shortCoeff component branch i) n‖ ≤
        coefficientBound component branch i
  sourceBound : ∀ component branch,
    hbSourceMass p component (.cutoff branch) ≤
      sourceError component branch +
        ∑ i : Fin (blockCount component branch),
        ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
          (componentEndpoints p.X p.beta p.eta component).2,
          (characterMovingMass
            (typeD1ClippedNorm
              (longLength component branch i : ℝ)
              (shortLength component branch i : ℝ) p.X (2 * p.X)
              (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
              (longCoeff component branch i) (shortCoeff component branch i))
            (stationaryWidth p.beta p.H) t) ^ 2

def packetFamilyV2OfClassification
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    (data : HBDyadicPolynomialClassification p) : HBPerronPacketFamilyV2 p where
  blockCount := fun _ branch => data.blockCount branch
  sourceError := fun component branch => remainderSourceMass p data component branch
  shortLength := fun _ branch => data.shortLength branch
  longLength := fun _ branch => data.longLength branch
  shortCoeff := fun _ branch => data.shortCoeff branch
  longCoeff := fun _ branch => scaledLongCoeff data branch
  perronHeight := fun _ branch => data.perronHeight branch
  coefficientBound := fun _ branch => scaledCoefficientBound data branch
  shortLength_one := fun _ branch i => data.shortLength_one branch i
  longLength_one := fun _ branch i => data.longLength_one branch i
  perronHeight_one := fun _ branch i => data.perronHeight_one branch i
  coefficientBound_nonneg := fun _ branch i =>
    mul_nonneg (packetScale_nonneg data branch)
      (data.coefficientBound_nonneg branch i)
  shortSupport := fun _ branch i => data.shortSupport branch i
  longSupport := fun _ branch i =>
    scaleNatCoefficient_supported (data.longSupport branch i)
  convolutionBound := fun _ branch i n => by
    unfold scaledLongCoeff scaledCoefficientBound
    rw [literalDirichletConvolution_scale_left, norm_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (packetScale_nonneg data branch)]
    exact mul_le_mul_of_nonneg_left (data.convolutionBound branch i n)
      (packetScale_nonneg data branch)
  sourceBound := hbSourceMass_le_packetIndexedScaled hp data

end
end HBPerronPacketIndexedSourceV2

#print axioms HBPerronPacketIndexedSourceV2.characterWindow_hb_le_remainder_add_packetMovingMass
#print axioms HBPerronPacketIndexedSourceV2.hbSourceMass_le_packetIndexedScaled
#print axioms HBPerronPacketIndexedSourceV2.packetFamilyV2OfClassification
