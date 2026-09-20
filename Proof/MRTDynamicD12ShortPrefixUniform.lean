import MRTDynamicD12ShortPrefix
import MRTDynamicD12FactorExtraction
import MRTLemma215DynamicTypeIIFiniteEnvelopeV3
namespace MRTDynamicD12ShortPrefix
open scoped BigOperators ArithmeticFunction
open MeasureTheory ArithmeticFunction MixedMellinCert
open MAPHBPerronSourceData MAPDynamicHBSourceV3 MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215DynamicHighPacketCertificateV3
open MAPMRTLemma210OrthogonalityReduction MontgomeryVaughanFiniteReduction
noncomputable section

theorem exists_uniform_shortPrefix (K : ℕ) : ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ,
    ∀ {X delta U : ℝ} {k N q : ℕ} [NeZero q],
    3 ≤ X → 0 ≤ delta → delta ≤ 1 → k < K → 1 ≤ N → 0 ≤ U →
    ∀ (t : ℝ)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k+1))
    (sub : List NatDyadicFactor),
    (∀ f ∈ sub, f ∈ sortedComponentFactorList logIndex zbag mbag) →
    sub.length ≤ 2*K → (N:ℝ) ≤ (2:ℝ)^(2*K)*Real.rpow X delta →
    (∫ v in (t-U)..(t+U), ∑ chi : DirichletCharacter ℂ q,
      (shortPrefixNormField q N (shortPrefixCoefficient zbag mbag sub) chi v)^2) ≤
    C*((q:ℝ)*U+Real.rpow X delta)*(Real.log X)^B := by
  let A : ℝ := 2^(2*K)
  let S : ℝ := ((K^K*Nat.factorial K*Nat.factorial K : ℕ) : ℝ)
  let E : ℕ := 8*K+4*K*K
  let D : ℝ := (1+Real.log (2*A))/Real.log 3+1
  have hA : 0 < A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by dsimp [A]; exact one_le_pow₀ (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hla : 0 ≤ Real.log (2*A) := Real.log_nonneg (by linarith)
  have hD : 0 < D := by dsimp [D]; positivity
  let C : ℝ := (2+8*Real.pi*A)*S^2*D^E+1
  refine ⟨C, by dsimp [C]; positivity, E, ?_⟩
  intro X delta U k N q _ hX hd hd1 hk hN hU t logIndex zbag mbag sub hsub hlen hNX
  have hXp : 0 < X := by linarith
  have hlX : 0 < Real.log X := Real.log_pos (by linarith)
  have hl3X : Real.log 3 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have hR : 0 < Real.rpow X delta := Real.rpow_pos_of_pos hXp _
  let L : ℝ := 1+Real.log (2*(N:ℝ))
  have hL : 1 ≤ L := by
    have := Real.log_nonneg (show 1 ≤ 2*(N:ℝ) by exact_mod_cast (show 1 ≤ 2*N by omega))
    dsimp [L]; linarith
  have hLD : L ≤ D*Real.log X := by
    have hh := Real.log_le_log (show 0 < 2*(N:ℝ) by positivity)
      (show 2*(N:ℝ) ≤ (2*A)*Real.rpow X delta by dsimp [A] at *; nlinarith)
    rw [Real.log_mul (by positivity) (ne_of_gt hR), Real.rpow_eq_pow, Real.log_rpow hXp delta] at hh
    have hdelta : delta*Real.log X ≤ Real.log X := by nlinarith
    have habs : 1+Real.log (2*A) ≤ ((1+Real.log (2*A))/Real.log 3)*Real.log X := by
      calc
        _ = ((1+Real.log (2*A))/Real.log 3)*Real.log 3 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hl3X (by positivity)
    dsimp [L, D]; nlinarith
  have hS : (((K^(k+1)*Nat.factorial k*Nat.factorial (k+1) : ℕ) : ℝ)) ≤ S := by
    have hp := pow_le_pow_right₀ (show 1 ≤ K by omega) (show k+1 ≤ K by omega)
    have hf := Nat.factorial_le (show k ≤ K by omega)
    have hg := Nat.factorial_le (show k+1 ≤ K by omega)
    dsimp [S]; exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul hp hf) hg
  have he : 4*sub.length+sub.length*sub.length ≤ E := by dsimp [E]; nlinarith [Nat.mul_self_le_mul_self hlen]
  have hp : L^(4*sub.length+sub.length*sub.length) ≤ D^E*(Real.log X)^E := by
    calc
      _ ≤ L^E := pow_le_pow_right₀ hL he
      _ ≤ (D*Real.log X)^E := pow_le_pow_left₀ (by linarith) hLD _
      _ = _ := mul_pow _ _ _
  have hscale : (q:ℝ)*(2*U)+8*Real.pi*(N:ℝ) ≤ (2+8*Real.pi*A)*((q:ℝ)*U+Real.rpow X delta) := by
    have hq : 0 ≤ (q:ℝ)*U := by positivity
    have hh : 8*Real.pi*(N:ℝ) ≤ 8*Real.pi*A*Real.rpow X delta := by
      have := mul_le_mul_of_nonneg_left hNX (show 0 ≤ 8*Real.pi by positivity)
      simpa [A, mul_assoc] using this
    nlinarith [Real.pi_pos, mul_nonneg (show 0 ≤ 8*Real.pi*A by positivity) hq]
  have hm := shortPrefix_localMeanSquare (q := q) hN hU t logIndex zbag mbag sub hsub
  calc
    _ ≤ ((q:ℝ)*(2*U)+8*Real.pi*(N:ℝ))*
        (((K^(k+1)*Nat.factorial k*Nat.factorial (k+1) : ℕ) : ℝ))^2 * L^(4*sub.length+sub.length*sub.length) := hm
    _ ≤ ((2+8*Real.pi*A)*((q:ℝ)*U+Real.rpow X delta))*S^2*(D^E*(Real.log X)^E) := by
      apply mul_le_mul _ hp (by positivity) (by positivity)
      exact mul_le_mul hscale (pow_le_pow_left₀ (by positivity) hS 2) (by positivity) (by positivity)
    _ ≤ C*((q:ℝ)*U+Real.rpow X delta)*(Real.log X)^E := by
      calc
        _ = ((2+8*Real.pi*A)*S^2*D^E)*((q:ℝ)*U+Real.rpow X delta)*(Real.log X)^E := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlX.le E)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp [C]; linarith

open MRTLemma215ScaleClassifierV3 MRTLemma215DynamicOutcomeWeldV3
open MRTLemma215DynamicTypeIIFiniteEnvelopeV3

def classifierShortPrefix {X delta : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k+1)) : List NatDyadicFactor :=
  (sortedComponentFactorList logIndex zbag mbag).take
    (largestSmallPrefix (dynamicPreliminaryScaleList (some logIndex) zbag mbag) (Real.rpow X delta))

theorem exists_classifierShortPrefix_localMeanSquare (K : ℕ) : ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ,
    ∀ {X delta U : ℝ} {k q : ℕ} [NeZero q],
    3 ≤ X → 0 ≤ delta → delta ≤ 1 → k < K → 0 ≤ U →
    ∀ (t : ℝ)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k+1)),
    let sub := classifierShortPrefix (delta := delta) logIndex zbag mbag
    (∫ v in (t-U)..(t+U), ∑ chi : DirichletCharacter ℂ q,
      (shortPrefixNormField q (factorUpperProduct sub) (shortPrefixCoefficient zbag mbag sub) chi v)^2) ≤
    C*((q:ℝ)*U+Real.rpow X delta)*(Real.log X)^B := by
  obtain ⟨C, hC, B, h⟩ := exists_uniform_shortPrefix K
  refine ⟨C, hC, B, ?_⟩
  intro X delta U k q _ hX hd hd1 hk hU t logIndex zbag mbag
  let sub := classifierShortPrefix (delta := delta) logIndex zbag mbag
  have hsub : ∀ f ∈ sub, f ∈ sortedComponentFactorList logIndex zbag mbag := by
    intro f hf
    exact List.mem_of_mem_take hf
  have hlen : sub.length ≤ 2*K := by
    have hh := sortedComponentFactorList_length_le logIndex zbag mbag
    have ht := List.length_take_le (largestSmallPrefix (dynamicPreliminaryScaleList (some logIndex) zbag mbag) (Real.rpow X delta)) (sortedComponentFactorList logIndex zbag mbag)
    dsimp [sub, classifierShortPrefix]
    simp only [List.length_take]
    omega
  have hone : ∀ f ∈ sub, 1 ≤ f.length := by
    intro f hf
    exact dynamicComponentFactorList_length_one logIndex zbag mbag (hsub f hf)
  have hpos : ∀ (l : List NatDyadicFactor), (∀ f ∈ l, 1 ≤ f.length) → 1 ≤ factorUpperProduct l := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons f fs ih =>
      intro hone
      rw [factorUpperProduct_cons]
      have hf := hone f (by simp)
      have hs := ih (fun g hg => hone g (by simp [hg]))
      nlinarith
  have hN := hpos sub hone
  have hupper := (MRTDynamicD12FactorExtraction.smallPrefix_upperProduct_le (by linarith : 1 ≤ X) hd logIndex zbag mbag).2
  have hNX : (factorUpperProduct sub : ℝ) ≤ (2:ℝ)^(2*K)*Real.rpow X delta := by
    exact hupper.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hlen) (Real.rpow_nonneg (by linarith) _))
  exact h hX hd hd1 hk hN hU t logIndex zbag mbag sub hsub hlen hNX
end
end MRTDynamicD12ShortPrefix
#print axioms MRTDynamicD12ShortPrefix.exists_uniform_shortPrefix

#print axioms MRTDynamicD12ShortPrefix.exists_classifierShortPrefix_localMeanSquare
