import FordNearIntegerCount
import Mathlib.Algebra.Order.Round

open scoped BigOperators
open FordNearIntegerCount

namespace FordDirichletShells
noncomputable section

/-- Integer differences satisfying the strict bound `|d| < K`. -/
def diffSet (K : ℕ) : Finset ℤ :=
  Finset.Icc (-(K : ℤ) + 1) ((K : ℤ) - 1)

/-- Distance of the real frequency to the nearest integer selected by `round`. -/
def roundDist (gamma : ℝ) (d : ℤ) : ℝ :=
  |(d : ℝ) * gamma - (round ((d : ℝ) * gamma) : ℝ)|

lemma mem_diffSet_iff {K : ℕ} {d : ℤ} (hK : 2 ≤ K) :
    d ∈ diffSet K ↔ |d| < (K : ℤ) := by
  simp only [diffSet, Finset.mem_Icc]
  constructor
  · intro h
    rw [abs_lt]
    constructor <;> omega
  · intro h
    rw [abs_lt] at h
    constructor <;> omega

lemma roundDist_nonneg (gamma : ℝ) (d : ℤ) : 0 ≤ roundDist gamma d := by
  exact abs_nonneg _

lemma roundDist_le_half (gamma : ℝ) (d : ℤ) : roundDist gamma d ≤ (1 : ℝ) / 2 := by
  unfold roundDist
  rw [abs_sub_round_eq_min]
  have hf0 := Int.fract_nonneg ((d : ℝ) * gamma)
  have hf1 := Int.fract_lt_one ((d : ℝ) * gamma)
  have hmin : min (Int.fract ((d : ℝ) * gamma))
      (1 - Int.fract ((d : ℝ) * gamma)) ≤ (1 : ℝ) / 2 := by
    by_cases h : Int.fract ((d : ℝ) * gamma) ≤ (1 : ℝ) / 2
    · exact min_le_left _ _ |>.trans h
    · have hh : (1 : ℝ) - Int.fract ((d : ℝ) * gamma) ≤ (1 : ℝ) / 2 := by linarith
      exact min_le_right _ _ |>.trans hh
  exact hmin

lemma round_filter_subset_near
    {K : ℕ} {gamma delta : ℝ} (hK : 2 ≤ K)
    (hdelta : 0 < delta) :
    (diffSet K).filter (fun d => roundDist gamma d < delta) ⊆
      nearIntegerSet K gamma delta := by
  classical
  intro d hd
  have hdS : d ∈ diffSet K := (Finset.mem_filter.mp hd).1
  have hdabs : |d| < (K : ℤ) := (mem_diffSet_iff hK).1 hdS
  have hdabs' := abs_lt.mp hdabs
  have hleft : -(K : ℤ) ≤ d := by omega
  have hright : d ≤ (K : ℤ) := by omega
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨hleft, hright⟩, ?_⟩
  refine ⟨round ((d : ℝ) * gamma), ?_⟩
  exact (Finset.mem_filter.mp hd).2

lemma round_filter_card_le
    {K : ℕ} {gamma delta : ℝ} (hK : 2 ≤ K)
    (hgamma : 0 < gamma) (hdelta : 0 < delta) :
    (((diffSet K).filter (fun d => roundDist gamma d < delta)).card : ℝ) ≤
      4 * (K : ℝ) * delta + 2 * (K : ℝ) * gamma +
        4 * delta / gamma + 2 := by
  classical
  have hsub := round_filter_subset_near (gamma := gamma) (delta := delta) hK hdelta
  have hcard := nearIntegerSet_card_le K hgamma hdelta
  have hcard' := Finset.card_le_card hsub
  have hcardR : (((diffSet K).filter
      (fun d => roundDist gamma d < delta)).card : ℝ) ≤
      ((nearIntegerSet K gamma delta).card : ℝ) := by
    exact_mod_cast hcard'
  exact hcardR.trans hcard

lemma central_subset_near
    {K L : ℕ} {gamma : ℝ} (hK : 2 ≤ K) (hL : 2 ≤ L)
    (hgamma : 0 < gamma) :
    (diffSet K).filter (fun d => roundDist gamma d < (1 : ℝ) / (2 * L)) ⊆
      nearIntegerSet K gamma ((1 : ℝ) / (2 * L)) := by
  apply round_filter_subset_near hK
  positivity

lemma exists_dyadic_index
    {L q : ℕ} (hL : 2 ≤ L) (hq : L < 2 ^ q)
    {delta : ℝ} (hdelta0 : (1 : ℝ) / (2 * L) ≤ delta)
    (hdelta1 : delta ≤ (1 : ℝ) / 2) :
    ∃ m ∈ Finset.Icc 1 q,
      ((2 : ℝ) ^ (m - 1)) / (2 * L) ≤ delta ∧
        delta < ((2 : ℝ) ^ m) / (2 * L) := by
  have hLpos : 0 < (L : ℝ) := by positivity
  let x : ℝ := (2 * L) * delta
  have hx1 : (1 : ℝ) ≤ x := by
    have hh : (1 : ℝ) ≤ delta * (2 * (L : ℝ)) := by
      apply (div_le_iff₀ (by positivity : 0 < (2 * (L : ℝ)))).mp
      simpa [one_div, mul_comm] using hdelta0
    dsimp [x]
    nlinarith
  have hx2 : x ≤ (L : ℝ) := by
    dsimp [x]
    nlinarith
  obtain ⟨n, hn0, hn1⟩ := exists_nat_pow_near hx1 (by norm_num : (1 : ℝ) < 2)
  have hxq : x < (2 : ℝ) ^ q := by
    exact hx2.trans_lt (by exact_mod_cast hq)
  have hpowq : (2 : ℝ) ^ n < 2 ^ q := by
    exact hn0.trans_lt hxq
  have hnq : n < q := by
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hpowq
  refine ⟨n + 1, ?_, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    omega
  · have hm : n + 1 - 1 = n := by omega
    rw [hm]
    apply (div_le_iff₀ (by positivity : 0 < (2 * (L : ℝ)))).2
    dsimp [x] at hn0
    nlinarith [hn0]
  · have hm : n + 1 = n.succ := rfl
    rw [hm]
    apply (lt_div_iff₀ (by positivity : 0 < (2 * (L : ℝ)))).2
    dsimp [x] at hn1
    simpa [Nat.succ_eq_add_one, mul_comm] using hn1

def dyadicSet (K L : ℕ) (gamma : ℝ) (m : ℕ) : Finset ℤ :=
  (diffSet K).filter (fun d =>
    ((2 : ℝ) ^ (m - 1)) / (2 * L) ≤ roundDist gamma d ∧
      roundDist gamma d < ((2 : ℝ) ^ m) / (2 * L))

lemma dyadic_card_le
    {K L m : ℕ} {gamma : ℝ} (hK : 2 ≤ K) (hL : 2 ≤ L)
    (hgamma : 0 < gamma) (hm : 1 ≤ m) :
    ((dyadicSet K L gamma m).card : ℝ) ≤
      (2 : ℝ) ^ (m + 1) * (K : ℝ) / L +
        2 * (K : ℝ) * gamma +
        (2 : ℝ) ^ (m + 1) / ((L : ℝ) * gamma) + 2 := by
  have hupper : 0 < ((2 : ℝ) ^ m) / (2 * L) := by positivity
  have hsub : dyadicSet K L gamma m ⊆
      (diffSet K).filter (fun d => roundDist gamma d < ((2 : ℝ) ^ m) / (2 * L)) := by
    intro d hd
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).1,
      (Finset.mem_filter.mp hd).2.2⟩
  have hcard := round_filter_card_le (gamma := gamma) (delta := ((2 : ℝ) ^ m) / (2 * L))
    hK hgamma hupper
  have hcard' := Finset.card_le_card hsub
  have hcardR : ((dyadicSet K L gamma m).card : ℝ) ≤
      (((diffSet K).filter
        (fun d => roundDist gamma d < ((2 : ℝ) ^ m) / (2 * L))).card : ℝ) := by
    exact_mod_cast hcard'
  have h := hcardR.trans hcard
  calc
    ((dyadicSet K L gamma m).card : ℝ) ≤
        4 * (K : ℝ) * (((2 : ℝ) ^ m) / (2 * L)) +
          2 * (K : ℝ) * gamma +
          4 * (((2 : ℝ) ^ m) / (2 * L)) / gamma + 2 := h
    _ = _ := by
      field_simp
      ring

lemma central_card_le
    {K L : ℕ} {gamma : ℝ} (hK : 2 ≤ K) (hL : 2 ≤ L)
    (hgamma : 0 < gamma) :
    (((diffSet K).filter
      (fun d => roundDist gamma d < (1 : ℝ) / (2 * L))).card : ℝ) ≤
      2 * (K : ℝ) / L + 2 * (K : ℝ) * gamma +
        2 / ((L : ℝ) * gamma) + 2 := by
  have h := round_filter_card_le hK hgamma
    (by positivity : 0 < (1 : ℝ) / (2 * L))
  have hK0 : 0 ≤ (K : ℝ) := by positivity
  have hL0 : 0 < (L : ℝ) := by positivity
  have hhalfK : 4 * (K : ℝ) * ((1 : ℝ) / (2 * L)) = 2 * (K : ℝ) / L := by
    field_simp
    ring
  have hhalfD : 4 * ((1 : ℝ) / (2 * L)) / gamma =
      2 / ((L : ℝ) * gamma) := by
    field_simp
    ring
  rw [hhalfK, hhalfD] at h
  exact h

end
end FordDirichletShells

#print axioms FordDirichletShells.central_card_le

namespace FordDirichletShells
noncomputable section

lemma geom_half_sum_formula : ∀ q : ℕ, 1 ≤ q →
    (∑ m ∈ Finset.Icc 1 q, 1 / ((2 : ℝ) ^ (m - 1))) =
      2 - 1 / ((2 : ℝ) ^ (q - 1)) := by
  intro q
  induction q with
  | zero =>
      intro h
      omega
  | succ q ih =>
      intro hq
      by_cases hq0 : q = 0
      · subst q
        norm_num
      · have hq1 : 1 ≤ q := by omega
        rw [Finset.sum_Icc_succ_top (by omega)]
        rw [ih hq1]
        have hp : (2 : ℝ) ^ q = (2 : ℝ) ^ (q - 1) * 2 := by
          calc
            (2 : ℝ) ^ q = (2 : ℝ) ^ ((q - 1) + 1) := by congr 1 <;> omega
            _ = (2 : ℝ) ^ (q - 1) * 2 := by rw [pow_succ]
        rw [show q + 1 - 1 = q by omega, hp]
        field_simp
        ring

lemma geom_half_sum_le {q : ℕ} (hq : 1 ≤ q) :
    (∑ m ∈ Finset.Icc 1 q, 1 / ((2 : ℝ) ^ (m - 1))) ≤ 2 := by
  rw [geom_half_sum_formula q hq]
  have hpos : 0 < (1 / ((2 : ℝ) ^ (q - 1)) : ℝ) := by positivity
  linarith

lemma shell_sum_eq {K L m : ℕ} {gamma : ℝ} :
    (∑ d ∈ diffSet K, if d ∈ dyadicSet K L gamma m then 2 / ((2 : ℝ) ^ m) else 0) =
      ((dyadicSet K L gamma m).card : ℝ) * (2 / ((2 : ℝ) ^ m)) := by
  have hsub : dyadicSet K L gamma m ⊆ diffSet K := by
    intro d hd
    exact (Finset.mem_filter.mp hd).1
  have hsum := Finset.sum_subset hsub (f := fun d : ℤ =>
      if d ∈ dyadicSet K L gamma m then 2 / ((2 : ℝ) ^ m) else 0)
      (by
        intro d hd hnd
        simp [hnd])
  have hleft : (∑ d ∈ dyadicSet K L gamma m,
      if d ∈ dyadicSet K L gamma m then 2 / ((2 : ℝ) ^ m) else 0) =
      ((dyadicSet K L gamma m).card : ℝ) * (2 / ((2 : ℝ) ^ m)) := by
    simp
  simpa [hleft] using hsum.symm

end
end FordDirichletShells

namespace FordDirichletShells
noncomputable section

def shellMajor (K L q : ℕ) (gamma : ℝ) (d : ℤ) : ℝ :=
  (if roundDist gamma d < (1 : ℝ) / (2 * L) then 1 else 0) +
    ∑ m ∈ Finset.Icc 1 q,
      if d ∈ dyadicSet K L gamma m then 2 / ((2 : ℝ) ^ m) else 0

lemma central_sum_eq {K L : ℕ} {gamma : ℝ} :
    (∑ d ∈ diffSet K,
      if roundDist gamma d < (1 : ℝ) / (2 * L) then 1 else 0) =
      (((diffSet K).filter
        (fun d => roundDist gamma d < (1 : ℝ) / (2 * L))).card : ℝ) := by
  rw [Finset.sum_boole]

lemma reciprocal_shell_weight_le
    {L m : ℕ} {gamma delta : ℝ} (hL : 2 ≤ L) (hm : 1 ≤ m)
    (hgamma : 0 < gamma) (hdelta : 0 < delta)
    (hlower : ((2 : ℝ) ^ (m - 1)) / (2 * L) ≤ delta) :
    1 / ((2 : ℝ) * L * delta) ≤ 2 / ((2 : ℝ) ^ m) := by
  have hL0 : 0 < (L : ℝ) := by positivity
  have hpow0 : 0 < (2 : ℝ) ^ m := by positivity
  have hden0 : 0 < (2 : ℝ) * L * delta := by positivity
  have hmrepr : m = (m - 1) + 1 := by omega
  have hpowm : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - 1) * 2 := by
    calc
      (2 : ℝ) ^ m = (2 : ℝ) ^ ((m - 1) + 1) := by congr 1 <;> omega
      _ = (2 : ℝ) ^ (m - 1) * 2 := by rw [pow_succ]
  have hpow_le : (2 : ℝ) ^ m ≤ 4 * (L : ℝ) * delta := by
    rw [hpowm]
    have h := (div_le_iff₀ (by positivity : 0 < (2 * (L : ℝ)))).mp hlower
    nlinarith
  apply (div_le_div_iff₀ hden0 hpow0).2
  nlinarith

lemma pointwise_shell_major
    {K L q : ℕ} {gamma : ℝ} (hK : 2 ≤ K) (hL : 2 ≤ L)
    (hq : L < 2 ^ q) (hgamma : 0 < gamma) (a : ℤ → ℝ)
    (ha_central : ∀ d ∈ diffSet K,
      roundDist gamma d < (1 : ℝ) / (2 * L) → a d ≤ 1)
    (ha_decay : ∀ d ∈ diffSet K, 0 < roundDist gamma d →
      a d ≤ 1 / ((2 : ℝ) * L * roundDist gamma d)) :
    ∀ d ∈ diffSet K, a d ≤ shellMajor K L q gamma d := by
  intro d hd
  by_cases hcentral : roundDist gamma d < (1 : ℝ) / (2 * L)
  · have ha := ha_central d hd hcentral
    have hsum_nonneg : 0 ≤ ∑ m ∈ Finset.Icc 1 q,
        if d ∈ dyadicSet K L gamma m then 2 / ((2 : ℝ) ^ m) else 0 := by
      positivity
    dsimp [shellMajor]
    rw [if_pos hcentral]
    linarith
  · have hdelta0 : (1 : ℝ) / (2 * L) ≤ roundDist gamma d := le_of_not_gt hcentral
    have hdelta1 := roundDist_le_half gamma d
    obtain ⟨m, hm, hmlower, hmupper⟩ :=
      exists_dyadic_index hL hq hdelta0 hdelta1
    have hrdpos : 0 < roundDist gamma d := by
      have hbase : 0 < (1 : ℝ) / (2 * L) := by positivity
      exact lt_of_lt_of_le hbase hdelta0
    have ha := ha_decay d hd hrdpos
    have hw := reciprocal_shell_weight_le hL (Finset.mem_Icc.mp hm).1
      hgamma hrdpos hmlower
    have hdD : d ∈ dyadicSet K L gamma m := by
      exact Finset.mem_filter.mpr ⟨hd, hmlower, hmupper⟩
    have hnonneg : ∀ j ∈ Finset.Icc 1 q,
        0 ≤ (if d ∈ dyadicSet K L gamma j then
          2 / ((2 : ℝ) ^ j) else 0) := by
      intro j hj
      by_cases hDj : d ∈ dyadicSet K L gamma j
      · simp [hDj]
        positivity
      · simp [hDj]
    have hsum := Finset.single_le_sum hnonneg hm
    dsimp [shellMajor]
    rw [if_neg hcentral]
    have hsum' : 2 / ((2 : ℝ) ^ m) ≤
        ∑ j ∈ Finset.Icc 1 q,
          if d ∈ dyadicSet K L gamma j then 2 / ((2 : ℝ) ^ j) else 0 := by
      simpa [hdD] using hsum
    exact (ha.trans hw).trans (by simpa using hsum')

end
end FordDirichletShells

namespace FordDirichletShells
noncomputable section

theorem weighted_shell_sum_le
    {K L q : ℕ} {gamma : ℝ} (hK : 2 ≤ K) (hL : 2 ≤ L)
    (hq : L < 2 ^ q) (hgamma : 0 < gamma) (a : ℤ → ℝ)
    (hmajor : ∀ d ∈ diffSet K, a d ≤ shellMajor K L q gamma d) :
    (∑ d ∈ diffSet K, a d) ≤
      6 + (4 * (q : ℝ) + 2) * (K : ℝ) / L +
        6 * (K : ℝ) * gamma + (4 * (q : ℝ) + 2) / ((L : ℝ) * gamma) := by
  have hq1 : 1 ≤ q := by
    by_contra h
    have hq0 : q = 0 := by omega
    subst q
    norm_num at hq
    omega
  have hsum_major := Finset.sum_le_sum (fun d hd => hmajor d hd)
  calc
    (∑ d ∈ diffSet K, a d) ≤ ∑ d ∈ diffSet K, shellMajor K L q gamma d := hsum_major
    _ =
        (∑ d ∈ diffSet K,
          if roundDist gamma d < (1 : ℝ) / (2 * L) then 1 else 0) +
          ∑ m ∈ Finset.Icc 1 q,
            ∑ d ∈ diffSet K,
              if d ∈ dyadicSet K L gamma m then 2 / ((2 : ℝ) ^ m) else 0 := by
      simp only [shellMajor, Finset.sum_add_distrib]
      rw [Finset.sum_comm]
    _ =
        (((diffSet K).filter
          (fun d => roundDist gamma d < (1 : ℝ) / (2 * L))).card : ℝ) +
          ∑ m ∈ Finset.Icc 1 q,
            ((dyadicSet K L gamma m).card : ℝ) *
              (2 / ((2 : ℝ) ^ m)) := by
      rw [central_sum_eq]
      apply congrArg (fun x => (((diffSet K).filter
          (fun d => roundDist gamma d < (1 : ℝ) / (2 * L))).card : ℝ) + x)
      apply Finset.sum_congr rfl
      intro m hm
      exact shell_sum_eq
    _ ≤
        (2 * (K : ℝ) / L + 2 * (K : ℝ) * gamma +
          2 / ((L : ℝ) * gamma) + 2) +
          ∑ m ∈ Finset.Icc 1 q,
            (4 * (K : ℝ) / L +
              (2 * (K : ℝ) * gamma) / ((2 : ℝ) ^ (m - 1)) +
              4 / ((L : ℝ) * gamma) +
              2 / ((2 : ℝ) ^ (m - 1))) := by
      have hcent := central_card_le hK hL hgamma
      have hterm : ∀ m ∈ Finset.Icc 1 q,
          ((dyadicSet K L gamma m).card : ℝ) *
              (2 / ((2 : ℝ) ^ m)) ≤
            4 * (K : ℝ) / L +
              (2 * (K : ℝ) * gamma) / ((2 : ℝ) ^ (m - 1)) +
              4 / ((L : ℝ) * gamma) +
              2 / ((2 : ℝ) ^ (m - 1)) := by
        intro m hm
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        have hcard := dyadic_card_le hK hL hgamma hm1
        have hpow : 0 ≤ (2 / ((2 : ℝ) ^ m) : ℝ) := by positivity
        have hmul := mul_le_mul_of_nonneg_right hcard hpow
        have hmrepr : m = (m - 1) + 1 := by omega
        have hpowm : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - 1) * 2 := by
          calc
            (2 : ℝ) ^ m = (2 : ℝ) ^ ((m - 1) + 1) := by congr 1 <;> omega
            _ = (2 : ℝ) ^ (m - 1) * 2 := by rw [pow_succ]
        have hpowm1 : (2 : ℝ) ^ (m + 1) = (2 : ℝ) ^ m * 2 := by
          rw [pow_succ]
        calc
          ((dyadicSet K L gamma m).card : ℝ) *
                (2 / ((2 : ℝ) ^ m)) ≤
              (2 ^ (m + 1) * (K : ℝ) / L + 2 * (K : ℝ) * gamma +
                2 ^ (m + 1) / ((L : ℝ) * gamma) + 2) *
                (2 / ((2 : ℝ) ^ m)) := hmul
          _ = 4 * (K : ℝ) / L +
              (2 * (K : ℝ) * gamma) / ((2 : ℝ) ^ (m - 1)) +
              4 / ((L : ℝ) * gamma) +
              2 / ((2 : ℝ) ^ (m - 1)) := by
                rw [hpowm1, hpowm]
                field_simp
                field_simp
                ring
      have hsumterms := Finset.sum_le_sum hterm
      exact add_le_add hcent hsumterms
    _ ≤ 6 + (4 * (q : ℝ) + 2) * (K : ℝ) / L +
        6 * (K : ℝ) * gamma + (4 * (q : ℝ) + 2) / ((L : ℝ) * gamma) := by
      have hgeom := geom_half_sum_le hq1
      have hnonneg : 0 ≤ (∑ m ∈ Finset.Icc 1 q,
          1 / ((2 : ℝ) ^ (m - 1))) := by
        positivity
      have hL0 : 0 < (L : ℝ) := by positivity
      have hgamma0 : 0 < gamma := hgamma
      calc
        (2 * (K : ℝ) / L + 2 * (K : ℝ) * gamma +
            2 / ((L : ℝ) * gamma) + 2) +
            ∑ m ∈ Finset.Icc 1 q,
              (4 * (K : ℝ) / L +
                (2 * (K : ℝ) * gamma) / ((2 : ℝ) ^ (m - 1)) +
                4 / ((L : ℝ) * gamma) +
                2 / ((2 : ℝ) ^ (m - 1)))
            = 2 * (K : ℝ) / L + 2 * (K : ℝ) * gamma +
                2 / ((L : ℝ) * gamma) + 2 +
              (q : ℝ) * (4 * (K : ℝ) / L + 4 / ((L : ℝ) * gamma)) +
                      (2 * (K : ℝ) * gamma + 2) *
                (∑ m ∈ Finset.Icc 1 q,
                  1 / ((2 : ℝ) ^ (m - 1))) := by
                simp only [Finset.sum_add_distrib]
                have hcardIcc : ((Finset.Icc 1 q).card : ℝ) = (q : ℝ) := by
                  rw [Nat.card_Icc]
                  norm_num
                have hsumconst1 :
                    (∑ m ∈ Finset.Icc 1 q, 4 * (K : ℝ) / L) =
                      (q : ℝ) * (4 * (K : ℝ) / L) := by
                  rw [Finset.sum_const]
                  simp only [nsmul_eq_mul]
                  rw [hcardIcc]
                have hsumconst2 :
                    (∑ m ∈ Finset.Icc 1 q, 4 / ((L : ℝ) * gamma)) =
                      (q : ℝ) * (4 / ((L : ℝ) * gamma)) := by
                  rw [Finset.sum_const]
                  simp only [nsmul_eq_mul]
                  rw [hcardIcc]
                have hsumrecip :
                    (∑ m ∈ Finset.Icc 1 q,
                      (2 * (K : ℝ) * gamma) / ((2 : ℝ) ^ (m - 1))) =
                      (2 * (K : ℝ) * gamma) *
                        (∑ m ∈ Finset.Icc 1 q,
                          1 / ((2 : ℝ) ^ (m - 1))) := by
                  calc
                    _ = ∑ m ∈ Finset.Icc 1 q,
                        (2 * (K : ℝ) * gamma) *
                          (1 / ((2 : ℝ) ^ (m - 1))) := by
                            apply Finset.sum_congr rfl
                            intro m hm
                            ring
                    _ = _ := by rw [Finset.mul_sum]
                have hsumrecip2 :
                    (∑ m ∈ Finset.Icc 1 q,
                      2 / ((2 : ℝ) ^ (m - 1))) =
                      2 * (∑ m ∈ Finset.Icc 1 q,
                        1 / ((2 : ℝ) ^ (m - 1))) := by
                  calc
                    _ = ∑ m ∈ Finset.Icc 1 q,
                        2 * (1 / ((2 : ℝ) ^ (m - 1))) := by
                          apply Finset.sum_congr rfl
                          intro m hm
                          ring
                    _ = _ := by rw [Finset.mul_sum]
                rw [hsumconst1, hsumconst2, hsumrecip, hsumrecip2]
                ring
        _ ≤ 6 + (4 * (q : ℝ) + 2) * (K : ℝ) / L +
            6 * (K : ℝ) * gamma + (4 * (q : ℝ) + 2) / ((L : ℝ) * gamma) := by
              have hcoef : 0 ≤ 2 * (K : ℝ) * gamma + 2 := by positivity
              have hgeom' := mul_le_mul_of_nonneg_left hgeom hcoef
              calc
                2 * (K : ℝ) / L + 2 * (K : ℝ) * gamma +
                    2 / ((L : ℝ) * gamma) + 2 +
                    (q : ℝ) * (4 * (K : ℝ) / L + 4 / ((L : ℝ) * gamma)) +
                    (2 * (K : ℝ) * gamma + 2) *
                      (∑ m ∈ Finset.Icc 1 q,
                        1 / ((2 : ℝ) ^ (m - 1)))
                    ≤
                    2 * (K : ℝ) / L + 2 * (K : ℝ) * gamma +
                    2 / ((L : ℝ) * gamma) + 2 +
                    (q : ℝ) * (4 * (K : ℝ) / L + 4 / ((L : ℝ) * gamma)) +
                    (2 * (K : ℝ) * gamma + 2) * 2 := by
                      linarith
                _ = 6 + (4 * (q : ℝ) + 2) * (K : ℝ) / L +
                    6 * (K : ℝ) * gamma +
                    (4 * (q : ℝ) + 2) / ((L : ℝ) * gamma) := by
                      ring

theorem weighted_shell_sum_le_of_decay
    {K L q : ℕ} {gamma : ℝ} (hK : 2 ≤ K) (hL : 2 ≤ L)
    (hq : L < 2 ^ q) (hgamma : 0 < gamma) (a : ℤ → ℝ)
    (ha_central : ∀ d ∈ diffSet K,
      roundDist gamma d < (1 : ℝ) / (2 * L) → a d ≤ 1)
    (ha_decay : ∀ d ∈ diffSet K, 0 < roundDist gamma d →
      a d ≤ 1 / ((2 : ℝ) * L * roundDist gamma d)) :
    (∑ d ∈ diffSet K, a d) ≤
      6 + (4 * (q : ℝ) + 2) * (K : ℝ) / L +
        6 * (K : ℝ) * gamma + (4 * (q : ℝ) + 2) / ((L : ℝ) * gamma) := by
  exact weighted_shell_sum_le hK hL hq hgamma a
    (pointwise_shell_major hK hL hq hgamma a ha_central ha_decay)

end
end FordDirichletShells
