import Mathlib

open scoped BigOperators
noncomputable section
namespace FordDifferencePairs

/-- Positive representatives in `Fin (P+1)`, i.e. integers in `[1,P]`. -/
def PositiveFin (P : ℕ) := {x : Fin (P + 1) // 0 < x.val}

/-- Positive heights bounded by `P/m`. -/
def PositiveHeight (P m : ℕ) := {h : Fin (P / m + 1) // 0 < h.val}

abbrev DifferenceCode (P m : ℕ) := Bool × PositiveHeight P m × PositiveFin P

/-- Unequal positive pairs in the literal interval, carrying the congruence. -/
def DifferencePair (P m : ℕ) :=
  {r : Fin (P + 1) × Fin (P + 1) //
    0 < r.1.val ∧ 0 < r.2.val ∧ r.1.val ≠ r.2.val ∧ Nat.ModEq m r.1.val r.2.val}

instance (P : ℕ) : Fintype (PositiveFin P) := by
  classical unfold PositiveFin; infer_instance
instance (P m : ℕ) : Fintype (PositiveHeight P m) := by
  classical unfold PositiveHeight; infer_instance
instance (P m : ℕ) : Fintype (DifferencePair P m) := by
  classical unfold DifferencePair; infer_instance

lemma dvd_sub_of_modEq {P m : ℕ} (hm : 0 < m)
    {a b : Fin (P + 1)} (hmod : Nat.ModEq m a.val b.val) (hab : a.val ≤ b.val) :
    m ∣ b.val - a.val := by
  have hd : (m : ℤ) ∣ (b.val : ℤ) - (a.val : ℤ) := hmod.dvd
  rw [← Int.natCast_sub hab] at hd
  exact Int.natCast_dvd_natCast.mp hd

lemma height_bound {P m d : ℕ} (hm : 0 < m) (hd : d ≤ P) :
    d / m ≤ P / m := Nat.div_le_div_right hd

lemma exists_difference_code {P m : ℕ} (hm : 0 < m) (r : DifferencePair P m) :
    ∃ c : DifferenceCode P m,
      (c.1 = true ∧ r.1.1.val = c.2.2.1.val + m * c.2.1.1.val ∧ r.1.2.val = c.2.2.1.val) ∨
      (c.1 = false ∧ r.1.1.val = c.2.2.1.val ∧ r.1.2.val = c.2.2.1.val + m * c.2.1.1.val) := by
  classical
  by_cases hlt : r.1.1.val < r.1.2.val
  · let d := r.1.2.val - r.1.1.val
    have hle : r.1.1.val ≤ r.1.2.val := Nat.le_of_lt hlt
    have hdpos : 0 < d := Nat.sub_pos_of_lt hlt
    have hdp : d ≤ P := by omega
    have hdiv : m ∣ d := dvd_sub_of_modEq hm r.2.2.2.2 hle
    let q := d / m
    have hmd : m ≤ d := Nat.le_of_dvd hdpos hdiv
    have hqpos : 0 < q := Nat.div_pos hmd hm
    have hqbound : q ≤ P / m := height_bound hm hdp
    let base : PositiveFin P := ⟨r.1.1, r.2.1⟩
    let hh : PositiveHeight P m := ⟨⟨q, by omega⟩, hqpos⟩
    refine ⟨(false, hh, base), Or.inr ⟨rfl, rfl, ?_⟩⟩
    have hrec : d = m * q := by
      dsimp [q]
      exact (Nat.mul_div_cancel' hdiv).symm
    dsimp [base, hh]
    omega
  · have hgt : r.1.2.val < r.1.1.val := by
      have hne := r.2.2.2.1
      omega
    let d := r.1.1.val - r.1.2.val
    have hle : r.1.2.val ≤ r.1.1.val := Nat.le_of_lt hgt
    have hdpos : 0 < d := Nat.sub_pos_of_lt hgt
    have hdp : d ≤ P := by omega
    have hdiv : m ∣ d := dvd_sub_of_modEq hm r.2.2.2.2.symm hle
    let q := d / m
    have hmd : m ≤ d := Nat.le_of_dvd hdpos hdiv
    have hqpos : 0 < q := Nat.div_pos hmd hm
    have hqbound : q ≤ P / m := height_bound hm hdp
    let base : PositiveFin P := ⟨r.1.2, r.2.2.1⟩
    let hh : PositiveHeight P m := ⟨⟨q, by omega⟩, hqpos⟩
    refine ⟨(true, hh, base), Or.inl ⟨rfl, ?_, rfl⟩⟩
    have hrec : d = m * q := by
      dsimp [q]
      exact (Nat.mul_div_cancel' hdiv).symm
    dsimp [base, hh]
    omega

noncomputable def encode (P m : ℕ) (hm : 0 < m) : DifferencePair P m → DifferenceCode P m :=
  fun r => Classical.choose (exists_difference_code hm r)

lemma encode_spec {P m : ℕ} (hm : 0 < m) (r : DifferencePair P m) :
      (encode P m hm r).1 = true ∧
        r.1.1.val = (encode P m hm r).2.2.1.val + m * (encode P m hm r).2.1.1.val ∧
        r.1.2.val = (encode P m hm r).2.2.1.val
      ∨
      (encode P m hm r).1 = false ∧
        r.1.1.val = (encode P m hm r).2.2.1.val ∧
        r.1.2.val = (encode P m hm r).2.2.1.val + m * (encode P m hm r).2.1.1.val :=
  Classical.choose_spec (exists_difference_code hm r)

lemma encode_injective {P m : ℕ} (hm : 0 < m) :
    Function.Injective (encode P m hm) := by
  intro r t h
  have hr := encode_spec hm r
  have ht := encode_spec hm t
  rcases hr with ⟨hs, hz, hw⟩ | ⟨hs, hz, hw⟩ <;>
    rcases ht with ⟨hs', tz, tw⟩ | ⟨hs', tz, tw⟩
  · have hz' : r.1.1.val = t.1.1.val := by
      calc
        r.1.1.val = (encode P m hm r).2.2.1.val + m * (encode P m hm r).2.1.1.val := hz
        _ = (encode P m hm t).2.2.1.val + m * (encode P m hm t).2.1.1.val := by rw [h]
        _ = t.1.1.val := tz.symm
    have hw' : r.1.2.val = t.1.2.val := by
      calc
        r.1.2.val = (encode P m hm r).2.2.1.val := hw
        _ = (encode P m hm t).2.2.1.val := by rw [h]
        _ = t.1.2.val := tw.symm
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · exact hz'
    · exact hw'
  · simp_all
  · simp_all
  · have hz' : r.1.1.val = t.1.1.val := by
      calc
        r.1.1.val = (encode P m hm r).2.2.1.val := hz
        _ = (encode P m hm t).2.2.1.val := by rw [h]
        _ = t.1.1.val := tz.symm
    have hw' : r.1.2.val = t.1.2.val := by
      calc
        r.1.2.val = (encode P m hm r).2.2.1.val + m * (encode P m hm r).2.1.1.val := hw
        _ = (encode P m hm t).2.2.1.val + m * (encode P m hm t).2.1.1.val := by rw [h]
        _ = t.1.2.val := tw.symm
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · exact hz'
    · exact hw'

end FordDifferencePairs

#print axioms FordDifferencePairs.encode_injective

namespace FordDifferencePairs

lemma differencePair_bounds {P m : ℕ} (r : DifferencePair P m) :
    0 < r.1.1.val ∧ 0 < r.1.2.val ∧
      r.1.1.val ≤ P ∧ r.1.2.val ≤ P := by
  exact ⟨r.2.1, r.2.2.1, by omega, by omega⟩

lemma encode_reconstruct {P m : ℕ} (hm : 0 < m) (r : DifferencePair P m) :
      ((encode P m hm r).1 = true ∧
        r.1.1.val = (encode P m hm r).2.2.1.val + m * (encode P m hm r).2.1.1.val ∧
        r.1.2.val = (encode P m hm r).2.2.1.val) ∨
      ((encode P m hm r).1 = false ∧
        r.1.1.val = (encode P m hm r).2.2.1.val ∧
        r.1.2.val = (encode P m hm r).2.2.1.val + m * (encode P m hm r).2.1.1.val) :=
  encode_spec hm r

lemma encode_difference_identity {P m : ℕ} (hm : 0 < m)
    (F : ℕ → ℤ) (r : DifferencePair P m) :
    F r.1.1.val - F r.1.2.val =
      if (encode P m hm r).1 then
        F ((encode P m hm r).2.2.1.val + m * (encode P m hm r).2.1.1.val) -
          F (encode P m hm r).2.2.1.val
      else
        -(F ((encode P m hm r).2.2.1.val + m * (encode P m hm r).2.1.1.val) -
          F (encode P m hm r).2.2.1.val) := by
  rcases encode_spec hm r with ⟨hs, hz, hw⟩ | ⟨hs, hz, hw⟩
  · simp only [if_pos hs]
    rw [hz, hw]
  · simp [hs, hz, hw]

end FordDifferencePairs

#print axioms FordDifferencePairs.encode_difference_identity

namespace FordDifferencePairs

lemma encode_gap {P m : ℕ} (hm : 0 < m)
    (r : DifferencePair P m) :
    (r.1.1.val ≤ r.1.2.val ∧
      r.1.2.val - r.1.1.val = m * (encode P m hm r).2.1.1.val) ∨
    (r.1.2.val ≤ r.1.1.val ∧
      r.1.1.val - r.1.2.val = m * (encode P m hm r).2.1.1.val) := by
  rcases encode_spec hm r with ⟨hs, hz, hw⟩ | ⟨hs, hz, hw⟩
  · right
    constructor
    · omega
    · omega
  · left
    constructor
    · omega
    · omega

end FordDifferencePairs

#print axioms FordDifferencePairs.encode_gap
