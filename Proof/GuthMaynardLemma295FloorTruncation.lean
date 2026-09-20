import GuthMaynardLemma295DualTail

/-!
# Exact real-to-natural truncation for Lemma 29.5

The source states the reflected cutoff at a real length `M`, whereas the
finite contour uses the natural prefix `floor M`.  These lemmas certify that
the two polynomials coincide and record the negative-power comparison used
for the discarded tail.
-/

namespace GuthMaynardLemma295FloorTruncation

open GuthMaynardJutilaReflection2941
open GuthMaynardJutilaTransference

noncomputable section

theorem natRealIoc_zero_floor_eq
    {M : ℝ} (hM : 0 ≤ M) :
    natRealIoc 0 (Nat.floor M : ℝ) = natRealIoc 0 M := by
  ext m
  rw [mem_natRealIoc_iff (by positivity : (0 : ℝ) ≤ Nat.floor M),
    mem_natRealIoc_iff hM]
  constructor
  · rintro ⟨hm0, hm⟩
    exact ⟨hm0, hm.trans (Nat.floor_le hM)⟩
  · rintro ⟨hm0, hm⟩
    refine ⟨hm0, ?_⟩
    exact_mod_cast Nat.le_floor hm

theorem lemma295ReflectedPolynomial_floor
    {M : ℝ} (hM : 0 ≤ M) (tau : ℝ) :
    lemma295ReflectedPolynomial (Nat.floor M) tau =
      lemma295ReflectedPolynomial M tau := by
  unfold lemma295ReflectedPolynomial
  rw [natRealIoc_zero_floor_eq hM]

theorem real_le_floor_add_one (M : ℝ) :
    M ≤ (Nat.floor M : ℝ) + 1 := by
  exact (Nat.lt_floor_add_one M).le

theorem floor_tail_rpow_le
    {M sigma : ℝ} (hM : 0 < M) (hsigma : sigma ≤ 0) :
    Real.rpow ((Nat.floor M : ℝ) + 1) sigma ≤ Real.rpow M sigma := by
  exact Real.rpow_le_rpow_of_nonpos hM
    (real_le_floor_add_one M) hsigma

end

end GuthMaynardLemma295FloorTruncation

#print axioms GuthMaynardLemma295FloorTruncation.lemma295ReflectedPolynomial_floor
#print axioms GuthMaynardLemma295FloorTruncation.floor_tail_rpow_le
