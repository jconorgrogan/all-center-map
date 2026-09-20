import FordP16PowerFiber
import Mathlib.Analysis.MeanInequalities

open scoped BigOperators

namespace MAPFordP16ResidueHolder
noncomputable section

open MAPFordP16PowerFiber

def residueWeight {p s d : ℕ} [NeZero p] {target : Fin d → ZMod p}
    (g : ZMod p → ℂ)
    (c : powerFiberTruncated (p := p) (s := s) (d := d) target) : ℂ :=
  ∏ i : Fin s, g (c.1 i)

def residueSum {p s d : ℕ} [NeZero p] (g : ZMod p → ℂ)
    (target : Fin d → ZMod p) : ℂ :=
  ∑ c : powerFiberTruncated (p := p) (s := s) (d := d) target,
    residueWeight (target := target) g c

lemma amgm_product_le_sum_pow {s : ℕ} (hs : 0 < s) (a : Fin s → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (s : ℝ) * ∏ i : Fin s, a i ≤ ∑ i : Fin s, a i ^ s := by
  let w : Fin s → ℝ := fun _ => (s : ℝ)⁻¹
  let z : Fin s → ℝ := fun i => a i ^ s
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin s)), 0 ≤ w i := by
    intro i hi
    positivity
  have hw' : 0 < ∑ i : Fin s, w i := by
    simp [w, hs]
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin s)), 0 ≤ z i := by
    intro i hi
    exact pow_nonneg (ha i) _
  have hgm := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin s)) w z hw hw' hz
  have hsreal : (0 : ℝ) < s := by exact_mod_cast hs
  have hsne : (s : ℝ) ≠ 0 := ne_of_gt hsreal
  have hw_sum : ∑ i : Fin s, w i = 1 := by
    simp [w]
    field_simp
  have hprod : (∏ i : Fin s, z i ^ w i) = ∏ i : Fin s, a i := by
    apply Finset.prod_congr rfl
    intro i hi
    dsimp [w, z]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (ha i)]
    have hsi : (s : ℝ) * (s : ℝ)⁻¹ = 1 := by
      field_simp
    rw [hsi, Real.rpow_one]
  rw [hprod] at hgm
  have hsumw : ∑ i : Fin s, w i * z i = (∑ i : Fin s, a i ^ s) / s := by
    simp_rw [w, z]
    rw [← Finset.mul_sum]
    ring
  rw [hw_sum, hsumw] at hgm
  simp only [inv_one, div_one] at hgm
  have hmul := (le_div_iff₀ hsreal).mp hgm
  simpa [mul_comm] using hmul

theorem residueSum_holder {p s d : ℕ} [NeZero p] (hp : p.Prime) (hd : d < p)
    (hds : d ≤ s) (hs : 0 < s) (g : ZMod p → ℂ) (target : Fin d → ZMod p) :
    (s : ℝ) * ‖residueSum (s := s) (d := d) g target‖ ^ 2 ≤
    (Nat.factorial d * p ^ (s-d) : ℝ) *
        ∑ c : powerFiberTruncated (p := p) (s := s) (d := d) target,
          ∑ i : Fin s, ‖g (c.1 i)‖ ^ (2*s) := by
  let F := powerFiberTruncated (p := p) (s := s) (d := d) target
  let W : F → ℝ := fun c => ‖residueWeight (target := target) g c‖
  let R : F → ℝ := fun c => ∑ i : Fin s, ‖g (c.1 i)‖ ^ (2*s)
  have hnorm : ‖residueSum (s := s) (d := d) g target‖ ≤ ∑ c : F, W c := by
    simpa [residueSum, W] using
      (norm_sum_le (Finset.univ : Finset F)
        (fun c : F => residueWeight (target := target) g c))
  have hcs0 :=
    (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset F))
      (f := W))
  have hcs : ‖residueSum (s := s) (d := d) g target‖ ^ 2 ≤
      (Fintype.card F : ℝ) * ∑ c : F, W c ^ 2 := by
    have hsumWnonneg : 0 ≤ ∑ c : F, W c := by
      exact Finset.sum_nonneg (fun c _ => by exact norm_nonneg _)
    have hnorm2 : ‖residueSum (s := s) (d := d) g target‖ ^ 2 ≤
        (∑ c : F, W c) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hsumWnonneg).mpr hnorm
    calc
      ‖residueSum (s := s) (d := d) g target‖ ^ 2 ≤
          (∑ c : F, W c) ^ 2 := hnorm2
      _ ≤ (Fintype.card F : ℝ) * ∑ c : F, W c ^ 2 := by
        simpa using hcs0
  have hweight : ∀ c : F,
      W c ^ 2 = ∏ i : Fin s, ‖g (c.1 i)‖ ^ 2 := by
    intro c
    simp [W, residueWeight, norm_prod, Finset.prod_pow]
  have hAMGM : ∀ c : F, (s : ℝ) * W c ^ 2 ≤ R c := by
    intro c
    rw [hweight c]
    have ha : ∀ i : Fin s, 0 ≤ ‖g (c.1 i)‖ ^ 2 := fun i => sq_nonneg _
    simpa [R, ← pow_mul, Nat.mul_comm] using
      (amgm_product_le_sum_pow hs (fun i : Fin s => ‖g (c.1 i)‖ ^ 2) ha)
  have hsum : (s : ℝ) * ∑ c : F, W c ^ 2 ≤ ∑ c : F, R c := by
    calc
      (s : ℝ) * ∑ c : F, W c ^ 2 = ∑ c : F, (s : ℝ) * W c ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ ∑ c : F, R c := by
        exact Finset.sum_le_sum (fun c _ => hAMGM c)
  have hcardNat := card_powerFiberTruncated_le hp hd hds target
  have hcard : (Fintype.card F : ℝ) ≤
      (Nat.factorial d * p ^ (s-d) : ℝ) := by
    exact_mod_cast hcardNat
  have hsreal : (0 : ℝ) ≤ s := by exact_mod_cast (Nat.zero_le s)
  have hbound : (0 : ℝ) ≤ (Nat.factorial d * p ^ (s-d) : ℝ) := by positivity
  calc
    (s : ℝ) * ‖residueSum (s := s) (d := d) g target‖ ^ 2 ≤
        (s : ℝ) * ((Fintype.card F : ℝ) * ∑ c : F, W c ^ 2) :=
      mul_le_mul_of_nonneg_left hcs hsreal
    _ = (Fintype.card F : ℝ) * ((s : ℝ) * ∑ c : F, W c ^ 2) := by ring
    _ ≤ (Nat.factorial d * p ^ (s-d) : ℝ) *
        ((s : ℝ) * ∑ c : F, W c ^ 2) := by
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ (Nat.factorial d * p ^ (s-d) : ℝ) * ∑ c : F, R c :=
      mul_le_mul_of_nonneg_left hsum hbound
    _ = (Nat.factorial d * p ^ (s-d) : ℝ) *
        ∑ c : powerFiberTruncated (p := p) (s := s) (d := d) target,
          ∑ i : Fin s, ‖g (c.1 i)‖ ^ (2*s) := by rfl

end
end MAPFordP16ResidueHolder

#print axioms MAPFordP16ResidueHolder.residueSum_holder
