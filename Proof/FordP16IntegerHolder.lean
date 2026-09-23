import FordP16FiniteTargetCount

open scoped BigOperators ZMod ComplexConjugate
set_option maxHeartbeats 5000000

namespace MAPFordP16IntegerHolder
noncomputable section

open MAPFordP16FiniteFourierBridge
open MAPFordFiniteFourierCharacterSum
open MAPFordP16FiniteHolder
open MAPFordP16FiniteTargetCount

abbrev targetPairAtOne
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) : Type :=
  fordFiniteTargetPair (L := 1) (p := p) (s := s) (k := k) (d := d)
    (Q := Q) (P := P) (q := q) hdk hp psi

abbrev fixedPairAtOne
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (b : ZMod p) : Type :=
  fordFinitePair (L := 1) (p := p) (s := s) (k := k) (d := d)
    (Q := Q) (P := P) hdk hp psi b

def fordTargetAliasModulus
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) : ℕ :=
  1 +
    (∑ r : targetPairAtOne (q := q) hdk hp psi,
      ∑ j : Fin k,
        (fordFiniteTargetPairFrequency (L := 1) (p := p) (s := s) (k := k)
          (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r j).natAbs) +
    (∑ b : ZMod p,
      ∑ r : fixedPairAtOne (q := q) hdk hp psi b,
        ∑ j : Fin k,
          (fordFinitePairFrequency (L := 1) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j).natAbs)

lemma target_alias_bound
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (r : targetPairAtOne (q := q) hdk hp psi) (j : Fin k) :
    |fordFiniteTargetPairFrequency (L := 1)
      (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P) (q := q)
      hdk hp psi r j| <
        (fordTargetAliasModulus (p := p) (s := s) (k := k) (d := d)
          (Q := Q) (P := P) (q := q) hdk hp psi : ℤ) := by
  let M := fordTargetAliasModulus (p := p) (s := s) (k := k) (d := d)
    (Q := Q) (P := P) (q := q) hdk hp psi
  have hsingle :
      (fordFiniteTargetPairFrequency (L := 1) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r j).natAbs ≤
      ∑ r' : targetPairAtOne (q := q) hdk hp psi,
        ∑ j' : Fin k,
          (fordFiniteTargetPairFrequency (L := 1) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r' j').natAbs := by
    calc
      _ ≤ ∑ j' : Fin k,
          (fordFiniteTargetPairFrequency (L := 1) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r j').natAbs := by
        exact Finset.single_le_sum
          (f := fun j' =>
            (fordFiniteTargetPairFrequency (L := 1) (p := p) (s := s) (k := k)
              (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r j').natAbs)
          (fun j' _ => Nat.zero_le _) (Finset.mem_univ j)
      _ ≤ _ := by
        exact Finset.single_le_sum
          (f := fun r' : targetPairAtOne (q := q) hdk hp psi =>
            ∑ j' : Fin k,
              (fordFiniteTargetPairFrequency (L := 1) (p := p) (s := s) (k := k)
                (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r' j').natAbs)
          (fun r' _ => Nat.zero_le _)
          (Finset.mem_univ r)
  have hnat :
      (fordFiniteTargetPairFrequency (L := 1) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r j).natAbs < M := by
    dsimp [M, fordTargetAliasModulus]
    omega
  rw [← Int.natCast_natAbs]
  exact_mod_cast hnat

lemma fixed_alias_bound
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (b : ZMod p) (r : fixedPairAtOne (q := q) hdk hp psi b) (j : Fin k) :
    |fordFinitePairFrequency (L := 1)
      (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P) (q := q)
      hdk hp psi b r j| <
        (fordTargetAliasModulus (p := p) (s := s) (k := k) (d := d)
          (Q := Q) (P := P) (q := q) hdk hp psi : ℤ) := by
  let M := fordTargetAliasModulus (p := p) (s := s) (k := k) (d := d)
    (Q := Q) (P := P) (q := q) hdk hp psi
  have hsingle :
      (fordFinitePairFrequency (L := 1) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j).natAbs ≤
      ∑ b' : ZMod p,
        ∑ r' : fixedPairAtOne (q := q) hdk hp psi b',
          ∑ j' : Fin k,
            (fordFinitePairFrequency (L := 1) (p := p) (s := s) (k := k)
              (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b' r' j').natAbs := by
    calc
      _ ≤ ∑ j' : Fin k,
          (fordFinitePairFrequency (L := 1) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j').natAbs := by
        exact Finset.single_le_sum
          (f := fun j' =>
            (fordFinitePairFrequency (L := 1) (p := p) (s := s) (k := k)
              (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j').natAbs)
          (fun j' _ => Nat.zero_le _) (Finset.mem_univ j)
      _ ≤ ∑ r' : fixedPairAtOne (q := q) hdk hp psi b,
          ∑ j' : Fin k,
            (fordFinitePairFrequency (L := 1) (p := p) (s := s) (k := k)
              (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r' j').natAbs := by
        exact Finset.single_le_sum
          (f := fun r' : fixedPairAtOne (q := q) hdk hp psi b =>
            ∑ j' : Fin k,
              (fordFinitePairFrequency (L := 1) (p := p) (s := s) (k := k)
                (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r' j').natAbs)
          (fun r' _ => Nat.zero_le _)
          (Finset.mem_univ r)
      _ ≤ _ := by
        exact Finset.single_le_sum
          (f := fun b' =>
            ∑ r' : fixedPairAtOne (q := q) hdk hp psi b',
              ∑ j' : Fin k,
                (fordFinitePairFrequency (L := 1) (p := p) (s := s) (k := k)
                  (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b' r' j').natAbs)
          (fun b' _ => Nat.zero_le _)
          (Finset.mem_univ b)
  have hnat :
      (fordFinitePairFrequency (L := 1) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j).natAbs < M := by
    dsimp [M, fordTargetAliasModulus]
    omega
  rw [← Int.natCast_natAbs]
  exact_mod_cast hnat

lemma finite_target_energy_count_real
    {L p s k d Q P q : ℕ} [NeZero L] [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (hbound : ∀ r j,
      |fordFiniteTargetPairFrequency (L := L) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r j| < (L : ℤ)) :
    (∑ alpha : Fin k → ZMod L,
      ‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
        hdk hp psi alpha‖ ^ 2 *
      ∑ target : Fin d → ZMod p,
        ‖fordFiniteTargetResidueSum (L := L) (p := p) (s := s) (k := k)
          (d := d) (Q := Q) alpha q target‖ ^ 2) =
      (L : ℝ) ^ k *
        Fintype.card {r : fordFiniteTargetPair (L := L) (p := p) (s := s) (k := k)
          (d := d) (Q := Q) (P := P) (q := q) hdk hp psi //
          ∀ j, fordFiniteTargetPairFrequency (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r j = 0} := by
  have h := finite_target_energy_count hdk hp psi hbound
  have hr := congrArg Complex.re h
  have hleft :
      Complex.re (∑ alpha : Fin k → ZMod L,
        (((‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
            hdk hp psi alpha‖ ^ 2 : ℝ) : ℂ) *
          ∑ target : Fin d → ZMod p,
            ((‖fordFiniteTargetResidueSum (L := L) (p := p) (s := s) (k := k)
              (d := d) (Q := Q) alpha q target‖ ^ 2 : ℝ) : ℂ))) =
      ∑ alpha : Fin k → ZMod L,
        ‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
          hdk hp psi alpha‖ ^ 2 *
        ∑ target : Fin d → ZMod p,
          ‖fordFiniteTargetResidueSum (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) alpha q target‖ ^ 2 := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro alpha halpha
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [Complex.re_sum]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  have hpow_all : ∀ n : ℕ, ((L : ℂ) ^ n).re = (L : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, Complex.mul_re, Complex.natCast_re,
          Complex.natCast_im, ih]
        ring
  have hright :
      Complex.re ((L : ℂ) ^ k *
        Fintype.card {r : fordFiniteTargetPair (L := L) (p := p) (s := s) (k := k)
          (d := d) (Q := Q) (P := P) (q := q) hdk hp psi //
          ∀ j, fordFiniteTargetPairFrequency (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r j = 0}) =
      (L : ℝ) ^ k * Fintype.card {r : fordFiniteTargetPair (L := L)
          (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P)
          hdk hp psi //
          ∀ j, fordFiniteTargetPairFrequency (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r j = 0} := by
    rw [Complex.mul_re, hpow_all, Complex.natCast_re, Complex.natCast_im]
    ring
  calc
    _ = Complex.re (∑ alpha : Fin k → ZMod L,
        (((‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
            hdk hp psi alpha‖ ^ 2 : ℝ) : ℂ) *
          ∑ target : Fin d → ZMod p,
            ((‖fordFiniteTargetResidueSum (L := L) (p := p) (s := s) (k := k)
              (d := d) (Q := Q) alpha q target‖ ^ 2 : ℝ) : ℂ))) := hleft.symm
    _ = Complex.re ((L : ℂ) ^ k * Fintype.card {r : fordFiniteTargetPair
        (L := L) (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P) (q := q)
        hdk hp psi // ∀ j, fordFiniteTargetPairFrequency (L := L) (p := p)
          (s := s) (k := k) (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r j = 0}) := hr
    _ = _ := hright

theorem integer_target_holder_of_bounds
    {L p s k d Q P q : ℕ} [NeZero L] [NeZero p]
    (hp : p.Prime) (hd : d < p) (hds : d ≤ s) (hs : 0 < s)
    (hdk : d ≤ k) (psi : Fin k → Polynomial ℤ)
    (htarget : ∀ r j,
      |fordFiniteTargetPairFrequency (L := L) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r j| < (L : ℤ))
    (hfixed : ∀ b r j,
      |fordFinitePairFrequency (L := L) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j| < (L : ℤ)) :
    Fintype.card {r : fordFiniteTargetPair (L := L) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi //
      ∀ j, fordFiniteTargetPairFrequency (L := L) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r j = 0} ≤
      (Nat.factorial d * p ^ (2*s-d-1) : ℕ) *
        ∑ b : ZMod p, Fintype.card {r : fordFinitePair (L := L)
          (p := p) (s := s) (k := k) (d := d) (Q := Q) hdk hp psi b //
          ∀ j, fordFinitePairFrequency (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j = 0} := by
  let C : ℝ := (Nat.factorial d * p ^ (2*s-d-1) : ℝ)
  have hcount := finite_target_energy_count_real hdk hp psi htarget
  have hholder0 := finite_target_energy_holder hp hd hds hs hdk psi hfixed
  have hholder :
      (∑ alpha : Fin k → ZMod L,
        ‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
          hdk hp psi alpha‖ ^ 2 *
        ∑ target : Fin d → ZMod p,
          ‖fordFiniteTargetResidueSum (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) alpha q target‖ ^ 2) ≤
      C * (L : ℝ) ^ k *
        ∑ b : ZMod p, Fintype.card {r : fordFinitePair (L := L)
          (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P)
          hdk hp psi b //
          ∀ j, fordFinitePairFrequency (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j = 0} := by
    simpa [C, fordFiniteResidueSum, fordFiniteTargetResidueSum] using hholder0
  have hmain :
      (L : ℝ) ^ k *
          Fintype.card {r : fordFiniteTargetPair (L := L) (p := p) (s := s)
            (k := k) (d := d) (Q := Q) (P := P) (q := q) hdk hp psi //
            ∀ j, fordFiniteTargetPairFrequency (L := L) (p := p) (s := s) (k := k)
              (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r j = 0} ≤
        C * (L : ℝ) ^ k *
          ∑ b : ZMod p, Fintype.card {r : fordFinitePair (L := L)
            (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P)
            hdk hp psi b //
            ∀ j, fordFinitePairFrequency (L := L) (p := p) (s := s) (k := k)
              (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j = 0} := by
    calc
      _ = (∑ alpha : Fin k → ZMod L,
        ‖fordFiniteFBlock (L := L) (p := p) (k := k) (d := d) (P := P)
          hdk hp psi alpha‖ ^ 2 *
        ∑ target : Fin d → ZMod p,
          ‖fordFiniteTargetResidueSum (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) alpha q target‖ ^ 2) := hcount.symm
      _ ≤ _ := hholder
  have hpos : 0 < (L : ℝ) ^ k := by
    have hLpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    exact pow_pos (by exact_mod_cast hLpos) _
  have hcancel :
      (Fintype.card {r : fordFiniteTargetPair (L := L) (p := p) (s := s)
          (k := k) (d := d) (Q := Q) (P := P) (q := q) hdk hp psi //
          ∀ j, fordFiniteTargetPairFrequency (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r j = 0} : ℝ) ≤
        C * ∑ b : ZMod p, Fintype.card {r : fordFinitePair (L := L)
          (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P)
          hdk hp psi b //
          ∀ j, fordFinitePairFrequency (L := L) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j = 0} := by
    apply le_of_mul_le_mul_left ?_ hpos
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
  dsimp [C] at hcancel
  exact_mod_cast hcancel

theorem integer_target_holder
    {p s k d Q P q : ℕ} [NeZero p]
    (hp : p.Prime) (hd : d < p) (hds : d ≤ s) (hs : 0 < s)
    (hdk : d ≤ k) (psi : Fin k → Polynomial ℤ) :
    Fintype.card {r : fordFiniteTargetPair (L := 1) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi //
      ∀ j, fordFiniteTargetPairFrequency (L := 1) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi r j = 0} ≤
      (Nat.factorial d * p ^ (2*s-d-1) : ℕ) *
        ∑ b : ZMod p, Fintype.card {r : fordFinitePair (L := 1)
          (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P)
          hdk hp psi b //
          ∀ j, fordFinitePairFrequency (L := 1) (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j = 0} := by
  let M := fordTargetAliasModulus (p := p) (s := s) (k := k) (d := d)
    (Q := Q) (P := P) (q := q) hdk hp psi
  letI : NeZero M := ⟨by
    dsimp [M, fordTargetAliasModulus]
    omega⟩
  have hgeneric := integer_target_holder_of_bounds (L := M) hp hd hds hs hdk psi
    (htarget := by
      intro r j
      simpa [M, targetPairAtOne] using!
        (target_alias_bound (p := p) (s := s) (k := k) (d := d)
          (Q := Q) (P := P) (q := q) hdk hp psi r j))
    (hfixed := by
      intro b r j
      simpa [M, fixedPairAtOne] using!
        (fixed_alias_bound (p := p) (s := s) (k := k) (d := d)
          (Q := Q) (P := P) (q := q) hdk hp psi b r j))
  simpa [M] using! hgeneric

end
end MAPFordP16IntegerHolder

#print axioms MAPFordP16IntegerHolder.target_alias_bound
#print axioms MAPFordP16IntegerHolder.fixed_alias_bound
#print axioms MAPFordP16IntegerHolder.integer_target_holder_of_bounds
#print axioms MAPFordP16IntegerHolder.integer_target_holder
