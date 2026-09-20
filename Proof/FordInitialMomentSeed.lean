import FordCompleteSystemMoment

/-!
# Ford's initial complete-system count and real recurrence seed

Ford's Lemma 3.5 (printed p. 22) starts its induction from the elementary
diagonal estimate `J_{k,k}(P) ≤ k! P^k`.  The proof below formalizes that
initial estimate for the literal finite model used by `completeMoment`.
The only nontrivial algebraic step is Newton's identities over `ℚ`, followed
by Vieta's root/multiset reconstruction.  No growing-degree mean-value bound
is used.
-/
open scoped BigOperators
open Finset
noncomputable section
namespace MAPFordInitialMomentSeed

def qTuple {k : ℕ} (x : Fin k → ℕ) : Fin k → ℚ := fun i => (x i : ℚ)
def xMulti {k : ℕ} (x : Fin k → ℕ) : Multiset ℚ := (List.ofFn (fun i => (x i : ℚ)) : Multiset ℚ)
def eVal {k : ℕ} (x : Fin k → ℕ) (n : ℕ) : ℚ :=
  MvPolynomial.aeval (qTuple x) (MvPolynomial.esymm (Fin k) ℚ n)
def pVal {k : ℕ} (x : Fin k → ℕ) (n : ℕ) : ℚ :=
  MvPolynomial.aeval (qTuple x) (MvPolynomial.psum (Fin k) ℚ n)

theorem psum_eval {k : ℕ} (x : Fin k → ℕ) (j : ℕ) :
    pVal x j = ∑ i : Fin k, (x i : ℚ) ^ j := by
  simp [pVal, MvPolynomial.psum, qTuple]

theorem esymm_eval {k : ℕ} (x : Fin k → ℕ) (n : ℕ) :
    eVal x n = (xMulti x).esymm n := by
  rw [eVal, MvPolynomial.aeval_esymm_eq_multiset_esymm]
  congr 1
  simp [xMulti, qTuple, List.ofFn_eq_map]

lemma eval_mul_esymm {k : ℕ} (x : Fin k → ℕ) (n : ℕ) :
    (n : ℚ) * eVal x n =
      (-1 : ℚ) ^ (n+1) *
       ∑ a ∈ antidiagonal n with a.1 < n,
         (-1 : ℚ)^a.1 * eVal x a.1 * pVal x a.2 := by
  have h := congrArg (MvPolynomial.aeval (qTuple x))
    (MvPolynomial.mul_esymm_eq_sum (Fin k) ℚ n)
  simpa [eVal, pVal, map_sum, map_mul, map_pow, map_natCast] using h

lemma eval_sum_term_eq {k : ℕ} {x y : Fin k → ℕ}
    (hp : ∀ j, 1 ≤ j → j ≤ k → pVal x j = pVal y j)
    (he : ∀ n, n < k → eVal x n = eVal y n) :
    ∀ a, a ∈ antidiagonal k → a.1 < k →
      (-1 : ℚ)^a.1 * eVal x a.1 * pVal x a.2 =
      (-1 : ℚ)^a.1 * eVal y a.1 * pVal y a.2 := by
  intro a ha ha_lt
  have hsum := mem_antidiagonal.mp ha
  have hpos : 1 ≤ a.2 := by omega
  have hale : a.2 ≤ k := by omega
  rw [he a.1 ha_lt]
  rw [hp a.2 hpos hale]

lemma eVal_eq_of_pVal_eq {k : ℕ} {x y : Fin k → ℕ}
    (hp : ∀ j, 1 ≤ j → j ≤ k → pVal x j = pVal y j) :
    ∀ n, n ≤ k → eVal x n = eVal y n := by
  have aux : ∀ n, n ≤ k → (∀ m, m < n → eVal x m = eVal y m) →
      eVal x n = eVal y n := by
    intro n hn hprev
    cases n with
    | zero => simp [eVal]
    | succ n =>
      have hx := eval_mul_esymm x (n+1)
      have hy := eval_mul_esymm y (n+1)
      have hsum :
          ∑ a ∈ antidiagonal (n+1) with a.1 < (n+1),
            (-1 : ℚ)^a.1 * eVal x a.1 * pVal x a.2 =
          ∑ a ∈ antidiagonal (n+1) with a.1 < (n+1),
            (-1 : ℚ)^a.1 * eVal y a.1 * pVal y a.2 := by
        apply sum_congr rfl
        intro a ha
        have hsum' := mem_antidiagonal.mp (mem_filter.mp ha).1
        have halt := (mem_filter.mp ha).2
        have hpos : 1 ≤ a.2 := by omega
        have hale : a.2 ≤ k := by omega
        have heq := hprev a.1 halt
        rw [heq, hp a.2 hpos hale]
      rw [hsum] at hx
      apply (mul_left_cancel₀ (show (↑(n+1) : ℚ) ≠ 0 by positivity))
      exact hx.trans hy.symm
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      apply aux n hn
      intro m hm
      exact ih m hm (by omega)

def polyOfMulti {k : ℕ} (x : Fin k → ℕ) : Polynomial ℚ :=
  (xMulti x).map (fun a => Polynomial.X - Polynomial.C a) |>.prod

lemma polyOfMulti_eq_of_pVal_eq {k : ℕ} {x y : Fin k → ℕ}
    (hp : ∀ j, 1 ≤ j → j ≤ k → pVal x j = pVal y j) :
    polyOfMulti x = polyOfMulti y := by
  have he := eVal_eq_of_pVal_eq hp
  have hcardx : (xMulti x).card = k := by simp [xMulti]
  have hcardy : (xMulti y).card = k := by simp [xMulti]
  rw [polyOfMulti, polyOfMulti, Multiset.prod_X_sub_X_eq_sum_esymm,
    Multiset.prod_X_sub_X_eq_sum_esymm, hcardx, hcardy]
  apply sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by simpa using (mem_range.mp hj)
  rw [← esymm_eval x j, ← esymm_eval y j, he j hjk]

lemma xMulti_eq_of_pVal_eq {k : ℕ} {x y : Fin k → ℕ}
    (hp : ∀ j, 1 ≤ j → j ≤ k → pVal x j = pVal y j) :
    xMulti x = xMulti y := by
  have hpoly := polyOfMulti_eq_of_pVal_eq hp
  have hxroots : (polyOfMulti x).roots = xMulti x := by
    rw [polyOfMulti]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  have hyroots : (polyOfMulti y).roots = xMulti y := by
    rw [polyOfMulti]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  rw [← hxroots, ← hyroots, hpoly]

lemma sortedTuple_eq_of_pVal_eq {k : ℕ} {x y : Fin k → ℕ}
    (hp : ∀ j, 1 ≤ j → j ≤ k → pVal x j = pVal y j) :
    qTuple x ∘ Tuple.sort (qTuple x) = qTuple y ∘ Tuple.sort (qTuple y) := by
  have hm := xMulti_eq_of_pVal_eq hp
  have hxy : List.Perm (List.ofFn (qTuple x)) (List.ofFn (qTuple y)) :=
    Multiset.coe_eq_coe.mp hm
  have hpx := Equiv.Perm.ofFn_comp_perm (Tuple.sort (qTuple x)) (qTuple x)
  have hpy := Equiv.Perm.ofFn_comp_perm (Tuple.sort (qTuple y)) (qTuple y)
  have hs : List.ofFn (qTuple x ∘ Tuple.sort (qTuple x)) =
      List.ofFn (qTuple y ∘ Tuple.sort (qTuple y)) :=
    (List.Perm.eq_of_sortedLE
      (Tuple.monotone_sort (qTuple x)).sortedLE_ofFn
      (Tuple.monotone_sort (qTuple y)).sortedLE_ofFn
      (hpx.trans (hxy.trans hpy.symm)))
  exact List.ofFn_injective hs

def toNatTuple {k P : ℕ} (x : Fin k → Fin P) : Fin k → ℕ :=
  fun i => (x i).val + 1

def ySort {k P : ℕ} (y : Fin k → Fin P) : Equiv.Perm (Fin k) :=
  Tuple.sort (qTuple (toNatTuple y))

lemma pVal_eq_of_matching {k P : ℕ} {x y : Fin k → Fin P}
    (h : ∀ j ∈ Icc 1 k,
      (∑ i : Fin k, ((x i).val + 1) ^ j) =
        ∑ i : Fin k, ((y i).val + 1) ^ j) :
    ∀ j, 1 ≤ j → j ≤ k → pVal (toNatTuple x) j = pVal (toNatTuple y) j := by
  intro j hj1 hjk
  rw [psum_eval, psum_eval]
  have hh := h j (mem_Icc.mpr ⟨hj1, hjk⟩)
  exact_mod_cast hh

lemma tuple_eq_of_matching_and_sort_eq {k P : ℕ} {y z : Fin k → Fin P}
    (hmatch : ∀ j ∈ Icc 1 k,
      (∑ i : Fin k, ((y i).val + 1) ^ j) =
        ∑ i : Fin k, ((z i).val + 1) ^ j)
    (hsort : ySort y = ySort z) : y = z := by
  have hp := pVal_eq_of_matching hmatch
  have hs := sortedTuple_eq_of_pVal_eq hp
  have hs' : qTuple (toNatTuple y) ∘ ySort y =
      qTuple (toNatTuple z) ∘ ySort z := by simpa [ySort] using hs
  rw [hsort] at hs'
  have hv : toNatTuple y = toNatTuple z := by
    funext i
    have hh := congrFun hs' ((ySort z).symm i)
    have hh' : qTuple (toNatTuple y) i = qTuple (toNatTuple z) i := by
      simpa [Function.comp_apply] using hh
    dsimp [qTuple] at hh'
    exact_mod_cast hh'
  funext i
  apply Fin.ext
  have hh := congrFun hv i
  dsimp [toNatTuple] at hh
  omega


def matching {k P : ℕ} (xy : (Fin k → Fin P) × (Fin k → Fin P)) : Prop :=
  ∀ j ∈ Icc 1 k,
    (∑ i : Fin k, ((xy.1 i).val + 1) ^ j) =
      ∑ i : Fin k, ((xy.2 i).val + 1) ^ j

def solutionFinset (k P : ℕ) :
    Finset ((Fin k → Fin P) × (Fin k → Fin P)) := by
  classical
  exact Finset.univ.filter matching

theorem solutionFinset_eq_completeMoment (k P : ℕ) :
    (solutionFinset k P).card =
      MAPFordCompleteSystemMoment.completeMoment k k P := by
  classical
  simp [solutionFinset, matching, MAPFordCompleteSystemMoment.completeMoment]

lemma solution_sorted_map_injective {k P : ℕ} :
    Function.Injective
      (fun z : solutionFinset k P =>
        (z.1.1, ySort z.1.2)) := by
  intro a b hab
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun q => q.1) hab
  · have hfirst : a.1.1 = b.1.1 := congrArg (fun q => q.1) hab
    have hsort : ySort a.1.2 = ySort b.1.2 := congrArg (fun q => q.2) hab
    apply tuple_eq_of_matching_and_sort_eq
      (y := a.1.2) (z := b.1.2) ?_ hsort
    intro j hj
    have ha : matching a.1 := by simpa [solutionFinset, matching] using a.2
    have hb : matching b.1 := by simpa [solutionFinset, matching] using b.2
    calc
      (∑ i : Fin k, ((a.1.2 i).val + 1) ^ j) =
          ∑ i : Fin k, ((a.1.1 i).val + 1) ^ j := (ha j hj).symm
      _ = ∑ i : Fin k, ((b.1.1 i).val + 1) ^ j := by rw [hfirst]
      _ = ∑ i : Fin k, ((b.1.2 i).val + 1) ^ j := hb j hj

theorem initialMoment_diagonal_bound (k P : ℕ) :
    -- This is Ford's `n = 1` base estimate `J_{k,k}(P) ≤ k! P^k`.
    MAPFordCompleteSystemMoment.completeMoment k k P ≤
      Nat.factorial k * P ^ k := by
  let sol := solutionFinset k P
  let f : sol → (Fin k → Fin P) × Equiv.Perm (Fin k) :=
    fun z => (z.1.1, ySort z.1.2)
  have hf : Function.Injective f := by
    dsimp [f]
    exact solution_sorted_map_injective
  have hc := Fintype.card_le_of_injective f hf
  have hcard_sol : Fintype.card sol = sol.card := Fintype.card_coe sol
  have hcard_codomain :
      Fintype.card ((Fin k → Fin P) × Equiv.Perm (Fin k)) =
        P ^ k * Nat.factorial k := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_perm]
    simp
  rw [hcard_sol, solutionFinset_eq_completeMoment] at hc
  rw [hcard_codomain] at hc
  simpa [Nat.mul_comm] using hc


/-- Ford's printed Lemma 3.5 initial deficit, `Δ₁ = ½ k²(1 - 1/k)`. -/
def deltaOne (k : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (k : ℝ) ^ 2 * (1 - 1 / (k : ℝ))

lemma deltaOne_eq_half_mul_k_mul_sub_one {k : ℕ} (hk : 1 ≤ k) :
    deltaOne k = ((k : ℝ) * ((k : ℝ) - 1)) / 2 := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  dsimp [deltaOne]
  field_simp

/-- The exponent in Ford's `n=1` row simplifies exactly to `k`. -/
def sourceSeedExponent (k : ℕ) : ℝ :=
  2 * (k : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 + deltaOne k

theorem sourceSeedExponent_eq_k {k : ℕ} (hk : 1 ≤ k) :
    sourceSeedExponent k = (k : ℝ) := by
  rw [sourceSeedExponent, deltaOne_eq_half_mul_k_mul_sub_one hk]
  ring

/-- Real-`P` form of Ford's initial `J_{k,k}` seed, with the literal
`completeMoment` count using `⌊P⌋₊` and the source exponent unchanged. -/
theorem initialMoment_real_seed {k : ℕ} (hk : 1 ≤ k) {P : ℝ} (hP : 1 ≤ P) :
    (MAPFordCompleteSystemMoment.completeMoment k k ⌊P⌋₊ : ℝ) ≤
      (Nat.factorial k : ℝ) * Real.rpow P (sourceSeedExponent k) := by
  have hdiag := initialMoment_diagonal_bound k ⌊P⌋₊
  have hdiagR :
      (MAPFordCompleteSystemMoment.completeMoment k k ⌊P⌋₊ : ℝ) ≤
        (Nat.factorial k : ℝ) * (⌊P⌋₊ : ℝ) ^ k := by
    exact_mod_cast hdiag
  have hP0 : 0 ≤ P := by linarith
  have hfloor : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le hP0
  have hfloor0 : 0 ≤ (⌊P⌋₊ : ℝ) := by positivity
  have hpow : (⌊P⌋₊ : ℝ) ^ k ≤ P ^ k := by
    exact pow_le_pow_left₀ hfloor0 hfloor k
  calc
    (MAPFordCompleteSystemMoment.completeMoment k k ⌊P⌋₊ : ℝ) ≤
        (Nat.factorial k : ℝ) * (⌊P⌋₊ : ℝ) ^ k := hdiagR
    _ ≤ (Nat.factorial k : ℝ) * P ^ k := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (Nat.factorial k : ℝ) * Real.rpow P (sourceSeedExponent k) := by
      rw [sourceSeedExponent_eq_k hk]
      exact congrArg (fun z : ℝ => (Nat.factorial k : ℝ) * z)
        (Real.rpow_natCast P k).symm


end MAPFordInitialMomentSeed

#print axioms MAPFordInitialMomentSeed.initialMoment_diagonal_bound
#print axioms MAPFordInitialMomentSeed.xMulti_eq_of_pVal_eq
