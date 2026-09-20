import HuxleyHalaszFront
import MontgomeryHybridCharacterSampling

/-!
# Montgomery Theorem 8.3: finite Halasz reduction and absorption

Montgomery's Theorem 8.3 is used after (12.28) through its Halasz
large-value refinement.  This file proves the complete finite reduction,
including the variable-character row geometry and the absorption of the
off-diagonal term.  It does not promote Theorem 8.3 itself to an opaque
proposition.

The one analytic input left visible at the source-facing theorem is the
literal correlation-kernel estimate produced in the proof of Theorem 8.3.
With `R` rows, coefficient energy `E`, length `N`, and off-diagonal scale
`K`, it has shape

`correlationEnergy <= R * C * (N + R*K)`.

The certified Halasz inequality then gives

`R^2 V^2 <= E * R * C * (N + R*K)`,

and the source threshold `2*C*E*K <= V^2` absorbs the `R*K` term, yielding

`R*V^2 <= 2*C*E*N`.
-/

namespace MAPMontgomeryTheorem83Halasz

open scoped BigOperators ComplexConjugate
open Complex
open CGLProofDAG MontgomeryVaughanFiniteReduction
open MAPJutilaDeterministicCore MAPHuxleyHalaszFront
open MAPMontgomeryHybridCharacterSampling
open MAPMRTLemma210DyadicMeanSquare

noncomputable section

/-! ## Generic finite Halasz step -/

/-- The exact pre-absorption inequality obtained from the certified finite
Halasz lemma and one explicit correlation-kernel estimate. -/
theorem finite_halasz_large_value_before_absorption
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (rows : Finset I) (cols : Finset J)
    (a : J → ℂ) (v : I → J → ℂ)
    {V C N K : ℝ}
    (hV : 0 ≤ V) (hC : 0 ≤ C) (hN : 0 ≤ N) (hK : 0 ≤ K)
    (hlarge : ∀ i ∈ rows, V ≤ ‖finitePolynomial cols a v i‖)
    (hkernel : ∀ eta : I → ℂ,
      (∀ i ∈ rows, ‖eta i‖ = 1) →
        correlationEnergy rows cols (fun _ => 1) eta v ≤
          (rows.card : ℝ) * C *
            (N + (rows.card : ℝ) * K)) :
    (((rows.card : ℝ) * V) ^ 2) ≤
      MAPHuxleyHalaszFront.coefficientEnergy cols a *
        ((rows.card : ℝ) * C *
          (N + (rows.card : ℝ) * K)) := by
  obtain ⟨eta, heta, hfront⟩ :=
    finite_halasz_large_value_front rows cols a v V hV hlarge
  have henergy :
      0 ≤ MAPHuxleyHalaszFront.coefficientEnergy cols a := by
    unfold MAPHuxleyHalaszFront.coefficientEnergy
    positivity
  exact hfront.trans <|
    mul_le_mul_of_nonneg_left (hkernel eta heta)
      henergy

/-- Montgomery's source absorption: once the off-diagonal kernel is at most
half the large-value threshold, the row cardinality is controlled only by
the diagonal length term. -/
theorem finite_halasz_large_value_absorbed
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (rows : Finset I) (cols : Finset J)
    (a : J → ℂ) (v : I → J → ℂ)
    {V C N K : ℝ}
    (hV : 0 ≤ V) (hC : 0 ≤ C) (hN : 0 ≤ N) (hK : 0 ≤ K)
    (hlarge : ∀ i ∈ rows, V ≤ ‖finitePolynomial cols a v i‖)
    (hkernel : ∀ eta : I → ℂ,
      (∀ i ∈ rows, ‖eta i‖ = 1) →
        correlationEnergy rows cols (fun _ => 1) eta v ≤
          (rows.card : ℝ) * C *
            (N + (rows.card : ℝ) * K))
    (hthreshold :
      2 * C * MAPHuxleyHalaszFront.coefficientEnergy cols a * K ≤
        V ^ 2) :
    (rows.card : ℝ) * V ^ 2 ≤
      2 * C * MAPHuxleyHalaszFront.coefficientEnergy cols a * N := by
  let R : ℝ := rows.card
  let E : ℝ := MAPHuxleyHalaszFront.coefficientEnergy cols a
  have hR : 0 ≤ R := by positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    unfold MAPHuxleyHalaszFront.coefficientEnergy
    positivity
  change R * V ^ 2 ≤ 2 * C * E * N
  by_cases hRzero : R = 0
  · rw [hRzero]
    simp only [zero_mul]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC) hE) hN
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hRzero)
    have hpre := finite_halasz_large_value_before_absorption
      rows cols a v hV hC hN hK hlarge hkernel
    change (R * V) ^ 2 ≤ E * (R * C * (N + R * K)) at hpre
    have hscaled :
        R * (R * V ^ 2) ≤
          R * (C * E * N + R * C * E * K) := by
      calc
        R * (R * V ^ 2) = (R * V) ^ 2 := by ring
        _ ≤ E * (R * C * (N + R * K)) := hpre
        _ = R * (C * E * N + R * C * E * K) := by ring
    have hcancelled :
        R * V ^ 2 ≤ C * E * N + R * C * E * K := by
      exact (mul_le_mul_iff_of_pos_left hRpos).mp hscaled
    have habsorb : 2 * R * C * E * K ≤ R * V ^ 2 := by
      have := mul_le_mul_of_nonneg_left hthreshold hR
      calc
        2 * R * C * E * K = R * (2 * C * E * K) := by ring
        _ ≤ R * V ^ 2 := by simpa [R, E] using this
    linarith

/-! ## Reduction of the correlation energy to the literal source kernel -/

/-- Exact finite reduction from Montgomery's source row-kernel estimate.
This form permits same-character nearby rows to contribute at the diagonal
`N` scale.  Spacing, character cancellation, and smoothing enter only in
`hrowKernel`; the phase and row-counting algebra are proved here. -/
theorem correlationEnergy_le_of_rowKernel
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (rows : Finset I) (cols : Finset J) (v : I → J → ℂ)
    (eta : I → ℂ) {C N K : ℝ}
    (heta : ∀ i ∈ rows, ‖eta i‖ = 1)
    (hrowKernel : ∀ i ∈ rows,
      ∑ j ∈ rows, ‖∑ k ∈ cols, conj (v i k) * v j k‖ ≤
        C * (N + (rows.card : ℝ) * K)) :
    correlationEnergy rows cols (fun _ => 1) eta v ≤
      (rows.card : ℝ) * C * (N + (rows.card : ℝ) * K) := by
  let B : I → I → ℂ := fun i j =>
    ∑ k ∈ cols, conj (v i k) * v j k
  let F : I → I → ℂ := fun i j =>
    conj (eta i) * eta j * B i j
  have hcorrNonneg :
      0 ≤ correlationEnergy rows cols (fun _ => 1) eta v := by
    unfold correlationEnergy
    positivity
  have hcorrExpanded :
      (correlationEnergy rows cols (fun _ => 1) eta v : ℂ) =
        ∑ i ∈ rows, ∑ j ∈ rows, F i j := by
    simpa [F, B] using
      correlationEnergy_eq_doubleSum rows cols (fun _ => 1) eta v
  calc
    correlationEnergy rows cols (fun _ => 1) eta v =
        ‖(correlationEnergy rows cols (fun _ => 1) eta v : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcorrNonneg]
    _ = ‖∑ i ∈ rows, ∑ j ∈ rows, F i j‖ := by rw [hcorrExpanded]
    _ ≤ ∑ i ∈ rows, ‖∑ j ∈ rows, F i j‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ rows, ∑ j ∈ rows, ‖F i j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sum_le _ _
    _ = ∑ i ∈ rows, ∑ j ∈ rows, ‖B i j‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp [F, norm_mul, Complex.norm_conj, heta i hi, heta j hj]
    _ ≤ ∑ _i ∈ rows,
        C * (N + (rows.card : ℝ) * K) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [B] using hrowKernel i hi
    _ = (rows.card : ℝ) * C * (N + (rows.card : ℝ) * K) := by
      simp
      ring

/-- A stronger sufficient reduction from a diagonal bound and a uniform
bound for every distinct-row pair.  This is useful for alternative kernels;
the literal Montgomery source route uses `correlationEnergy_le_of_rowKernel`.
-/
theorem correlationEnergy_le_of_pairwise_kernel
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (rows : Finset I) (cols : Finset J) (v : I → J → ℂ)
    (eta : I → ℂ) {C N K : ℝ}
    (hC : 0 ≤ C) (hN : 0 ≤ N) (hK : 0 ≤ K)
    (heta : ∀ i ∈ rows, ‖eta i‖ = 1)
    (hdiag : ∀ i ∈ rows,
      ‖∑ k ∈ cols, conj (v i k) * v i k‖ ≤ C * N)
    (hoff : ∀ i ∈ rows, ∀ j ∈ rows, i ≠ j →
      ‖∑ k ∈ cols, conj (v i k) * v j k‖ ≤ C * K) :
    correlationEnergy rows cols (fun _ => 1) eta v ≤
      (rows.card : ℝ) * C * (N + (rows.card : ℝ) * K) := by
  let B : I → I → ℂ := fun i j =>
    ∑ k ∈ cols, conj (v i k) * v j k
  let F : I → I → ℂ := fun i j =>
    conj (eta i) * eta j * B i j
  have hcorrNonneg :
      0 ≤ correlationEnergy rows cols (fun _ => 1) eta v := by
    unfold correlationEnergy
    positivity
  have hcorrExpanded :
      (correlationEnergy rows cols (fun _ => 1) eta v : ℂ) =
        ∑ i ∈ rows, ∑ j ∈ rows, F i j := by
    simpa [F, B] using
      correlationEnergy_eq_doubleSum rows cols (fun _ => 1) eta v
  have hrow (i : I) (hi : i ∈ rows) :
      ‖∑ j ∈ rows, F i j‖ ≤
        C * N + (rows.card : ℝ) * C * K := by
    have herase := Finset.sum_erase_add rows (fun j => F i j) hi
    have hdiagF : ‖F i i‖ ≤ C * N := by
      simpa [F, B, norm_mul, Complex.norm_conj, heta i hi] using hdiag i hi
    have hoffF :
        ‖∑ j ∈ rows.erase i, F i j‖ ≤
          ∑ j ∈ rows.erase i, C * K := by
      calc
        ‖∑ j ∈ rows.erase i, F i j‖ ≤
            ∑ j ∈ rows.erase i, ‖F i j‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ rows.erase i, C * K := by
          apply Finset.sum_le_sum
          intro j hj
          have hjRows : j ∈ rows := (Finset.mem_erase.mp hj).2
          have hji : i ≠ j := fun hij => (Finset.mem_erase.mp hj).1 hij.symm
          simpa [F, B, norm_mul, Complex.norm_conj, heta i hi,
            heta j hjRows] using hoff i hi j hjRows hji
    have hcardErase : ((rows.erase i).card : ℝ) ≤ rows.card := by
      exact_mod_cast
        (Finset.card_erase_le : (rows.erase i).card ≤ rows.card)
    have hCK : 0 ≤ C * K := mul_nonneg hC hK
    calc
      ‖∑ j ∈ rows, F i j‖ =
          ‖F i i + ∑ j ∈ rows.erase i, F i j‖ := by
            rw [add_comm, herase]
      _ ≤ ‖F i i‖ + ‖∑ j ∈ rows.erase i, F i j‖ := norm_add_le _ _
      _ ≤ C * N + ∑ j ∈ rows.erase i, C * K :=
        add_le_add hdiagF hoffF
      _ = C * N + ((rows.erase i).card : ℝ) * C * K := by
        simp
        ring
      _ ≤ C * N + (rows.card : ℝ) * C * K := by
        gcongr
  calc
    correlationEnergy rows cols (fun _ => 1) eta v =
        ‖(correlationEnergy rows cols (fun _ => 1) eta v : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcorrNonneg]
    _ = ‖∑ i ∈ rows, ∑ j ∈ rows, F i j‖ := by rw [hcorrExpanded]
    _ ≤ ∑ i ∈ rows, ‖∑ j ∈ rows, F i j‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ rows,
        (C * N + (rows.card : ℝ) * C * K) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hrow i hi
    _ = (rows.card : ℝ) * C * (N + (rows.card : ℝ) * K) := by
      simp
      ring

/-! ## Exact variable-character row geometry -/

/-- The finite row set consisting of one row for every chosen ordinate of
every character modulo `q`. -/
def characterRows {q : ℕ}
    (W : DirichletCharacter ℂ q → Finset ℝ) :
    Finset ((chi : DirichletCharacter ℂ q) × ℝ) :=
  Finset.univ.sigma W

theorem card_characterRows {q : ℕ}
    (W : DirichletCharacter ℂ q → Finset ℝ) :
    (characterRows W).card =
      ∑ chi : DirichletCharacter ℂ q, (W chi).card := by
  simpa [characterRows] using
    (Finset.card_sigma (Finset.univ : Finset (DirichletCharacter ℂ q)) W)

/-- The Hilbert-space row vector used in Montgomery's Theorem 8.3. -/
def characterRowVector {q : ℕ}
    (row : (chi : DirichletCharacter ℂ q) × ℝ) (n : ℕ) : ℂ :=
  row.1 n * phase n row.2

/-- The abstract finite polynomial on a character row is exactly the
standard character Dirichlet packet. -/
theorem finitePolynomial_characterRowVector
    {q N : ℕ} (a : ℕ → ℂ)
    (row : (chi : DirichletCharacter ℂ q) × ℝ) :
    finitePolynomial (dyadicSupport N) a characterRowVector row =
      characterPacketPolynomial q (dyadicSupport N) a row.1 row.2 := by
  unfold finitePolynomial characterRowVector characterPacketPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Every entry of a character row vector has norm at most one. -/
theorem norm_characterRowVector_le_one
    {q : ℕ} (row : (chi : DirichletCharacter ℂ q) × ℝ) (n : ℕ) :
    ‖characterRowVector row n‖ ≤ 1 := by
  unfold characterRowVector
  rw [norm_mul]
  have hphase : ‖phase n row.2‖ = 1 := by
    unfold phase
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hphase, mul_one]
  exact row.1.norm_le_one _

/-- The diagonal row kernel is bounded by the dyadic length with constant
one.  This is a useful check on Montgomery's `B` kernel.  The literal source
route nevertheless keeps the whole rowwise sum of absolute kernels, because
same-character nearby rows need not obey a uniform off-diagonal estimate. -/
theorem characterRowVector_diagonal_le_length
    {q N : ℕ} (row : (chi : DirichletCharacter ℂ q) × ℝ) :
    ‖∑ n ∈ dyadicSupport N,
        conj (characterRowVector row n) * characterRowVector row n‖ ≤ N := by
  calc
    ‖∑ n ∈ dyadicSupport N,
        conj (characterRowVector row n) * characterRowVector row n‖ ≤
        ∑ n ∈ dyadicSupport N,
          ‖conj (characterRowVector row n) * characterRowVector row n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ dyadicSupport N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_conj]
      have hv := norm_characterRowVector_le_one row n
      nlinarith [norm_nonneg (characterRowVector row n)]
    _ = N := by
      simp [dyadicSupport, Nat.card_Ioc]
      omega

/-- Source-facing finite form of Montgomery Theorem 8.3's large-value
corollary.  The only premise not proved in this file is the displayed
correlation-kernel estimate: this is the first analytic line in the source
proof, before the elementary absorption.  The spacing and height hypotheses
are retained literally so an eventual kernel proof cannot silently weaken
the source geometry. -/
theorem character_halasz_large_values_absorbed
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N)
    (a : ℕ → ℂ) {T V C K : ℝ}
    (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖)
    (hkernel : ∀ eta : ((chi : DirichletCharacter ℂ q) × ℝ) → ℂ,
      (∀ row ∈ characterRows W, ‖eta row‖ = 1) →
        correlationEnergy (characterRows W) (dyadicSupport N)
            (fun _ => 1) eta characterRowVector ≤
          ((characterRows W).card : ℝ) * C *
            ((N : ℝ) + ((characterRows W).card : ℝ) * K))
    (hthreshold :
      2 * C * MontgomeryVaughanFiniteReduction.coefficientEnergy a N * K ≤
        V ^ 2) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      2 * C * MontgomeryVaughanFiniteReduction.coefficientEnergy a N * N := by
  have _ := hN
  have _ := hT
  have _ := hsep
  have _ := hheight
  have hlargeRows : ∀ row ∈ characterRows W,
      V ≤ ‖finitePolynomial (dyadicSupport N) a characterRowVector row‖ := by
    intro row hrow
    have hm := Finset.mem_sigma.mp hrow
    rw [finitePolynomial_characterRowVector]
    exact hlarge row.1 row.2 hm.2
  have h := finite_halasz_large_value_absorbed
    (characterRows W) (dyadicSupport N) a characterRowVector
    hV hC (by positivity : 0 ≤ (N : ℝ)) hK hlargeRows hkernel
    (by simpa [MAPHuxleyHalaszFront.coefficientEnergy,
      MontgomeryVaughanFiniteReduction.coefficientEnergy] using hthreshold)
  rw [card_characterRows] at h
  push_cast at h
  simpa [MAPHuxleyHalaszFront.coefficientEnergy,
    MontgomeryVaughanFiniteReduction.coefficientEnergy] using h

/-- Source-faithful fixed-real-part specialization of Montgomery's Theorem
8.3.  The only analytic premise is the rowwise absolute `B`-kernel bound used
in the published proof.  Everything from that bound through the Halasz phase
choice and the absorption step is proved in this file. -/
theorem character_halasz_large_values_absorbed_of_rowKernel
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N)
    (a : ℕ → ℂ) {T V C K : ℝ}
    (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖)
    (hrowKernel : ∀ row ∈ characterRows W,
      ∑ row' ∈ characterRows W,
          ‖∑ n ∈ dyadicSupport N,
              conj (characterRowVector row n) *
                characterRowVector row' n‖ ≤
        C * ((N : ℝ) + ((characterRows W).card : ℝ) * K))
    (hthreshold :
      2 * C * MontgomeryVaughanFiniteReduction.coefficientEnergy a N * K ≤
        V ^ 2) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      2 * C * MontgomeryVaughanFiniteReduction.coefficientEnergy a N * N := by
  apply character_halasz_large_values_absorbed hN a hT hV hC hK W
    hsep hheight hlarge
  · intro eta heta
    exact correlationEnergy_le_of_rowKernel
      (characterRows W) (dyadicSupport N) characterRowVector eta heta hrowKernel
  · exact hthreshold

/-- The literal hybrid scale in Montgomery Theorem 8.3 after fixing unit
spacing.  The coefficient multiplying this scale is kept separate as `C` in
the source-facing theorem below. -/
def theorem83KernelScale (q : ℕ) (T : ℝ) : ℝ :=
  Real.sqrt ((q : ℝ) * T) * Real.log ((q : ℝ) * T)

theorem theorem83KernelScale_nonneg {q : ℕ} {T : ℝ}
    (hscale : 1 ≤ (q : ℝ) * T) :
    0 ≤ theorem83KernelScale q T := by
  unfold theorem83KernelScale
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hscale)

/-- **Legacy hard-cutoff conditional; not a source theorem.**

This implication is algebraically valid, but its `hrowKernel` premise is a
false strengthening of Montgomery's published argument: the hard dyadic
kernel can have row mass of order `N log R`.  The source inserts a positive
smooth majorant before forming `B`; see
`MontgomeryTheorem83SmoothHalasz.lean` and
`MONTGOMERY_HARD_ROW_KERNEL_DEATH_CERTIFICATE.md`.

It is retained only so old callers fail at the visibly impossible premise,
and must never be cited as certification of Theorem 8.3.  The conditional
conclusion is

`sum_j |B_ij| <= C * (N + R * sqrt(q*T) * log(q*T))`.
 -/
theorem character_halasz_large_values_absorbed_sourceScale
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N)
    (a : ℕ → ℂ) {T V C : ℝ}
    (hT : 0 ≤ T) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hscale : 1 ≤ (q : ℝ) * T)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖)
    (hrowKernel : ∀ row ∈ characterRows W,
      ∑ row' ∈ characterRows W,
          ‖∑ n ∈ dyadicSupport N,
              conj (characterRowVector row n) *
                characterRowVector row' n‖ ≤
        C * ((N : ℝ) + ((characterRows W).card : ℝ) *
          theorem83KernelScale q T))
    (hthreshold :
      2 * C * MontgomeryVaughanFiniteReduction.coefficientEnergy a N *
          theorem83KernelScale q T ≤ V ^ 2) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      2 * C * MontgomeryVaughanFiniteReduction.coefficientEnergy a N * N := by
  exact character_halasz_large_values_absorbed_of_rowKernel
    hN a hT hV hC (theorem83KernelScale_nonneg hscale) W
      hsep hheight hlarge hrowKernel hthreshold

/-- A stronger sufficient route that replaces the source's rowwise `B` bound
by separate diagonal and uniform distinct-row estimates.  It is retained for
alternative kernels, but is not the literal Montgomery route. -/
theorem character_halasz_large_values_absorbed_of_pairwise
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N)
    (a : ℕ → ℂ) {T V C K : ℝ}
    (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖)
    (hdiag : ∀ row ∈ characterRows W,
      ‖∑ n ∈ dyadicSupport N,
          conj (characterRowVector row n) * characterRowVector row n‖ ≤
        C * N)
    (hoff : ∀ row ∈ characterRows W,
      ∀ row' ∈ characterRows W, row ≠ row' →
        ‖∑ n ∈ dyadicSupport N,
            conj (characterRowVector row n) *
              characterRowVector row' n‖ ≤ C * K)
    (hthreshold :
      2 * C * MontgomeryVaughanFiniteReduction.coefficientEnergy a N * K ≤
        V ^ 2) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      2 * C * MontgomeryVaughanFiniteReduction.coefficientEnergy a N * N := by
  apply character_halasz_large_values_absorbed hN a hT hV hC hK W
    hsep hheight hlarge
  · intro eta heta
    exact correlationEnergy_le_of_pairwise_kernel
      (characterRows W) (dyadicSupport N) characterRowVector eta
      hC (by positivity) hK heta hdiag hoff
  · exact hthreshold

/-- An optional stronger route in which the diagonal is discharged
internally and a uniform distinct-row estimate is assumed.  Montgomery's
published proof instead uses the weaker rowwise bound above. -/
theorem character_halasz_large_values_absorbed_of_offDiagonal
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N)
    (a : ℕ → ℂ) {T V C K : ℝ}
    (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hCone : 1 ≤ C) (hK : 0 ≤ K)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖)
    (hoff : ∀ row ∈ characterRows W,
      ∀ row' ∈ characterRows W, row ≠ row' →
        ‖∑ n ∈ dyadicSupport N,
            conj (characterRowVector row n) *
              characterRowVector row' n‖ ≤ C * K)
    (hthreshold :
      2 * C * MontgomeryVaughanFiniteReduction.coefficientEnergy a N * K ≤
        V ^ 2) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      2 * C * MontgomeryVaughanFiniteReduction.coefficientEnergy a N * N := by
  apply character_halasz_large_values_absorbed_of_pairwise hN a hT hV
    (zero_le_one.trans hCone) hK W hsep hheight hlarge
  · intro row hrow
    have hdiag := characterRowVector_diagonal_le_length (N := N) row
    have hNnonneg : (0 : ℝ) ≤ N := by positivity
    exact hdiag.trans (by simpa using mul_le_mul_of_nonneg_right hCone hNnonneg)
  · exact hoff
  · exact hthreshold

end
end MAPMontgomeryTheorem83Halasz

#print axioms MAPMontgomeryTheorem83Halasz.finite_halasz_large_value_before_absorption
#print axioms MAPMontgomeryTheorem83Halasz.finite_halasz_large_value_absorbed
#print axioms MAPMontgomeryTheorem83Halasz.correlationEnergy_le_of_rowKernel
#print axioms MAPMontgomeryTheorem83Halasz.correlationEnergy_le_of_pairwise_kernel
#print axioms MAPMontgomeryTheorem83Halasz.card_characterRows
#print axioms MAPMontgomeryTheorem83Halasz.finitePolynomial_characterRowVector
#print axioms MAPMontgomeryTheorem83Halasz.characterRowVector_diagonal_le_length
#print axioms MAPMontgomeryTheorem83Halasz.character_halasz_large_values_absorbed
#print axioms MAPMontgomeryTheorem83Halasz.character_halasz_large_values_absorbed_of_rowKernel
#print axioms MAPMontgomeryTheorem83Halasz.character_halasz_large_values_absorbed_sourceScale
#print axioms MAPMontgomeryTheorem83Halasz.character_halasz_large_values_absorbed_of_pairwise
#print axioms MAPMontgomeryTheorem83Halasz.character_halasz_large_values_absorbed_of_offDiagonal
