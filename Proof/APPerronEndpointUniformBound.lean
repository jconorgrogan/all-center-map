import APTailReserveAbsorption

/-!
# Uniform endpoint bounds for the inside/outside Perron tails

The exact closed endpoint estimates are collapsed to one character-uniform
`X log^2 X / T` bound on the AP support.  Constants are deliberately loose;
the positive power reserve absorbs them and every polylogarithmic family
loss.
-/

namespace MAPAPPerronEndpointUniformBound

open PrimitiveTruncatedExplicitFormulaBridge TruncatedTwistedPerron
open PaperEdgePrimitiveComponents
open MAPAPCorrectedPaperEdgeComponentSource

noncomputable section

theorem endpoint_scale_log_bounds
    {N : ℕ} {X : ℝ} (hN : 1 ≤ N) (hNX : (N : ℝ) ≤ 5 * X)
    (hX : Real.exp 1 ≤ X) :
    let L := Real.log X
    let u := halfIntegerPoint N
    u ≤ 6 * X ∧
      Real.log u ≤ 6 * L ∧
      Real.log N ≤ 6 * L ∧
      Real.log (N + 1 : ℝ) ≤ 6 * L ∧
      Real.log (2 * N + 1 : ℝ) ≤ 12 * L := by
  let L := Real.log X
  let u := halfIntegerPoint N
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hXone : 1 ≤ X :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hX
  have hL : 1 ≤ L := by
    dsimp only [L]
    exact (Real.le_log_iff_exp_le hX0).2 hX
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hu1 : 1 < u := by
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp only [u, halfIntegerPoint]
    linarith
  have hu0 : 0 < u := zero_lt_one.trans hu1
  have huX : u ≤ 6 * X := by
    dsimp only [u, halfIntegerPoint]
    linarith
  have hlog6 : Real.log (6 : ℝ) ≤ 5 :=
    by nlinarith [Real.log_le_sub_one_of_pos (x := (6 : ℝ)) (by norm_num)]
  have hlog12 : Real.log (12 : ℝ) ≤ 11 :=
    by nlinarith [Real.log_le_sub_one_of_pos (x := (12 : ℝ)) (by norm_num)]
  have hlog6X : Real.log (6 * X) ≤ 6 * L := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    linarith
  have hlu : Real.log u ≤ 6 * L :=
    (Real.log_le_log hu0 huX).trans hlog6X
  have hlogN : Real.log N ≤ 6 * L := by
    have hNu : (N : ℝ) ≤ u := by dsimp only [u, halfIntegerPoint]; linarith
    exact (Real.log_le_log hN0 hNu).trans hlu
  have hNp1 : (N + 1 : ℝ) ≤ 6 * X := by
    push_cast
    linarith
  have hNp1pos : 0 < (N + 1 : ℝ) := by positivity
  have hlogNp1 : Real.log (N + 1 : ℝ) ≤ 6 * L :=
    (Real.log_le_log hNp1pos hNp1).trans hlog6X
  have htwoN : (2 * N + 1 : ℝ) ≤ 12 * X := by
    push_cast
    linarith
  have htwoNpos : 0 < (2 * N + 1 : ℝ) := by positivity
  have hlog12X : Real.log (12 * X) ≤ 12 * L := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    linarith
  have hlogTwoN : Real.log (2 * N + 1 : ℝ) ≤ 12 * L :=
    (Real.log_le_log htwoNpos htwoN).trans hlog12X
  exact ⟨huX, hlu, hlogN, hlogNp1, hlogTwoN⟩

/-- Uniform inside-Perron endpoint bound on `N ≤ 5X`. -/
theorem norm_insideComponent_endpoint_le
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {N : ℕ} {X T : ℝ} (hN : 1 ≤ N) (hNX : (N : ℝ) ≤ 5 * X)
    (hX : Real.exp 1 ≤ X) (hT : 0 < T) :
    ‖insideKernelError chi N (standardEdge N) T‖ ≤
      3000 * X * (Real.log X) ^ 2 / T := by
  obtain ⟨huX, hlu, hlogN, -, -⟩ := endpoint_scale_log_bounds hN hNX hX
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hL : 1 ≤ Real.log X := (Real.le_log_iff_exp_le hX0).2 hX
  have hu1 : 1 < halfIntegerPoint N := by
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    unfold halfIntegerPoint
    linarith
  have hlu0 : 0 ≤ Real.log (halfIntegerPoint N) := (Real.log_pos hu1).le
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hN)
  have hnum :
      3 * Real.exp 1 * halfIntegerPoint N *
          Real.log (halfIntegerPoint N) ≤
        3 * 3 * (6 * X) * (6 * Real.log X) := by
    gcongr
    exact Real.exp_one_lt_three.le
  have hnum0 : 0 ≤ 3 * 3 * (6 * X) * (6 * Real.log X) := by positivity
  have hfactor :
      3 * Real.exp 1 * halfIntegerPoint N *
          Real.log (halfIntegerPoint N) / (Real.pi * T) ≤
        3 * 3 * (6 * X) * (6 * Real.log X) / T := by
    calc
      3 * Real.exp 1 * halfIntegerPoint N *
          Real.log (halfIntegerPoint N) / (Real.pi * T) ≤
        (3 * 3 * (6 * X) * (6 * Real.log X)) /
          (Real.pi * T) :=
        div_le_div_of_nonneg_right hnum (mul_pos Real.pi_pos hT).le
      _ ≤ (3 * 3 * (6 * X) * (6 * Real.log X)) / T :=
        div_le_div_of_nonneg_left hnum0 hT (by nlinarith [Real.pi_gt_three])
  have hfactor0 : 0 ≤
      3 * 3 * (6 * X) * (6 * Real.log X) / T := by positivity
  have hbase := PaperEdgePerronRemainder.norm_insideKernelError_standardEdge_le_log
    chi N hN hT
  change ‖insideKernelError chi N (standardEdge N) T‖ ≤ _
  change ‖insideKernelError chi N
      (1 + (Real.log (halfIntegerPoint N))⁻¹) T‖ ≤ _
  calc
    ‖insideKernelError chi N
        (1 + (Real.log (halfIntegerPoint N))⁻¹) T‖ ≤
      (3 * Real.exp 1 * halfIntegerPoint N *
        Real.log (halfIntegerPoint N) / (Real.pi * T)) *
          (1 + Real.log N) := hbase
    _ ≤ (3 * 3 * (6 * X) * (6 * Real.log X) / T) *
          (7 * Real.log X) := by
      exact mul_le_mul hfactor (by linarith)
        (by linarith) hfactor0
    _ = 2268 * X * (Real.log X) ^ 2 / T := by ring
    _ ≤ 3000 * X * (Real.log X) ^ 2 / T := by
      gcongr <;> norm_num

/-- Uniform outside-Perron endpoint bound on `N ≤ 5X`. -/
theorem norm_outsideComponent_endpoint_le
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {N : ℕ} {X T : ℝ} (hN : 1 ≤ N) (hNX : (N : ℝ) ≤ 5 * X)
    (hX : Real.exp 1 ≤ X) (hT : 0 < T) :
    ‖coefficientTail chi (halfIntegerPoint N) (standardEdge N) T
        (Finset.Icc 1 N)‖ ≤
      9000 * X * (Real.log X) ^ 2 / T := by
  obtain ⟨huX, hlu, -, hlogNp1, hlogTwoN⟩ :=
    endpoint_scale_log_bounds hN hNX hX
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hL : 1 ≤ Real.log X := (Real.le_log_iff_exp_le hX0).2 hX
  have hu1 : 1 < halfIntegerPoint N := by
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    unfold halfIntegerPoint
    linarith
  have hlu0 : 0 < Real.log (halfIntegerPoint N) := Real.log_pos hu1
  have hharm : ((harmonic (N + 1) : ℚ) : ℝ) ≤ 7 * Real.log X := by
    calc
      ((harmonic (N + 1) : ℚ) : ℝ) ≤ 1 + Real.log ((N + 1 : ℕ) : ℝ) :=
        harmonic_le_one_add_log (N + 1)
      _ = 1 + Real.log ((N : ℝ) + 1) := by norm_num
      _ ≤ 7 * Real.log X := by linarith
  have hharm0 : 0 ≤ ((harmonic (N + 1) : ℚ) : ℝ) := by
    exact_mod_cast (harmonic_pos (Nat.succ_ne_zero N)).le
  have hsecond :
      (4 / (Real.log (halfIntegerPoint N))⁻¹) *
          (1 + (((Real.log (halfIntegerPoint N))⁻¹ / 2)⁻¹)) ≤
        312 * (Real.log X) ^ 2 := by
    have heq :
        (4 / (Real.log (halfIntegerPoint N))⁻¹) *
            (1 + (((Real.log (halfIntegerPoint N))⁻¹ / 2)⁻¹)) =
          4 * Real.log (halfIntegerPoint N) *
            (1 + 2 * Real.log (halfIntegerPoint N)) := by
      field_simp [hlu0.ne']
    rw [heq]
    have hinner : 1 + 2 * Real.log (halfIntegerPoint N) ≤
        1 + 12 * Real.log X := by linarith
    calc
      4 * Real.log (halfIntegerPoint N) *
          (1 + 2 * Real.log (halfIntegerPoint N)) ≤
        4 * (6 * Real.log X) * (1 + 12 * Real.log X) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hlu (by norm_num)) hinner
            (by positivity) (by positivity)
      _ ≤ 312 * (Real.log X) ^ 2 := by nlinarith
  have hbracket :
      2 * Real.log (2 * N + 1 : ℝ) *
            ((harmonic (N + 1) : ℚ) : ℝ) +
          (4 / (Real.log (halfIntegerPoint N))⁻¹) *
            (1 + (((Real.log (halfIntegerPoint N))⁻¹ / 2)⁻¹)) ≤
        480 * (Real.log X) ^ 2 := by
    have hfirst :
        2 * Real.log (2 * N + 1 : ℝ) *
            ((harmonic (N + 1) : ℚ) : ℝ) ≤
          2 * (12 * Real.log X) * (7 * Real.log X) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hlogTwoN (by norm_num)) hharm
        hharm0 (by positivity)
    calc
      2 * Real.log (2 * N + 1 : ℝ) *
            ((harmonic (N + 1) : ℚ) : ℝ) +
          (4 / (Real.log (halfIntegerPoint N))⁻¹) *
            (1 + (((Real.log (halfIntegerPoint N))⁻¹ / 2)⁻¹)) ≤
        2 * (12 * Real.log X) * (7 * Real.log X) +
          312 * (Real.log X) ^ 2 := by
            exact add_le_add hfirst hsecond
      _ = 480 * (Real.log X) ^ 2 := by ring
  have hbase :=
    PaperEdgeOutsidePerronTail.norm_coefficientTail_standardEdge_le
      chi N hN hT
  have hfactor :
      Real.exp 1 * halfIntegerPoint N / (Real.pi * T) ≤
        3 * (6 * X) / T := by
    have hnum : Real.exp 1 * halfIntegerPoint N ≤ 3 * (6 * X) :=
      mul_le_mul Real.exp_one_lt_three.le huX (halfIntegerPoint_pos N).le
        (by norm_num)
    have hnum0 : 0 ≤ 3 * (6 * X) := by positivity
    calc
      Real.exp 1 * halfIntegerPoint N / (Real.pi * T) ≤
        (3 * (6 * X)) / (Real.pi * T) :=
          div_le_div_of_nonneg_right hnum (mul_pos Real.pi_pos hT).le
      _ ≤ (3 * (6 * X)) / T :=
        div_le_div_of_nonneg_left hnum0 hT (by nlinarith [Real.pi_gt_three])
  have hbracket0 : 0 ≤
      2 * Real.log (2 * N + 1 : ℝ) *
            ((harmonic (N + 1) : ℚ) : ℝ) +
          (4 / (Real.log (halfIntegerPoint N))⁻¹) *
            (1 + (((Real.log (halfIntegerPoint N))⁻¹ / 2)⁻¹)) := by
    have hlogTwoN0 : 0 ≤ Real.log (2 * N + 1 : ℝ) := by
      apply Real.log_nonneg
      push_cast
      have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    rw [show (4 / (Real.log (halfIntegerPoint N))⁻¹) *
            (1 + (((Real.log (halfIntegerPoint N))⁻¹ / 2)⁻¹)) =
          4 * Real.log (halfIntegerPoint N) *
            (1 + 2 * Real.log (halfIntegerPoint N)) by
      field_simp [hlu0.ne']]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hlogTwoN0) hharm0)
      (mul_nonneg
        (mul_nonneg (by norm_num) hlu0.le)
        (by linarith [hlu0]))
  change ‖coefficientTail chi (halfIntegerPoint N) (standardEdge N) T
      (Finset.Icc 1 N)‖ ≤ _
  calc
    ‖coefficientTail chi (halfIntegerPoint N) (standardEdge N) T
        (Finset.Icc 1 N)‖ ≤
      (Real.exp 1 * halfIntegerPoint N / (Real.pi * T)) *
        (2 * Real.log (2 * N + 1 : ℝ) *
            ((harmonic (N + 1) : ℚ) : ℝ) +
          (4 / (Real.log (halfIntegerPoint N))⁻¹) *
            (1 + (((Real.log (halfIntegerPoint N))⁻¹ / 2)⁻¹))) := hbase
    _ ≤ (3 * (6 * X) / T) * (480 * (Real.log X) ^ 2) := by
      exact mul_le_mul hfactor hbracket hbracket0 (by positivity)
    _ = 8640 * X * (Real.log X) ^ 2 / T := by ring
    _ ≤ 9000 * X * (Real.log X) ^ 2 / T := by
      gcongr <;> norm_num

/-- Uniform normalized aligned inside-window bound at every legal aperture. -/
theorem norm_insideComponent_window_div_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor]
    {X T x Y H : ℝ} (hX : Real.exp 1 ≤ X) (hT : 0 < T)
    (hx : 1 ≤ x) (hY : 0 < Y) (hxy : x + Y ≤ 5 * X)
    (hHY : H ≤ Y) (hH : 0 < H) :
    ‖(insideComponent chi T (x + Y) - insideComponent chi T x) /
        (Y : ℂ)‖ ≤
      6000 * X * (Real.log X) ^ 2 / (T * H) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hxy1 : 1 ≤ x + Y := by linarith
  have hNx : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hNxy : 1 ≤ ⌊x + Y⌋₊ := Nat.le_floor (by exact_mod_cast hxy1)
  have hfloorX : (⌊x⌋₊ : ℝ) ≤ 5 * X :=
    (Nat.floor_le hx0).trans (by linarith)
  have hfloorXY : (⌊x + Y⌋₊ : ℝ) ≤ 5 * X :=
    (Nat.floor_le (by linarith)).trans hxy
  have hIx := norm_insideComponent_endpoint_le chi.primitiveCharacter
    hNx hfloorX hX hT
  have hIxy := norm_insideComponent_endpoint_le chi.primitiveCharacter
    hNxy hfloorXY hX hT
  have hIx' : ‖insideComponent chi T x‖ ≤
      3000 * X * (Real.log X) ^ 2 / T := by
    simpa [insideComponent] using hIx
  have hIxy' : ‖insideComponent chi T (x + Y)‖ ≤
      3000 * X * (Real.log X) ^ 2 / T := by
    simpa [insideComponent] using hIxy
  have hnum := (norm_sub_le (insideComponent chi T (x + Y))
    (insideComponent chi T x)).trans (add_le_add hIxy' hIx')
  have hnum' : ‖insideComponent chi T (x + Y) - insideComponent chi T x‖ ≤
      6000 * X * (Real.log X) ^ 2 / T := by
    calc
      _ ≤ 3000 * X * (Real.log X) ^ 2 / T +
          3000 * X * (Real.log X) ^ 2 / T := hnum
      _ = _ := by ring
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hP0 : 0 ≤ 6000 * X * (Real.log X) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) hX0.le) (sq_nonneg _)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY]
  calc
    ‖insideComponent chi T (x + Y) - insideComponent chi T x‖ / Y ≤
      (6000 * X * (Real.log X) ^ 2 / T) / Y :=
        div_le_div_of_nonneg_right hnum' hY.le
    _ = (6000 * X * (Real.log X) ^ 2) / (T * Y) := by ring
    _ ≤ (6000 * X * (Real.log X) ^ 2) / (T * H) := by
      apply div_le_div_of_nonneg_left hP0 (mul_pos hT hH)
      exact mul_le_mul_of_nonneg_left hHY hT.le

/-- Uniform normalized aligned outside-window bound at every legal aperture. -/
theorem norm_outsideComponent_window_div_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor]
    {X T x Y H : ℝ} (hX : Real.exp 1 ≤ X) (hT : 0 < T)
    (hx : 1 ≤ x) (hY : 0 < Y) (hxy : x + Y ≤ 5 * X)
    (hHY : H ≤ Y) (hH : 0 < H) :
    ‖(outsideComponent chi T (x + Y) - outsideComponent chi T x) /
        (Y : ℂ)‖ ≤
      18000 * X * (Real.log X) ^ 2 / (T * H) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hxy1 : 1 ≤ x + Y := by linarith
  have hNx : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hNxy : 1 ≤ ⌊x + Y⌋₊ := Nat.le_floor (by exact_mod_cast hxy1)
  have hfloorX : (⌊x⌋₊ : ℝ) ≤ 5 * X :=
    (Nat.floor_le hx0).trans (by linarith)
  have hfloorXY : (⌊x + Y⌋₊ : ℝ) ≤ 5 * X :=
    (Nat.floor_le (by linarith)).trans hxy
  have hEx := norm_outsideComponent_endpoint_le chi.primitiveCharacter
    hNx hfloorX hX hT
  have hExy := norm_outsideComponent_endpoint_le chi.primitiveCharacter
    hNxy hfloorXY hX hT
  have hEx' : ‖outsideComponent chi T x‖ ≤
      9000 * X * (Real.log X) ^ 2 / T := by
    simpa [outsideComponent] using hEx
  have hExy' : ‖outsideComponent chi T (x + Y)‖ ≤
      9000 * X * (Real.log X) ^ 2 / T := by
    simpa [outsideComponent] using hExy
  have hnum := (norm_sub_le (outsideComponent chi T (x + Y))
    (outsideComponent chi T x)).trans (add_le_add hExy' hEx')
  have hnum' : ‖outsideComponent chi T (x + Y) - outsideComponent chi T x‖ ≤
      18000 * X * (Real.log X) ^ 2 / T := by
    calc
      _ ≤ 9000 * X * (Real.log X) ^ 2 / T +
          9000 * X * (Real.log X) ^ 2 / T := hnum
      _ = _ := by ring
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hP0 : 0 ≤ 18000 * X * (Real.log X) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) hX0.le) (sq_nonneg _)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY]
  calc
    ‖outsideComponent chi T (x + Y) - outsideComponent chi T x‖ / Y ≤
      (18000 * X * (Real.log X) ^ 2 / T) / Y :=
        div_le_div_of_nonneg_right hnum' hY.le
    _ = (18000 * X * (Real.log X) ^ 2) / (T * Y) := by ring
    _ ≤ (18000 * X * (Real.log X) ^ 2) / (T * H) := by
      apply div_le_div_of_nonneg_left hP0 (mul_pos hT hH)
      exact mul_le_mul_of_nonneg_left hHY hT.le

end

end MAPAPPerronEndpointUniformBound
