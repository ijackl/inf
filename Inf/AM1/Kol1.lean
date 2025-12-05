import Inf.AM1.Cwi3
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace AM1.Kol1

theorem Zad1 : ∀ n ≥ 2, ∑ k ∈ Finset.Icc 1 n, (1 / (k : ℕ) ^ 2 : ℚ) < 2 - 1 / n := by
  intro n hn
  induction hn
  case refl => simp [Finset.Icc_eq_cons_Ioc]; norm_num
  case step n hn ih =>
    simp [Finset.sum_Icc_succ_top] at *; grw [ih]
    have h : (n : ℚ)⁻¹ - (n + 1 : ℚ)⁻¹ = (n + n ^ 2 : ℚ)⁻¹ := by
        rw [inv_sub_inv] <;> try positivity
        grind
    rw [sub_add_eq_add_sub, sub_lt_iff_lt_add, add_comm_sub, h]
    simp; rw [inv_lt_inv₀, add_sq] <;> try positivity
    simp [two_mul]; linarith


open Real

theorem Zad2a : Set.InvOn (fun y => (π - arcsin y) / 2) (fun x => sin (2 * x)) (Set.Icc (π / 4) (π / 2)) (Set.Icc 0 1) := by
  simp [Set.InvOn, Set.LeftInvOn]; and_intros
  · intro x hl hu; rw [← sin_pi_sub, arcsin_sin] <;> linarith
  · intro x hl hu; field_simp; rw [sin_pi_sub, sin_arcsin] <;> linarith


theorem Zad2b : Set.InvOn (fun y => π / 4 + arccos y / 2) (fun x => sin (2 * x)) (Set.Icc (π / 4) (π / 2)) (Set.Icc 0 1) := by
  simp [Set.InvOn, Set.LeftInvOn]; and_intros
  · intro x hl hu; rw [arccos, ← sin_pi_sub, arcsin_sin] <;> linarith
  · intro x hl hu; rw [arccos]; ring_nf; rw [sin_pi_sub, sin_arcsin] <;> linarith

/-- This one is slightly modified to avoid taking cube roots of negative numbers (a painful endeavor) (it still ends up a painful endeavor btw). -/
theorem Zad3a : HasLim (fun n => (n - cbrt (n ^ 3 - 1)) * sqrt (n ^ 4 + 3 * n)) (1 / 3) := by
  apply HasLim.of_eventually_eq ⟨1, fun n hn => by calc
    (n - cbrt (n ^ 3 - 1)) * sqrt (n ^ 4 + 3 * n) =
      (n ^ 2 + n * cbrt (n ^ 3 - 1) + cbrt (n ^ 3 - 1) ^ 2) * _ * _ / (n ^ 2 + n * cbrt (n ^ 3 - 1) + cbrt (n ^ 3 - 1) ^ 2) := by
        rw [mul_assoc]; symm; apply mul_div_cancel_left₀
        apply left_ne_zero_of_mul (b := n - cbrt (n ^ 3 - 1))
        rw [cbrt]; ring_nf; simp; rw [← Nat.cast_ofNat (R := ℝ), Real.rpow_inv_natCast_pow] <;> simp
        apply one_le_pow₀; simpa
    _ = sqrt (n ^ 4 + 3 * n) / (n ^ 2 + n * cbrt (n ^ 3 - 1) + cbrt (n ^ 3 - 1) ^ 2) := by
      rw [mul_div_assoc, mul_left_eq_self₀]; left; ring_nf
      simp [cbrt]; rw [← Nat.cast_ofNat (R := ℝ), Real.rpow_inv_natCast_pow] <;> simp
      apply one_le_pow₀; simpa
    _ = 1 / ((n ^ 2 + n * cbrt (n ^ 3 - 1) + cbrt (n ^ 3 - 1) ^ 2) / sqrt (n ^ 4 + 3 * n)) := by simp
  ⟩
  apply HasLim.const_div; case hg => simp
  simp_rw [add_div, show (3 : ℝ) = 1 + 1 + 1 by norm_num]; repeat apply HasLim.add
  · norm_num; apply HasLim.of_eq (fun n => by calc
      n ^ 2 / √(n ^ 4 + 3 * n) = √(n ^ 4 / (n ^ 4 + 3 * n)) := by
        simp; congr; simp [sqrt_eq_rpow, eq_rpow_inv, ← pow_mul]
      _ = √(1 - 3 / (n ^ 3 + 3)) := by field_simp; simp
    )
    convert (HasLim'.id.top_pow_const' (show 0 < 3 by simp)).top_add (HasLim.const _).bddBelow
      |>.inv_top.const_mul 3 |>.const_sub 1 |>.pow_const' ?_ (show 0 ≤ 1 / 2 by simp) using 1
    · ext n; rw [Real.sqrt_eq_rpow]; congr 4; simp
    · simp
    · intro n; field_simp; simp
  · norm_num; apply HasLim.of_eventually_eq ⟨1, fun n hn => by calc
      n * cbrt (n ^ 3 - 1) / √(n ^ 4 + 3 * n) = (n ^ 6 * (n ^ 3 - 1) ^ 2 / (n ^ 4 + 3 * n) ^ 3) ^ (6 : ℝ)⁻¹ := by
        rw [div_rpow, mul_rpow] <;> first | positivity | congr
        · symm; convert pow_rpow_inv_natCast _ _ <;> simp
        · nth_rw 2 [← rpow_natCast]; rw [← rpow_mul, cbrt]; norm_num; simp
          rw [ge_iff_le, ← Nat.one_le_cast (α := ℝ)] at hn; exact one_le_pow₀ hn
        · nth_rw 2 [← rpow_natCast]; rw [← rpow_mul, sqrt_eq_rpow]; norm_num; positivity
    ⟩
    ring_nf; simp [← div_eq_mul_inv, div_mul_eq_mul_div]; rw [show (1 : ℝ) = (0 - 0 + 1) ^ (6 : ℝ)⁻¹ by simp]
    apply HasLim.pow_const' <;> try positivity
    · intro n; rw [← sub_div, ← add_div]; apply div_nonneg <;> try positivity
      convert show 0 ≤ ((n : ℝ) ^ 6 - n ^ 3) ^ 2 by positivity
      field
    apply HasLim.add; apply HasLim.sub
    · apply HasLim.const_squeeze (c := fun n => (n : ℝ) ^ 6 / (n ^ 6 + n ^ 12))
      · exact ⟨0, fun n hn => by positivity⟩
      · exact ⟨1, fun n hn => by gcongr; simp [← sub_nonneg]; ring_nf; positivity⟩
      · simp_rw [show 12 = 6 + 6 by simp, pow_add, ← mul_one_add]
        apply HasLim.of_eventually_eq ⟨1, fun n hn => div_mul_cancel_left₀ (by positivity) _⟩
        convert ((HasLim'.id.top_pow_const' (show 0 < 6 by simp)).add_top (HasLim.const 1).bddBelow).inv_top
        simp
    · apply HasLim.const_squeeze (c := fun n => (n : ℝ) ^ 9 * 2 / (n ^ 9 + n ^ 12))
      · exact ⟨0, fun n hn => by positivity⟩
      · exact ⟨1, fun n hn => by gcongr; simp [← sub_nonneg]; ring_nf; positivity⟩
      · simp_rw [show 12 = 9 + 3 by simp, pow_add, ← mul_one_add]
        apply HasLim.of_eventually_eq ⟨1, fun n hn => mul_div_mul_left _ _ (by positivity)⟩
        convert ((HasLim'.id.top_pow_const' (show 0 < 3 by simp)).add_top (HasLim.const 1).bddBelow).inv_top.const_mul 2 using 2
        simp [div_eq_mul_inv]; norm_num
    · rw [← inv_one]; convert HasLim.inv ?_ one_ne_zero using 1 <;> try exact inferInstance
      · ext n; symm; exact inv_div _ _
      apply HasLim.of_eventually_eq ⟨1, fun n hn => (div_add_one (by positivity)).symm⟩
      nth_rw 2 [show (1 : ℝ) = 0 + 1 by simp]; apply HasLim.add_const
      apply HasLim.const_squeeze (c := fun n => (n ^ 9 * 27 + n ^ 9 * 27 + n ^ 9 * 9) / (n : ℝ) ^ 12)
      · exact ⟨0, fun n hn => by positivity⟩
      · exact ⟨1, fun n hn => by gcongr <;> simp <;> assumption⟩
      · field_simp; norm_num; convert (HasLim'.id.top_pow_const' (show 0 < 3 by simp)).inv_top.const_mul 63 using 2
        simp [div_eq_mul_inv]; norm_num
  · norm_num; apply HasLim.of_eventually_eq ⟨1, fun n hn => by calc
      cbrt (n ^ 3 - 1) ^ 2 / √(n ^ 4 + 3 * n) = ((n ^ 3 - 1) ^ 4 / (n ^ 4 + 3 * n) ^ 3) ^ (6 : ℝ)⁻¹ := by
        rw [div_rpow, cbrt, rpow_eq_pow, sqrt_eq_rpow] <;> first | positivity | congr 1
        · nth_rw 1 [← rpow_natCast]; nth_rw 2 [← rpow_natCast]; rw [← rpow_mul, ← rpow_mul]; norm_num
          all_goals simp; norm_cast; exact one_le_pow₀ hn
        · nth_rw 2 [← rpow_natCast]; rw [← rpow_mul]; norm_num; positivity
      _ = (((n ^ 3 - 1) * (n ^ 3 - 1) ^ 3) / ((n : ℝ) ^ 3 * (n ^ 3 + 3) ^ 3)) ^ (6 : ℝ)⁻¹ := by
        congr; · exact pow_succ' _ 3
        rw [← mul_pow, mul_add, ← pow_succ', mul_comm]
      _ = ((n ^ 3 - 1) / n ^ 3 * ((n ^ 3 - 1) / (n ^ 3 + 3)) ^ 3) ^ (6 : ℝ)⁻¹ := by
        rw [div_pow]; congr 1; apply mul_div_mul_comm
    ⟩
    nth_rw 3 [show (1 : ℝ) = 1 ^ (6 : ℝ)⁻¹ by simp]; apply HasLim.pow_const' <;> try positivity
    · intro n; rw [div_pow, ← mul_div_mul_comm, ← pow_succ']; simp; positivity
    nth_rw 3 [show (1 : ℝ) = 1 * 1 by simp]; apply HasLim.mul
    · apply HasLim.of_eventually_eq ⟨1, fun n hn => (one_sub_div (by positivity)).symm⟩
      convert (HasLim'.id.top_pow_const' (show 0 < 3 by simp)).inv_top.const_sub 1 <;> try simp
      ext x; simp
    · nth_rw 2 [show (1 : ℝ) = 1 ^ 3 by simp]; simp_rw [pow_three]
      refine HasLim.mul ?h (HasLim.mul ?h ?h); simp [← pow_three]
      apply HasLim.of_eq fun n => show ((n : ℝ) ^ 3 - 1) / (n ^ 3 + 3) = 1 - 4 / (n ^ 3 + 3) by
        rw [one_sub_div]; ring; positivity
      have H := ((HasLim'.id.top_pow_const' (show 0 < 3 by simp)).top_add (HasLim.const 3).bddBelow).inv_top
      convert (H.const_mul 4).const_sub 1 using 3 <;> simp [div_eq_mul_inv]

theorem Zad3b : HasLim (fun n => ∑ k ∈ Finset.Icc 1 n, 1 / sqrt (n ^ 2 + k)) 1 := by
  apply HasLim.squeeze_const (a := fun n => ∑ k ∈ Finset.Icc 1 n, 1 / sqrt (n ^ 2 + 2 * n + 1))
  · exists 1; intro n hn; apply Finset.sum_le_sum
    intro k hk; apply div_le_div_of_nonneg_left <;> try positivity
    apply Real.sqrt_le_sqrt; simp [add_assoc]; norm_cast; replace hk := (Finset.mem_Icc.mp hk).2
    omega
  · exists 1; intro n hn
    have hsum : ∑ k ∈ Finset.Icc 1 n, 1 / sqrt (n ^ 2) = 1 := by simp; apply mul_inv_cancel₀; simp; omega
    nth_rw 2 [← hsum]; apply Finset.sum_le_sum; intro k hk; apply div_le_div_of_nonneg_left <;> try positivity
    apply Real.sqrt_le_sqrt; simp
  · simp; have h (r : ℕ) : √(r ^ 2 + 2 * r + 1) = r + 1 := by rw [Real.sqrt_eq_cases]; left; ring_nf; simp; positivity
    simp_rw [h]
    convert (HasLim'.id.top_add (HasLim.const (1 : ℝ)).bddBelow).inv_top.const_sub 1 using 2 <;> field
