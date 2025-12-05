import Inf.AM1.Limit
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

theorem HasLim'.one_add_inv_pow {a : ℕ → ℝ} (h : HasLim' a ⊤) :
    HasLim (fun n => (1 + (a n)⁻¹) ^ (a n)) (Real.exp 1) := by
  rw [hasLim_iff_tendsto]
  convert (Real.tendsto_one_add_div_rpow_exp 1).comp (hasLim'_top_iff_tendsto.mp h)
  simp

namespace AM1.Cwi3

/-- Here, it's significant that we're working with `PNat` and not `ℕ` -/
theorem Zad1a : Antitone fun (n : PNat) => (4 ^ n.val : ℚ) / (n.val + 2).factorial := by
  suffices Antitone fun n => (4 ^ (n + 1) : Rat) / (n + 1 + 2).factorial by
    simp [Antitone] at *
    intro a b hab; specialize @this a.natPred b.natPred; simp at this; exact this hab
  apply antitone_nat_of_succ_le; intro n
  rw [div_le_div_iff₀, mul_comm (4 ^ (n + 1)), ←div_le_div_iff₀, Nat.factorial] <;> try positivity
  simp [Rat.pow_succ, mul_div_assoc]; rw [div_self] <;> try positivity
  linarith

theorem Zad1b_below : BddBelow (Set.range fun (n : ℕ) => 1 + (n : ℝ) ^ (3⁻¹ : ℝ)) := by
  simp [bddBelow_def]; exists 1; intro n; simp; positivity

theorem Zad1b_above : ¬BddAbove (Set.range fun (n : ℕ) => 1 + (n : ℝ) ^ (3⁻¹ : ℝ)) := by
  simp [bddAbove_def]; intro x; exists ⌈x⌉₊ ^ 3; simp
  rw [←Real.rpow_ofNat, Real.rpow_rpow_inv] <;> try simp
  grw [←Nat.le_ceil x]; simp

theorem Zad2a : HasLim (fun n => (2 * n - 1) / (4 * n + 1) : ℕ → ℚ) (1 / 2) := by
  intro e he; exists ⌊(3 / (8 * e)) - (1 / 4)⌋₊ + 1; intro n hn
  rw [abs_sub_comm, div_sub_div]; ring_nf; rw [abs_of_nonneg]
  replace hn := lt_of_lt_of_le (Nat.lt_floor_add_one ((3 / (8 * e)) - (1 / 4)))
    (Nat.cast_one (R := ℚ) ▸ Nat.cast_add (R := ℚ) ⌊3 / (8 * e) - 1 / 4⌋₊ 1 ▸ Nat.cast_le.mpr hn)
  rw [sub_lt_iff_lt_add, ← div_div, div_lt_comm₀] at hn
  field_simp; field_simp at hn; grind
  repeat positivity

theorem Zad2b : HasLim' (fun n => (3 : ℚ) - 2 * n) ⊥ := by
  intro D; exists ⌊(3 - D) / 2⌋₊ + 1; intro n hn
  replace hn := lt_of_lt_of_le (Nat.lt_floor_add_one ((3 - D) / 2))
    (Nat.cast_one (R := ℚ) ▸ Nat.cast_add (R := ℚ) ⌊(3 - D) / 2⌋₊ 1 ▸ Nat.cast_le.mpr hn)
  linarith

open HasLim HasLim' Real

theorem Zad3 : HasLim (fun n => 3 ^ n / n.factorial : ℕ → ℚ) 0 := by
  refine const_squeeze ⟨0, fun n _ => by positivity⟩ ?_ (hasLim_const_pow (a := 3 / 4) (by norm_num))
  exists 9; intro n hn; induction hn
  case refl => norm_num
  case step n hn ih =>
    suffices (3 : ℚ) ^ n / n.factorial * (3 / n.succ) ≤ (3 / 4) ^ n * (3 / 4) by
      simp [Nat.factorial, pow_succ] at *; field_simp at *; assumption
    apply mul_le_mul ih <;> try positivity
    field_simp; simp at hn; norm_cast; omega

theorem Zad4 {an : ℕ → ℝ} {a : ℝ} (hnn : ∀ n, 0 ≤ an n) (h : HasLim an a) :
    HasLim (an ^ (3⁻¹ : ℝ)) (a ^ (3⁻¹ : ℝ)) := h.pow_const' hnn (by simp)

theorem Zad5a : HasLim' (fun n => n ^ 2 / (sqrt (n + 1) - sqrt (n + 4))) ⊥ := by
  apply HasLim'.of_eq (fun n => by calc
    n ^ 2 / (sqrt (n + 1) - sqrt (n + 4)) =
        ((sqrt (n + 1) + sqrt (n + 4)) * n ^ 2) / ((sqrt (n + 1) + sqrt (n + 4)) * _) := by
      symm; refine mul_div_mul_left _ _ ?_; positivity
    _ = ((sqrt (n + 1) + sqrt (n + 4)) * n ^ 2) / -3 := by
      rw [← sq_sub_sq, Real.sq_sqrt, Real.sq_sqrt]; norm_num; repeat positivity
  )
  have h1 := (HasLim'.id.top_add (const (1 : ℝ)).bddBelow).top_pow_const' (half_pos one_pos)
  have h2 := (HasLim'.id.top_add (const (4 : ℝ)).bddBelow).top_pow_const' (half_pos one_pos)
  convert ((h1.add h2).top_mul_top (top_pow_const' zero_lt_two id)).top_mul_neg (by simp) (const (-3)⁻¹) using 1
  simp [div_eq_mul_inv, Real.sqrt_eq_rpow]

noncomputable def _root_.Real.cbrt := fun r : ℝ => r.rpow 3⁻¹

theorem Zad5b : HasLim (fun n => n * (cbrt (n ^ 3 + n) - n)) (1 / 3) := by
  apply HasLim.of_eventually_eq ⟨1, fun n hn => by calc
    n * (cbrt (n ^ 3 + n) - n) = n * n / (cbrt (n ^ 3 + n) ^ 2 + cbrt (n ^ 3 + n) * n + n ^ 2) := by
      rw [mul_div_assoc]; simp; left
      simp [cbrt]; apply eq_div_of_mul_eq (by positivity)
      ring_nf; simp; rw [← Nat.cast_ofNat (R := ℝ)]
      rw [rpow_inv_natCast_pow (by positivity) (by simp)]; simp
    _ = ((cbrt (n ^ 3 + n) / n) ^ 2 + cbrt (n ^ 3 + n) / n + 1)⁻¹ := by
      rw [← inv_div]; congr
      simp [add_div]; congr 2
      · simp [← sq, ← div_pow]
      · rw [mul_div_mul_right]; positivity
      · simp [sq]; rw [div_self]; positivity
    _ = (cbrt (1 + (n⁻¹ : ℝ) ^ 2) ^ 2 + cbrt (1 + (n⁻¹ : ℝ) ^ 2) + 1)⁻¹ := by
      congr; all_goals (
        nth_rw 3 [← pow_rpow_inv_natCast (show 0 ≤ (n : ℝ) by positivity) (show 3 ≠ 0 by simp)]
        simp [cbrt]; rw [← div_rpow] <;> try positivity
        field_simp
      )
  ⟩
  simp; apply inv; case hg => simp
  rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num]; simp [cbrt]
  apply add_const; apply HasLim.add
  · convert (((HasLim'.id.top_pow_const' zero_lt_two).inv_top.const_add _).pow_const' ?_ (inv_nonneg.mpr zero_le_three)).pow_const' ?_ zero_le_two
    · simp; rfl
    · simp
    all_goals intro n; positivity
  · convert ((HasLim'.id.top_pow_const' zero_lt_two).inv_top.const_add _).pow_const' ?_ (inv_nonneg.mpr zero_le_three) <;> simp
    intro n; positivity

theorem Zad5c : HasLim (fun n => (n ^ 2 + 5 : ℝ) ^ (n⁻¹ : ℝ)) 1 := by
  apply squeeze (a := fun n => (n ^ 2 : ℝ) ^ (n⁻¹ : ℝ)) (c := fun n => ((2 * n) ^ 2 : ℝ) ^ (n⁻¹ : ℝ))
  · exact ⟨0, fun n hn => by apply rpow_le_rpow <;> simp⟩
  · exact ⟨2, fun n hn => by
      norm_cast; apply rpow_le_rpow
      · positivity
      · gcongr; rw [ge_iff_le, ← sq_le_sq₀ zero_le_two n.zero_le] at hn; linarith
      · simp⟩
  · refine of_eq (fun n => (rpow_pow_comm n.cast_nonneg n⁻¹ 2).symm) ?_
    rw [← one_pow 2]; convert hasLim_pow_inv.pow_const' (fun n => by positivity) zero_le_two <;> norm_num
  · apply HasLim.of_eq (fun n => by calc
      ((2 * n) ^ 2 : ℝ) ^ (n : ℝ)⁻¹ = ((2 * n) ^ (n : ℝ)⁻¹) ^ 2 := (rpow_pow_comm (by positivity) n⁻¹ 2).symm
      _ = (2 ^ (n⁻¹ : ℝ) * n ^ (n⁻¹ : ℝ)) ^ (2 : ℝ) := by simp; congr; exact mul_rpow zero_le_two (by simp)
      _ = (2 ^ (n⁻¹ : ℝ)) ^ (2 : ℝ) * (n ^ (n⁻¹ : ℝ)) ^ (2 : ℝ) := (mul_rpow (by positivity) (by positivity))
    )
    convert ((hasLim_const_pow_inv one_lt_two).pow_const' (fun n => by positivity) zero_le_two).mul
      (hasLim_pow_inv.pow_const' (fun n => by positivity) zero_le_two)
    simp

theorem Zad5d : HasLim (fun n => (7 ^ n + (-3) ^ n : ℝ) ^ (n⁻¹ : ℝ)) 7 := by
  apply squeeze (a := fun n => (7 ^ (n - 1) : ℝ) ^ (n⁻¹ : ℝ)) (c := fun n => (7 ^ n + 7 ^ n : ℝ) ^ (n⁻¹ : ℝ))
  · exact ⟨1, fun n hn => by
      apply rpow_le_rpow
      · simp
      · rw [neg_pow]; cases neg_one_pow_eq_or ℝ n <;> simp [*]
        · exact le_trans (pow_le_pow_right₀ (by simp) (show n - 1 ≤ n by simp)) (le_add_of_nonneg_right (by positivity))
        · calc
            (7 : ℝ) ^ (n - 1) + 3 ^ n = 7 ^ (n - 1) + 3 * 3 ^ (n - 1) := by simp; rw [mul_pow_sub_one]; positivity
            _ ≤ 7 ^ (n - 1) + 6 * 7 ^ (n - 1) := by
              simp; apply mul_le_mul <;> (try norm_num); apply pow_le_pow_left₀ <;> norm_num
            _ = 7 ^ n := by simp [← one_add_mul]; norm_num; rw [mul_pow_sub_one]; positivity
      · positivity⟩
  · exact ⟨0, fun n hn => by
      apply rpow_le_rpow
      · rw [neg_pow]; cases neg_one_pow_eq_or ℝ n <;> simp [*]
        · positivity
        · apply pow_le_pow_left₀ <;> norm_num
      · simp; rw [neg_pow]; cases neg_one_pow_eq_or ℝ n <;> simp [*]
        · apply pow_le_pow_left₀ <;> norm_num
        · exact le_trans (show -3 ^ n ≤ 0 by simp) (by positivity)
      · simp⟩
  · apply HasLim.of_eventually_eq ⟨1, fun n hn => by calc
      ((7 : ℝ) ^ (n - 1)) ^ (n : ℝ)⁻¹ = (7 ^ n / 7) ^ (n : ℝ)⁻¹ := by congr; field_simp; rw [pow_sub_one_mul]; positivity
      _ = 7 / 7 ^ (n : ℝ)⁻¹ := by rw [div_rpow, pow_rpow_inv_natCast] <;> positivity
    ⟩
    convert const_div 7 (hasLim_const_pow_inv (show 1 < 7 by norm_num)); simp
  · apply HasLim.of_eventually_eq ⟨1, fun n hn => by calc
      (7 ^ n + 7 ^ n : ℝ) ^ (n : ℝ)⁻¹ = (2 * 7 ^ n) ^ (n : ℝ)⁻¹ := by congr; symm; exact two_mul _
      _ = 2 ^ (n : ℝ)⁻¹ * 7 := by rw [mul_rpow, pow_rpow_inv_natCast] <;> positivity
    ⟩
    convert mul_const 7 (hasLim_const_pow_inv (show 1 < 2 by norm_num)); simp

theorem Zad6 {a : ℕ → ℤ} {g : ℝ} (h : HasLim (fun n => (a n : ℝ)) g) : ∃ n₀, ∀ n ≥ n₀, a n = g := by
  have ⟨n₀, h1⟩ := hasLim_iff_isCauSeq.mp ⟨g, h⟩ 1 (by simp); exists n₀
  have hc : ∀ n ≥ n₀, (a n₀ : ℝ) = a n := by
    intro n hn; replace ⟨h1, h2⟩ := abs_sub_lt_iff.mp (h1 n hn)
    rw [← Int.cast_one, ← Int.cast_sub, Int.cast_lt] at h1 h2
    congr 1; omega
  replace h := (HasLim.of_eventually_eq ⟨n₀, hc⟩ h).eq (const _)
  intro n hn; specialize hc n hn; rw [← hc, ← h]

theorem Zad7_sup {a : ℕ → ℝ} (h : HasLim a 0) (hp : ∀ n, 0 < a n) : iSup a ∈ Set.range a := by
  simp; have isup_pos := (lt_ciSup_iff h.bddAbove).mpr ⟨0, hp 0⟩
  replace ⟨n₀, h₀⟩ := h (iSup a / 2) (half_pos isup_pos); simp at h₀
  have hn₀ : n₀ ≠ 0 := by
    by_contra!; subst this; simp at h₀
    exact not_le_of_gt (half_lt_self isup_pos) (ciSup_le fun n => le_of_abs_le (h₀ n).le)
  have ⟨n, hn, hs⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_range_iff.mpr hn₀) a
  exists n
  refine ge_antisymm (ciSup_le ?bound) (le_ciSup h.bddAbove n)
  intro x; rw [← hs]; by_cases! x < n₀
  case pos hx => exact Finset.le_sup' a (by simpa)
  case neg hx =>
    by_contra!; replace this := lt_trans this (lt_of_abs_lt (h₀ x hx))
    refine not_le_of_gt (half_lt_self isup_pos) (ciSup_le fun n => ?_)
    by_cases! n < n₀
    case pos hn => exact le_trans (Finset.le_sup' a (by simpa)) this.le
    case neg hn => exact le_of_abs_le (h₀ n hn).le

theorem Zad7_inf {a : ℕ → ℝ} (h : HasLim a 0) (hp : ∀ n, 0 < a n) : iInf a ∉ Set.range a := by
  simp; suffices iInf a = 0 by rw [this]; exact fun n => ne_of_gt (hp n)
  refine ge_antisymm (le_ciInf fun n => (hp n).le) (Real.sInf_le_iff h.bddBelow (Set.range_nonempty a) |>.mpr ?_)
  simp [HasLim] at *; intro e he; replace ⟨n, h⟩ := h e he; exact ⟨n, lt_of_abs_lt (h n le_rfl)⟩

theorem Zad15 [Field R] [LinearOrder R] [IsOrderedRing R] : ¬ ∀ a b : ℕ → R,
    HasLim (a * b) 0 → (HasLim a 0 ∨ HasLim b 0) := by
  simp; exists (fun n => ↑(n % 2)), (fun n => ↑(1 - n % 2)); and_intros
  · apply HasLim.of_eq fun n => show ↑(n % 2) * ↑(1 - n % 2) = (0 : R) by
      by_cases h : n % 2 = 0
      · simp [h]
      · simp at h; simp [h]
    exact const 0
  · simp [HasLim]; exists 1, (by positivity); intro n; exists 2 * n + 1, (by omega); simp
  · simp [HasLim]; exists 1, (by positivity); intro n; exists 2 * n, (by omega); simp
