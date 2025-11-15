import Mathlib.Tactic
import Mathlib.Order.Monotone.Defs
import Mathlib.Data.Int.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-- "Increasing" translates to mathlib as `StrictMono` -/
theorem zad1_inc [Preorder α] [Preorder β] [Preorder γ] {f : α → β} {g : β → γ}
    (hf : StrictMono f) (hg : StrictMono g) : StrictMono (g ∘ f) :=
  hg.comp hf

/-- "Decreasing" translates to mathlib as `StrictAnti` -/
theorem zad1_dec [Preorder α] [Preorder β] [Preorder γ] {f : α → β} {g : β → γ}
    (hf : StrictAnti f) (hg : StrictAnti g) : StrictMono (g ∘ f) :=
  hg.comp hf

theorem zad2a : (fun (⟨k, l⟩ : ℤ × ℤ) => min k l).Surjective := by
  simp [Function.Surjective]
  exact fun b => ⟨b, b, min_self b⟩

theorem zad2b : ¬(fun (⟨k, l⟩ : ℤ × ℤ) => min k l).Injective := by
  simp [Function.Injective]
  exact ⟨0, 1, 0, 2, rfl, fun _ => nofun⟩

theorem zad3_inj : Set.InjOn (fun x : ℝ => x^2 - 4*x + 1) (Set.Iio 2) := by
  simp [Set.InjOn]
  intro x hx y hy heq
  rw [← sub_right_inj, ← pow_left_inj₀]
  · rw [sub_sq_comm 2 x, sub_sq_comm 2 y]; grind
  · simp; exact le_of_lt hx
  · simp; exact le_of_lt hy
  · norm_num

theorem zad3_inv : Set.LeftInvOn (fun y : ℝ => 2 - (y + 3).sqrt)
    (fun x : ℝ => x^2 - 4*x + 1) (Set.Iio 2) := by
  simp [Set.LeftInvOn]
  intro x hx
  apply sub_eq_of_eq_add'; apply eq_add_of_sub_eq
  rw [← Real.sqrt_sq (x := 2 - x)]
  · grind
  · simp; exact le_of_lt hx

open Real

theorem zad5a : arcsin (-1/2) = -π / 6 := by
  rw [neg_div, neg_div, arcsin_neg]
  congr
  apply arcsin_eq_of_sin_eq sin_pi_div_six
  simp; constructor <;> (field_simp; norm_num)

theorem zad5b : arcsin (sqrt 3 / 2) = π / 3 := by
  apply arcsin_eq_of_sin_eq sin_pi_div_three
  simp; constructor <;> (field_simp; norm_num)

theorem zad5c : arccos 0 = π / 2 := arccos_zero

theorem zad5d : arctan 0 = 0 := arctan_zero

/-- For some reason arc cotangent isn't defined in mathlib -/
noncomputable def Real.arccot (x : ℝ) : ℝ := π / 2 - arctan x

theorem zad5e : arccot 0 = π / 2 := by simp [arccot]

theorem zad5f : arccot (-sqrt 3) = (5/6)*π := by
  simp [arccot]
  apply add_eq_of_eq_sub'
  ring_nf; simp
  apply arctan_eq_of_tan_eq tan_pi_div_three
  simp; constructor <;> (field_simp; norm_num)

theorem zad5g : arccot (tan (7 / 8 * π)) = (5 / 8) * π := by
  rw [arccot, ← tan_sub_pi, sub_eq_of_eq_add]
  apply eq_add_of_sub_eq'
  ring_nf
  rw [arctan_tan] <;> (field_simp; norm_num)

theorem zad5h : cos (2 * arcsin (4 / 5)) = -7 / 25 := by
  rw [cos_two_mul, cos_arcsin, sub_eq_of_eq_add]
  ring_nf

theorem zad5i : arccos (sin (15 / 7 * π)) = (5 / 14) * π := by
  rw [arccos, ← sin_sub_two_pi, arcsin_sin] <;> (field_simp; norm_num)

theorem zad5j : sin (1 / 2 * arccos (3 / 7)) = sqrt (2 / 7) := by
  rw [one_div_mul_eq_div, sin_half_eq_sqrt, cos_arccos] <;> (field_simp; norm_num)
  · exact arccos_nonneg _
  · calc
      arccos (3 / 7) ≤ π := arccos_le_pi (3 / 7)
      π ≤ 2 * π := by field_simp; norm_num

theorem zad6a : Set.LeftInvOn (fun y => π - arcsin y) sin (Set.Icc (π / 2) (3 / 2 * π)) := by
  simp [Set.LeftInvOn]
  intro x hl hr
  rw [← sin_pi_sub, arcsin_sin]
  · field
  · norm_num; ring_nf at ⊢ hr; assumption
  · rw [sub_le_comm]; ring_nf at ⊢ hl; assumption

theorem zad6b : Set.LeftInvOn (fun y => arccos y + π / 2) sin (Set.Icc (π / 2) (3 / 2 * π)) := by
  simp [Set.LeftInvOn, arccos]
  intro x hl hr
  rw [← sin_pi_sub, arcsin_sin]
  · field
  · norm_num; ring_nf at ⊢ hr; assumption
  · rw [sub_le_comm]; ring_nf at ⊢ hl; assumption

theorem zad7 : Set.LeftInvOn (fun y => (3 / 2 * π) - arccot y) tan
    (Set.Ioo (3 / 4 * π) (5 / 4 * π)) := by
  simp [Set.LeftInvOn, arccot]
  intro x hl hr
  rw [← tan_sub_pi, arctan_tan]
  · field
  · rw [lt_sub_iff_add_lt]; ring_nf; calc
      π * (1 / 2) < 3 / 4 * π := by field_simp; norm_num
      _ < x := hl
  · rw [sub_lt_iff_lt_add]; ring_nf; calc
      x < 5 / 4 * π := hr
      _ < π * (3 / 2) := by field_simp; norm_num
