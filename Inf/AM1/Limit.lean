import Mathlib.Tactic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.Algebra.Order.Ring.WithTop

/-! ## Roughly the content of lectures 2 & 3 -/

variable [Field R] [LinearOrder R]

/-- `g` is a limit of a sequence `a` iff the sequence is eventually bounded arbitrarily close to it. -/
def HasLim (a : ℕ → R) (g : R) := ∀ ε > 0, ∃ n₀, ∀ n ≥ n₀, abs (a n - g) < ε

/-- **Th. 2.1.** A constant sequence is convergent. -/
lemma HasLim.const [AddLeftMono R] (a : R) : HasLim (fun _ => a) a := by
  intro e he; exists 0; intro n hn; convert he.lt; simp

/-- **Th. 2.2.** A convergent sequence has only one limit. -/
lemma HasLim.unique [IsOrderedRing R] (a : ℕ → R) : Subsingleton {g // HasLim a g} where
  allEq := by
    simp [HasLim]
    intro g1 hg1 g2 hg2
    by_contra! h
    have he : 0 < abs (g1 - g2) / 2 := by field_simp; simp; grind
    have ⟨n1, hg1⟩ := hg1 _ he
    have ⟨n2, hg2⟩ := hg2 _ he
    let n := max n1 n2
    have hg1 := hg1 n (by omega)
    have hg2 := hg2 n (by omega)
    have h := add_lt_add hg1 hg2; revert h; simp
    convert abs_sub_le g1 (a n) g2 using 2
    exact abs_sub_comm (a n) g1

/-- **Th. 2.3.** A convergent sequence is bounded. -/
lemma HasLim.bddAbove [IsOrderedRing R] {a : ℕ → R} {g : R} (h : HasLim a g) :
    BddAbove (Set.range a) := by
  simp [HasLim, bddAbove_def] at *
  have ⟨n, h⟩ := h 1 (by simp)
  exists WithBot.unbot (↑(g + 1) ::ₘ (Multiset.range n).map ((↑) ∘ a)).sup ?H
  · simp --mathlib pls give us Multiset.sup'
  intro i; simp [WithBot.le_unbot_iff]
  by_cases! hi : i < n
  · right; apply Multiset.le_sup; apply Multiset.mem_map_of_mem; simpa
  · left; rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]
    have h := abs_lt.mp (h i hi)
    grind

/-- **Th. 2.3.** A convergent sequence is bounded. -/
lemma HasLim.bddBelow [IsOrderedRing R] {a : ℕ → R} {g : R} (h : HasLim a g) :
    BddBelow (Set.range a) := by
  simp [HasLim, bddBelow_def] at *
  have ⟨n, h⟩ := h 1 (by simp)
  exists WithTop.untop (↑(g - 1) ::ₘ (Multiset.range n).map ((↑) ∘ a)).inf ?H
  · simp
  intro i; simp [WithTop.untop_le_iff]
  by_cases! hi : i < n
  · right; apply Multiset.inf_le; apply Multiset.mem_map_of_mem; simpa
  · left; rw [← WithTop.coe_one, ← WithTop.LinearOrderedAddCommGroup.coe_sub, WithTop.coe_le_coe] -- "shouldn't create diamonds" my ass
    have h := abs_lt.mp (h i hi)
    grind

/-! **Th. 2.4.** Continuity of arithmetic operations: -/
lemma HasLim.add [IsOrderedRing R] {an bn : ℕ → R} {a b : R} (ha : HasLim an a) (hb : HasLim bn b) :
    HasLim (an + bn) (a + b) := by
  intro e he
  have ⟨n, hab⟩ := exists_forall_ge_and (ha (e / 2) (by positivity)) (hb (e / 2) (by positivity))
  exists n; intro n hn;
  have h := (hab n hn).elim add_lt_add; simp at h
  rw [Pi.add_apply, add_sub_add_comm]
  exact lt_of_le_of_lt (abs_add_le _ _) h

lemma HasLim.add_const {a : ℕ → R} {g b : R} (h : HasLim a g) :
    HasLim (a + fun _ => b) (g + b) := by simpa [HasLim]

lemma HasLim.const_add (a : ℕ → R) {g b : R} {h : HasLim a g} :
    HasLim ((fun _ => b) + a) (b + g) := by simpa [HasLim]

lemma HasLim.mul [IsOrderedRing R] {an bn : ℕ → R} {a b : R} (ha : HasLim an a) (hb : HasLim bn b) :
    HasLim (an * bn) (a * b) := by
  intro e he
  have ⟨n, hab⟩ := exists_forall_ge_and (ha (e / 2 / max (|a| + |b|) (e + 1)) (by positivity))
    (hb (e / 2 / max (|a| + |b|) (e + 1)) (by positivity))
  exists n; intro n hn; replace ⟨ha, hb⟩ := hab n hn
  have hab1 := mul_lt_mul'' ha hb (by simp) (by simp); rw [← abs_mul, ← sq] at hab1
  replace ha := mul_le_mul_of_nonneg_left ha.le (abs_nonneg b)
  replace hb := mul_le_mul_of_nonneg_left hb.le (abs_nonneg a)
  have hab2 := ((add_mul |a| |b| _) ▸ add_le_add hb ha).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ (e + 1)) (by positivity))
  field_simp at hab2; rw [← le_div_iff₀, ← abs_mul, ← abs_mul] at hab2
  simp [-abs_mul, mul_sub] at hab2
  apply (abs_add_le _ _).trans at hab2
  have hab := add_lt_add_of_lt_of_le hab1 hab2;
  apply lt_of_le_of_lt (abs_add_le _ _) at hab
  ring_nf at hab; refine lt_of_lt_of_le hab ?_
  field_simp; rw [two_mul, add_mul]; simp;
  have h : e * 2 ≤ (1 + e) ^ 2 := by
    ring_nf; exact le_add_of_le_of_nonneg (le_add_of_nonneg_left (by simp)) (by positivity)
  apply fun h => le_trans h ((sq_le_sq₀ (by positivity) (by positivity)).mpr
    (le_max_right (|a|+|b|) (1 + e))) at h
  grind; simp

lemma HasLim.mul_const [IsOrderedRing R] {a : ℕ → R} {g b : R} (h : HasLim a g) :
    HasLim (a * fun _ => b) (g * b) := mul h (const _)

lemma HasLim.const_mul [IsOrderedRing R] {a : ℕ → R} {g b : R} (h : HasLim a g) :
    HasLim ((fun _ => b) * a) (b * g) := mul (const _) h

lemma HasLim.neg {a : ℕ → R} {g : R} (h : HasLim a g) : HasLim (-a) (-g) := by
  simp [HasLim, abs_sub_comm, neg_add_eq_sub] at *; assumption

lemma HasLim.sub [IsOrderedRing R] {an bn : ℕ → R} {a b : R} (ha : HasLim an a) (hb : HasLim bn b) :
    HasLim (an - bn) (a - b) := by rw [sub_eq_add_neg, sub_eq_add_neg]; exact add ha hb.neg

lemma HasLim.sub_const {a : ℕ → R} {g b : R} (h : HasLim a g) :
    HasLim (a - fun _ => b) (g - b) := by simpa [HasLim]

lemma HasLim.const_sub (a : ℕ → R) {g b : R} {h : HasLim a g} :
    HasLim ((fun _ => b) - a) (b - g) := by simp [HasLim, abs_sub_comm] at *; assumption

lemma HasLim.inv [IsOrderedRing R] {a : ℕ → R} {g : R} (h : HasLim a g) (hg : g ≠ 0) : HasLim a⁻¹ g⁻¹ := by
  wlog hg : 0 < g generalizing a g
  · have this := neg <| this h.neg (by simpa) (by grind); simpa
  simp [HasLim]
  intro e he
  wlog heg : e < g⁻¹ generalizing e
  · have ⟨n, h⟩ := this (g⁻¹ / 2) (by positivity) (by simpa)
    exists n; intro n hn; replace h := h n hn
    simp at heg; exact lt_of_lt_of_le h (le_trans (half_le_self (by positivity)) heg)
  have ⟨n, h⟩ := h (e / (g⁻¹ * (g⁻¹ + e))) (by positivity)
  exists n; intro n hn; replace h := h n hn
  rw (occs := .pos [1]) [← add_sub_cancel_left g⁻¹ e, ← inv_sub_inv, inv_inv] at h <;> try positivity
  have han : 0 < a n := sub_self g ▸ (sub_lt_comm.mp <| lt_of_abs_lt <|
    (abs_sub_comm (a n) g ▸ h).trans (sub_lt_self g (by positivity)))
  rw [abs_lt, neg_lt, neg_sub]; constructor
  · rw [sub_lt_comm, lt_inv_comm₀, ← sub_lt_sub_iff_right g]
    apply lt_of_lt_of_le (lt_of_abs_lt h); rw (occs := .pos [1,4]) [← inv_inv g]
    rw [inv_sub_inv, inv_sub_inv]; field_simp; simp; field_simp; rw [one_le_div]
    simp; ring_nf; apply le_add_of_nonneg_right; positivity
    have hge := (mul_lt_mul_iff_right₀ hg).mpr heg; rw [mul_inv_cancel₀] at hge; simpa; assumption
    exact sub_ne_zero_of_ne (ne_of_gt heg); (repeat positivity); exact sub_pos_of_lt heg
    · exact han
  · rw [sub_lt_iff_lt_add, inv_lt_comm₀, ← sub_lt_sub_iff_left g]; rw [abs_sub_comm] at h
    case right.ha => exact han
    case right.hb => exact add_pos he (he.trans heg)
    apply lt_of_lt_of_le (lt_of_abs_lt h); field_simp; simp; ring_nf; simp

lemma HasLim.div [IsOrderedRing R] {an bn : ℕ → R} {a b : R} (ha : HasLim an a) (hb : HasLim bn b)
    (hne : b ≠ 0) : HasLim (an / bn) (a / b) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]; exact mul ha (inv hb hne)

lemma HasLim.div_const [IsOrderedRing R] {a : ℕ → R} {g b : R} (h : HasLim a g) :
    HasLim (a / fun _ => b) (g / b) := by rw [div_eq_mul_inv, div_eq_mul_inv]; exact mul_const h

lemma HasLim.const_div [IsOrderedRing R] {a : ℕ → R} {g b : R} (h : HasLim a g) (hb : b ≠ 0) :
    HasLim (a / fun _ => b) (g / b) := div h (const _) hb

/-- **Th. 2.5.** (continuity of absolute value) -/
lemma HasLim.abs [AddLeftMono R] {a : ℕ → R} {g : R} : HasLim a g → HasLim |a| |g| :=
  forall₂_imp fun _ _ => Exists.imp fun _ => forall₂_imp fun _ _ => lt_of_le_of_lt <| abs_abs_sub_abs_le _ _

lemma HasLim.abs_zero_iff [AddLeftMono R] {a : ℕ → R} : HasLim a 0 ↔ HasLim |a| 0 where
  mp := fun h => abs_zero (α := R) ▸ abs h
  mpr := by simp [HasLim]

/-- **Th. 2.6.** If one sequence (eventually) dominates another, then the inequality goes over to their limits. -/
lemma HasLim.le [IsOrderedRing R] {an bn : ℕ → R} {a b : R} (h : ∃ n₀, ∀ n ≥ n₀, an n ≤ bn n)
    (ha : HasLim an a) (hb : HasLim bn b) : a ≤ b := by
  by_contra!
  let ⟨n, hab⟩ := exists_forall_ge_and (ha ((a - b) / 2) (by simpa)) <|
    exists_forall_ge_and (hb ((a - b) / 2) (by simpa)) h
  replace ⟨ha, hb, h⟩ := hab n (by simp)
  replace ha := (abs_sub_lt_iff.mp ha).right
  replace hb := lt_of_abs_lt hb
  linarith

/-- **Th.2.7.** The squeeze theorem. -/
lemma HasLim.squeeze [IsOrderedRing R] {a b c : ℕ → R} {g : R} (hab : ∃ n₀, ∀ n ≥ n₀, a n ≤ b n)
    (hbc : ∃ n₀, ∀ n ≥ n₀, b n ≤ c n) (ha : HasLim a g) (hc : HasLim c g) : HasLim b g := by
  intro e he;
  let ⟨n, h⟩ := exists_forall_ge_and hab <| exists_forall_ge_and hbc <| exists_forall_ge_and (ha e he) (hc e he)
  exists n; intro n hn; let ⟨hab, hbc, ha, hc⟩ := h n hn
  rw [abs_sub_lt_iff]; constructor
  · exact lt_of_le_of_lt (by simpa) (lt_of_abs_lt hc)
  · exact lt_of_le_of_lt (by linarith) (abs_sub_lt_iff.mp ha).right

lemma HasLim.squeeze_const [IsOrderedRing R] {a b : ℕ → R} {g : R} (hab : ∃ n₀, ∀ n ≥ n₀, a n ≤ b n)
    (hbg : ∃ n₀, ∀ n ≥ n₀, b n ≤ g) (ha : HasLim a g) : HasLim b g := squeeze hab hbg ha (const _)

lemma HasLim.const_squeeze [IsOrderedRing R] {b c : ℕ → R} {g : R} (hgb : ∃ n₀, ∀ n ≥ n₀, g ≤ b n)
    (hbc : ∃ n₀, ∀ n ≥ n₀, b n ≤ c n) (hc : HasLim c g) : HasLim b g := squeeze hgb hbc (const _) hc

/-- **Th. 2.8.** A monotone (nondecreasing), bounded sequence is convergent. -/
lemma HasLim.of_monotone {a : ℕ → ℝ} (hm : Monotone a) (hb : BddAbove (Set.range a)) : HasLim a (iSup a) := by
  intro e he
  have ⟨n₀, hn₀⟩ := (lt_ciSup_iff hb).mp (sub_lt_self _ he)
  exists n₀; intro n hn
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr <| le_ciSup hb n)]
  exact lt_of_le_of_lt (sub_le_sub_left (hm hn) (iSup a)) (sub_lt_comm.mp hn₀)

/-- **Th. 2.8.** An antitone (nonincreasing), bounded sequence is convergent. -/
lemma HasLim.of_antitone {a : ℕ → ℝ} (hm : Antitone a) (hb : BddBelow (Set.range a)) : HasLim a (iInf a) := by
  intro e he
  have ⟨n₀, hn₀⟩ := (ciInf_lt_iff hb).mp (lt_add_of_pos_right _ he)
  exists n₀; intro n hn
  rw [abs_of_nonneg (sub_nonneg.mpr <| ciInf_le hb n)]
  exact lt_of_le_of_lt (sub_le_sub_right (hm hn) (iInf a)) (sub_left_lt_of_lt_add hn₀)

/-- Diverging to infinity, expressed as "converging" to `⊤` or `⊥` -/
def HasLim' (a : ℕ → R) : (g : WithBot (WithTop R)) → Prop
  | some (some g) => HasLim a g
  | ⊤ => ∀ D, ∃ n₀, ∀ n ≥ n₀, a n > D
  | ⊥ => ∀ D, ∃ n₀, ∀ n ≥ n₀, a n < D

lemma HasLim'.id [IsOrderedRing R] [FloorSemiring R] : HasLim' (fun n => (n : R)) ⊤ :=
  fun D => ⟨⌊D⌋₊ + 1, fun n hn => lt_of_lt_of_le (Nat.lt_floor_add_one D) (by norm_cast; exact Nat.cast_le.mpr hn)⟩

lemma HasLim'.le [IsOrderedRing R] {an bn : ℕ → R} {a b : WithBot (WithTop R)}
    (h : ∃ n₀, ∀ n ≥ n₀, an n ≤ bn n) (ha : HasLim' an a) (hb : HasLim' bn b) : a ≤ b := by
  match a, b with
  | ⊥, _ => exact bot_le
  | _, ⊤ => exact le_top
  | ⊤, ⊥ =>
    let ⟨n, h⟩ := exists_forall_ge_and h (exists_forall_ge_and (ha 0) (hb 0))
    specialize h n le_rfl; order
  | WithBot.some (WithTop.some a), WithBot.some (WithTop.some b) =>
    simp; exact HasLim.le h ha hb
  | WithBot.some (WithTop.some a), ⊥ =>
    specialize hb (a - 1); specialize ha 1 (by simp)
    let ⟨n, h⟩ := exists_forall_ge_and h (exists_forall_ge_and ha hb)
    replace ⟨h, ha, hb⟩ := h n (le_refl n); apply neg_lt_of_abs_lt at ha; grind
  | ⊤,  WithBot.some (WithTop.some b) =>
    specialize ha (b + 1); specialize hb 1 (by simp)
    let ⟨n, h⟩ := exists_forall_ge_and h (exists_forall_ge_and ha hb)
    replace ⟨h, ha, hb⟩ := h n (le_refl n); apply lt_of_abs_lt at hb; grind

/-- **Th. 2.9.** Squeeze theorem for divergence to positive infinity (`⊤`). -/
lemma HasLim'.squeeze_top {a b : ℕ → R} (h : ∃ n₀, ∀ n ≥ n₀, a n ≤ b n)
    (ha : HasLim' a ⊤) : HasLim' b ⊤ := by
  intro D; specialize ha D; replace ⟨n, h⟩ := exists_forall_ge_and h ha
  exists n; intro n hn; replace ⟨h, ha⟩ := h n hn; order

/-- **Th. 2.9.** Squeeze theorem for divergence to negative infinity (`⊥`). -/
lemma HasLim'.bot_squeeze {a b : ℕ → R} (h : ∃ n₀, ∀ n ≥ n₀, a n ≤ b n)
    (hb : HasLim' b ⊥) : HasLim' a ⊥ := by
  intro D; specialize hb D; replace ⟨n, h⟩ := exists_forall_ge_and h hb
  exists n; intro n hn; replace ⟨h, hb⟩ := h n hn; order

lemma HasLim'.neg_top [IsOrderedAddMonoid R] {a : ℕ → R} (h : HasLim' a ⊤) : HasLim' (-a) ⊥ := by
  intro D; replace ⟨n, h⟩ := h (-D); exists n; intro n hn; exact neg_lt.mp (h n hn)

lemma HasLim'.neg_bot [IsOrderedAddMonoid R] {a : ℕ → R} (h : HasLim' a ⊥) : HasLim' (-a) ⊤ := by
  intro D; replace ⟨n, h⟩ := h (-D); exists n; intro n hn; exact lt_neg.mp (h n hn)

lemma HasLim'.inv_top [IsOrderedRing R] {a : ℕ → R} (h : HasLim' a ⊤) : HasLim a⁻¹ 0 := by
  intro e he; replace ⟨n, h⟩ := h e⁻¹; exists n; intro n hn; specialize h n hn
  rw [abs_of_pos] <;> simp
  · exact inv_lt_of_inv_lt₀ he h
  · exact lt_trans (inv_pos.mpr he) h

lemma HasLim'.inv_bot [IsOrderedRing R] {a : ℕ → R} (h : HasLim' a ⊥) : HasLim a⁻¹ 0 := by
  intro e he; replace ⟨n, h⟩ := h (-e⁻¹); exists n; intro n hn; specialize h n hn
  have : a n < 0 := lt_trans h (by simpa)
  rw [abs_of_neg] <;> (simp; try assumption)
  rw [neg_lt]; rw [neg_inv] at h; rw [lt_inv_of_neg] <;> try assumption
  simpa

lemma HasLim'.top_add [IsOrderedAddMonoid R] {a b : ℕ → R} (hb : BddBelow (Set.range b))
    (ha : HasLim' a ⊤) : HasLim' (a + b) ⊤ := by
  intro D; replace ⟨lb, hb⟩ := bddBelow_def.mp hb; simp at *
  replace ⟨n, ha⟩ := ha (D - lb); exists n; intro n hn; specialize ha n hn; specialize hb n
  grind

lemma HasLim'.add_top [IsOrderedAddMonoid R] {a b : ℕ → R} (ha : BddBelow (Set.range a))
    (hb : HasLim' b ⊤) : HasLim' (a + b) ⊤ := by rw [add_comm]; exact top_add ha hb

lemma HasLim'.bot_add [IsOrderedAddMonoid R] {a b : ℕ → R} (hb : BddAbove (Set.range b))
    (ha : HasLim' a ⊥) : HasLim' (a + b) ⊥ := by
  rw [← neg_neg (a + b)]; apply neg_top; simp
  exact add_top (Set.neg_range (f := b) ▸ hb.neg) ha.neg_bot

lemma HasLim'.add_bot [IsOrderedAddMonoid R] {a b : ℕ → R} (ha : BddAbove (Set.range a))
    (hb : HasLim' b ⊥) : HasLim' (a + b) ⊥ := by rw [add_comm]; exact bot_add ha hb

lemma HasLim'.add [IsOrderedRing R] {an bn : ℕ → R} {a b : WithBot (WithTop R)} (ha : HasLim' an a) (hb : HasLim' bn b)
    (hn : ¬(a = ⊤ ∧ b = ⊥) ∧ ¬(a = ⊥ ∧ b = ⊤) := by decide) : HasLim' (an + bn) (a + b) :=
  match a, b with
  | some (some a), some (some b) => HasLim.add ha hb
  | some (some a), ⊤ => hb.add_top ha.bddBelow
  | some (some a), ⊥ => hb.add_bot ha.bddAbove
  | ⊤, some (some b) => ha.top_add hb.bddBelow
  | ⊤, ⊤ => by
    intro D; have ⟨n, h⟩ := exists_forall_ge_and (ha (D / 2)) (hb (D / 2))
    exists n; intro n hn; replace ⟨ha, hb⟩ := h n hn; replace h := add_lt_add ha hb; simp at *; exact h
  | ⊤, ⊥ => by revert hn; tauto
  | ⊥, some (some b) => ha.bot_add hb.bddAbove
  | ⊥, ⊤ => by revert hn; tauto
  | ⊥, ⊥ => by
    intro D; have ⟨n, h⟩ := exists_forall_ge_and (ha (D / 2)) (hb (D / 2))
    exists n; intro n hn; replace ⟨ha, hb⟩ := h n hn; replace h := add_lt_add ha hb; simp at *; exact h

lemma HasLim'.top_mul_pos [IsOrderedRing R] {a b : ℕ → R} {g : R} (hg : 0 < g)
    (ha : HasLim' a ⊤) (hb : HasLim b g) : HasLim' (a * b) ⊤ := by
  intro D; have ⟨n, h⟩ := exists_forall_ge_and (ha (max 0 (2 * D / g))) (hb (g / 2) (half_pos hg))
  exists n; intro n hn; replace ⟨ha, hb⟩ := h n hn
  rw [abs_sub_comm] at hb; apply lt_of_abs_lt at hb; rw [sub_lt_comm, sub_half] at hb
  replace h := mul_lt_mul'' ha hb (le_max_left 0 _) (half_pos hg).le
  replace h := lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_right 0 _) (half_pos hg).le) h
  field_simp at h; exact h

lemma HasLim'.top_mul_neg [IsOrderedRing R] {a b : ℕ → R} {g : R} (hg : g < 0)
    (ha : HasLim' a ⊤) (hb : HasLim b g) : HasLim' (a * b) ⊥ :=
  neg_neg (a * b) ▸ mul_neg a b ▸ (ha.top_mul_pos (neg_pos.mpr hg) hb.neg).neg_top

lemma HasLim'.pos_mul_top [IsOrderedRing R] {a b : ℕ → R} {g : R} (hg : 0 < g)
    (ha : HasLim a g) (hb : HasLim' b ⊤) : HasLim' (a * b) ⊤ :=
  mul_comm a b ▸ top_mul_pos hg hb ha

lemma HasLim'.neg_mul_top [IsOrderedRing R] {a b : ℕ → R} {g : R} (hg : g < 0)
    (ha : HasLim a g) (hb : HasLim' b ⊤) : HasLim' (a * b) ⊥ :=
  mul_comm a b ▸ top_mul_neg hg hb ha

lemma HasLim'.bot_mul_pos [IsOrderedRing R] {a b : ℕ → R} {g : R} (hg : 0 < g)
    (ha : HasLim' a ⊥) (hb : HasLim b g) : HasLim' (a * b) ⊥ :=
  neg_mul_neg a b ▸ ha.neg_bot.top_mul_neg (neg_neg_iff_pos.mpr hg) hb.neg

lemma HasLim'.bot_mul_neg [IsOrderedRing R] {a b : ℕ → R} {g : R} (hg : g < 0)
    (ha : HasLim' a ⊥) (hb : HasLim b g) : HasLim' (a * b) ⊤ :=
  neg_mul_neg a b ▸ ha.neg_bot.top_mul_pos (neg_pos.mpr hg) hb.neg

lemma HasLim'.pos_mul_bot [IsOrderedRing R] {a b : ℕ → R} {g : R} (hg : 0 < g)
    (ha : HasLim a g) (hb : HasLim' b ⊥) : HasLim' (a * b) ⊥ :=
  mul_comm a b ▸ bot_mul_pos hg hb ha

lemma HasLim'.neg_mul_bot [IsOrderedRing R] {a b : ℕ → R} {g : R} (hg : g < 0)
    (ha : HasLim a g) (hb : HasLim' b ⊥) : HasLim' (a * b) ⊤ :=
  mul_comm a b ▸ bot_mul_neg hg hb ha

lemma HasLim'.top_mul_top {a b : ℕ → ℝ} (ha : HasLim' a ⊤) (hb : HasLim' b ⊤) : HasLim' (a * b) ⊤ := by
  intro D; have ⟨n, h⟩ := exists_forall_ge_and (ha √D) (hb √D)
  exists n; intro n hn; replace ⟨ha, hb⟩ := h n hn
  replace h := mul_lt_mul'' ha hb D.sqrt_nonneg D.sqrt_nonneg
  rw [← sq, Real.sq_sqrt'] at h
  exact (max_lt_iff.mp h).1

lemma HasLim'.top_mul_bot {a b : ℕ → ℝ} (ha : HasLim' a ⊤) (hb : HasLim' b ⊥) : HasLim' (a * b) ⊥ :=
  neg_neg (a * b) ▸ mul_neg a b ▸ (ha.top_mul_top hb.neg_bot).neg_top

lemma HasLim'.bot_mul_top {a b : ℕ → ℝ} (ha : HasLim' a ⊥) (hb : HasLim' b ⊤) : HasLim' (a * b) ⊥ :=
  neg_neg (a * b) ▸ neg_mul a b ▸ (ha.neg_bot.top_mul_top hb).neg_top

lemma HasLim'.bot_mul_bot {a b : ℕ → ℝ} (ha : HasLim' a ⊥) (hb : HasLim' b ⊥) : HasLim' (a * b) ⊤ :=
  neg_mul_neg a b ▸ ha.neg_bot.top_mul_top hb.neg_bot

lemma HasLim.const_pow_n [IsOrderedRing R] [Archimedean R] {a : R} (h : |a| < 1) : HasLim (fun n => a ^ n) 0 := by
  by_cases ha : a = 0
  · subst ha; intro _ _; simp; exists 1; intro n hn; rw [zero_pow]; simpa; omega
  intro e he; simp
  have ⟨b, hb⟩ := exists_pow_lt_of_lt_one he h
  exists b; intro n hn
  exact lt_of_le_of_lt ((pow_le_pow_iff_right_of_lt_one₀ (abs_pos.mpr ha) h).mpr hn) hb

lemma HasLim.const_pow_inv_n {a : ℝ} (h : 1 < a) : HasLim (fun n => a ^ (n⁻¹ : ℝ)) 1 := by
  intro e he
  have ⟨b, hb⟩ := pow_unbounded_of_one_lt a (lt_add_of_pos_left 1 he)
  exists b; intro n hn
  by_cases hn0 : n = 0; · subst hn0; simpa
  rw [abs_of_nonneg (by simp; apply Real.one_le_rpow h.le; positivity), sub_lt_iff_lt_add]
  apply lt_of_pow_lt_pow_left₀ n (by positivity)
  rw [Real.rpow_inv_natCast_pow (by positivity) hn0]
  exact lt_of_lt_of_le hb (pow_le_pow_right₀ (lt_add_of_pos_left 1 he).le hn)

lemma HasLim.pow_const' {a : ℕ → ℝ} {g r : ℝ} (hnn : ∀ n, 0 ≤ a n) (hr : 0 ≤ r)
    (h : HasLim a g) : HasLim (a ^ r) (g ^ r) := by
  intro e he
  by_cases hr : r = 0; · subst hr; simp; exact ⟨0, fun _ _ => he⟩
  rcases lt_trichotomy g 0 with hg | hg | hg
  · replace ⟨n, h⟩ := h (-g) (by simpa); specialize h n le_rfl; specialize hnn n
    apply lt_of_abs_lt at h; linarith
  · subst hg; rw [Real.zero_rpow hr]
    replace ⟨n, h⟩ := h (e ^ r⁻¹) (by positivity); exists n; intro n hn; specialize h n hn; simp at *
    rw [abs_of_nonneg (hnn n)] at h; rw [abs_of_nonneg (Real.rpow_nonneg (hnn n) r)]
    convert Real.rpow_lt_rpow (hnn n) h (show 0 < r by positivity)
    symm; exact Real.rpow_inv_rpow he.le hr
  let lb := (max 0 (g ^ r - e)) ^ r⁻¹
  let ub := (g ^ r + e) ^ r⁻¹
  replace ⟨n, h⟩ := h (min (g - lb) (ub - g)) (by
    simp [lb, ub]; constructor
    · nth_rw 2 [← Real.rpow_rpow_inv hg.le hr]
      refine Real.rpow_lt_rpow (le_max_left 0 _) ?_ (by positivity); simp; constructor <;> positivity
    · nth_rw 1 [← Real.rpow_rpow_inv hg.le hr]
      refine Real.rpow_lt_rpow (by positivity) ?_ (by positivity); simpa)
  exists n; intro n hn; specialize h n hn; rw [abs_lt]; constructor
  · replace h := lt_of_abs_lt (abs_sub_comm (a n) g ▸ (lt_min_iff.mp h).1); simp [lb] at h
    replace h := Real.rpow_lt_rpow (Real.rpow_nonneg (le_max_left 0 _) _) h (show 0 < r by positivity)
    rw [Real.rpow_inv_rpow (le_max_left 0 _) hr] at h; replace h := (max_lt_iff.mp h).2
    simp; linarith
  · replace h := lt_of_abs_lt ((lt_min_iff.mp h).2); simp [ub] at h
    replace h := Real.rpow_lt_rpow (hnn n) h (show 0 < r by positivity)
    rw [Real.rpow_inv_rpow (by positivity) hr] at h; simp; linarith

lemma HasLim'.top_pow_const' {a : ℕ → ℝ} {r : ℝ} (hr : 0 < r) (h : HasLim' a ⊤) : HasLim' (a ^ r) ⊤ := by
  intro D; replace ⟨n, h⟩ := h ((max 0 D) ^ r⁻¹); exists n; intro n hn; specialize h n hn
  replace h := Real.rpow_lt_rpow (Real.rpow_nonneg (le_max_left 0 _) _) h hr
  rw [Real.rpow_inv_rpow (le_max_left 0 _) hr.ne'] at h; exact (max_lt_iff.mp h).2
