/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
prelude
import init.algebra.order init.algebra.group

/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
set_option default_priority 100

set_option old_structure_cmd true

universe u

class ordered_cancel_comm_monoid (α : Type u)
      extends add_comm_monoid α, add_left_cancel_semigroup α,
              add_right_cancel_semigroup α, partial_order α :=
(add_le_add_left : ∀ a b c : α, a + b ≤ a + c ↔ b ≤ c)
(add_lt_add_left : ∀ a b c : α, a + b < a + c ↔ b < c)

section ordered_cancel_comm_monoid
variable {α : Type u}
variable [ordered_cancel_comm_monoid α]

@[simp] lemma add_le_add_left : ∀ a {b c : α}, a + b ≤ a + c ↔ b ≤ c :=
ordered_cancel_comm_monoid.add_le_add_left

lemma add_le_add_of_le_left {a b : α} (h : a ≤ b) (c : α) : c + a ≤ c + b := (add_le_add_left c).2 h
lemma le_of_add_le_add_left {a b c : α} : a + b ≤ a + c → b ≤ c := (add_le_add_left a).1

@[simp] lemma add_le_add_right {a b : α} (c : α) : a + c ≤ b + c ↔ a ≤ b :=
add_comm c a ▸ add_comm c b ▸ add_le_add_left c

lemma add_le_add_of_le_right {a b : α} (h : a ≤ b) (c : α) : a + c ≤ b + c := (add_le_add_right c).2 h
lemma le_of_add_le_add_right {a b c : α} : a + b ≤ c + b → a ≤ c := (add_le_add_right b).1

@[simp] lemma add_lt_add_left : ∀ a {b c : α}, a + b < a + c ↔ b < c :=
ordered_cancel_comm_monoid.add_lt_add_left

lemma add_lt_add_of_lt_left {a b : α} (h : a < b) (c : α) : c + a < c + b := (add_lt_add_left c).2 h
lemma lt_of_add_lt_add_left {a b c : α} : a + b < a + c → b < c := (add_lt_add_left a).1

@[simp] lemma add_lt_add_right {a b : α} (c : α) : a + c < b + c ↔ a < b :=
add_comm c a ▸ add_comm c b ▸ add_lt_add_left c

lemma add_lt_add_of_lt_right {a b : α} (h : a < b) (c : α) : a + c < b + c := (add_lt_add_right c).2 h
lemma lt_of_add_lt_add_right {a b c : α} : a + b < c + b → a < c := (add_lt_add_right b).1

lemma add_le_add {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
le_trans (add_le_add_of_le_right h₁ c) (add_le_add_of_le_left h₂ b)

@[simp] lemma le_add_iff_nonneg_right a {b : α} : a ≤ a + b ↔ 0 ≤ b :=
have a + 0 ≤ a + b ↔ 0 ≤ b, from add_le_add_left a,
by rwa add_zero at this

lemma le_add_of_nonneg_right (a : α) {b : α} : b ≥ 0 → a ≤ a + b := (le_add_iff_nonneg_right a).2

@[simp] lemma le_add_iff_nonneg_left a {b : α} : a ≤ b + a ↔ 0 ≤ b :=
have a ≤ a + b ↔ 0 ≤ b, from le_add_iff_nonneg_right a,
by rwa add_comm at this

lemma le_add_of_nonneg_left (a : α) {b : α} : b ≥ 0 → a ≤ b + a := (le_add_iff_nonneg_left a).2

lemma add_lt_add {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
lt_trans (add_lt_add_of_lt_right h₁ c) (add_lt_add_of_lt_left h₂ b)

lemma add_lt_add_of_le_of_lt {a b c d : α} (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d :=
lt_of_le_of_lt (add_le_add_of_le_right h₁ c) (add_lt_add_of_lt_left h₂ b)

lemma add_lt_add_of_lt_of_le {a b c d : α} (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d :=
lt_of_lt_of_le (add_lt_add_of_lt_right h₁ c) (add_le_add_of_le_left h₂ b)

@[simp] lemma lt_add_iff_pos_right (a : α) {b : α} : a < a + b ↔ 0 < b :=
have a + 0 < a + b ↔ 0 < b, from add_lt_add_left a,
by rwa add_zero at this

lemma lt_add_of_pos_right (a : α) {b : α} : b > 0 → a < a + b := (lt_add_iff_pos_right a).2

@[simp] lemma lt_add_iff_pos_left (a : α) {b : α} : a < b + a ↔ 0 < b :=
have a < a + b ↔ 0 < b, from lt_add_iff_pos_right a,
by rwa add_comm at this

lemma lt_add_of_pos_left (a : α) {b : α} : b > 0 → a < b + a := (lt_add_iff_pos_left a).2

-- here we start using properties of zero.
lemma add_nonneg {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
zero_add (0:α) ▸ add_le_add ha hb

lemma add_pos {a b : α} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  zero_add (0:α) ▸ add_lt_add ha hb

lemma add_pos_of_pos_of_nonneg {a b : α} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
zero_add (0:α) ▸ add_lt_add_of_lt_of_le ha hb

lemma add_pos_of_nonneg_of_pos {a b : α} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b :=
zero_add (0:α) ▸ add_lt_add_of_le_of_lt ha hb

lemma add_nonpos {a b : α} (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 :=
zero_add (0:α) ▸ add_le_add ha hb

lemma add_neg {a b : α} (ha : a < 0) (hb : b < 0) : a + b < 0 :=
zero_add (0:α) ▸ add_lt_add ha hb

lemma add_neg_of_neg_of_nonpos {a b : α} (ha : a < 0) (hb : b ≤ 0) : a + b < 0 :=
zero_add (0:α) ▸ add_lt_add_of_lt_of_le ha hb

lemma add_neg_of_nonpos_of_neg {a b : α} (ha : a ≤ 0) (hb : b < 0) : a + b < 0 :=
zero_add (0:α) ▸ add_lt_add_of_le_of_lt ha hb

lemma add_eq_zero_iff_eq_zero_of_nonneg
    {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) : a + b = 0 ↔ a = 0 ∧ b = 0 :=
⟨λ hab : a + b = 0, 
by constructor; apply le_antisymm; try {assumption};
   rw ← hab; simp [ha, hb],
λ ⟨ha', hb'⟩, by rw [ha', hb', add_zero]⟩

lemma le_add_of_nonneg_of_le {a b c : α} (ha : 0 ≤ a) (hbc : b ≤ c) : b ≤ a + c :=
zero_add b ▸ add_le_add ha hbc

lemma le_add_of_le_of_nonneg {a b c : α} (hbc : b ≤ c) (ha : 0 ≤ a) : b ≤ c + a :=
add_zero b ▸ add_le_add hbc ha

lemma lt_add_of_pos_of_le {a b c : α} (ha : 0 < a) (hbc : b ≤ c) : b < a + c :=
zero_add b ▸ add_lt_add_of_lt_of_le ha hbc

lemma lt_add_of_le_of_pos {a b c : α} (hbc : b ≤ c) (ha : 0 < a) : b < c + a :=
add_zero b ▸ add_lt_add_of_le_of_lt hbc ha

lemma add_le_of_nonpos_of_le {a b c : α} (ha : a ≤ 0) (hbc : b ≤ c) : a + b ≤ c :=
zero_add c ▸ add_le_add ha hbc

lemma add_le_of_le_of_nonpos {a b c : α} (hbc : b ≤ c) (ha : a ≤ 0) : b + a ≤ c :=
add_zero c ▸ add_le_add hbc ha

lemma add_lt_of_neg_of_le {a b c : α} (ha : a < 0) (hbc : b ≤ c) : a + b < c :=
zero_add c ▸ add_lt_add_of_lt_of_le ha hbc

lemma add_lt_of_le_of_neg {a b c : α} (hbc : b ≤ c) (ha : a < 0) : b + a < c :=
add_zero c ▸ add_lt_add_of_le_of_lt hbc ha

lemma lt_add_of_nonneg_of_lt {a b c : α} (ha : 0 ≤ a) (hbc : b < c) : b < a + c :=
zero_add b ▸ add_lt_add_of_le_of_lt ha hbc

lemma lt_add_of_lt_of_nonneg {a b c : α} (hbc : b < c) (ha : 0 ≤ a) : b < c + a :=
add_zero b ▸ add_lt_add_of_lt_of_le hbc ha

lemma lt_add_of_pos_of_lt {a b c : α} (ha : 0 < a) (hbc : b < c) : b < a + c :=
zero_add b ▸ add_lt_add ha hbc

lemma lt_add_of_lt_of_pos {a b c : α} (hbc : b < c) (ha : 0 < a) : b < c + a :=
add_zero b ▸ add_lt_add hbc ha

lemma add_lt_of_nonpos_of_lt {a b c : α} (ha : a ≤ 0) (hbc : b < c) : a + b < c :=
zero_add c ▸ add_lt_add_of_le_of_lt ha hbc

lemma add_lt_of_lt_of_nonpos {a b c : α} (hbc : b < c) (ha : a ≤ 0)  : b + a < c :=
add_zero c ▸ add_lt_add_of_lt_of_le hbc ha

lemma add_lt_of_neg_of_lt {a b c : α} (ha : a < 0) (hbc : b < c) : a + b < c :=
zero_add c ▸ add_lt_add ha hbc

lemma add_lt_of_lt_of_neg {a b c : α} (hbc : b < c) (ha : a < 0) : b + a < c :=
add_zero c ▸ add_lt_add hbc ha

end ordered_cancel_comm_monoid

class ordered_comm_group (α : Type u) extends add_comm_group α, partial_order α :=
(add_le_add_left_of_le : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(add_lt_add_left_of_lt : ∀ a b : α, a < b → ∀ c : α, c + a < c + b)

section ordered_comm_group
variables {α : Type u} [ordered_comm_group α]

instance ordered_comm_group.to_ordered_cancel_comm_monoid
  (α : Type u) [s : ordered_comm_group α] : ordered_cancel_comm_monoid α :=
{ s with
  add_left_cancel  := @add_left_cancel α _,
  add_right_cancel := @add_right_cancel α _,
  add_le_add_left  := λ a b c,
    ⟨λ h, by have := ordered_comm_group.add_le_add_left_of_le _ _ h (-a);
      rwa [neg_add_cancel_left, neg_add_cancel_left] at this,
    λ h, ordered_comm_group.add_le_add_left_of_le _ _ h _⟩,
  add_lt_add_left  := λ a b c,
    ⟨λ h, by have := ordered_comm_group.add_lt_add_left_of_lt _ _ h (-a);
      rwa [neg_add_cancel_left, neg_add_cancel_left] at this,
    λ h, ordered_comm_group.add_lt_add_left_of_lt _ _ h _⟩ }

@[simp] lemma neg_le_neg {a b : α} : -a ≤ -b ↔ b ≤ a :=
have a + b + -a ≤ a + b + -b ↔ -a ≤ -b, from add_le_add_left _,
by simp at this; simp [this]

lemma neg_le_neg_of_le {a b : α} : a ≤ b → -b ≤ -a := neg_le_neg.2
lemma le_of_neg_le_neg {a b : α} : -b ≤ -a → a ≤ b := neg_le_neg.1

lemma neg_le {a b : α} : -a ≤ b ↔ -b ≤ a :=
have -a ≤ -(-b) ↔ -b ≤ a, from neg_le_neg,
by rwa neg_neg at this

lemma neg_le_of_neg_le {a b : α} : -a ≤ b → -b ≤ a := neg_le.1

lemma le_neg {a b : α} : a ≤ -b ↔ b ≤ -a :=
have -(-a) ≤ -b ↔ b ≤ -a, from neg_le_neg,
by rwa neg_neg at this

lemma le_neg_of_le_neg {a b : α} : a ≤ -b → b ≤ -a := le_neg.1

@[simp] lemma neg_nonpos {a : α} : -a ≤ 0 ↔ 0 ≤ a :=
have -a ≤ -0 ↔ 0 ≤ a, from neg_le_neg,
by rwa neg_zero at this

lemma nonneg_of_neg_nonpos {a : α} : -a ≤ 0 → 0 ≤ a := neg_nonpos.1
lemma neg_nonpos_of_nonneg {a : α} : 0 ≤ a → -a ≤ 0 := neg_nonpos.2

@[simp] lemma neg_nonneg {a : α} : 0 ≤ -a ↔ a ≤ 0 :=
have -0 ≤ -a ↔ a ≤ 0, from neg_le_neg,
by rwa neg_zero at this

lemma nonpos_of_neg_nonneg {a : α} : 0 ≤ -a → a ≤ 0 := neg_nonneg.1
lemma neg_nonneg_of_nonpos {a : α} : a ≤ 0 → 0 ≤ -a := neg_nonneg.2

@[simp] lemma neg_lt_neg {a b : α} : -a < -b ↔ b < a :=
have a + b + -a < a + b + -b ↔ -a < -b, from add_lt_add_left _,
by simp at this; simp [this]

lemma neg_lt_neg_of_lt {a b : α} : a < b → -b < -a := neg_lt_neg.2
lemma lt_of_neg_lt_neg {a b : α} : -b < -a → a < b := neg_lt_neg.1

lemma neg_lt_zero {a : α} : -a < 0 ↔ 0 < a :=
have -a < -0 ↔ 0 < a, from neg_lt_neg,
by rwa neg_zero at this

lemma pos_of_neg_neg {a : α} : -a < 0 → 0 < a := neg_lt_zero.1
lemma neg_neg_of_pos {a : α} : 0 < a → -a < 0 := neg_lt_zero.2

lemma neg_pos {a : α} : 0 < -a ↔ a < 0 :=
have -0 < -a ↔ a < 0, from neg_lt_neg,
by rwa neg_zero at this

lemma neg_of_neg_pos {a : α} : 0 < -a → a < 0 := neg_pos.1
lemma neg_pos_of_neg {a : α} : a < 0 → 0 < -a := neg_pos.2

lemma neg_lt {a b : α} : -a < b ↔ -b < a :=
have -a < -(-b) ↔ -b < a, from neg_lt_neg,
by rwa neg_neg at this

lemma neg_lt_of_neg_lt {a b : α} : -a < b → -b < a := neg_lt.1

lemma lt_neg {a b : α} : a < -b ↔ b < -a :=
have -(-a) < -b ↔ b < -a, from neg_lt_neg,
by rwa neg_neg at this

lemma lt_neg_of_lt_neg {a b : α} : a < -b → b < -a := lt_neg.1

lemma sub_le_sub_left (a : α) {b c : α} : a - b ≤ a - c ↔ c ≤ b :=
(add_le_add_left _).trans neg_le_neg

lemma sub_le_sub_of_le_left {a b : α} (h : a ≤ b) (c : α) : c - b ≤ c - a := (sub_le_sub_left c).2 h

lemma sub_le_sub_right {a b : α} (c : α) : a - c ≤ b - c ↔ a ≤ b :=
add_le_add_right _

lemma sub_le_sub_of_le_right {a b : α} (h : a ≤ b) (c : α) : a - c ≤ b - c := (sub_le_sub_right c).2 h

lemma sub_lt_sub_left (a : α) {b c : α} : a - b < a - c ↔ c < b :=
(add_lt_add_left _).trans neg_lt_neg

lemma sub_lt_sub_of_lt_left {a b : α} (h : a < b) (c : α) : c - b < c - a := (sub_lt_sub_left c).2 h

lemma sub_lt_sub_right {a b : α} (c : α) : a - c < b - c ↔ a < b :=
add_lt_add_right _

lemma sub_lt_sub_of_lt_right {a b : α} (h : a < b) (c : α) : a - c < b - c := (sub_lt_sub_right c).2 h

@[simp] lemma sub_nonneg {a b : α} : 0 ≤ a - b ↔ b ≤ a :=
have a - a ≤ a - b ↔ b ≤ a, from sub_le_sub_left a,
by rwa sub_self at this

lemma sub_nonneg_of_le {a b : α} : b ≤ a → 0 ≤ a - b := sub_nonneg.2
lemma le_of_sub_nonneg {a b : α} : 0 ≤ a - b → b ≤ a := sub_nonneg.1

@[simp] lemma sub_nonpos {a b : α} : a - b ≤ 0 ↔ a ≤ b :=
have a - b ≤ b - b ↔ a ≤ b, from sub_le_sub_right b,
by rwa sub_self at this

lemma sub_nonpos_of_le {a b : α} : a ≤ b → a - b ≤ 0 := sub_nonpos.2
lemma le_of_sub_nonpos {a b : α} : a - b ≤ 0 → a ≤ b := sub_nonpos.1

@[simp] lemma sub_pos {a b : α} : 0 < a - b ↔ b < a :=
have a - a < a - b ↔ b < a, from sub_lt_sub_left a,
by rwa sub_self at this

lemma sub_pos_of_lt {a b : α} : b < a → 0 < a - b := sub_pos.2
lemma lt_of_sub_pos {a b : α} : 0 < a - b → b < a := sub_pos.1

@[simp] lemma sub_lt_zero {a b : α} : a - b < 0 ↔ a < b :=
have a - b < b - b ↔ a < b, from sub_lt_sub_right b,
by rwa sub_self at this

lemma sub_neg_of_lt {a b : α} : a < b → a - b < 0 := sub_lt_zero.2
lemma lt_of_sub_neg {a b : α} : a - b < 0 → a < b := sub_lt_zero.1

@[simp] lemma le_neg_add_iff_add_le {a b c : α} : b ≤ -a + c ↔ a + b ≤ c :=
have -a + (a + b) ≤ -a + c ↔ a + b ≤ c, from add_le_add_left _,
by rwa neg_add_cancel_left at this

lemma add_le_of_le_neg_add {a b c : α} : b ≤ -a + c → a + b ≤ c := le_neg_add_iff_add_le.1
lemma le_neg_add_of_add_le {a b c : α} : a + b ≤ c → b ≤ -a + c := le_neg_add_iff_add_le.2

lemma le_sub_left_iff_add_le {a b c : α} : b ≤ c - a ↔ a + b ≤ c :=
by rw [sub_eq_add_neg, add_comm, le_neg_add_iff_add_le]

lemma add_le_of_le_sub_left {a b c : α} : b ≤ c - a → a + b ≤ c := le_sub_left_iff_add_le.1
lemma le_sub_left_of_add_le {a b c : α} : a + b ≤ c → b ≤ c - a := le_sub_left_iff_add_le.2

@[simp] lemma le_sub_right_iff_add_le {a b c : α} : a ≤ c - b ↔ a + b ≤ c :=
by rw [le_sub_left_iff_add_le, add_comm]

lemma add_le_of_le_sub_right {a b c : α} : a ≤ c - b → a + b ≤ c := le_sub_right_iff_add_le.1
lemma le_sub_right_of_add_le {a b c : α} : a + b ≤ c → a ≤ c - b := le_sub_right_iff_add_le.2

@[simp] lemma neg_add_le_iff_le_add {a b c : α} : -b + a ≤ c ↔ a ≤ b + c :=
have -b + a ≤ -b + (b + c) ↔ a ≤ b + c, from add_le_add_left _,
by rwa neg_add_cancel_left at this

lemma le_add_of_neg_add_le {a b c : α} : -b + a ≤ c → a ≤ b + c := neg_add_le_iff_le_add.1
lemma neg_add_le_of_le_add {a b c : α} : a ≤ b + c → -b + a ≤ c := neg_add_le_iff_le_add.2

def le_add_of_neg_add_le_left := @le_add_of_neg_add_le
def neg_add_le_left_of_le_add := @neg_add_le_of_le_add

lemma sub_left_le_iff_le_add {a b c : α} : a - b ≤ c ↔ a ≤ b + c :=
by rw [sub_eq_add_neg, add_comm, neg_add_le_iff_le_add]

lemma le_add_of_sub_left_le {a b c : α} : a - b ≤ c → a ≤ b + c := sub_left_le_iff_le_add.1
lemma sub_left_le_of_le_add {a b c : α} : a ≤ b + c → a - b ≤ c := sub_left_le_iff_le_add.2

@[simp] lemma sub_right_le_iff_le_add {a b c : α} : a - c ≤ b ↔ a ≤ b + c :=
by rw [sub_left_le_iff_le_add, add_comm]

lemma le_add_of_sub_right_le {a b c : α} : a - c ≤ b → a ≤ b + c := sub_right_le_iff_le_add.1
lemma sub_right_le_of_le_add {a b c : α} : a ≤ b + c → a - c ≤ b := sub_right_le_iff_le_add.2

lemma neg_add_le_iff_le_add_right {a b c : α} : -c + a ≤ b ↔ a ≤ b + c :=
by rw [neg_add_le_iff_le_add, add_comm]

lemma le_add_of_neg_add_le_right {a b c : α} : -c + a ≤ b → a ≤ b + c := neg_add_le_iff_le_add_right.1
lemma neg_add_le_right_of_le_add {a b c : α} : a ≤ b + c → -c + a ≤ b := neg_add_le_iff_le_add_right.2

@[simp] lemma neg_le_sub_iff_le_add {a b c : α} : -b ≤ a - c ↔ c ≤ a + b :=
le_sub_right_iff_add_le.trans neg_add_le_iff_le_add_right

lemma le_add_of_neg_le_sub_right {a b c : α} : -b ≤ a - c → c ≤ a + b := neg_le_sub_iff_le_add.1
lemma neg_le_sub_right_of_le_add {a b c : α} : c ≤ a + b → -b ≤ a - c := neg_le_sub_iff_le_add.2

lemma neg_le_sub_iff_le_add_left {a b c : α} : -a ≤ b - c ↔ c ≤ a + b :=
by rw [neg_le_sub_iff_le_add, add_comm]

lemma le_add_of_neg_le_sub_left {a b c : α} : -a ≤ b - c → c ≤ a + b := neg_le_sub_iff_le_add_left.1
lemma neg_le_sub_left_of_le_add {a b c : α} : c ≤ a + b → -a ≤ b - c := neg_le_sub_iff_le_add_left.2

lemma sub_le {a b c : α} : a - b ≤ c ↔ a - c ≤ b :=
sub_left_le_iff_le_add.trans sub_right_le_iff_le_add.symm

lemma sub_le_of_sub_le {a b c : α} : a - b ≤ c → a - c ≤ b := sub_le.1

lemma sub_le_sub {a b c d : α} (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
add_le_add hab (neg_le_neg.2 hcd)

@[simp] lemma lt_neg_add_iff_add_lt {a b c : α} : b < -a + c ↔ a + b < c :=
have -a + (a + b) < -a + c ↔ a + b < c, from add_lt_add_left _,
by rwa neg_add_cancel_left at this

lemma add_lt_of_lt_neg_add {a b c : α} : b < -a + c → a + b < c := lt_neg_add_iff_add_lt.1
lemma lt_neg_add_of_add_lt {a b c : α} : a + b < c → b < -a + c := lt_neg_add_iff_add_lt.2

lemma lt_sub_left_iff_add_lt {a b c : α} : b < c - a ↔ a + b < c :=
by rw [sub_eq_add_neg, add_comm, lt_neg_add_iff_add_lt]

lemma add_lt_of_lt_sub_left {a b c : α} : b < c - a → a + b < c := lt_sub_left_iff_add_lt.1
lemma lt_sub_left_of_add_lt {a b c : α} : a + b < c → b < c - a := lt_sub_left_iff_add_lt.2

@[simp] lemma lt_sub_right_iff_add_lt {a b c : α} : a < c - b ↔ a + b < c :=
by rw [lt_sub_left_iff_add_lt, add_comm]

lemma add_lt_of_lt_sub_right {a b c : α} : a < c - b → a + b < c := lt_sub_right_iff_add_lt.1
lemma lt_sub_right_of_add_lt {a b c : α} : a + b < c → a < c - b := lt_sub_right_iff_add_lt.2

@[simp] lemma neg_add_lt_iff_lt_add {a b c : α} : -b + a < c ↔ a < b + c :=
have -b + a < -b + (b + c) ↔ a < b + c, from add_lt_add_left _,
by rwa neg_add_cancel_left at this

lemma lt_add_of_neg_add_lt {a b c : α} : -b + a < c → a < b + c := neg_add_lt_iff_lt_add.1
lemma neg_add_lt_of_lt_add {a b c : α} : a < b + c → -b + a < c := neg_add_lt_iff_lt_add.2

def lt_add_of_neg_add_lt_left := @lt_add_of_neg_add_lt
def neg_add_lt_left_of_lt_add := @neg_add_lt_of_lt_add

lemma sub_left_lt_iff_lt_add {a b c : α} : a - b < c ↔ a < b + c :=
by rw [sub_eq_add_neg, add_comm, neg_add_lt_iff_lt_add]

lemma lt_add_of_sub_left_lt {a b c : α} : a - b < c → a < b + c := sub_left_lt_iff_lt_add.1
lemma sub_left_lt_of_lt_add {a b c : α} : a < b + c → a - b < c := sub_left_lt_iff_lt_add.2

@[simp] lemma sub_right_lt_iff_lt_add {a b c : α} : a - c < b ↔ a < b + c :=
by rw [sub_left_lt_iff_lt_add, add_comm]

lemma lt_add_of_sub_right_lt {a b c : α} : a - c < b → a < b + c := sub_right_lt_iff_lt_add.1
lemma sub_right_lt_of_lt_add {a b c : α} : a < b + c → a - c < b := sub_right_lt_iff_lt_add.2

lemma neg_add_lt_iff_lt_add_right {a b c : α} : -c + a < b ↔ a < b + c :=
by rw [neg_add_lt_iff_lt_add, add_comm]

lemma lt_add_of_neg_add_lt_right {a b c : α} : -c + a < b → a < b + c := neg_add_lt_iff_lt_add_right.1
lemma neg_add_lt_right_of_lt_add {a b c : α} : a < b + c → -c + a < b := neg_add_lt_iff_lt_add_right.2

@[simp] lemma neg_lt_sub_iff_lt_add {a b c : α} : -b < a - c ↔ c < a + b :=
lt_sub_right_iff_add_lt.trans neg_add_lt_iff_lt_add_right

lemma lt_add_of_neg_lt_sub_right {a b c : α} : -b < a - c → c < a + b := neg_lt_sub_iff_lt_add.1
lemma neg_lt_sub_right_of_lt_add {a b c : α} : c < a + b → -b < a - c := neg_lt_sub_iff_lt_add.2

lemma neg_lt_sub_iff_lt_add_left {a b c : α} : -a < b - c ↔ c < a + b :=
by rw [neg_lt_sub_iff_lt_add, add_comm]

lemma lt_add_of_neg_lt_sub_left {a b c : α} : -a < b - c → c < a + b := neg_lt_sub_iff_lt_add_left.1
lemma neg_lt_sub_left_of_lt_add {a b c : α} : c < a + b → -a < b - c := neg_lt_sub_iff_lt_add_left.2

lemma sub_lt {a b c : α} : a - b < c ↔ a - c < b :=
sub_left_lt_iff_lt_add.trans sub_right_lt_iff_lt_add.symm

lemma sub_lt_of_sub_lt {a b c : α} : a - b < c → a - c < b := sub_lt.1

lemma sub_lt_sub {a b c d : α} (hab : a < b) (hcd : c < d) : a - d < b - c :=
add_lt_add hab (neg_lt_neg.2 hcd)

lemma sub_lt_sub_of_le_of_lt {a b c d : α} (hab : a ≤ b) (hcd : c < d) : a - d < b - c :=
add_lt_add_of_le_of_lt hab (neg_lt_neg.2 hcd)

lemma sub_lt_sub_of_lt_of_le {a b c d : α} (hab : a < b) (hcd : c ≤ d) : a - d < b - c :=
add_lt_add_of_lt_of_le hab (neg_le_neg.2 hcd)

lemma sub_le_self (a : α) {b : α} : a - b ≤ a ↔ 0 ≤ b :=
sub_left_le_iff_le_add.trans (le_add_iff_nonneg_left _)

lemma sub_le_self_of_nonneg (a : α) {b : α} : b ≥ 0 → a - b ≤ a := (sub_le_self a).2

lemma sub_lt_self (a : α) {b : α} : a - b < a ↔ 0 < b :=
sub_left_lt_iff_lt_add.trans (lt_add_iff_pos_left _)

lemma sub_lt_self_of_pos (a : α) {b : α} : b > 0 → a - b < a := (sub_lt_self a).2

lemma add_le_add_three {a b c d e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) :
      a + b + c ≤ d + e + f :=
add_le_add (add_le_add h₁ h₂) h₃

end ordered_comm_group

class decidable_linear_ordered_comm_group (α : Type u)
    extends add_comm_group α, decidable_linear_order α :=
(add_le_add_left_of_le : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(add_lt_add_left_of_lt : ∀ a b : α, a < b → ∀ c : α, c + a < c + b)

instance decidable_linear_ordered_comm_group.to_ordered_comm_group (α : Type u)
  [s : decidable_linear_ordered_comm_group α] : ordered_comm_group α :=
{ s with add := s.add }

class decidable_linear_ordered_cancel_comm_monoid (α : Type u)
      extends ordered_cancel_comm_monoid α, decidable_linear_order α
