/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura
-/
prelude
import init.algebra.ordered_ring init.algebra.field

set_option old_structure_cmd true

universe u

class linear_ordered_field (α : Type u) extends linear_ordered_ring α, field α

section linear_ordered_field
variables {α : Type u} [linear_ordered_field α]

lemma inv_pos_of_pos {a : α} (h : 0 < a) : 0 < a⁻¹ :=
(mul_lt_mul_left h).1 $
by rw [mul_zero, mul_inv_cancel' (ne_of_gt h)];
   exact zero_lt_one

@[simp] lemma inv_pos {a : α} : 0 < a⁻¹ ↔ 0 < a :=
⟨λ h, by have := inv_pos_of_pos h; rwa division_ring.inv_inv at this, inv_pos_of_pos⟩

lemma one_div_pos {a : α} : 0 < 1 / a ↔ 0 < a :=
by rw [one_div_eq_inv, inv_pos]

lemma pos_of_one_div_pos {a : α} : 0 < 1 / a → 0 < a := one_div_pos.1
lemma one_div_pos_of_pos {a : α} : 0 < a → 0 < 1 / a := one_div_pos.2

lemma inv_neg_of_neg {a : α} (h : a < 0) : a⁻¹ < 0 :=
have 0 < (-a)⁻¹, from inv_pos.2 (neg_pos.2 h),
by simp at this; exact neg_pos.1 this

@[simp] lemma inv_lt_zero {a : α} : a⁻¹ < 0 ↔ a < 0 :=
⟨λ h, by have := inv_neg_of_neg h; rwa division_ring.inv_inv at this, inv_neg_of_neg⟩

lemma one_div_neg {a : α} : 1 / a < 0 ↔ a < 0 :=
by simp

lemma one_div_neg_of_neg {a : α} : a < 0 → 1 / a < 0 := one_div_neg.2
lemma neg_of_one_div_neg {a : α} : 1 / a < 0 → a < 0 := one_div_neg.1

lemma le_div_iff_mul_le {a b c : α} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b :=
have a ≤ b / c ↔ _, from (mul_le_mul_right hc).symm,
by rwa div_mul_cancel_right _ (ne_of_gt hc) at this

lemma mul_le_of_le_div {a b c : α} (hc : 0 < c) : a ≤ b / c → a * c ≤ b := (le_div_iff_mul_le hc).1
lemma le_div_of_mul_le {a b c : α} (hc : 0 < c) : a * c ≤ b → a ≤ b / c := (le_div_iff_mul_le hc).2

lemma lt_div_iff_mul_lt {a b c : α} (hc : 0 < c) : a < b / c ↔ a * c < b :=
have a < b / c ↔ _, from (mul_lt_mul_right hc).symm,
by rwa div_mul_cancel_right _ (ne_of_gt hc) at this

lemma mul_lt_of_lt_div {a b c : α} (hc : 0 < c) : a < b / c → a * c < b := (lt_div_iff_mul_lt hc).1
lemma lt_div_of_mul_lt {a b c : α} (hc : 0 < c) : a * c < b → a < b / c := (lt_div_iff_mul_lt hc).2

lemma div_le_iff_mul_le_of_neg {a b c : α} (hc : c < 0) : b / c ≤ a ↔ a * c ≤ b :=
have b / c ≤ a ↔ _, from (mul_le_mul_right_of_neg hc).symm,
by rwa div_mul_cancel_right _ (ne_of_lt hc) at this

lemma mul_le_of_div_le_of_neg {a b c : α} (hc : c < 0) : b / c ≤ a → a * c ≤ b := (div_le_iff_mul_le_of_neg hc).1
lemma div_le_of_mul_le_of_neg {a b c : α} (hc : c < 0) : a * c ≤ b → b / c ≤ a := (div_le_iff_mul_le_of_neg hc).2

lemma div_lt_iff_mul_lt_of_neg {a b c : α} (hc : c < 0) : b / c < a ↔ a * c < b :=
have b / c < a ↔ _, from (mul_lt_mul_right_of_neg hc).symm,
by rwa div_mul_cancel_right _ (ne_of_lt hc) at this

lemma mul_lt_of_gt_div_of_neg {a b c : α} (hc : c < 0) : a > b / c → a * c < b := (div_lt_iff_mul_lt_of_neg hc).1
lemma div_lt_of_mul_gt_of_neg {a b c : α} (hc : c < 0) : a * c < b → b / c < a := (div_lt_iff_mul_lt_of_neg hc).2

lemma div_lt_iff_lt_mul {a b c : α} (hc : 0 < c) : b / c < a ↔ b < a * c :=
le_iff_le_iff_lt_iff_lt.1 (le_div_iff_mul_le hc)

lemma div_lt_of_mul_lt_of_pos {a b c : α} (hc : c > 0) : b < a * c → b / c < a := (div_lt_iff_lt_mul hc).2

lemma div_le_iff_le_mul {a b c : α} (hc : 0 < c) : a / c ≤ b ↔ a ≤ b * c :=
le_iff_le_iff_lt_iff_lt.2 (lt_div_iff_mul_lt hc)

lemma le_mul_of_div_le {a b c : α} (hc : c > 0) : a / c ≤ b → a ≤ b * c := (div_le_iff_le_mul hc).1

lemma div_le_iff_le_mul' {a b c : α} (hb : 0 < b) : a / b ≤ c ↔ a ≤ b * c :=
mul_comm c b ▸ div_le_iff_le_mul hb

lemma div_le_of_le_mul {a b c : α} (hb : b > 0) : a ≤ b * c → a / b ≤ c := (div_le_iff_le_mul' hb).2

lemma one_le_div_iff_le {a b : α} (hb : b > 0) : 1 ≤ a / b ↔ b ≤ a :=
by rw [le_div_iff_mul_le hb, one_mul]

lemma one_le_div_of_le {a b : α} (hb : b > 0) : b ≤ a → 1 ≤ a / b := (one_le_div_iff_le hb).2
lemma le_of_one_le_div {a b : α} (hb : b > 0) : 1 ≤ a / b → b ≤ a := (one_le_div_iff_le hb).1

lemma one_lt_div_iff_lt {a b : α} (hb : b > 0) : 1 < a / b ↔ b < a :=
by rw [lt_div_iff_mul_lt hb, one_mul]

lemma one_lt_div_of_lt (a : α) {b : α} (hb : b > 0) : b < a → 1 < a / b := (one_lt_div_iff_lt hb).2
lemma lt_of_one_lt_div (a : α) {b : α} (hb : b > 0) : 1 < a / b → b < a := (one_lt_div_iff_lt hb).1

  -- following these in the isabelle file, there are 8 biconditionals for the above with - signs
  -- skipping for now

lemma mul_sub_mul_div_mul_neg {a b c d : α} (hc : c ≠ 0) (hd : d ≠ 0) :
      (a * d - b * c) / (c * d) < 0 ↔ a / c < b / d :=
by rw [mul_comm b c, ← div_sub_div _ _ hc hd, sub_lt_zero]

lemma mul_sub_mul_div_neg_of_div_lt_div {a b c d : α} (hc : c ≠ 0) (hd : d ≠ 0) :
      a / c < b / d → (a * d - b * c) / (c * d) < 0 := (mul_sub_mul_div_mul_neg hc hd).2
lemma div_lt_div_of_mul_sub_mul_div_neg {a b c d : α} (hc : c ≠ 0) (hd : d ≠ 0) :
      (a * d - b * c) / (c * d) < 0 → a / c < b / d := (mul_sub_mul_div_mul_neg hc hd).1

lemma mul_sub_mul_div_mul_nonpos {a b c d : α} (hc : c ≠ 0) (hd : d ≠ 0) :
      (a * d - b * c) / (c * d) ≤ 0 ↔ a / c ≤ b / d :=
by rw [mul_comm b c, ← div_sub_div _ _ hc hd, sub_nonpos]

lemma div_le_div_of_mul_sub_mul_div_nonpos {a b c d : α} (hc : c ≠ 0) (hd : d ≠ 0) :
      (a * d - b * c) / (c * d) ≤ 0 → a / c ≤ b / d := (mul_sub_mul_div_mul_nonpos hc hd).1

lemma div_pos {a b : α} (ha : 0 < a) (hb : 0 < b) : 0 < a / b :=
mul_pos ha (inv_pos.2 hb)

def div_pos_of_pos_of_pos := @div_pos

lemma div_nonneg {a b : α} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b :=
mul_nonneg ha (le_of_lt (inv_pos.2 hb))

def div_nonneg_of_nonneg_of_pos := @div_nonneg

lemma div_neg_of_neg_of_pos {a b : α} (ha : a < 0) (hb : 0 < b) : a / b < 0 :=
mul_neg_of_neg_of_pos ha (inv_pos.2 hb)

lemma div_nonpos_of_nonpos_of_pos {a b : α} (ha : a ≤ 0) (hb : 0 < b) : a / b ≤ 0 :=
mul_nonpos_of_nonpos_of_nonneg ha (le_of_lt (inv_pos.2 hb))

lemma div_neg_of_pos_of_neg {a b : α} (ha : 0 < a) (hb : b < 0) : a / b < 0 :=
mul_neg_of_pos_of_neg ha (inv_lt_zero.2 hb)

lemma div_nonpos_of_nonneg_of_neg {a b : α} (ha : 0 ≤ a) (hb : b < 0) : a / b ≤ 0 :=
mul_nonpos_of_nonneg_of_nonpos ha (le_of_lt (inv_lt_zero.2 hb))

lemma div_pos_of_neg_of_neg {a b : α} (ha : a < 0) (hb : b < 0) : 0 < a / b :=
mul_pos_of_neg_of_neg ha (inv_lt_zero.2 hb)

lemma div_nonneg_of_nonpos_of_neg {a b : α} (ha : a ≤ 0) (hb : b < 0) : 0 ≤ a / b :=
mul_nonneg_of_nonpos_of_nonpos ha (le_of_lt (inv_lt_zero.2 hb))

lemma div_lt_div_right {a b c : α} (hc : 0 < c) : a / c < b / c ↔ a < b :=
(mul_lt_mul_left hc).symm.trans $
by repeat { rw mul_div_cancel_right' _ (ne_of_gt hc) }

lemma div_lt_div_of_lt_of_pos {a b c : α} (h : a < b) (hc : 0 < c) : a / c < b / c := (div_lt_div_right hc).2 h

lemma div_le_div_right {a b c : α} (hc : 0 < c) : a / c ≤ b / c ↔ a ≤ b :=
(mul_le_mul_left hc).symm.trans $
by repeat { rw mul_div_cancel_right' _ (ne_of_gt hc) }

lemma div_le_div_of_le_of_pos {a b c : α} (h : a ≤ b) (hc : 0 < c) : a / c ≤ b / c := (div_le_div_right hc).2 h

lemma div_lt_div_right_of_neg {a b c : α} (hc : c < 0) : a / c < b / c ↔ b < a :=
(mul_lt_mul_left_of_neg hc).symm.trans $
by repeat { rw mul_div_cancel_right' _ (ne_of_lt hc) }

lemma div_lt_div_of_lt_of_neg {a b c : α} (h : b < a) (hc : c < 0) : a / c < b / c := (div_lt_div_right_of_neg hc).2 h

lemma div_le_div_right_of_neg {a b c : α} (hc : c < 0) : a / c ≤ b / c ↔ b ≤ a :=
(mul_le_mul_left_of_neg hc).symm.trans $
by repeat { rw mul_div_cancel_right' _ (ne_of_lt hc) }

lemma div_le_div_of_le_of_neg {a b c : α} (h : b ≤ a) (hc : c < 0) : a / c ≤ b / c := (div_le_div_right_of_neg hc).2 h

lemma two_pos : (2:α) > 0 :=
add_pos zero_lt_one zero_lt_one

lemma two_ne_zero : (2:α) ≠ 0 :=
ne.symm (ne_of_lt two_pos)

lemma two_gt_one : (2:α) > 1 :=
calc (2:α) > 1+0 : (add_lt_add_left _).2 zero_lt_one
     ...   = 1   : add_zero 1

lemma two_ge_one : (2:α) ≥ 1 :=
le_of_lt two_gt_one

lemma add_self_div_two (a : α) : (a + a) / 2 = a :=
by rw [← two_mul, mul_div_cancel_left _ two_ne_zero]

lemma add_halves (a : α) : a / 2 + a / 2 = a :=
by rw [← add_div_distrib, add_self_div_two]

lemma sub_self_div_two (a : α) : a - a / 2 = a / 2 :=
sub_eq_iff_eq_add.2 (add_halves _).symm

lemma half_pos {a : α} (h : 0 < a) : 0 < a / 2 :=
div_pos h two_pos

lemma half_lt_self {a : α} (h : 0 < a) : a / 2 < a :=
have a * 1 < a * 2, from (mul_lt_mul_left h).2 two_gt_one,
(div_lt_iff_lt_mul two_pos).2 $ by rwa mul_one at this

lemma add_midpoint {a b : α} (h : a < b) : a + (b - a) / 2 < b :=
lt_sub_left_iff_add_lt.1 $ half_lt_self $ sub_pos.2 h

lemma div_two_sub_self (a : α) : a / 2 - a = - (a / 2) :=
by rw [← neg_sub, neg_inj, sub_self_div_two]

lemma four_pos : (4:α) > 0 :=
add_pos two_pos two_pos

lemma mul_le_mul_of_mul_div_le {a b c d : α} (h : a * (b / c) ≤ d) (hc : c > 0) : b * a ≤ d * c :=
by rwa [← mul_div_assoc, div_le_iff_le_mul hc, mul_comm] at h

lemma div_two_lt_of_pos {a b : α} : a > 0 → a / 2 < a :=
half_lt_self

lemma div_mul_le_div_mul_of_div_le_div_pos {a b c d e : α} (hb : b ≠ 0) (hd : d ≠ 0) (h : a / b ≤ c / d)
      (he : e > 0) : a / (b * e) ≤ c / (d * e) :=
by rwa [← field.div_div_eq_div_mul, ← field.div_div_eq_div_mul, div_le_div_right he]

lemma exists_add_lt_and_pos_of_lt {a b : α} (h : b < a) : ∃ c : α, b + c < a ∧ c > 0 :=
⟨(a - b) / 2, add_midpoint h, half_pos $ sub_pos.2 h⟩

lemma ge_of_forall_ge_sub {a b : α} (h : ∀ ε : α, ε > 0 → a ≥ b - ε) : a ≥ b :=
le_of_not_gt $ λ hb,
let ⟨ε, hε, h0⟩ := exists_add_lt_and_pos_of_lt hb in
not_lt_of_ge (h _ h0) (lt_sub_right_iff_add_lt.2 hε)

lemma one_div_lt_one_div_of_lt {a b : α} (ha : 0 < a) (h : a < b) : 1 / b < 1 / a :=
(div_lt_iff_lt_mul (lt_trans ha h)).2 $
by rw ← div_eq_one_div_mul; exact (one_lt_div_iff_lt ha).2 h

lemma inv_lt_inv_of_lt {a b : α} (ha : 0 < a) (h : a < b) : b⁻¹ < a⁻¹ :=
by rw [inv_eq_one_div, inv_eq_one_div]; exact one_div_lt_one_div_of_lt ha h

lemma one_div_le_one_div_of_le {a b : α} (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a :=
(div_le_iff_le_mul (lt_of_lt_of_le ha h)).2 $
by rw ← div_eq_one_div_mul; exact (one_le_div_iff_le ha).2 h

lemma inv_le_inv_of_le {a b : α} (ha : 0 < a) (h : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
by rw [inv_eq_one_div, inv_eq_one_div]; exact one_div_le_one_div_of_le ha h

lemma one_div_lt_one_div_of_lt_of_neg {a b : α} (hb : b < 0) (h : a < b) : 1 / b < 1 / a :=
(div_lt_iff_mul_lt_of_neg hb).2 $
by rwa [← div_eq_one_div_mul, div_lt_iff_mul_lt_of_neg (lt_trans h hb), one_mul]

lemma one_div_le_one_div_of_le_of_neg {a b : α} (hb : b < 0) (h : a ≤ b) : 1 / b ≤ 1 / a :=
(div_le_iff_mul_le_of_neg hb).2 $
by rwa [← div_eq_one_div_mul, div_le_iff_mul_le_of_neg (lt_of_le_of_lt h hb), one_mul]

lemma inv_lt_inv_of_lt_of_neg {a b : α} (hb : b < 0) (h : a < b) : b⁻¹ < a⁻¹ :=
by rw [inv_eq_one_div, inv_eq_one_div]; exact one_div_lt_one_div_of_lt_of_neg hb h

lemma inv_le_inv_of_le_of_neg {a b : α} (hb : b < 0) (h : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
by rw [inv_eq_one_div, inv_eq_one_div]; exact one_div_le_one_div_of_le_of_neg hb h

lemma le_of_inv_le_inv {a b : α} (h : 0 < a) : a⁻¹ ≤ b⁻¹ → b ≤ a :=
le_imp_le_iff_lt_imp_lt.2 (inv_lt_inv_of_lt h)

lemma le_of_one_div_le_one_div {a b : α} (h : 0 < a) (hl : 1 / a ≤ 1 / b) : b ≤ a :=
by simp at hl; exact le_of_inv_le_inv h hl

lemma lt_of_inv_lt_inv {a b : α} (h : 0 < a) : a⁻¹ < b⁻¹ → b < a :=
le_imp_le_iff_lt_imp_lt.1 (inv_le_inv_of_le h)

lemma lt_of_one_div_lt_one_div {a b : α} (h : 0 < a) : 1 / a < 1 / b → b < a :=
by simp; exact lt_of_inv_lt_inv h

lemma le_of_inv_le_inv_of_neg {a b : α} (h : b < 0) : a⁻¹ ≤ b⁻¹ → b ≤ a :=
le_imp_le_iff_lt_imp_lt.2 (inv_lt_inv_of_lt_of_neg h)

lemma le_of_one_div_le_one_div_of_neg {a b : α} (h : b < 0) (hl : 1 / a ≤ 1 / b) : b ≤ a :=
by simp at hl; exact le_of_inv_le_inv_of_neg h hl

lemma lt_of_inv_lt_inv_of_neg {a b : α} (h : b < 0) : a⁻¹ < b⁻¹ → b < a :=
le_imp_le_iff_lt_imp_lt.1 (inv_le_inv_of_le_of_neg h)

lemma lt_of_one_div_lt_one_div_of_neg {a b : α} (h : b < 0) (hl : 1 / a < 1 / b) : b < a :=
by simp at hl; exact lt_of_inv_lt_inv_of_neg h hl

lemma inv_le_of_inv_le {a b : α} (ha : a > 0) (h : a⁻¹ ≤ b) : b⁻¹ ≤ a :=
le_of_inv_le_inv ha $ by simp [h]

lemma one_div_le_of_one_div_le {a b : α} (ha : a > 0) (h : 1 / a ≤ b) : 1 / b ≤ a :=
by rw one_div_eq_inv at *; exact inv_le_of_inv_le ha h

def one_div_le_of_one_div_le_of_pos := @one_div_le_of_one_div_le

lemma inv_le_of_inv_le_of_neg {a b : α} (hb : b < 0) (h : a⁻¹ ≤ b) : b⁻¹ ≤ a :=
le_of_inv_le_inv_of_neg (inv_lt_zero.2 hb) $ by simp [h]

lemma one_div_le_of_one_div_le_of_neg {a b : α} (hb : b < 0) (h : 1 / a ≤ b) : 1 / b ≤ a :=
by rw one_div_eq_inv at *; exact inv_le_of_inv_le_of_neg hb h

lemma one_lt_one_div {a : α} (h : 0 < a) : 1 < 1 / a ↔ a < 1 :=
one_lt_div_iff_lt h

lemma one_lt_one_div_of_lt {a : α} (h1 : 0 < a) (h2 : a < 1) : 1 < 1 / a := (one_lt_one_div h1).2 h2

lemma one_lt_inv {a : α} (h : 0 < a) : 1 < a⁻¹ ↔ a < 1 :=
by have := one_lt_one_div h; simp at this; assumption

lemma one_le_one_div {a : α} (h : 0 < a) : 1 ≤ 1 / a ↔ a ≤ 1 :=
one_le_div_iff_le h

lemma one_le_one_div_of_le {a : α} (h1 : 0 < a) (h2 : a ≤ 1) : 1 ≤ 1 / a := (one_le_one_div h1).2 h2

lemma one_le_inv {a : α} (h : 0 < a) : 1 ≤ a⁻¹ ↔ a ≤ 1 :=
by have := one_le_one_div h; simp at this; assumption

lemma inv_lt_neg_one {a : α} (h1 : a < 0) : a⁻¹ < -1 ↔ -1 < a :=
by have := one_lt_inv (neg_pos.2 h1);
   rwa [inv_neg, lt_neg, neg_lt] at this

lemma one_div_lt_neg_one {a : α} (h1 : a < 0) : 1 / a < -1 ↔ -1 < a :=
by simp; exact inv_lt_neg_one h1

lemma one_div_lt_neg_one_of_lt {a : α} (h1 : a < 0) : -1 < a → 1 / a < -1 := (one_div_lt_neg_one h1).2

lemma inv_le_neg_one {a : α} (h1 : a < 0) : a⁻¹ ≤ -1 ↔ -1 ≤ a :=
by have := one_le_inv (neg_pos.2 h1);
   rwa [inv_neg, le_neg, neg_le] at this

lemma one_div_le_neg_one {a : α} (h1 : a < 0) : 1 / a ≤ -1 ↔ -1 ≤ a :=
by simp; exact inv_le_neg_one h1

lemma one_div_le_neg_one_of_le {a : α} (h1 : a < 0) : -1 ≤ a → 1 / a ≤ -1 := (one_div_le_neg_one h1).2

lemma div_lt_div_of_lt_left {a b c : α} (hb : 0 < b) (hc : 0 < c) (h : b < a) : c / a < c / b :=
(mul_lt_mul_left hc).2 (inv_lt_inv_of_lt hb h)

lemma div_lt_div_of_pos_of_lt_of_pos {a b c : α} (hb : 0 < b) (h : b < a) (hc : 0 < c) : c / a < c / b :=
div_lt_div_of_lt_left hb hc h

lemma div_le_div_of_le_left {a b c : α} (hb : 0 < b) (hc : 0 < c) (h : b ≤ a) : c / a ≤ c / b :=
(mul_le_mul_left hc).2 (inv_le_inv_of_le hb h)

lemma lt_of_div_lt_div_left {a b c : α} (ha : 0 < a) (hc : 0 < c) : c / a < c / b → b < a :=
le_imp_le_iff_lt_imp_lt.1 (div_le_div_of_le_left ha hc)

lemma le_of_div_le_div_left {a b c : α} (ha : 0 < a) (hc : 0 < c) : c / a ≤ c / b → b ≤ a :=
le_imp_le_iff_lt_imp_lt.2 (div_lt_div_of_lt_left ha hc)

lemma div_le_div_left {a b c : α} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : c / a ≤ c / b ↔ b ≤ a :=
⟨le_of_div_le_div_left ha hc, div_le_div_of_le_left hb hc⟩

lemma div_lt_div_left {a b c : α} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : c / a < c / b ↔ b < a :=
⟨lt_of_div_lt_div_left ha hc, div_lt_div_of_lt_left hb hc⟩

lemma div_mul_lt_div_mul_of_lt_right {a b c d e : α} (h : a / b ≤ c / d)
          (he : e > 0) : a / (b * e) ≤ c / (d * e) :=
by repeat { rw ← field.div_div_eq_div_mul };
   exact div_le_div_of_le_of_pos h he

end linear_ordered_field

class decidable_linear_ordered_field (α : Type u) extends linear_ordered_field α,
    decidable_linear_order α

instance decidable_linear_ordered_field.to_decidable_linear_ordered_comm_ring
  (α : Type u) [d : decidable_linear_ordered_field α] : decidable_linear_ordered_comm_ring α :=
{ d with
  decidable_le := @decidable_linear_order.decidable_le α _ }
