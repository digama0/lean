/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura

Structures with multiplicative and additive components, including division rings and fields.
The development is modeled after Isabelle's library.
-/
prelude
import init.algebra.ring
universe u

/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
set_option default_priority 100

set_option old_structure_cmd true

class division_ring (α : Type u) extends ring α, has_inv α, zero_ne_one_class α :=
(inv_zero : (0:α)⁻¹ = 0)
(mul_inv_cancel : ∀ {a : α}, a ≠ 0 → a * a⁻¹ = 1)
(inv_mul_cancel : ∀ {a : α}, a ≠ 0 → a⁻¹ * a = 1)

variable {α : Type u}

section division_ring
variables [division_ring α]

@[simp] lemma inv_zero : 0⁻¹ = (0:α) :=
division_ring.inv_zero α

protected definition algebra.div (a b : α) : α :=
a * b⁻¹

instance division_ring_has_div [division_ring α] : has_div α :=
⟨algebra.div⟩

lemma div_eq_mul_inv (a b : α) : a / b = a * b⁻¹ :=
rfl

def division_def := @div_eq_mul_inv

local attribute [simp] div_eq_mul_inv

@[simp] lemma mul_inv_cancel' {a : α} (h : a ≠ 0) : a * a⁻¹ = 1 :=
division_ring.mul_inv_cancel h

@[simp] lemma inv_mul_cancel' {a : α} (h : a ≠ 0) : a⁻¹ * a = 1 :=
division_ring.inv_mul_cancel h

@[simp] lemma division_ring.mul_inv_cancel_left {a : α} (b : α) (h : a ≠ 0) : a * (a⁻¹ * b) = b :=
by rw [← mul_assoc, mul_inv_cancel' h, one_mul]

@[simp] lemma division_ring.inv_mul_cancel_left {a: α} (b : α) (h : a ≠ 0) : a⁻¹ * (a * b) = b :=
by rw [← mul_assoc, inv_mul_cancel' h, one_mul]

@[simp] lemma division_ring.mul_inv_cancel_right (a : α) {b : α} (h : b ≠ 0) : a * b * b⁻¹ = a :=
by rw [mul_assoc, mul_inv_cancel' h, mul_one]

@[simp] lemma division_ring.inv_mul_cancel_right (a : α) {b : α} (h : b ≠ 0) : a * b⁻¹ * b = a :=
by rw [mul_assoc, inv_mul_cancel' h, mul_one]

@[simp] lemma one_div_eq_inv (a : α) : 1 / a = a⁻¹ :=
one_mul a⁻¹

lemma inv_eq_one_div (a : α) : a⁻¹ = 1 / a :=
by simp

lemma div_eq_mul_one_div (a b : α) : a / b = a * (1 / b) :=
by simp

lemma mul_one_div_cancel {a : α} (h : a ≠ 0) : a * (1 / a) = 1 :=
by simp [h]

lemma one_div_mul_cancel {a : α} (h : a ≠ 0) : (1 / a) * a = 1 :=
by simp [h]

lemma div_self {a : α} (h : a ≠ 0) : a / a = 1 :=
by simp [h]

@[simp] lemma division_ring.one_inv : 1⁻¹ = (1:α) :=
by simp [inv_eq_one_div, div_self]

def one_inv_eq := @division_ring.one_inv

lemma div_one (a : α) : a / 1 = a :=
by simp

lemma one_div_one : 1 / 1 = (1:α) :=
div_one _

lemma mul_div_assoc (a b c : α) : (a * b) / c = a * (b / c) :=
by simp

lemma div_zero (a : α) : a / 0 = 0 :=
by simp

lemma zero_div (a : α) : 0 / a = 0 :=
by simp

lemma division_ring.eq_zero_or_eq_zero_of_mul_eq_zero
    {a b : α} (h : a * b = 0) : a = 0 ∨ b = 0 :=
(classical.em _).imp_right $ λ h',
  by rw [← one_mul b, ← division_ring.inv_mul_cancel h', mul_assoc, h, mul_zero]

instance division_ring.to_domain [s : division_ring α] : domain α :=
{ s with eq_zero_or_eq_zero_of_mul_eq_zero :=
  @division_ring.eq_zero_or_eq_zero_of_mul_eq_zero _ _ }

@[simp] lemma division_ring.inv_eq_of_mul_eq_one {a b : α} (h : a * b = 1) : a⁻¹ = b :=
have a ≠ 0, by intro a0; subst a0; simp at h; contradiction,
(domain.mul_left_inj this).1 $ by simp [this, h]

@[simp] lemma division_ring.inv_inv (a : α) : a⁻¹⁻¹ = a :=
(classical.em (a = 0)).elim (λ e, e.symm ▸ by simp) $
λ h, division_ring.inv_eq_of_mul_eq_one $ division_ring.inv_mul_cancel h

lemma one_div_one_div (a : α) : 1 / (1 / a) = a :=
by simp

lemma division_ring.eq_inv_of_mul_eq_one {a b : α} (h : a * b = 1) : a = b⁻¹ :=
by rw [← division_ring.inv_eq_of_mul_eq_one h, division_ring.inv_inv]

lemma one_div_eq_of_mul_eq_one {a b : α} (h : a * b = 1) : 1 / a = b :=
by simp [division_ring.inv_eq_of_mul_eq_one h]

lemma eq_one_div_of_mul_eq_one {a b : α} (h : a * b = 1) : a = 1 / b :=
by simp [division_ring.eq_inv_of_mul_eq_one h]

@[simp] lemma division_ring.inv_inj {a b : α} : a⁻¹ = b⁻¹ ↔ a = b :=
⟨λ h, by rw [← division_ring.inv_inv a, h, division_ring.inv_inv], congr_arg _⟩

@[simp] lemma one_div_inj {a b : α} : 1 / a = 1 / b ↔ a = b :=
by simp

lemma division_ring.eq_of_one_div_eq_one_div {a b : α} : 1 / a = 1 / b → a = b :=
one_div_inj.1

@[simp] lemma inv_eq_zero {a : α} : a⁻¹ = 0 ↔ a = 0 :=
iff.trans (by rw inv_zero) division_ring.inv_inj

@[simp] lemma inv_ne_zero {a : α} : a⁻¹ ≠ 0 ↔ a ≠ 0 :=
not_congr inv_eq_zero

lemma one_div_eq_zero {a : α} : 1 / a = 0 ↔ a = 0 :=
by simp

lemma one_div_ne_zero {a : α} : 1 / a ≠ 0 ↔ a ≠ 0 :=
not_congr one_div_eq_zero

lemma one_div_ne_zero_of_ne_zero {a : α} : a ≠ 0 → 1 / a ≠ 0 :=
one_div_ne_zero.2

@[simp] lemma division_ring.mul_inv (a b : α) : (b * a)⁻¹ = a⁻¹ * b⁻¹ :=
(classical.em (a = 0)).elim (λ e, e.symm ▸ by simp) $ λ a0,
(classical.em (b = 0)).elim (λ e, e.symm ▸ by simp) $ λ b0,
division_ring.inv_eq_of_mul_eq_one $
by rw [mul_assoc, division_ring.mul_inv_cancel_left _ a0, mul_inv_cancel' b0]

def mul_inv_eq := @division_ring.mul_inv

lemma one_div_mul_one_div (a b : α) : (1 / a) * (1 / b) = 1 / (b * a) :=
by simp

@[simp] lemma inv_neg (a : α) : (- a)⁻¹ = - a⁻¹ :=
(classical.em (a = 0)).elim (λ e, by simp [e]) $ λ a0,
division_ring.inv_eq_of_mul_eq_one $ by rw [neg_mul_neg, mul_inv_cancel' a0]

lemma div_neg (a b : α) : b / (- a) = - (b / a) :=
by simp

def div_neg_eq_neg_div := @div_neg

lemma division_ring.one_div_neg_eq_neg_one_div (a : α) : 1 / (- a) = - (1 / a) :=
div_neg _ _

lemma one_div_neg_one_eq_neg_one : (1:α) / (-1) = -1 :=
by simp

lemma neg_div (a b : α) : (-b) / a = - (b / a) :=
by simp

lemma neg_div_neg (a b : α) : (-a) / (-b) = a / b :=
by simp

def division_ring.neg_div_neg_eq := @neg_div_neg

lemma mul_div_cancel_right (a : α) {b : α} (hb : b ≠ 0) : a * b / b = a :=
by simp [hb]

lemma div_mul_cancel_right (a : α) {b : α} (hb : b ≠ 0) : a / b * b = a :=
by simp [hb]

lemma add_div_distrib (a b c : α) : (a + b) / c = a / c + b / c :=
right_distrib a b (c⁻¹)

lemma sub_div_distrib (a b c : α) : (a - b) / c = (a / c) - (b / c) :=
(add_div_distrib _ _ _).trans $ by simp

lemma div_add_div_same (a b c : α) : a / c + b / c = (a + b) / c :=
(add_div_distrib _ _ _).symm

lemma div_sub_div_same (a b c : α) : (a / c) - (b / c) = (a - b) / c :=
(sub_div_distrib _ _ _).symm

lemma inv_add_inv {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
          a⁻¹ + b⁻¹ = a⁻¹ * (a + b) * b⁻¹ :=
by rw [left_distrib a⁻¹, inv_mul_cancel' ha, right_distrib, one_mul,
       division_ring.mul_inv_cancel_right _ hb, add_comm]

lemma one_div_add_one_div {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
          1 / a + 1 / b = (1 / a) * (a + b) * (1 / b) :=
by simp only [one_div_eq_inv, inv_add_inv ha hb]

lemma inv_sub_inv {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
          a⁻¹ - b⁻¹ = a⁻¹ * (b - a) * b⁻¹ :=
by rw [mul_sub_left_distrib a⁻¹, inv_mul_cancel' ha,
       mul_sub_right_distrib, one_mul, division_ring.mul_inv_cancel_right _ hb]

lemma one_div_sub_one_div {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
          1 / a - 1 / b = (1 / a) * (b - a) * (1 / b) :=
by simp only [one_div_eq_inv, inv_sub_inv ha hb]

lemma one_div_mul_add_mul_one_div_eq_one_div_add_one_div {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
          (1 / a) * (a + b) * (1 / b) = 1 / a + 1 / b :=
(one_div_add_one_div ha hb).symm

lemma one_div_mul_sub_mul_one_div_eq_one_div_add_one_div {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
          (1 / a) * (b - a) * (1 / b) = 1 / a - 1 / b :=
(one_div_sub_one_div ha hb).symm

lemma div_right_inj {a b c : α} (h : c ≠ 0) : a / c = b / c ↔ a = b :=
domain.mul_right_inj (inv_ne_zero.2 h)

lemma div_left_inj {a b c : α} (h : a ≠ 0) : a / b = a / c ↔ b = c :=
(domain.mul_left_inj h).trans division_ring.inv_inj

lemma div_eq_one {a b : α} (hb : b ≠ 0) : a / b = 1 ↔ a = b :=
iff.trans (by rw div_self hb) (div_right_inj hb)

def div_eq_one_iff_eq := @div_eq_one

lemma eq_of_div_eq_one {a b : α} (Hb : b ≠ 0) : a / b = 1 → a = b :=
(div_eq_one Hb).1

lemma eq_div_iff_mul_eq {a b c : α} (hc : c ≠ 0) : a = b / c ↔ a * c = b :=
(domain.mul_right_inj hc).symm.trans $ by rw div_mul_cancel_right _ hc

lemma eq_div_of_mul_eq {a b c : α} (hc : c ≠ 0) : a * c = b → a = b / c :=
(eq_div_iff_mul_eq hc).2

lemma mul_eq_of_eq_div {a b c : α} (hc : c ≠ 0) : a = b / c → a * c = b :=
(eq_div_iff_mul_eq hc).1

lemma div_eq_iff_eq_mul {a b c : α} (hc : c ≠ 0) : b / c = a ↔ b = a * c :=
by rw [eq_comm, @eq_comm _ b]; exact eq_div_iff_mul_eq hc

lemma add_div_eq_mul_add_div (a b : α) {c : α} (hc : c ≠ 0) : a + b / c = (a * c + b) / c :=
by rw [add_div_distrib, mul_div_cancel_right _ hc]

lemma mul_mul_div (a : α) {b : α} (hb : b ≠ 0) : a = a * b * (1 / b) :=
by simp [hb]

lemma inv_div (a b : α) : (a / b)⁻¹ = b / a :=
by rw [div_eq_mul_inv, division_ring.mul_inv, division_ring.inv_inv]; refl

lemma one_div_div (a b : α) : 1 / (a / b) = b / a :=
by rw [one_div_eq_inv, inv_div]

lemma div_div_eq_mul_div (a b c : α) :
      a / (b / c) = (a * c) / b :=
by rw [div_eq_mul_one_div, one_div_div, ← mul_div_assoc]

lemma div_mul_cancel_right' {a b : α} (h : b ≠ 0) : b / (a * b) = 1 / a :=
by rw [div_eq_mul_inv, division_ring.mul_inv,
       division_ring.mul_inv_cancel_left _ h, one_div_eq_inv]

lemma div_div_eq_div_mul (a b c : α) : (a / b) / c = a / (c * b) :=
by simp

end division_ring

class field (α : Type u) extends division_ring α, comm_ring α

section field

variable [field α]

lemma div_eq_one_div_mul (a b : α) : a / b = 1 / b * a :=
by rw [div_eq_mul_one_div, mul_comm]

lemma field.mul_inv (a b : α) : (a * b)⁻¹ = a⁻¹ * b⁻¹ :=
by rw [division_ring.mul_inv, mul_comm]

lemma field.one_div_mul_one_div (a b : α) : (1 / a) * (1 / b) = 1 / (a * b) :=
by rw [one_div_mul_one_div, mul_comm b]

lemma field.div_mul_cancel_left (a : α) {b : α} (h : a ≠ 0) : a / (a * b) = 1 / b :=
by simp [div_eq_mul_inv]; rw [division_ring.mul_inv_cancel_left _ h]; simp

lemma mul_div_cancel_left {a : α} (b : α) (ha : a ≠ 0) : a * b / a = b :=
by rw [mul_comm a, mul_div_cancel_right _ ha]

lemma mul_div_cancel_right' (a : α) {b : α} (hb : b ≠ 0) : b * (a / b) = a :=
by rw [mul_comm, div_mul_cancel_right _ hb]

lemma field.div_div_eq_div_mul (a b c : α) : (a / b) / c = a / (b * c) :=
by rw [div_div_eq_div_mul, mul_comm]

lemma field.one_div_add_one_div {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) :=
by rw [one_div_add_one_div ha hb, ← div_eq_one_div_mul, ← div_eq_mul_one_div, field.div_div_eq_div_mul]

lemma div_mul_div (a b c d : α) : (a / b) * (c / d) = (a * c) / (b * d) :=
by simp [div_eq_mul_inv]

lemma mul_div_mul_left (a b : α) {c : α} (hc : c ≠ 0) : (c * a) / (c * b) = a / b :=
by rw [← div_mul_div, div_self hc, one_mul]

lemma mul_div_mul_right (a b : α) {c : α} (hc : c ≠ 0) : (a * c) / (b * c) = a / b :=
by rw [mul_comm a, mul_comm b, mul_div_mul_left _ _ hc]

lemma div_mul_eq_mul_div (a b c : α) : (b / c) * a = (b * a) / c :=
by simp [div_eq_mul_inv]

lemma field.div_mul_eq_mul_div_comm (a b c : α) : (a / c) * b = a * (b / c) :=
by rw [div_mul_eq_mul_div, mul_div_assoc]

lemma div_add_div (a : α) {b : α} (c : α) {d : α} (hb : b ≠ 0) (hd : d ≠ 0) :
      a / b + c / d = (a * d + b * c) / (b * d) :=
by rw [add_div_distrib, mul_div_mul_left _ _ hb, mul_div_mul_right _ _ hd]

lemma div_sub_div (a : α) {b : α} (c : α) {d : α} (hb : b ≠ 0) (hd : d ≠ 0) :
      a / b - c / d = (a * d - b * c) / (b * d) :=
by rw [sub_div_distrib, mul_div_mul_left _ _ hb, mul_div_mul_right _ _ hd]

lemma div_eq_div_iff_mul_eq_mul {a b c d : α} (hb : b ≠ 0) (hd : d ≠ 0) :
  a / b = c / d ↔ a * d = c * b :=
by rw [eq_div_iff_mul_eq hd, div_mul_eq_mul_div, div_eq_iff_eq_mul hb]

lemma mul_eq_mul_of_div_eq_div {a b c d : α} (hb : b ≠ 0) (hd : d ≠ 0) :
  a / b = c / d → a * d = c * b :=
(div_eq_div_iff_mul_eq_mul hb hd).1

lemma field.div_div_div (a : α) {b c d : α} (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
      (a / b) / (c / d) = (a * d) / (b * c) :=
by rw [div_div_eq_mul_div, div_mul_eq_mul_div, field.div_div_eq_div_mul]

def field.div_div_div_div_eq := @field.div_div_div

lemma field.div_mul_eq_div_mul_one_div (a b c : α) :
      a / (b * c) = (a / b) * (1 / c) :=
by rw [← field.div_div_eq_div_mul, ← div_eq_mul_one_div]

end field
