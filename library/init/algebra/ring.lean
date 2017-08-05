/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
prelude
import init.algebra.group

/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
set_option default_priority 100

set_option old_structure_cmd true

universe u

class distrib (α : Type u) extends has_mul α, has_add α :=
(left_distrib : ∀ a b c : α, a * (b + c) = (a * b) + (a * c))
(right_distrib : ∀ a b c : α, (a + b) * c = (a * c) + (b * c))

variable {α : Type u}

lemma left_distrib [distrib α] (a b c : α) : a * (b + c) = a * b + a * c :=
distrib.left_distrib a b c

def mul_add := @left_distrib

lemma right_distrib [distrib α] (a b c : α) : (a + b) * c = a * c + b * c :=
distrib.right_distrib a b c

def add_mul := @right_distrib

class mul_zero_class (α : Type u) extends has_mul α, has_zero α :=
(zero_mul : ∀ a : α, 0 * a = 0)
(mul_zero : ∀ a : α, a * 0 = 0)

@[simp] lemma zero_mul [mul_zero_class α] (a : α) : 0 * a = 0 :=
mul_zero_class.zero_mul a

@[simp] lemma mul_zero [mul_zero_class α] (a : α) : a * 0 = 0 :=
mul_zero_class.mul_zero a

class zero_ne_one_class (α : Type u) extends has_zero α, has_one α :=
(zero_ne_one : 0 ≠ (1:α))

@[simp]
lemma zero_ne_one [s: zero_ne_one_class α] : 0 ≠ (1:α) :=
@zero_ne_one_class.zero_ne_one α s

@[simp]
lemma one_ne_zero [s: zero_ne_one_class α] : (1:α) ≠ 0 :=
assume h, @zero_ne_one_class.zero_ne_one α s h.symm

/- semiring -/

class semiring (α : Type u) extends add_comm_monoid α, monoid α, distrib α, mul_zero_class α

section semiring
  variables [semiring α]

  lemma one_add_one_eq_two : 1 + 1 = (2 : α) :=
  by unfold bit0

  lemma two_mul (n : α) : 2 * n = n + n :=
  eq.trans (right_distrib 1 1 n) (by simp)

  lemma ne_zero_of_mul_ne_zero_right {a b : α} : a * b ≠ 0 → a ≠ 0 :=
  mt $ λ h, h.symm ▸ zero_mul _

  lemma ne_zero_of_mul_ne_zero_left {a b : α} : a * b ≠ 0 → b ≠ 0 :=
  mt $ λ h, h.symm ▸ mul_zero _

  lemma distrib_three_right (a b c d : α) : (a + b + c) * d = a * d + b * d + c * d :=
  by simp [right_distrib]
end semiring

class comm_semiring (α : Type u) extends semiring α, comm_monoid α

section comm_semiring
  variables [comm_semiring α] (a b c : α)

  instance comm_semiring_has_dvd : has_dvd α :=
  has_dvd.mk (λ a b, ∃ c, b = a * c)

  -- TODO: this used to not have c explicit, but that seems to be important
  --       for use with tactics, similar to exist.intro
  lemma dvd.intro {a b : α} (c : α) (h : a * c = b) : a ∣ b :=
  exists.intro c h^.symm

  def dvd_of_mul_right_eq := @dvd.intro

  lemma dvd.intro_left {a b : α} (c : α) (h : c * a = b) : a ∣ b :=
  dvd.intro _ (begin rewrite mul_comm at h, apply h end)

  def dvd_of_mul_left_eq := @dvd.intro_left

  lemma exists_eq_mul_right_of_dvd {a b : α} (h : a ∣ b) : ∃ c, b = a * c := h

  lemma dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : ∀ c, b = a * c → P) : P :=
  exists.elim H₁ H₂

  lemma exists_eq_mul_left_of_dvd {a b : α} (h : a ∣ b) : ∃ c, b = c * a :=
  dvd.elim h (assume c, assume H1 : b = a * c, exists.intro c (eq.trans H1 (mul_comm a c)))

  lemma dvd.elim_left {P : Prop} {a b : α} (h₁ : a ∣ b) (h₂ : ∀ c, b = c * a → P) : P :=
  exists.elim (exists_eq_mul_left_of_dvd h₁) (assume c, assume h₃ : b = c * a, h₂ c h₃)

  @[simp] lemma dvd_refl : a ∣ a :=
  dvd.intro 1 (by simp)

  lemma dvd_trans {a b c : α} (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c :=
  match h₁, h₂ with
  | ⟨d, (h₃ : b = a * d)⟩, ⟨e, (h₄ : c = b * e)⟩ :=
    ⟨d * e, show c = a * (d * e), by simp [h₃, h₄]⟩
  end

  def dvd.trans := @dvd_trans

  lemma eq_zero_of_zero_dvd {a : α} (h : 0 ∣ a) : a = 0 :=
  dvd.elim h (assume c, assume H' : a = 0 * c, eq.trans H' (zero_mul c))

  @[simp] lemma dvd_zero : a ∣ 0 := dvd.intro 0 (by simp)

  @[simp] lemma one_dvd : 1 ∣ a := dvd.intro a (by simp)

  @[simp] lemma dvd_mul_right : a ∣ a * b := dvd.intro b rfl

  @[simp] lemma dvd_mul_left : a ∣ b * a := dvd.intro b (by simp)

  lemma dvd_mul_of_dvd_left {a b : α} (h : a ∣ b) (c : α) : a ∣ b * c :=
  dvd.elim h (λ d h', begin rw [h', mul_assoc], apply dvd_mul_right end)

  lemma dvd_mul_of_dvd_right {a b : α} (h : a ∣ b) (c : α) : a ∣ c * b :=
  begin rw mul_comm, exact dvd_mul_of_dvd_left h _ end

  lemma mul_dvd_mul : ∀ {a b c d : α}, a ∣ b → c ∣ d → a * c ∣ b * d
  | a ._ c ._ ⟨e, rfl⟩ ⟨f, rfl⟩ := ⟨e * f, by simp⟩

  lemma mul_dvd_mul_left (a : α) {b c : α} (h : b ∣ c) : a * b ∣ a * c :=
  mul_dvd_mul (dvd_refl a) h

  lemma mul_dvd_mul_right {a b : α} (h : a ∣ b) (c : α) : a * c ∣ b * c :=
  mul_dvd_mul h (dvd_refl c)

  lemma dvd_add {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
  dvd.elim h₁ (λ d hd, dvd.elim h₂ (λ e he, dvd.intro (d + e) (by simp [left_distrib, hd, he])))

  lemma dvd_of_mul_right_dvd {a b c : α} (h : a * b ∣ c) : a ∣ c :=
  dvd.elim h (begin intros d h₁, rw [h₁, mul_assoc], apply dvd_mul_right end)

  lemma dvd_of_mul_left_dvd {a b c : α} (h : a * b ∣ c) : b ∣ c :=
  dvd.elim h (λ d ceq, dvd.intro (a * d) (by simp [ceq]))
end comm_semiring

/- ring -/

class ring (α : Type u) extends add_comm_group α, monoid α, distrib α

lemma ring.mul_zero [ring α] (a : α) : a * 0 = 0 :=
add_left_cancel $ show a * 0 + a * 0 = a * 0 + 0,
by rw [← left_distrib, add_zero, add_zero]

lemma ring.zero_mul [ring α] (a : α) : 0 * a = 0 :=
add_right_cancel $ show 0 * a + 0 * a = 0 + 0 * a,
by rw [← right_distrib, zero_add, zero_add]

instance ring.to_semiring [s : ring α] : semiring α :=
{ s with
  mul_zero := ring.mul_zero,
  zero_mul := ring.zero_mul }

lemma neg_mul_eq_neg_mul [s : ring α] (a b : α) : -(a * b) = -a * b :=
neg_eq_of_add_eq_zero $
by rw [← right_distrib, add_right_neg, zero_mul]

lemma neg_mul_eq_mul_neg [s : ring α] (a b : α) : -(a * b) = a * -b :=
neg_eq_of_add_eq_zero $
by rw [← left_distrib, add_right_neg, mul_zero]

@[simp] lemma neg_mul_eq_neg_mul_symm [s : ring α] (a b : α) : - a * b = - (a * b) :=
eq.symm (neg_mul_eq_neg_mul a b)

@[simp] lemma mul_neg_eq_neg_mul_symm [s : ring α] (a b : α) : a * - b = - (a * b) :=
eq.symm (neg_mul_eq_mul_neg a b)

lemma neg_mul_neg [s : ring α] (a b : α) : -a * -b = a * b :=
by simp

lemma neg_mul_comm [s : ring α] (a b : α) : -a * b = a * -b :=
by simp

lemma neg_eq_neg_one_mul [s : ring α] (a : α) : -a = -1 * a :=
by simp

lemma mul_sub_left_distrib [s : ring α] (a b c : α) : a * (b - c) = a * b - a * c :=
(left_distrib a b (-c)).trans $ by simp

def mul_sub := @mul_sub_left_distrib

lemma mul_sub_right_distrib [s : ring α] (a b c : α) : (a - b) * c = a * c - b * c :=
(right_distrib a (-b) c).trans $ by simp

def sub_mul := @mul_sub_right_distrib

class comm_ring (α : Type u) extends ring α, comm_semigroup α

instance comm_ring.to_comm_semiring [s : comm_ring α] : comm_semiring α :=
{ s with
  mul_zero := mul_zero,
  zero_mul := zero_mul }

section comm_ring
  variable [comm_ring α]

  lemma mul_self_sub_mul_self_eq (a b : α) : a * a - b * b = (a + b) * (a - b) :=
  by simp [right_distrib, left_distrib]

  lemma mul_self_sub_one_eq (a : α) : a * a - 1 = (a + 1) * (a - 1) :=
  by simp [right_distrib, left_distrib]

  lemma add_mul_self_eq (a b : α) : (a + b) * (a + b) = a*a + 2*a*b + b*b :=
  calc (a + b)*(a + b) = a*a + (1+1)*a*b + b*b : by simp [right_distrib, left_distrib]
               ...     = a*a + 2*a*b + b*b     : by rw one_add_one_eq_two

  lemma dvd_neg_of_dvd {a b : α} (h : a ∣ b) : (a ∣ -b) :=
  dvd.elim h
    (assume c, assume : b = a * c,
      dvd.intro (-c) (by simp [this]))

  lemma dvd_of_dvd_neg {a b : α} (h : a ∣ -b) : (a ∣ b) :=
  let t := dvd_neg_of_dvd h in by rwa neg_neg at t

  @[simp] lemma dvd_neg (a b : α) : (a ∣ -b) ↔ (a ∣ b) :=
  ⟨dvd_of_dvd_neg, dvd_neg_of_dvd⟩

  lemma neg_dvd_of_dvd {a b : α} (h : a ∣ b) : -a ∣ b :=
  dvd.elim h
    (assume c, assume : b = a * c,
      dvd.intro (-c) (by simp [this]))

  lemma dvd_of_neg_dvd {a b : α} (h : -a ∣ b) : a ∣ b :=
  let t := neg_dvd_of_dvd h in by rwa neg_neg at t

  @[simp] lemma neg_dvd (a b : α) : (-a ∣ b) ↔ (a ∣ b) :=
  ⟨dvd_of_neg_dvd, neg_dvd_of_dvd⟩

  lemma dvd_sub {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c :=
  dvd_add h₁ (dvd_neg_of_dvd h₂)

  lemma dvd_add_iff_left {a b c : α} (h : a ∣ c) : a ∣ b ↔ a ∣ b + c :=
  ⟨λh₂, dvd_add h₂ h, λH, by have t := dvd_sub H h; rwa add_sub_cancel at t⟩

  lemma dvd_add_iff_right {a b c : α} (h : a ∣ b) : a ∣ c ↔ a ∣ b + c :=
  by rw add_comm; exact dvd_add_iff_left h
end comm_ring

class no_zero_divisors (α : Type u) extends has_mul α, has_zero α :=
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀ a b : α, a * b = 0 → a = 0 ∨ b = 0)

lemma eq_zero_or_eq_zero_of_mul_eq_zero [no_zero_divisors α] {a b : α} (h : a * b = 0) : a = 0 ∨ b = 0 :=
no_zero_divisors.eq_zero_or_eq_zero_of_mul_eq_zero a b h

lemma eq_zero_of_mul_self_eq_zero [no_zero_divisors α] {a : α} (h : a * a = 0) : a = 0 :=
(eq_zero_or_eq_zero_of_mul_eq_zero h).elim id id

class domain (α : Type u) extends ring α, no_zero_divisors α, zero_ne_one_class α

section domain
  variable [domain α]

  lemma mul_eq_zero {a b : α} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  ⟨eq_zero_or_eq_zero_of_mul_eq_zero, λo,
    or.elim o (λh, by rw h; apply zero_mul) (λh, by rw h; apply mul_zero)⟩

  lemma mul_ne_zero {a b : α} (h₁ : a ≠ 0) (h₂ : b ≠ 0) : a * b ≠ 0 :=
  λ h, or.elim (eq_zero_or_eq_zero_of_mul_eq_zero h) h₁ h₂

  lemma domain.mul_right_inj {a b c : α} (ha : a ≠ 0) : b * a = c * a ↔ b = c :=
  by rw [← sub_eq_zero, ← mul_sub_right_distrib, mul_eq_zero];
     simp [ha]; exact sub_eq_zero

  lemma domain.mul_left_inj {a b c : α} (ha : a ≠ 0) : a * b = a * c ↔ b = c :=
  by rw [← sub_eq_zero, ← mul_sub_left_distrib, mul_eq_zero];
     simp [ha]; exact sub_eq_zero

  lemma eq_of_mul_eq_mul_of_nonzero_left {a b c : α} (h : a ≠ 0) : a * b = a * c → b = c :=
  (domain.mul_left_inj h).1

  lemma eq_of_mul_eq_mul_of_nonzero_right {a b c : α} (h : c ≠ 0) : a * c = b * c → a = b :=
  (domain.mul_right_inj h).1

  lemma eq_zero_of_mul_eq_self_right {a b : α} (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
  by apply (mul_eq_zero.1 _).resolve_right (sub_ne_zero.2 h₁);
     rw [mul_sub_left_distrib, mul_one, sub_eq_zero, h₂]

  lemma eq_zero_of_mul_eq_self_left {a b : α} (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
  by apply (mul_eq_zero.1 _).resolve_left (sub_ne_zero.2 h₁);
     rw [mul_sub_right_distrib, one_mul, sub_eq_zero, h₂]

  lemma mul_ne_zero_comm {a b : α} (h : a * b ≠ 0) : b * a ≠ 0 :=
  mul_ne_zero (ne_zero_of_mul_ne_zero_left h) (ne_zero_of_mul_ne_zero_right h)

end domain

class integral_domain (α : Type u) extends domain α, comm_semigroup α

instance integral_domain.to_comm_ring [s : integral_domain α] : comm_ring α :=
{ s with mul_comm := mul_comm }

section integral_domain
  variable [integral_domain α]

  lemma mul_self_eq_mul_self (a b : α) : a * a = b * b ↔ a = b ∨ a = -b :=
  by rw [← sub_eq_zero, mul_self_sub_mul_self_eq, mul_eq_zero];
     exact or.comm.trans (or_congr sub_eq_zero add_eq_zero_iff_eq_neg)

  lemma mul_self_eq_one (a : α) : a * a = 1 ↔ a = 1 ∨ a = -1 :=
  by have := mul_self_eq_mul_self a 1; rwa mul_one at this

end integral_domain

/- TODO(Leo): remove the following annotations as soon as we have support for arithmetic
   in the SMT tactic framework -/
attribute [ematch] add_zero zero_add mul_one one_mul mul_zero zero_mul
