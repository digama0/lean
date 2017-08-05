/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.bool.basic init.meta

attribute [simp] cond bor band bnot bxor

instance forall_decidable {P : bool → Prop} [decidable_pred P] : decidable (∀b, P b) :=
suffices P ff ∧ P tt ↔ _, from decidable_of_decidable_of_iff (by apply_instance) this,
⟨λ⟨pf, pt⟩ b, bool.rec_on b pf pt, λal, ⟨al _, al _⟩⟩

@[simp] theorem coe_sort_eq_coe (b : bool) : coe_sort.{1 1} b = ↑b := rfl

@[simp] theorem eq_tt_iff_coe {b : bool} : b = tt ↔ ↑b := iff.rfl

@[simp] theorem eq_ff_iff_not : ∀ {b : bool}, b = ff ↔ ¬ ↑b := dec_trivial

@[simp] theorem band_self : ∀ (b : bool), b && b = b := dec_trivial

@[simp] theorem band_tt : ∀ (b : bool), b && tt = b := dec_trivial

@[simp] theorem band_ff : ∀ (b : bool), b && ff = ff := dec_trivial

@[simp] theorem tt_band : ∀ (b : bool), tt && b = b := dec_trivial

@[simp] theorem ff_band : ∀ (b : bool), ff && b = ff := dec_trivial

@[simp] theorem bor_self : ∀ (b : bool), b || b = b := dec_trivial

@[simp] theorem bor_tt : ∀ (b : bool), b || tt = tt := dec_trivial

@[simp] theorem bor_ff : ∀ (b : bool), b || ff = b := dec_trivial

@[simp] theorem tt_bor : ∀ (b : bool), tt || b = tt := dec_trivial

@[simp] theorem ff_bor : ∀ (b : bool), ff || b = b := dec_trivial

@[simp] theorem bxor_self : ∀ (b : bool), bxor b b = ff := dec_trivial

@[simp] theorem bxor_tt : ∀ (b : bool), bxor b tt = bnot b := dec_trivial

@[simp] theorem bxor_ff : ∀ (b : bool), bxor b ff = b := dec_trivial

@[simp] theorem tt_bxor : ∀ (b : bool), bxor tt b = bnot b := dec_trivial

@[simp] theorem ff_bxor : ∀ (b : bool), bxor ff b = b := dec_trivial

@[simp] theorem bnot_bnot : ∀ (b : bool), bnot (bnot b) = b := dec_trivial

@[simp] theorem tt_ne_ff : tt ≠ ff := dec_trivial

@[simp] theorem coe_ff : ¬ ↑ff := dec_trivial

@[simp] theorem coe_tt : (↑tt : Prop) := dec_trivial

@[simp] theorem coe_to_bool {p : Prop} [d : decidable p] : to_bool p ↔ p :=
match d with
| is_true hp := ⟨λh, hp, λ_, rfl⟩
| is_false hnp := ⟨λh, bool.no_confusion h, λhp, absurd hp hnp⟩
end

@[simp] theorem to_bool_coe : ∀ (b : bool), to_bool b = b := dec_trivial

@[simp] theorem to_bool_tt {p : Prop} [decidable p] : p → to_bool p = tt := coe_to_bool.2

@[simp] theorem to_bool_ff {p : Prop} [decidable p] : to_bool p = ff ↔ ¬p := by simp

@[simp] theorem to_bool_ff_of_not {p : Prop} [decidable p] : ¬p → to_bool p = ff := to_bool_ff.2

theorem to_bool_congr {p q : Prop} [decidable p] [decidable q] (h : p ↔ q) : to_bool p = to_bool q :=
by congr; exact propext h

@[simp] theorem coe_bor : ∀ (a b : bool), a || b ↔ a ∨ b := dec_trivial

@[simp] theorem coe_band : ∀ (a b : bool), a && b ↔ a ∧ b := dec_trivial

@[simp] theorem coe_bxor : ∀ (a b : bool), bxor a b ↔ xor a b := dec_trivial

@[simp] theorem {u} ite_eq_cond {α : Sort u} (b : bool) (t f : α) : cond b t f = ite b t f :=
by cases b; simp
