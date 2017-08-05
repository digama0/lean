/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.classical init.meta.name
/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
set_option default_priority 100

set_option old_structure_cmd true

universe u
variables {α : Type u}

set_option auto_param.check_exists false
class preorder (α : Type u) extends has_le α, has_lt α :=
(le_refl : ∀ a : α, a ≤ a)
(le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
(lt := λ a b, a ≤ b ∧ ¬ b ≤ a)
(lt_iff_le_not_le : ∀ a b : α, a < b ↔ (a ≤ b ∧ ¬ b ≤ a) . order_laws_tac)

class partial_order (α : Type u) extends preorder α :=
(le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b)

class linear_order (α : Type u) extends partial_order α :=
(le_total : ∀ a b : α, a ≤ b ∨ b ≤ a)

@[refl] lemma le_refl [preorder α] : ∀ a : α, a ≤ a :=
preorder.le_refl

@[trans] lemma le_trans [preorder α] : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c :=
preorder.le_trans

lemma lt_iff_le_not_le [preorder α] : ∀ {a b : α}, a < b ↔ (a ≤ b ∧ ¬ b ≤ a) :=
preorder.lt_iff_le_not_le _

lemma lt_of_le_not_le [preorder α] {a b : α} (hab : a ≤ b) (hba : ¬ b ≤ a) : a < b :=
lt_iff_le_not_le.2 ⟨hab, hba⟩

lemma le_not_le_of_lt [preorder α] {a b : α} : a < b → a ≤ b ∧ ¬ b ≤ a :=
lt_iff_le_not_le.1

lemma le_antisymm [partial_order α] : ∀ {a b : α}, a ≤ b → b ≤ a → a = b :=
partial_order.le_antisymm

lemma le_of_eq [preorder α] {a b : α} (h : a = b) : a ≤ b :=
h ▸ le_refl a
 
lemma le_antisymm_iff [partial_order α] {a b : α} : a = b ↔ a ≤ b ∧ b ≤ a :=
⟨λe, ⟨le_of_eq e, le_of_eq e.symm⟩, λ⟨h1, h2⟩, le_antisymm h1 h2⟩

@[trans] lemma ge_trans [preorder α] {a b c : α} (h₁ : a ≥ b) (h₂ : b ≥ c) : a ≥ c :=
le_trans h₂ h₁

lemma le_total [linear_order α] : ∀ a b : α, a ≤ b ∨ b ≤ a :=
linear_order.le_total

lemma le_of_not_le [linear_order α] {a b : α} : ¬ a ≤ b → b ≤ a :=
or.resolve_left (le_total a b)

lemma le_of_not_ge [linear_order α] {a b : α} : ¬ a ≥ b → a ≤ b :=
le_of_not_le

lemma lt_irrefl [preorder α] (a : α) : ¬ a < a
| haa := match le_not_le_of_lt haa with
  | ⟨h1, h2⟩ := false.rec _ (h2 h1)
  end

lemma gt_irrefl [preorder α] : ∀ a : α, ¬ a > a :=
lt_irrefl

@[trans] lemma lt_trans [preorder α] {a b c : α} (hab : a < b) (hbc : b < c) : a < c :=
match le_not_le_of_lt hab, le_not_le_of_lt hbc with
| ⟨hab, hba⟩, ⟨hbc, hcb⟩ := lt_of_le_not_le (le_trans hab hbc) (λ hca, hcb (le_trans hca hab))
end

def lt.trans := @lt_trans

@[trans] lemma gt_trans [preorder α] {a b c : α} (h₁ : a > b) (h₂ : b > c) : a > c :=
lt_trans h₂ h₁

def gt.trans := @gt_trans

lemma ne_of_lt [preorder α] {a b : α} (h : a < b) : a ≠ b
| he := absurd h (he ▸ lt_irrefl a)

lemma ne_of_gt [preorder α] {a b : α} (h : a > b) : a ≠ b :=
(ne_of_lt h).symm

lemma lt_asymm [preorder α] {a b : α} (h : a < b) : ¬ b < a :=
mt (lt_trans h) (lt_irrefl a)

lemma not_lt_of_lt [linear_order α] {a b : α} (h : a < b) : ¬ b < a :=
lt_asymm h

lemma not_lt_of_gt [linear_order α] {a b : α} (h : a > b) : ¬ a < b :=
lt_asymm h

lemma le_of_lt [preorder α] {a b : α} (h : a < b) : a ≤ b :=
(le_not_le_of_lt h).left

@[trans] lemma lt_of_lt_of_le [preorder α] {a b c : α} (hab : a < b) (hbc : b ≤ c) : a < c :=
let ⟨hab, hba⟩ := le_not_le_of_lt hab in
lt_of_le_not_le (le_trans hab hbc) $ λ hca, hba (le_trans hbc hca)

@[trans] lemma lt_of_le_of_lt [preorder α] {a b c : α} (hab : a ≤ b) (hbc : b < c) : a < c :=
let ⟨hbc, hcb⟩ := le_not_le_of_lt hbc in
lt_of_le_not_le (le_trans hab hbc) $ λ hca, hcb (le_trans hca hab)

@[trans] lemma gt_of_gt_of_ge [preorder α] {a b c : α} (h₁ : a > b) (h₂ : b ≥ c) : a > c :=
lt_of_le_of_lt h₂ h₁

@[trans] lemma gt_of_ge_of_gt [preorder α] {a b c : α} (h₁ : a ≥ b) (h₂ : b > c) : a > c :=
lt_of_lt_of_le h₂ h₁

lemma not_le_of_lt [preorder α] {a b : α} (h : a < b) : ¬ b ≤ a :=
(le_not_le_of_lt h).right

lemma not_le_of_gt [preorder α] {a b : α} : a > b → ¬ a ≤ b :=
not_le_of_lt

lemma not_lt_of_le [preorder α] {a b : α} (h : a ≤ b) : ¬ b < a
| hab := not_le_of_gt hab h

lemma not_lt_of_ge [preorder α] {a b : α} : a ≥ b → ¬ a < b :=
not_lt_of_le

lemma lt_of_le_of_ne [partial_order α] {a b : α} (h₁ : a ≤ b) (h₂ : a ≠ b) : a < b :=
lt_of_le_not_le h₁ $ mt (le_antisymm h₁) h₂

lemma lt_or_eq_of_le [partial_order α] {a b : α}
  (hab : a ≤ b) : a < b ∨ a = b :=
classical.by_cases or.inr (λ e, or.inl (lt_of_le_of_ne hab e))

lemma le_of_lt_or_eq [preorder α] {a b : α} (h : a < b ∨ a = b) : a ≤ b :=
h.elim le_of_lt le_of_eq

lemma le_of_eq_or_lt [preorder α] {a b : α} (h : a = b ∨ a < b) : a ≤ b :=
h.elim le_of_eq le_of_lt

lemma le_iff_lt_or_eq [partial_order α] {a b : α} : a ≤ b ↔ a < b ∨ a = b :=
⟨lt_or_eq_of_le, le_of_lt_or_eq⟩

lemma le_iff_eq_or_lt [partial_order α] {a b : α} : a ≤ b ↔ a = b ∨ a < b :=
le_iff_lt_or_eq.trans or.comm

lemma lt_or_gt_of_ne [linear_order α] {a b : α} (e : a ≠ b) : a < b ∨ a > b :=
(le_total a b).elim
  (λ h : a ≤ b, or.inl $ lt_of_le_of_ne h e)
  (λ h : b ≤ a, or.inr $ lt_of_le_of_ne h $ ne.symm e)

lemma ne_iff_lt_or_gt [linear_order α] {a b : α} : a ≠ b ↔ a < b ∨ a > b :=
⟨lt_or_gt_of_ne, λo, o.elim ne_of_lt ne_of_gt⟩

lemma lt_trichotomy [linear_order α] (a b : α) :
  a < b ∨ a = b ∨ b < a :=
classical.by_cases
  (λ e, (or.inl e).inr)
  (λ e, (lt_or_gt_of_ne e).imp_right or.inr)

lemma lt_or_ge [linear_order α] (a b : α) : a < b ∨ a ≥ b :=
(or_rotate.2 $ lt_trichotomy b a).imp_right le_iff_lt_or_eq.2

lemma le_or_gt [linear_order α] (a b : α) : a ≤ b ∨ a > b :=
(lt_or_ge b a).swap

@[simp] lemma not_lt [linear_order α] {a b : α} : ¬ a < b ↔ b ≤ a :=
⟨(lt_or_ge a b).resolve_left, not_lt_of_le⟩

lemma le_of_not_lt [linear_order α] {a b : α} : ¬ a < b → b ≤ a :=
not_lt.1

lemma le_of_not_gt [linear_order α] {a b : α} : ¬ a > b → a ≤ b :=
not_lt.1

@[simp] lemma not_le [linear_order α] {a b : α} : ¬ a ≤ b ↔ b < a :=
(lt_iff_le_not_le.trans ⟨and.right,
  λ h, ⟨(le_total _ _).resolve_left h, h⟩⟩).symm

lemma lt_of_not_ge [linear_order α] {a b : α} : ¬ a ≥ b → a < b :=
not_le.1

lemma lt_iff_not_ge [linear_order α] {a b : α} : a < b ↔ ¬ a ≥ b :=
not_le.symm

lemma not_lt_iff_eq_or_lt [linear_order α] {a b : α} : ¬ a < b ↔ a = b ∨ b < a :=
not_lt.trans $ le_iff_eq_or_lt.trans $ or_congr eq_comm iff.rfl

lemma eq_or_lt_of_not_lt [linear_order α] {a b : α} : ¬ a < b → a = b ∨ b < a :=
not_lt_iff_eq_or_lt.1

lemma le_imp_le_iff_lt_imp_lt [linear_order α] {a b c d : α} :
  (a ≤ b → c ≤ d) ↔ (d < c → b < a) :=
⟨λ H h, lt_of_not_ge $ λ h', not_lt_of_ge (H h') h,
λ H h, le_of_not_gt $ λ h', not_le_of_gt (H h') h⟩

lemma le_iff_le_iff_lt_iff_lt [linear_order α] {a b c d : α} :
  (a ≤ b ↔ c ≤ d) ↔ (b < a ↔ d < c) :=
⟨λ H, not_le.symm.trans $ iff.trans (not_congr H) $ not_le,
λ H, not_lt.symm.trans $ iff.trans (not_congr H) $ not_lt⟩

instance decidable_lt_of_decidable_le [preorder α]
  [d : @decidable_rel α (≤)] : @decidable_rel α (<)
| a b := decidable_of_decidable_of_iff and.decidable lt_iff_le_not_le.symm

instance decidable_eq_of_decidable_le [partial_order α]
  [@decidable_rel α (≤)] : decidable_eq α
| a b := decidable_of_decidable_of_iff and.decidable le_antisymm_iff.symm

class decidable_linear_order (α : Type u) extends linear_order α :=
(decidable_le : decidable_rel (≤))
(decidable_eq : decidable_eq α := @decidable_eq_of_decidable_le _ _ decidable_le)
(decidable_lt : @decidable_rel α (<) :=
    @decidable_lt_of_decidable_le _ _ decidable_le)

instance decidable_linear_order.lt_decidable [decidable_linear_order α]
  (a b : α) : decidable (a < b) :=
decidable_linear_order.decidable_lt α a b

instance decidable_linear_order.le_decidable [decidable_linear_order α]
  (a b : α) : decidable (a ≤ b) :=
decidable_linear_order.decidable_le α a b

instance decidable_linear_order.eq_decidable [decidable_linear_order α]
  (a b : α) : decidable (a = b) :=
decidable_linear_order.decidable_eq α a b
