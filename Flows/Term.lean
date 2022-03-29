/-
Copyright (c) 2021-2022 Julien Marquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Marquet
-/

import Lean

import Flows.Groundwork

open Classical

set_option codegen false

universe u

inductive Term (α : Type u) (β : Type u)
  | Cst (c : α)
  | Var (x : β)
  | Cons (t₁ : Term α β) (t₂ : Term α β)

section

variable {α : Type u} {β : Type u}

def map_reduce (θ : β → Term α β) (u : Term α β) : Term α β := match u with
  | Term.Cst c => Term.Cst c
  | Term.Var x => θ x
  | Term.Cons t₁ t₂ => Term.Cons (map_reduce θ t₁) (map_reduce θ t₂)

def comp (f g : β → Term α β) (x : β) : Term α β :=
  map_reduce g (f x)

theorem map_one (u : Term α β) : map_reduce Term.Var u = u :=
  by induction u with
  | Cst c => rfl
  | Var x => rfl
  | Cons t₁ t₂ ht₁ ht₂ => simp [map_reduce, ht₁, ht₂]

theorem map_comp (u : Term α β) (f g : β → Term α β) :
  map_reduce g (map_reduce f u) = map_reduce (comp f g) u := by induction u with
  | Cst c => rfl
  | Var x => rfl
  | Cons t₁ t₂ ht₁ ht₂ => simp [map_reduce, ht₁, ht₂]

instance fun_monoid : Monoid (β → Term α β) where
  one := Term.Var
  mul := comp
  one_mul := by intros; rfl
  mul_one := by intros; funext x; apply map_one
  mul_assoc := by intros; funext x; apply map_comp

instance term_action : RAction (Term α β) (β → Term α β) where
  smul x θ := map_reduce θ x
  smul_one := map_one
  smul_mul := map_comp

end

section

variable {α β : Type u}

def mass : (u : Term α β) → Nat
| Term.Cst _ => 0
| Term.Var _ => 0
| Term.Cons l r => mass l + mass r + 1

theorem mass_decr_l (l r : Term β α) : mass l < mass (Term.Cons l r) :=
  Nat.lt_succ_of_le <| Nat.le_add_right _ _

theorem mass_decr_r (l r : Term β α) : mass r < mass (Term.Cons l r) :=
  Nat.lt_succ_of_le <| Nat.le_add_left _ _

def Term.mass_wfRel : WellFoundedRelation (Term α β) := measure mass

def weight (x : β) : (u : Term α β) → Nat
| Term.Cst _ => 0
| Term.Var y => if x = y then 1 else 0
| Term.Cons l r => weight x l + weight x r

end
