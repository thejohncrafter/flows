/-
Copyright (c) 2021-2022 Julien Marquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Marquet
-/

import Lean

import Flows.Groundwork
import Flows.SolveSets
import Flows.Term
import Flows.Subst
import Flows.Vehicle
import Flows.Vanishing
import Flows.Unifier

open Classical

set_option codegen false

universe u

section

theorem cons_carrier_in {θ φ : Subst α β} {l₁ r₁ l₂ r₂ : Term α β}
  (h₁ : (𝒱 θ : Fintype β) ⊆ 𝒱 l₁ ∪ 𝒱 l₂)
  (h₂ : (𝒱 φ : Fintype β) ⊆ 𝒱 (r₁ • θ) ∪ 𝒱 (r₂ • θ))
  (h₃ : vanishing θ) (h₄ : vanishing φ)
  (h₅ : carrier θ ⊆ 𝒱 l₁ ∪ 𝒱 l₂) (h₆ : carrier φ ⊆ 𝒱 (r₁ • θ) ∪ 𝒱 (r₂ • θ)) :
  carrier (θ * φ) ⊆ 𝒱 (Term.Cons l₁ r₁) ∪ 𝒱 (Term.Cons l₂ r₂) := by
  apply Fintype.included_trans (carrier_cons _ _)
  simp only [vehicle_cons]
  rw [Fintype.union_assoc]
  apply Fintype.union_included_iff.2 (And.intro _ _)
  focus
    apply Fintype.included_trans h₅
    solve_sets
  focus
    apply Fintype.included_trans h₆
    apply Fintype.union_included_iff.2 ⟨ _, _ ⟩
      <;> apply Fintype.included_trans (vehicle_on_image h₁ _)
      <;> solve_sets

end

section

theorem lex_of_le_and_lt {α β : Type u}
  {ha : WellFoundedRelation α} {hb : WellFoundedRelation β}
  {a₁ a₂ : α} {b₁ b₂ : β} (h₁ : ha.rel a₁ a₂ ∨ a₁ = a₂) (h₂ : hb.rel b₁ b₂) :
  (Prod.lex ha hb).rel (a₁, b₁) (a₂, b₂) := by
  cases h₁ with
  | inl h₁ =>
    apply Prod.Lex.left
    exact h₁
  | inr h₁ =>
    rw [h₁]
    apply Prod.Lex.right
    exact h₂

end

section

variable {α β : Type u}

private theorem flush_add_left (a : Nat) {b c : Nat} : b + c + a = b + a + c := by
  simp only [Nat.add_assoc]
  rw [Nat.add_comm a c]

theorem mass_lower_bound {x : β} {v : Term α β} (h : Term.Var x ≠ v) (u : Term α β)
  (θ : Subst α β) : mass u + weight x u * mass (v • θ) ≤ mass (u • (Subst.elementary h * θ)) := by
  induction u with
  | Cst c => match θ with
    | ⟨ θ, _ ⟩ =>
      suffices p : ∀ n, 0 + 0 * n ≤ 0 from p (mass (map_reduce θ v))
      intros; simp
  | Var y => match θ with
    | ⟨ θ, _ ⟩ =>
      by_cases p : x = y
        <;> simp [mass, weight, RSMul.smul, map_reduce, Subst.elementary, HMul.hMul, Mul.mul, comp, p]
      rw [Nat.one_mul]
      exact Nat.le.refl
      simp [Ne.symm p, map_reduce, Nat.zero_le]
  | Cons l r hl hr =>
    simp only [mass, weight, subst_cons]
    simp only [Nat.left_distrib, Nat.right_distrib, ← Nat.add_assoc]
    simp only [flush_add_left ((weight x r) * mass (v • θ))]
    simp only [flush_add_left (mass r)]
    simp only [flush_add_left ((weight x l) * mass (v • θ))]
    simp only [flush_add_left (mass l)]
    apply Nat.succ_le_succ
    rw [Nat.add_assoc]
    exact Nat.le_of_le_of_le hl hr

theorem weight_nonzero_of_mem_vehicle {x : β} {u : Term α β} (h : x ∈ (𝒱 u : Fintype β)) :
  weight x u ≠ 0 := by
  induction u with
  | Cst _ => exact False.elim <| Fintype.not_mem_empty _ h
  | Var y =>
    suffices p : x = y by
      rw [p]
      simp [weight]
    cases h <;> trivial
  | Cons l r hl hr =>
    simp only [weight]
    rw [vehicle_cons, Fintype.mem_union_iff] at h
    cases h with
    | inl h => exact Nat.add_ne_zero_of_l_ne_zero <| hl h
    | inr h => exact Nat.add_ne_zero_of_r_ne_zero <| hr h

end

section

variable {α β : Type u} [Monoid α]

theorem smul_cons_eq {l r : Term α β} {θ : Subst α β} :
  (Term.Cons l r) • θ = (Term.Cons (l • θ) (r • θ)) :=
  match θ with
  | ⟨ θ, hθ ⟩ => rfl

private theorem cons_mgu {l₁ r₁ l₂ r₂ : Term α β} {θ φ : Subst α β}
  (θ_mgu : is_mgu _ l₁ l₂ θ) (φ_mgu : is_mgu _ (r₁ • θ) (r₂ • θ) φ) :
  is_mgu _ (Term.Cons l₁ r₁) (Term.Cons l₂ r₂) (θ * φ) := by
  apply mgu_of_unifies_and_most_general
  focus
    simp [smul_cons_eq, ← RAction.smul_mul,
      unifies_of_mgu θ_mgu, unifies_of_mgu φ_mgu]
  focus
    intro
    simp [smul_cons_eq]
    intro ⟨ h₁, h₂ ⟩
    let ⟨ ρ₁, hρ₁ ⟩ := most_general_of_mgu θ_mgu h₁
    rw [← hρ₁, ← RAction.smul_mul, ← RAction.smul_mul] at h₂
    let ⟨ ρ₂, hρ₂ ⟩ := most_general_of_mgu φ_mgu h₂
    exact ⟨ ρ₂, (Monoid.mul_assoc _ _ _ ▸ hρ₂ ▸ hρ₁ ▸ rfl) ⟩

private def rel : WellFoundedRelation (Term α β × Term α β) :=
  invImage (λ (u, v) => ((𝒱 u ∪ 𝒱 v : Fintype β), (u, v)))
  <| Prod.lex
    (Fintype.included_wfRel)
    (Prod.rprod Term.mass_wfRel Term.mass_wfRel)

@[inline]
private def P (x : Term α β × Term α β) := match x with
  | (u, v) => strangers (Subst α β) u v
    ⊕' { θ : Subst α β // is_mgu _ u v θ
      ∧ (𝒱 θ : Fintype β) ⊆ 𝒱 u ∪ 𝒱 v
      ∧ vanishing θ
      ∧ carrier θ ⊆ 𝒱 u ∪ 𝒱 v }

private theorem P_comm (u v : Term α β) : P (u, v) → P (v, u) := by
  revert u v
  intro u v h
  match h with
  | PSum.inl h =>
    apply PSum.inl
    simp_all only [strangers_iff_no_unifier]
    intro θ h'
    exact h θ h'.symm
  | PSum.inr ⟨ θ, θ_mgu, θ_vehicle, θ_vanishing, θ_carrier ⟩ =>
    apply PSum.inr (Subtype.mk θ _)
    apply And.intro _ (And.intro _ (And.intro _ _))
    focus
      simp only [is_mgu]
      suffices p : unifiers (Subst α β) v u = unifiers (Subst α β) u v by
        rw [p]
        exact θ_mgu
      funext φ
      simp [unifiers]
      apply propext
      apply Iff.intro
      intro h; rw [h]
      intro h; rw [h]
    focus
      rw [Fintype.union_comm]
      exact θ_vehicle
    focus
      exact θ_vanishing
    focus
      rw [Fintype.union_comm]
      exact θ_carrier

private theorem decr_left (l₁ r₁ l₂ r₂ : Term α β) :
  rel.rel (l₁, l₂) (Term.Cons l₁ r₁, Term.Cons l₂ r₂) := by
  simp [rel, invImage, InvImage]
  apply lex_of_le_and_lt
  focus
    simp [invImage, InvImage, Fintype.included_wfRel]
    simp only [WellFoundedRelation.rel]
    simp only [vehicle_cons]
    suffices h : (𝒱 l₁ ∪ 𝒱 l₂ : Fintype β)
      ⊆ 𝒱 (Term.Cons l₁ r₁) ∪ 𝒱 (Term.Cons l₂ r₂) by
      by_cases p : (𝒱 l₁ ∪ 𝒱 l₂ : Fintype β)
        = 𝒱 (Term.Cons l₁ r₁) ∪ 𝒱 (Term.Cons l₂ r₂)
      exact Or.inr p
      exact Or.inl ⟨ h, p ⟩
    simp only [vehicle_cons]
    solve_sets
  focus
    exact Prod.RProd.intro (mass_decr_l _ _) (mass_decr_l _ _)

private theorem decr_right (l₁ r₁ l₂ r₂ : Term α β) {θ : Subst α β}
  (θ_vehicle : (𝒱 θ : Fintype β) ⊆ 𝒱 l₁ ∪ 𝒱 l₂)
  (θ_vanishing : vanishing θ) (θ_carrier : carrier θ ⊆ 𝒱 l₁ ∪ 𝒱 l₂) :
  rel.rel (r₁ • θ, r₂ • θ) (Term.Cons l₁ r₁, Term.Cons l₂ r₂) := by
  by_cases h : θ = 1
  focus
    rw [h, RAction.smul_one, RAction.smul_one]
    apply lex_of_le_and_lt
    focus
      simp [invImage, InvImage, Fintype.included_wfRel]
      suffices h : (𝒱 r₁ ∪ 𝒱 r₂ : Fintype β)
        ⊆ 𝒱 (Term.Cons l₁ r₁) ∪ 𝒱 (Term.Cons l₂ r₂) by
        by_cases p : (𝒱 r₁ ∪ 𝒱 r₂ : Fintype β)
          = 𝒱 (Term.Cons l₁ r₁) ∪ 𝒱 (Term.Cons l₂ r₂)
        exact Or.inr p
        exact Or.inl ⟨ h, p ⟩
      simp only [vehicle_cons]
      solve_sets
    focus
      exact Prod.RProd.intro (mass_decr_r _ _) (mass_decr_r _ _)
  focus
    apply Prod.Lex.left
    apply And.intro
    focus
      simp only [vehicle_cons]
      apply Fintype.union_included_iff.2 <| And.intro _ _
      focus
        apply Fintype.included_trans (vehicle_on_image Fintype.included_refl r₁)
        apply Fintype.union_included_iff.2
          <| And.intro (Fintype.included_trans θ_vehicle _) _
          <;> solve_sets
      focus
        apply Fintype.included_trans (vehicle_on_image Fintype.included_refl r₂)
        apply Fintype.union_included_iff.2 <| And.intro (Fintype.included_trans θ_vehicle _) _
          <;> solve_sets
    focus
      let ⟨ x, hx ⟩ := (not_one_iff_modifying θ).1 h
      let not_in_r₁ := vanishing_on_term θ_vanishing hx r₁
      let not_in_r₂ := vanishing_on_term θ_vanishing hx r₂
      let not_in_lhs : ¬ x ∈ (𝒱 (r₁ • θ) ∪ 𝒱 (r₂ • θ) : Fintype β) :=
        λ h => match (Fintype.mem_union_iff _ _ _).1 h with
          | Or.inl h => not_in_r₁ h
          | Or.inr h => not_in_r₂ h
      let in_rhs : x ∈ (𝒱 (Term.Cons l₁ r₁) ∪ 𝒱 (Term.Cons l₂ r₂) : Fintype β) := by
        simp only [vehicle_cons]
        have p := carrier_spec.2 hx
        rw [Fintype.mem_iff_singleton_included]
        rw [Fintype.mem_iff_singleton_included] at p
        apply Fintype.included_trans p
        apply Fintype.included_trans θ_carrier
        solve_sets
      exact Fintype.different_if_not_same_element not_in_lhs in_rhs

private theorem prepend_elementary_on_variable_unifier {x : β} {u : Term α β} {θ : Subst α β}
  (h : Term.Var x ≠ u) (h' : (Term.Var x : Term α β) • θ = u • θ) :
  θ = (Subst.elementary h) * θ := by
  apply Subst.ext.2
  intro y
  rw [← RAction.smul_mul]
  by_cases p : y = x
  focus
    rw [p, h', Subst.elementary_spec₁]
  focus
    rw [Subst.elementary_spec₂]
    exact p

private theorem unify_variable_of_not_in_vehicle {x : β} {u : Term α β}
  (h : ¬ x ∈ (𝒱 u : Fintype β)) : P ((Term.Var x), u) := by
  have x_ne_u : Term.Var x ≠ u := by
    intro h'
    rw [← h'] at h
    apply h
    apply List.Mem.head
  apply PSum.inr ∘ Subtype.mk (Subst.elementary x_ne_u)
  apply And.intro (mgu_of_unifies_and_most_general _ _)
    (And.intro _ (And.intro _ _))
  focus
    rw [Subst.elementary_spec₁ x_ne_u]
    rw [elementary_on_not_in_vehicle]
    exact h
  focus
    intro θ hθ
    apply Exists.intro θ
    exact Eq.symm <| prepend_elementary_on_variable_unifier x_ne_u hθ
  focus
    rw [vehicle_elementary]
    apply Fintype.included_union_l _ <| Fintype.included_refl
  focus
    apply elementary_vanishing
    exact h
  focus
    rw [elementary_carrier]
    exact Fintype.included_union_r _ <| Fintype.included_refl

-- Clearly not well written, I sould automate this...
-- But since I don't do a lot of calculus in the proofs here, I don't feel the need
-- to spend time writing tactics for numbers.
private theorem variable_stranger_of_in_vehicle {x : β} {u : Term α β}
  (h₁ : mass u ≠ 0) (h₂ : x ∈ (𝒱 u : Fintype β)) :
  strangers (Subst α β) (Term.Var x) u := by
  have x_ne_u : Term.Var x ≠ u := by
    intro h
    apply h₁
    rw [← h]
    rfl
  rw [strangers_iff_no_unifier]
  intro θ h
  have p := prepend_elementary_on_variable_unifier x_ne_u h
  conv at h => rhs; rw [p]
  have p' := mass_lower_bound x_ne_u u θ
  conv at p' => rhs; rw [← p]
  have p'' := Nat.mul_le_mul_right (mass (u • θ))
    <| Nat.one_le_of_ne_zero
    <| weight_nonzero_of_mem_vehicle h₂
  rw [Nat.one_mul] at p''
  have p₄ := Nat.le_trans p' p''
  have p₅ : mass u = 0 := by
    apply byContradiction
    intro h
    have p := Nat.lt_of_succ_le <| Nat.one_le_of_ne_zero h
    have p' := Nat.add_lt_add_right p (weight x u * mass (u • θ))
    have p''' := Nat.lt_of_lt_of_le p' p₄
    rw [Nat.zero_add] at p'''
    exact False.elim <| Nat.not_lt_self _ p'''
  exact h₁ p₅

private theorem unify_mass_nonzero (x : β) {u : Term α β} (h : mass u ≠ 0) :
  P ((Term.Var x), u) :=
  if p : x ∈ (𝒱 u : Fintype β) then by
    exact PSum.inl <| variable_stranger_of_in_vehicle h p
  else by
    exact unify_variable_of_not_in_vehicle p

private theorem unify_cst (x : β) (c : α) : P (Term.Var x, Term.Cst c) := by
  have p' : (Term.Var x : Term α β) ≠ Term.Cst c := by
    intro h
    apply Term.noConfusion h
  apply unify_variable_of_not_in_vehicle
  intro h; cases h <;> trivial

private theorem unify_cons (c : α) (l r : Term α β) : P (Term.Cst c, Term.Cons l r) := by
  apply PSum.inl
  apply strangers_iff_no_unifier.2
  intro ⟨ θ, _ ⟩ h
  apply Term.noConfusion h

private def robinsonR (x : Term α β × Term α β)
  (rh : ∀ y, rel.rel y x → P y) : P x := match x with
  | (Term.Cons l₁ r₁, Term.Cons l₂ r₂) =>
    match rh (l₁, l₂) (decr_left _ _ _ _) with
    | PSum.inl h => by
      apply PSum.inl
      rw [strangers_iff_no_unifier]
      rw [strangers_iff_no_unifier] at h
      intro θ h'
      apply h θ
      simp only [subst_cons] at h'
      apply Term.noConfusion h'
      exact λ h _ => h
    | PSum.inr ⟨ θ, θ_mgu, θ_vehicle, θ_vanishing, θ_carrier ⟩ =>
      match rh (r₁ • θ, r₂ • θ) (by apply decr_right <;> assumption) with
      | PSum.inl h => by
        apply PSum.inl
        rw [strangers_iff_no_unifier]
        rw [strangers_iff_no_unifier] at h
        intro φ h'
        suffices h' : l₁ • φ = l₂ • φ ∧ r₁ • φ = r₂ • φ by
          let ⟨ ρ, hρ ⟩ := most_general_of_mgu θ_mgu h'.1
          apply h ρ
          simp only [RAction.smul_mul, hρ]
          exact h'.2
        simp only [subst_cons] at h'
        apply And.intro <;> apply Term.noConfusion h'
          <;> intros
          <;> assumption
      | PSum.inr ⟨ φ, φ_mgu, φ_vehicle, φ_vanishing, φ_carrier ⟩ => by
        apply PSum.inr
        apply Subtype.mk (θ * φ)
        apply And.intro _ _
        focus
          exact cons_mgu θ_mgu φ_mgu
        focus
          exact ⟨ cons_vehicle_in θ_vehicle φ_vehicle,
            cons_vanishing θ_vehicle φ_vehicle θ_vanishing φ_vanishing,
            cons_carrier_in θ_vehicle φ_vehicle θ_vanishing φ_vanishing
              θ_carrier φ_carrier ⟩
  | (Term.Var x, Term.Cons l r) => by
    apply unify_mass_nonzero
    apply Ne.symm ∘ Nat.ne_of_lt
      <| Nat.lt_of_lt_of_le (Nat.zero_lt_one) (Nat.le_add_left _ _)
  | (Term.Cons l r, Term.Var x) => by
    apply P_comm
    apply unify_mass_nonzero
    apply Ne.symm ∘ Nat.ne_of_lt
      <| Nat.lt_of_lt_of_le (Nat.zero_lt_one) (Nat.le_add_left _ _)
  | (Term.Var x, Term.Var y) =>
    if p : x = y then by
      apply PSum.inr ∘ Subtype.mk 1
      rw [p]
      apply And.intro _ (And.intro _ (And.intro _ _))
      focus
        funext θ
        apply propext
        suffices p : ∃ ρ, 1 * ρ = θ by
          simp [unifiers, generated_by, p]
        apply Exists.intro θ
        exact Monoid.one_mul _
      focus
        rw [vehicle_one]
        exact Fintype.empty_included _
      focus
        exact λ h => False.elim (h rfl)
      focus
        rw [is_one_iff_empty_carrier.1 rfl]
        apply Fintype.empty_included _
    else by
      have p' : (Term.Var x : Term α β) ≠ Term.Var y :=
        λ h => p <| Term.noConfusion h id
      apply unify_variable_of_not_in_vehicle
      intro h; apply p; cases h <;> trivial
  | (Term.Cst a, Term.Cst b) =>
    if p : a = b then by
      apply PSum.inr ∘ Subtype.mk 1
      rw [p]
      -- Duplicate of the above, may be extracted to a lemma
      apply And.intro _ (And.intro _ (And.intro _ _))
      focus
        funext θ
        apply propext
        suffices p : ∃ ρ, 1 * ρ = θ by
          simp [unifiers, generated_by, p]
        apply Exists.intro θ
        exact Monoid.one_mul _
      focus
        rw [vehicle_one]
        exact Fintype.empty_included _
      focus
        exact λ h => False.elim (h rfl)
      focus
        rw [is_one_iff_empty_carrier.1 rfl]
        apply Fintype.empty_included _
    else by
      apply PSum.inl
      rw [strangers_iff_no_unifier]
      exact λ θ h => p <| match θ with
      | ⟨ _, _ ⟩ => Term.noConfusion h id
  | (Term.Cst c, Term.Cons l r) => by
    apply unify_cons
  | (Term.Cst c, Term.Var x) => by
    apply P_comm
    apply unify_cst
  | (Term.Cons l r, Term.Cst c) => by
    apply P_comm
    apply unify_cons
  | (Term.Var x, Term.Cst c) => by
    apply unify_cst

theorem herbrand (u v : Term α β) :
  strangers (Subst α β) u v ∨ ∃ θ : Subst α β, is_mgu _ u v θ :=
  match rel.wf.recursion (u, v) robinsonR with
  | PSum.inl p => Or.inl p
  | PSum.inr ⟨ θ, p, _ ⟩ => Or.inr ⟨ θ, p ⟩

def robinson (u v : Term α β) : Option (Subst α β) :=
  match WellFounded.fix rel.wf robinsonR (u, v) with
  | PSum.inl p => Option.none
  | PSum.inr ⟨ θ, _ ⟩ => Option.some θ

end
