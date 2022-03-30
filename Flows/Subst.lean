/-
Copyright (c) 2021-2022 Julien Marquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Marquet
-/

import Flows.Term

open Classical

set_option codegen false

def Subst (α : Type u) (β : Type u) := { f : β → Term α β // finite { x : β // f x ≠ Term.Var x } }

private theorem comp_carrier {f g : β → Term α β} {x : β} :
  ((f * g) x ≠ Term.Var x) → f x ≠ Term.Var x ∨ g x ≠ Term.Var x := by
  rw [← Decidable.not_and_iff_or_not]
  apply contrapose
  exact λ ⟨ h₁, h₂ ⟩ => by simp [HMul.hMul, Mul.mul, comp, map_reduce, h₁, h₂]

private def carriers_arrow (f g : β → Term α β) : ({ x : β // (f * g) x ≠ Term.Var x }) →
  { x // f x ≠ Term.Var x } ⊕ { x // g x ≠ Term.Var x } :=
  λ ⟨ x, p ⟩ =>
    if hf : f x ≠ Term.Var x then Sum.inl ⟨ x, hf ⟩
    else if hg : g x ≠ Term.Var x then Sum.inr ⟨ x, hg ⟩
    else False.elim <| match comp_carrier p with
    | Or.inl p => hf p
    | Or.inr p => hg p

private theorem carriers_arrow_inj (f g : β → Term α β) (x y : {x // (f * g) x ≠ Term.Var x})
  (h : carriers_arrow f g x = carriers_arrow f g y) : x = y := by
  revert x y
  intro ⟨ x, hx ⟩ ⟨ y, hy ⟩ h
  apply Subtype.eq
  simp [carriers_arrow] at h
  have x_nontriv : {P : Prop} → ¬ f x ≠ Term.Var x → ¬ g x ≠ Term.Var x → P :=
    λ p q => False.elim <| match comp_carrier hx with | Or.inl r => p r | Or.inr r => q r
  have y_nontriv : {P : Prop} → ¬ f y ≠ Term.Var y → ¬ g y ≠ Term.Var y → P :=
    λ p q => False.elim <| match comp_carrier hy with | Or.inl r => p r | Or.inr r => q r
  by_cases p₁ : f x ≠ Term.Var x <;> by_cases p₂ : g x ≠ Term.Var x
    <;> by_cases p₃ : f y ≠ Term.Var y <;> by_cases p₄ : g y ≠ Term.Var y
    <;> simp [dif_pos p₁, dif_neg p₁, dif_pos p₂, dif_neg p₂,
      dif_pos p₃, dif_neg p₃, dif_pos p₄, dif_neg p₄] at h
    <;> first
      | assumption
      | apply x_nontriv; assumption; assumption
      | apply y_nontriv; assumption; assumption

instance : Monoid (Subst α β) where
  one := ⟨ Term.Var, ⟨ [], λ ⟨ _, p ⟩ => False.elim <| p rfl ⟩ ⟩
  mul := λ ⟨ f, pf ⟩ ⟨ g, pg ⟩ =>
    ⟨ f * g, invimage_finite_of_inj (sum_finite pf pg) (carriers_arrow_inj f g) ⟩
  one_mul := λ ⟨ _, _ ⟩ => rfl
  mul_one := λ ⟨ _, _ ⟩ => Subtype.eq <| fun_monoid.mul_one _
  mul_assoc := λ ⟨ _, _ ⟩ ⟨ _, _ ⟩ ⟨ _, _ ⟩ => Subtype.eq <| fun_monoid.mul_assoc _ _ _

instance subst_self_action : RAction (Subst α β) (Subst α β) := self_action _

instance subst_term_action : RAction (Term α β) (Subst α β) where
  smul := λ x ⟨ f, hf ⟩ => x • f
  smul_one := term_action.smul_one
  smul_mul := λ _ ⟨ _, _ ⟩ ⟨ _, _ ⟩ => term_action.smul_mul _ _ _

def Subst.ext {θ φ : Subst α β} : θ = φ
  ↔ ∀ x, (Term.Var x : Term α β) • θ = (Term.Var x : Term α β) • φ := by
  apply Iff.intro (by intro h _; rw [h])
  intro h
  match θ with
  | ⟨ θ, _ ⟩ => match φ with
    | ⟨ φ, _ ⟩ =>
      apply Subtype.eq
      funext x
      exact h x

def Subst.elementary {x : β} {u : Term α β} (h : Term.Var x ≠ u) : Subst α β :=
  ⟨ λ z => if z = x then u else Term.Var z, by
    apply Exists.intro [⟨ x, by simp [h.symm] ⟩]
    intro ⟨ z, hz ⟩
    rw [List.mem_head_or_mem_tail]
    apply Or.inl
    apply Subtype.eq
    apply byContradiction
    intro h'
    simp [h'] at hz ⟩

theorem Subst.elementary_spec₁ {x : β} {u : Term α β} (h : Term.Var x ≠ u) :
  (Term.Var x : Term α β) • (elementary h : Subst α β) = u := by
  simp [RSMul.smul, elementary, map_reduce]

theorem Subst.elementary_spec₂ {x z : β} {u : Term α β} (h : Term.Var x ≠ u) (h' : z ≠ x) :
  (Term.Var z : Term α β) • (elementary h : Subst α β) = Term.Var z := by
  simp [RSMul.smul, elementary, map_reduce, h']

def carrier (θ : Subst α β) : Fintype β :=
  match θ with
  | ⟨ θ, h ⟩ =>
    let π : {x // θ x ≠ Term.Var x} → β := λ ⟨ x, _ ⟩ => x
    Fintype.mk <| List.map π (epsilon <| λ l => ∀ a, a ∈ l)

def carrier_spec {θ : Subst α β} {y : β} :
  y ∈ carrier θ ↔ (Term.Var y : Term α β) • θ ≠ Term.Var y :=
  match θ with
  | ⟨ θ, hθ ⟩ => by
    apply Iff.intro
    focus
      intro h
      let ⟨ ⟨ x, hx ⟩, ⟨ _, h₂ ⟩ ⟩ := List.mem_map_iff_image.1 h
      exact h₂ ▸ hx
    focus
      let π : {x // θ x ≠ Term.Var x} → β := λ ⟨ x, _ ⟩ => x
      intro h'
      rw [show y = π ⟨ y, h' ⟩ from rfl]
      apply List.mem_map
      apply epsilon_spec hθ

theorem is_one_iff_empty_carrier {θ : Subst α β} : θ = 1 ↔ carrier θ = ∅ := by
  apply Iff.intro
  focus
    intro h
    rw [h, Fintype.ext]
    intro x
    apply Iff.intro _ (False.elim ∘ Fintype.not_mem_empty _)
    rw [carrier_spec]
    exact λ h => False.elim <| h rfl
  focus
    intro h
    rw [Subst.ext]
    intro x
    apply byContradiction
    intro h'
    apply Fintype.not_mem_empty x
    rw [← h, carrier_spec]
    exact h'

theorem carrier_one : carrier (1 : Subst α β) = ∅ :=
  is_one_iff_empty_carrier.1 rfl

theorem is_one_iff_not_modifying (θ : Subst α β) :
  θ = 1 ↔ ∀ x, (Term.Var x : Term α β) • θ = Term.Var x := Subst.ext

theorem not_one_iff_modifying (θ : Subst α β) :
  θ ≠ 1 ↔ ∃ x, (Term.Var x : Term α β) • θ ≠ Term.Var x := by
  apply Iff.intro
  focus
    intro h
    apply byContradiction
    intro h'
    apply h
    rw [Subst.ext]
    intro x
    apply byContradiction
    intro h''
    exact h' ⟨ x, h'' ⟩
  focus
    intro ⟨ x, h ⟩ h'
    rw [is_one_iff_not_modifying] at h'
    exact h (h' x)

theorem elementary_carrier {x : β} {u : Term α β} {h : Term.Var x ≠ u} :
  carrier (Subst.elementary h : Subst α β) = Fintype.mk [x] := by
  apply Fintype.ext.2
  intro y
  rw [carrier_spec]
  apply Iff.intro
  focus
    by_cases p : y = x
    focus
      rw [p]
      intro _
      simp [Fintype.mem_mk_iff]
      apply List.Mem.head
    focus
      intro h'
      apply False.elim ∘ h'
      simp [Subst.elementary, RSMul.smul, map_reduce, p]
  focus
    rw [Fintype.mem_mk_iff]
    intro p
    rw [show y = x by cases p <;> trivial, Subst.elementary_spec₁]
    exact Ne.symm h

theorem carrier_cons (θ φ : Subst α β) : carrier (θ * φ) ⊆ carrier θ ∪ carrier φ := by
  intro x
  rw [Fintype.mem_union_iff]
  simp only [carrier_spec]
  match θ with
  | ⟨ θ, _ ⟩ => match φ with
    | ⟨ φ, _ ⟩ => exact comp_carrier

theorem subst_cons {u v : Term α β} {θ : Subst α β} :
  Term.Cons u v • θ = Term.Cons (u • θ) (v • θ) := by
  cases θ; rfl

