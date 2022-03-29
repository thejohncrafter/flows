/-
Copyright (c) 2021-2022 Julien Marquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Marquet
-/

import Flows.Groundwork
import Flows.Term
import Flows.Subst
import Flows.Vehicle

open Classical

set_option codegen false

section

variable {α β : Type u}

def vanishing (θ : Subst α β) :=
  ∀ {x}, (Term.Var x : Term α β) • θ ≠ Term.Var x →
    ∀ y, ¬ (x ∈ (𝒱 ((Term.Var y : Term α β) • θ) : Fintype β))

theorem vanishing_on_term {θ : Subst α β} (h₁ : vanishing θ)
  {x : β} (h₂ : (Term.Var x : Term α β) • θ ≠ Term.Var x)
  (u : Term α β) : ¬ x ∈ (𝒱 (u • θ) : Fintype β) := by
  induction u with
  | Cst c => match θ with
    | ⟨ θ, h ⟩ => intro h; exact h
  | Var y => exact h₁ h₂ _
  | Cons l r hl hr =>
    rw [subst_cons]
    intro h
    cases (Fintype.mem_union_iff _ _ _).1 h with
    | inl h => exact hl h
    | inr h => exact hr h

theorem vanishing_on_vehicle {θ : Subst α β} (h₁ : vanishing θ)
  {x : β} (h₂ : (Term.Var x : Term α β) • θ ≠ Term.Var x) :
  ¬ x ∈ (𝒱 θ : Fintype β) := by
  suffices h : 𝒱 θ ⊆ 𝒱 θ \ (Fintype.mk [x]) by
    apply Fintype.not_mem_iff_in_without.2
    exact h
  conv => lhs; simp only [HasVehicle.vehicle, Subst.vehicle]
  apply Fintype.image_in_of_all_in
  intro a h
  apply Fintype.included_trans _
    <| Fintype.included_without_of_included _
    <| Fintype.in_image_of_is_image h
  apply Fintype.not_mem_iff_in_without.1
  apply vanishing_on_term h₁ h₂

theorem vanishing_respects_vehicle {θ : Subst α β} (h₁ : vanishing θ) {x : β}
  (h₂ : ¬ x ∈ (𝒱 θ : Fintype β)) {u : Term α β} (h₃ : ¬ x ∈ (𝒱 u : Fintype β)) :
  ¬ x ∈ (𝒱 (u • θ) : Fintype β) := by
  apply Fintype.not_mem_of_superset_not_mem (vehicle_on_image Fintype.included_refl _)
  intro h
  rw [Fintype.mem_union_iff] at h
  exact match h with
  | Or.inl h => h₂ h
  | Or.inr h => h₃ h

theorem cons_vanishing {θ φ : Subst α β} {l₁ r₁ l₂ r₂ : Term α β}
  (h₁ : (𝒱 θ : Fintype β) ⊆ 𝒱 l₁ ∪ 𝒱 l₂)
  (h₂ : (𝒱 φ : Fintype β) ⊆ 𝒱 (r₁ • θ) ∪ 𝒱 (r₂ • θ))
  (h₃ : vanishing θ) (h₄ : vanishing φ) : vanishing (θ * φ) := by
  intro x hx y
  by_cases hθ : (Term.Var x : Term α β) • θ = Term.Var x
  focus
    let p := show (Term.Var x : Term α β) • φ ≠ Term.Var x by
      intro hφ
      apply hx
      rw [← RAction.smul_mul, hθ, hφ]
    rw [← RAction.smul_mul]
    apply vanishing_on_term h₄ p
  focus
    let p := show ¬ x ∈ (𝒱 φ : Fintype β) by
      apply Fintype.not_mem_of_superset_not_mem h₂
      intro h
      rw [Fintype.mem_union_iff] at h
      exact match h with
      | Or.inl h => (vanishing_on_term h₃ hθ r₁) h
      | Or.inr h => (vanishing_on_term h₃ hθ r₂) h
    rw [← RAction.smul_mul]
    exact vanishing_respects_vehicle h₄ p (h₃ hθ _)

theorem elementary_vanishing {x : β} {u : Term α β} {h₁ : Term.Var x ≠ u}
  (h₂ : ¬ x ∈ (𝒱 u : Fintype β)) :
  vanishing (Subst.elementary h₁ : Subst α β) := by
  intro z hz t
  intro h'
  have p : z = x := by
    let p := carrier_spec.2 hz
    rw [elementary_carrier, Fintype.mem_mk_iff] at p
    simp_all [List.mem]
  rw [p] at h'
  by_cases p' : t = x
  focus
    rw [p'] at h'
    rw [Subst.elementary_spec₁] at h'
    exact h₂ h'
  focus
    rw [Subst.elementary_spec₂ _ p'] at h'
    apply Ne.symm p'
    simp_all [HasVehicle.vehicle, Term.vehicle, Fintype.mem_mk_iff, List.mem]

end

