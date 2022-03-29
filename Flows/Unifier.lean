/-
Copyright (c) 2021-2022 Julien Marquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Marquet
-/

import Flows.Term
import Flows.Subst

open Classical

set_option codegen false

section

variable {χ : Type u} (α : Type u) [Monoid α] [RAction χ α]

def unifiers (a b : χ) := λ (θ : α) => a • θ = b • θ

def generated_by (θ : α) := λ (φ : α) => ∃ ρ, θ * ρ = φ

def is_mgu (a b : χ) (θ : α) := unifiers α a b = generated_by α θ
def strangers (a b : χ) := unifiers α a b = λ _ => False

def mgu_or_strangers (a b : χ) :=
  (∃ θ : α, unifiers α a b = generated_by α θ) ∨ strangers α a b

end

section

variable {χ : Type u} {α : Type u} [Monoid α] [RAction χ α]

theorem unifies_of_mgu {u v : χ} {θ : α} (h : is_mgu α u v θ) : u • θ = v • θ := by
  suffices unifiers _ _ _ _ by assumption
  exact h ▸ Exists.intro 1 (Monoid.mul_one _)

theorem most_general_of_mgu {a b : χ} {θ φ : α}
  (h₁ : is_mgu α a b θ) (h₂ : a • φ = b • φ) : ∃ ρ, θ * ρ = φ := by
  suffices generated_by α θ φ by assumption
  exact h₁ ▸ h₂

theorem mgu_of_unifies_and_most_general {a b : χ} {θ : α}
  (unifies : a • θ = b • θ)
  (most_general : ∀ φ, a • φ = b • φ → ∃ ρ, θ * ρ = φ) : is_mgu α a b θ := by
  funext φ
  apply propext
  apply Iff.intro (most_general _)
  intro ⟨ ρ, hρ ⟩
  rw [← hρ, ← RAction.smul_mul, ← RAction.smul_mul, unifies]

theorem strangers_iff_no_unifier {u v : χ} :
  strangers α u v ↔ ∀ θ : α, u • θ ≠ v • θ := by
  apply Iff.intro
  focus
    intro h θ h'
    suffices p : unifiers α u v θ by
      rw [h] at p; exact False.elim p
    exact h'
  focus
    intro h
    funext θ
    apply propext
    apply Iff.intro (λ h' => h θ h') (λ h => False.elim h)

end
