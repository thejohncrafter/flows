/-
Copyright (c) 2021-2022 Julien Marquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Marquet
-/

import Flows.SolveSets
import Flows.Term
import Flows.Subst

--open Classical

set_option codegen false

section

variable {α β : Type u}

def Term.vehicle : Term α β → Fintype β
| Term.Cst _ => ∅
| Term.Var x => Fintype.mk [x]
| Term.Cons l r => vehicle l ∪ vehicle r

instance : HasVehicle (Term α β) (Fintype β) where
  vehicle := Term.vehicle

def Subst.vehicle (θ : Subst α β) : Fintype β := Fintype.image
  (λ x => 𝒱 ((Term.Var x : Term α β) • θ)) (carrier θ)

instance : HasVehicle (Subst α β) (Fintype β) where
  vehicle := Subst.vehicle

theorem vehicle_cons {u v : Term α β} : 
  (𝒱 (Term.Cons u v) : Fintype β) = 𝒱 u ∪ 𝒱 v := rfl

theorem vehicle_one : 𝒱 (1 : Subst α β) = (∅ : Fintype β) := by
  rw [Fintype.ext]
  intro x
  apply Iff.intro
  focus
    simp only [HasVehicle.vehicle, Subst.vehicle]
    rw [Fintype.mem_image_iff, carrier_one]
    intro ⟨ _, p, _ ⟩
    exact False.elim <| Fintype.not_mem_empty _ p
  focus
    exact λ h => False.elim <| Fintype.not_mem_empty _ h

theorem vehicle_elementary {x : β} {u : Term α β} (h : Term.Var x ≠ u) :
  𝒱 (Subst.elementary h : Subst α β) = (𝒱 u : Fintype β) := by
  apply Fintype.ext.2
  intro z
  apply Iff.intro
  focus
    intro h'
    simp only [HasVehicle.vehicle, Subst.vehicle] at h'
    let ⟨ t, t_in, in_img ⟩ := Fintype.mem_image_iff.1 h'
    rw [elementary_carrier, Fintype.mem_mk_iff] at t_in
    rw [show t = x by cases t_in <;> trivial,
      Subst.elementary_spec₁] at in_img
    exact in_img
  focus
    intro p
    simp only [HasVehicle.vehicle, Subst.vehicle]
    apply Fintype.mem_image_iff.2 ⟨ x, (show x ∈ carrier _ from _), _ ⟩
    focus
      rw [elementary_carrier, Fintype.mem_mk_iff]
      apply List.Mem.head
    focus
      rw [Subst.elementary_spec₁]
      exact p

theorem vehicle_on_image {θ : Subst α β} {A : Fintype β}
  (h₁ : 𝒱 θ ⊆ A) (u : Term α β) :
  𝒱 (u • θ) ⊆ A ∪ 𝒱 u := by
    induction u with
    | Cst c => cases θ; apply Fintype.empty_included
    | Var x =>
      by_cases h : (Term.Var x : Term α β) • θ = Term.Var x
      focus
        apply Fintype.included_union_l
        rw [h]
        exact Fintype.included_refl
      focus
        apply Fintype.included_union_r
        apply Fintype.included_trans _ h₁
        intro y h'
        apply Fintype.in_image_of_is_image <| carrier_spec.2 h
        exact h'
    | Cons l r hl hr =>
      rw [subst_cons]
      simp only [Term.vehicle]
      apply Fintype.included_trans (Fintype.union_on_included hl hr)
      rw [vehicle_cons]
      solve_sets

theorem vehicle_on_image_contained {θ : Subst α β} {A : Fintype β} {u : Term α β}
  (h₁ : 𝒱 θ ⊆ A) (h₂ : 𝒱 u ⊆ A) : 𝒱 (u • θ) ⊆ A :=
  Fintype.included_trans (vehicle_on_image h₁ u) <|
    Fintype.union_included_iff.2 ⟨ Fintype.included_refl, h₂ ⟩

theorem vehicle_on_comp {θ φ : Subst α β} {A : Fintype β}
  (h₁ : 𝒱 θ ⊆ A) (h₂ : 𝒱 φ ⊆ A) : 𝒱 (θ * φ) ⊆ A := by
  simp only [HasVehicle.vehicle, Subst.vehicle]
  apply Fintype.image_in_of_all_in
  intro x h
  rw [carrier_spec] at h
  simp only [] -- Better way to do it ?
  rw [← RAction.smul_mul]
  by_cases hθ : (Term.Var x : Term α β) • θ = Term.Var x
  focus
    have hφ := show (Term.Var x : Term α β) • φ ≠ Term.Var x by
      intro hφ
      apply h
      rw [← RAction.smul_mul, hθ, hφ]
    rw [hθ]
    apply Fintype.included_trans _ h₂
    intro y h'
    apply Fintype.in_image_of_is_image <| carrier_spec.2 hφ
    exact h'
  focus
    apply vehicle_on_image_contained h₂
    -- The pattern of the four following lines occurs often.
    -- Make it a lemma ?
    apply Fintype.included_trans _ h₁
    intro y h'
    apply Fintype.in_image_of_is_image <| carrier_spec.2 hθ
    exact h'

theorem vehicle_on_comp₁ (θ φ : Subst α β) : 
  (𝒱 (θ * φ) : Fintype β) ⊆ 𝒱 θ ∪ 𝒱 φ := vehicle_on_comp
  (Fintype.included_union_r _ <| Fintype.included_refl)
  (Fintype.included_union_l _ <| Fintype.included_refl)

theorem cons_vehicle_in {θ φ : Subst α β} {l₁ r₁ l₂ r₂ : Term α β}
  (h₁ : (𝒱 θ : Fintype β) ⊆ 𝒱 l₁ ∪ 𝒱 l₂)
  (h₂ : (𝒱 φ : Fintype β) ⊆ 𝒱 (r₁ • θ) ∪ 𝒱 (r₂ • θ)) :
  (𝒱 (θ * φ) : Fintype β) ⊆ 𝒱 (Term.Cons l₁ r₁) ∪ 𝒱 (Term.Cons l₂ r₂) := by
  rw [vehicle_cons, vehicle_cons]
  apply Fintype.included_trans (vehicle_on_comp₁ θ φ)
  rw [Fintype.union_included_iff]; apply And.intro
  focus
    apply Fintype.included_trans h₁
    solve_sets
  focus
    apply Fintype.included_trans h₂
    apply Fintype.union_included_iff.2 ⟨ _, _ ⟩
      <;> apply vehicle_on_image_contained
      <;> try apply Fintype.included_trans h₁
    all_goals solve_sets

theorem elementary_on_not_in_vehicle {x : β} {u v : Term α β} (h : Term.Var x ≠ u)
  (h' : ¬ x ∈ (𝒱 v : Fintype β)) :
  v • (Subst.elementary h : Subst α β) = v := by
  induction v with
  | Cst c => rfl
  | Var y =>
    apply Subst.elementary_spec₂
    intro h
    apply h'
    rw [h]
    apply List.Mem.head
  | Cons l r hl hr =>
    rw [vehicle_cons, Fintype.mem_union_iff] at h'
    rw [subst_cons, hl (λ h => h' <| Or.inl h), hr (λ h => h' <| Or.inr h)]

end
