
import Lean

import MyPackage.Base
import MyPackage.Notation
import MyPackage.Groundwork

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
  byCases p₁ : f x ≠ Term.Var x <;> byCases p₂ : g x ≠ Term.Var x
    <;> byCases p₃ : f y ≠ Term.Var y <;> byCases p₄ : g y ≠ Term.Var y
    <;> simp [dif_pos p₁, dif_neg p₁, dif_pos p₂, dif_neg p₂,
      dif_pos p₃, dif_neg p₃, dif_pos p₄, dif_neg p₄] at h
    <;> first
      | assumption
      | apply x_nontriv; assumption; assumption
      | apply y_nontriv; assumption; assumption

instance : Monoid (Subst α β) where
  one := ⟨ Term.Var, ⟨ [], λ ⟨ _, p ⟩ => p rfl ⟩ ⟩
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

def Subst.elementary {x y : β} (h : x ≠ y) : Subst α β :=
  ⟨ λ z => Term.Var <| if z = x then y else z, by
    apply Exists.intro [⟨ x, by simp [h.symm] ⟩]
    intro ⟨ z, hz ⟩
    simp [List.mem]
    apply byContradiction
    intro h'
    apply hz
    simp [h'] ⟩

theorem Subst.elementary_spec₁ {x y : β} (h : x ≠ y) :
  (Term.Var x : Term α β) • (elementary h : Subst α β) = Term.Var y := by
  simp [RSMul.smul, elementary, map_reduce]

theorem Subst.elementary_spec₂ {x y z : β} (h : x ≠ y) (h' : z ≠ x) :
  (Term.Var z : Term α β) • (elementary h : Subst α β) = Term.Var z := by
  simp [RSMul.smul, elementary, map_reduce, h']

def carrier (θ : Subst α β) : Fintype β :=
  match θ with
  | ⟨ θ, h ⟩ =>
    let π : {x // θ x ≠ Term.Var x} → β := λ ⟨ x, _ ⟩ => x
    Fintype.mk <| List.map π (epsilon <| λ l => ∀ a, List.mem a l)

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
  admit

theorem is_one_iff_not_modifying (θ : Subst α β) :
  θ = 1 ↔ ∀ x, (Term.Var x : Term α β) • θ = Term.Var x := by
  admit

theorem not_one_iff_modifying (θ : Subst α β) :
  θ ≠ 1 ↔ ∃ x, (Term.Var x : Term α β) • θ ≠ Term.Var x := by
  admit

theorem elementary_carrier {x y : β} {h : x ≠ y} :
  carrier (Subst.elementary h : Subst α β) = Fintype.mk [x] := by
  apply Fintype.ext.2
  intro a
  rw [carrier_spec]
  apply Iff.intro
  focus
    admit
  focus
    rw [Fintype.mem_mk_iff]
    intro p
    rw [show a = x by simp_all [List.mem], Subst.elementary_spec₁]
    exact λ h' => h <| Term.noConfusion h' Eq.symm

theorem carrier_cons (θ φ : Subst α β) : carrier (θ * φ) ⊆ carrier θ ∪ carrier φ := by
  rw [Fintype.included_iff]
  intro x
  rw [Fintype.mem_union_iff]
  simp only [carrier_spec]
  match θ with
  | ⟨ θ, _ ⟩ => match φ with
    | ⟨ φ, _ ⟩ => exact comp_carrier

theorem subst_cons {u v : Term α β} {θ : Subst α β} :
  Term.Cons u v • θ = Term.Cons (u • θ) (v • θ) := by
  cases θ; rfl

end 

section

variable {α β : Type u}

def depth : (u : Term α β) → Nat
| Term.Cst _ => 0
| Term.Var _ => 0
| Term.Cons l r => depth l + depth r + 1

theorem depth_decr_l (l r : Term β α) : depth l < depth (Term.Cons l r) :=
  Nat.lt_succ_of_le <| Nat.le_add_right _ _

theorem depth_decr_r (l r : Term β α) : depth r < depth (Term.Cons l r) :=
  Nat.lt_succ_of_le <| Nat.le_add_left _ _

def Term.depth_wfRel : WellFoundedRelation (Term α β) := measure depth

end

section

variable {α : Type u}

theorem included_refl {a : Fintype α} : a ⊆ a := sorry

theorem included_trans {a b c : Fintype α} (h : a ⊆ b) (h' : b ⊆ c) : a ⊆ c := by
  admit

theorem empty_included (a : Fintype α) : ∅ ⊆ a := sorry

theorem union_on_included {a b c d : Fintype α}
  (h₁ : a ⊆ b) (h₂ : c ⊆ d) : a ∪ c ⊆ b ∪ d := by
  admit

theorem union_included_iff {a b c : Fintype α} : a ∪ b ⊆ c ↔ a ⊆ c ∧ b ⊆ c := sorry

theorem included_union_iff {a b c : Fintype α} : a ⊆ b ∪ c ↔ a ⊆ b ∨ a ⊆ c := sorry

theorem mem_of_subset_mem {x y : Fintype α} {a : α} (h : x ⊆ y) : a ∈ x → a ∈ y := sorry

theorem not_mem_of_superset_not_mem {x y : Fintype α} {a : α} (h : x ⊆ y) :
  ¬ a ∈ y → ¬ a ∈ x := contrapose (mem_of_subset_mem h)

theorem mem_iff_singleton_included {x : Fintype α} {a : α} : a ∈ x ↔ (Fintype.mk [a]) ⊆ x := sorry

theorem not_mem_iff_in_without {x : Fintype α} {a : α} :
  ¬ a ∈ x ↔ x ⊆ x \ Fintype.mk [a] := sorry

theorem included_without_of_included {a b: Fintype α} (c : Fintype α) (h : a ⊆ b) :
  a \ c ⊆ b \ c := sorry

theorem union_comm (a b : Fintype α) : a ∪ b = b ∪ a := sorry

theorem union_idempotent (a : Fintype α) : a ∪ a = a := sorry

/- Two hacky lemmas, would be best with a tactic. -/
theorem flush_union_left (a : Fintype β) : ∀ b c, c ∪ b ∪ a = c ∪ a ∪ b := sorry

theorem union_idempotent' (a b : Fintype β) : a ∪ b ∪ b = a ∪ b := sorry

theorem different_if_not_same_element {x y : Fintype β} {a : β} (h₁ : ¬ a ∈ x) (h₂ : a ∈ y) : x ≠ y := sorry

end

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
  admit

theorem vehicle_elementary {x y : β} (h : x ≠ y) :
  𝒱 (Subst.elementary h : Subst α β) = Fintype.mk [y] := by
  apply Fintype.ext.2
  intro z
  apply Iff.intro
  focus
    intro h'
    simp only [HasVehicle.vehicle, Subst.vehicle] at h'
    let ⟨ t, t_in, in_img ⟩ := Fintype.mem_image_iff.1 h'
    rw [elementary_carrier, Fintype.mem_mk_iff] at t_in
    rw [show t = x by simp_all [List.mem],
      Subst.elementary_spec₁] at in_img
    exact in_img
  focus
    intro p
    rw [Fintype.mem_mk_iff] at p
    rw [show z = y by simp_all [List.mem]]
    simp only [HasVehicle.vehicle, Subst.vehicle]
    apply Fintype.mem_image_iff.2 ⟨ x, (show x ∈ carrier _ from _), _ ⟩
    focus
      rw [elementary_carrier, Fintype.mem_mk_iff]
      simp [List.mem]
    focus
      rw [Subst.elementary_spec₁]
      apply Fintype.mem_mk_iff.2
      simp [List.mem]

theorem vehicle_on_image {θ : Subst α β} {A : Fintype β}
  (h₁ : 𝒱 θ ⊆ A) (u : Term α β) :
  𝒱 (u • θ) ⊆ A ∪ 𝒱 u := by
    induction u with
    | Cst c => cases θ; apply empty_included
    | Var x =>
      byCases h : (Term.Var x : Term α β) • θ = Term.Var x
      focus
        apply included_union_iff.2 ∘ Or.inr
        rw [h]
        exact included_refl
      focus
        apply included_union_iff.2 ∘ Or.inl
        apply included_trans _ h₁
        exact Fintype.in_image_of_is_image <| carrier_spec.2 h
    | Cons l r hl hr =>
      rw [subst_cons]
      simp only [Term.vehicle]
      apply included_trans (union_on_included hl hr)
      conv =>
        rhs
        rw [vehicle_cons, ← Fintype.union_assoc]
        rw [← union_idempotent A]
        conv =>
          lhs
          conv => rw [Fintype.union_assoc]; rhs; rw [union_comm]
          rw [← Fintype.union_assoc]
        rw [Fintype.union_assoc]
      exact included_refl

theorem vehicle_on_image_contained {θ : Subst α β} {A : Fintype β} {u : Term α β}
  (h₁ : 𝒱 θ ⊆ A) (h₂ : 𝒱 u ⊆ A) : 𝒱 (u • θ) ⊆ A :=
  included_trans (vehicle_on_image h₁ u) <|
    union_included_iff.2 ⟨ included_refl, h₂ ⟩

theorem vehicle_on_comp {θ φ : Subst α β} {A : Fintype β}
  (h₁ : 𝒱 θ ⊆ A) (h₂ : 𝒱 φ ⊆ A) : 𝒱 (θ * φ) ⊆ A := by
  apply Fintype.image_in_of_all_in
  intro x h
  rw [carrier_spec] at h
  simp only [] -- Better way to do it ?
  rw [← RAction.smul_mul]
  byCases hθ : (Term.Var x : Term α β) • θ = Term.Var x
  focus
    have hφ := show (Term.Var x : Term α β) • φ ≠ Term.Var x by
      intro hφ
      apply h
      rw [← RAction.smul_mul, hθ, hφ]
    rw [hθ]
    apply included_trans _ h₂
    exact Fintype.in_image_of_is_image <| carrier_spec.2 hφ
  focus
    apply vehicle_on_image_contained h₂
    -- The pattern of the two following lines occurs often.
    -- Make it a lemma ?
    apply included_trans _ h₁
    exact Fintype.in_image_of_is_image <| carrier_spec.2 hθ

theorem vehicle_on_comp₁ (θ φ : Subst α β) : 
  (𝒱 (θ * φ) : Fintype β) ⊆ 𝒱 θ ∪ 𝒱 φ := vehicle_on_comp
  (included_union_iff.2 ∘ Or.inl <| included_refl)
  (included_union_iff.2 ∘ Or.inr <| included_refl)

theorem cons_vehicle_in {θ φ : Subst α β} {l₁ r₁ l₂ r₂ : Term α β}
  (h₁ : (𝒱 θ : Fintype β) ⊆ 𝒱 l₁ ∪ 𝒱 l₂)
  (h₂ : (𝒱 φ : Fintype β) ⊆ 𝒱 (r₁ • θ) ∪ 𝒱 (r₂ • θ)) :
  (𝒱 (θ * φ) : Fintype β) ⊆ 𝒱 (Term.Cons l₁ r₁) ∪ 𝒱 (Term.Cons l₂ r₂) := by
  rw [vehicle_cons, vehicle_cons]
  apply included_trans (vehicle_on_comp₁ θ φ)
  rw [union_included_iff]; apply And.intro
  focus
    apply included_trans h₁
    conv =>
      rhs
      rw [← Fintype.union_assoc]
      lhs
      conv => rw [Fintype.union_assoc]; rhs; rw [union_comm]
      rw [← Fintype.union_assoc]
    rw [Fintype.union_assoc]
    apply included_union_iff.2 ∘ Or.inl
    exact included_refl
  focus
    apply included_trans h₂
    suffices h : (𝒱 (r₁ • θ) ∪ 𝒱 (r₂ • θ) : Fintype β)
      ⊆ 𝒱 l₁ ∪ 𝒱 l₂ ∪ 𝒱 r₁ ∪ (𝒱 l₁ ∪ 𝒱 l₂ ∪ 𝒱 r₂) by
      apply included_trans h
      simp only [← Fintype.union_assoc]
      -- Let's use our hacky lemmas
      simp only [flush_union_left (𝒱 l₂)]
      simp only [flush_union_left (𝒱 l₁)]
      simp only [union_idempotent, union_idempotent']
      exact included_refl
    apply union_on_included
      <;> apply vehicle_on_image_contained
      <;> first
        | apply included_trans h₁
          apply included_union_iff.2 ∘ Or.inl
          exact included_refl
        | apply included_union_iff.2 ∘ Or.inr
          exact included_refl

end

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
    rw [mem_iff_singleton_included] at h
    let h := included_union_iff.1 h
    simp only [← mem_iff_singleton_included] at h
    cases h with
    | inl h => exact hl h
    | inr h => exact hr h

theorem vanishing_on_vehicle {θ : Subst α β} (h₁ : vanishing θ)
  {x : β} (h₂ : (Term.Var x : Term α β) • θ ≠ Term.Var x) :
  ¬ x ∈ (𝒱 θ : Fintype β) := by
  suffices h : 𝒱 θ ⊆ 𝒱 θ \ (Fintype.mk [x]) by
    apply not_mem_iff_in_without.2
    exact h
  apply Fintype.image_in_of_all_in
  intro a h
  apply included_trans _
    <| included_without_of_included _
    <| Fintype.in_image_of_is_image h
  apply not_mem_iff_in_without.1
  apply vanishing_on_term h₁ h₂

theorem vanishing_respects_vehicle {θ : Subst α β} (h₁ : vanishing θ) {x : β}
  (h₂ : ¬ x ∈ (𝒱 θ : Fintype β)) {u : Term α β} (h₃ : ¬ x ∈ (𝒱 u : Fintype β)) :
  ¬ x ∈ (𝒱 (u • θ) : Fintype β) := by
  apply not_mem_of_superset_not_mem (vehicle_on_image included_refl _)
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
  byCases hθ : (Term.Var x : Term α β) • θ = Term.Var x
  focus
    let p := show (Term.Var x : Term α β) • φ ≠ Term.Var x by
      intro hφ
      apply hx
      rw [← RAction.smul_mul, hθ, hφ]
    rw [← RAction.smul_mul]
    apply vanishing_on_term h₄ p
  focus
    let p := show ¬ x ∈ (𝒱 φ : Fintype β) by
      apply not_mem_of_superset_not_mem h₂
      intro h
      rw [Fintype.mem_union_iff] at h
      exact match h with
      | Or.inl h => (vanishing_on_term h₃ hθ r₁) h
      | Or.inr h => (vanishing_on_term h₃ hθ r₂) h
    rw [← RAction.smul_mul]
    exact vanishing_respects_vehicle h₄ p (h₃ hθ _)

theorem elementary_vanishing {x y : β} {h : x ≠ y} :
  vanishing (Subst.elementary h : Subst α β) := by
  intro z hz t
  intro h'
  have p : z = x := by
    let p := carrier_spec.2 hz
    rw [elementary_carrier, Fintype.mem_mk_iff] at p
    simp_all [List.mem]
  rw [p] at h'
  (byCases p' : t = x
    <;> first
      | rw [p'] at h'
        rw [Subst.elementary_spec₁] at h'
        apply h
      | rw [Subst.elementary_spec₂ _ p'] at h'
        apply Ne.symm p')
    <;> simp_all [HasVehicle.vehicle, Term.vehicle, Fintype.mem_mk_iff, List.mem]

end

section

theorem cons_carrier_in {θ φ : Subst α β} {l₁ r₁ l₂ r₂ : Term α β}
  (h₁ : (𝒱 θ : Fintype β) ⊆ 𝒱 l₁ ∪ 𝒱 l₂)
  (h₂ : (𝒱 φ : Fintype β) ⊆ 𝒱 (r₁ • θ) ∪ 𝒱 (r₂ • θ))
  (h₃ : vanishing θ) (h₄ : vanishing φ)
  (h₅ : carrier θ ⊆ 𝒱 l₁ ∪ 𝒱 l₂) (h₆ : carrier φ ⊆ 𝒱 (r₁ • θ) ∪ 𝒱 (r₂ • θ)) :
  carrier (θ * φ) ⊆ 𝒱 (Term.Cons l₁ r₁) ∪ 𝒱 (Term.Cons l₂ r₂) := by
  apply included_trans (carrier_cons _ _)
  simp only [vehicle_cons, ← Fintype.union_assoc, flush_union_left (𝒱 l₂)]
  rw [Fintype.union_assoc]
  apply union_included_iff.2 (And.intro _ _)
  focus
    apply included_trans h₅
    apply included_union_iff.2 ∘ Or.inl
    exact included_refl
  focus
    apply included_trans h₆
    apply union_included_iff.2 (And.intro _ _)
      <;> first
        | apply included_trans (vehicle_on_image h₁ _)
          apply union_included_iff.2 (And.intro _ _)
          focus
            apply included_union_iff.2 ∘ Or.inl
            exact included_refl
          focus
            apply included_union_iff.2 ∘ Or.inr
    exact included_union_iff.2 ∘ Or.inl <| included_refl
    exact included_union_iff.2 ∘ Or.inr <| included_refl

end

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

theorem stangers_iff_no_unifier {u v : χ} :
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

section

theorem lex_of_le_and_lt {α β : Type u}
  {ha : WellFoundedRelation α} {hb : WellFoundedRelation β}
  {a₁ a₂ : α} {b₁ b₂ : β} (h₁ : ha.rel a₁ a₂ ∨ a₁ = a₂) (h₂ : hb.rel b₁ b₂) :
  (Prod.lex ha hb).rel (a₁, b₁) (a₂, b₂) := sorry

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
    (Prod.rprod Term.depth_wfRel Term.depth_wfRel)

@[inline]
private def P (x : Term α β × Term α β) := match x with
  | (u, v) => strangers (Subst α β) u v
    ∨ ∃ θ : Subst α β, is_mgu _ u v θ
      ∧ (𝒱 θ : Fintype β) ⊆ 𝒱 u ∪ 𝒱 v
      ∧ vanishing θ
      ∧ carrier θ ⊆ 𝒱 u ∪ 𝒱 v

private theorem decr_left (l₁ r₁ l₂ r₂ : Term α β) :
  rel.rel (l₁, l₂) (Term.Cons l₁ r₁, Term.Cons l₂ r₂) := by
  simp [rel, invImage, InvImage]
  apply lex_of_le_and_lt
  focus
    simp [invImage, InvImage, Fintype.included_wfRel]
    suffices h : (𝒱 l₁ ∪ 𝒱 l₂ : Fintype β)
      ⊆ 𝒱 (Term.Cons l₁ r₁) ∪ 𝒱 (Term.Cons l₂ r₂) by
      byCases p : (𝒱 l₁ ∪ 𝒱 l₂ : Fintype β)
        = 𝒱 (Term.Cons l₁ r₁) ∪ 𝒱 (Term.Cons l₂ r₂)
      exact Or.inr p
      exact Or.inl ⟨ h, p ⟩
    simp only [vehicle_cons, ← Fintype.union_assoc]
    simp only [flush_union_left (𝒱 l₂)]
    rw [Fintype.union_assoc]
    exact included_union_iff.2 ∘ Or.inl <| included_refl
  focus
        exact Prod.RProd.intro (depth_decr_l _ _) (depth_decr_l _ _)

private theorem decr_right (l₁ r₁ l₂ r₂ : Term α β) {θ : Subst α β}
  (θ_vehicle : (𝒱 θ : Fintype β) ⊆ 𝒱 l₁ ∪ 𝒱 l₂)
  (θ_vanishing : vanishing θ) (θ_carrier : carrier θ ⊆ 𝒱 l₁ ∪ 𝒱 l₂) :
  rel.rel (r₁ • θ, r₂ • θ) (Term.Cons l₁ r₁, Term.Cons l₂ r₂) := by
  byCases h : θ = 1
  focus
    rw [h, RAction.smul_one, RAction.smul_one]
    apply lex_of_le_and_lt
    focus
      simp [invImage, InvImage, Fintype.included_wfRel]
      suffices h : (𝒱 r₁ ∪ 𝒱 r₂ : Fintype β)
        ⊆ 𝒱 (Term.Cons l₁ r₁) ∪ 𝒱 (Term.Cons l₂ r₂) by
        byCases p : (𝒱 r₁ ∪ 𝒱 r₂ : Fintype β)
          = 𝒱 (Term.Cons l₁ r₁) ∪ 𝒱 (Term.Cons l₂ r₂)
        exact Or.inr p
        exact Or.inl ⟨ h, p ⟩
      simp only [vehicle_cons, ← Fintype.union_assoc]
      simp only [flush_union_left (𝒱 l₂)]
      rw [Fintype.union_assoc]
      exact included_union_iff.2 ∘ Or.inr <| included_refl
    focus
      exact Prod.RProd.intro (depth_decr_r _ _) (depth_decr_r _ _)
  focus
    apply Prod.Lex.left
    apply And.intro
    focus
      simp only [vehicle_cons]
      apply union_included_iff.2 <| And.intro _ _
      focus
        apply included_trans (vehicle_on_image included_refl r₁)
        apply union_included_iff.2 <| And.intro _ _
        focus
          apply included_trans θ_vehicle
          simp only [← Fintype.union_assoc, flush_union_left (𝒱 l₂)]
          rw [Fintype.union_assoc]
          apply included_union_iff.2 ∘ Or.inl <| included_refl
        focus
          simp only [← Fintype.union_assoc, ← flush_union_left (𝒱 r₁)]
          apply included_union_iff.2 ∘ Or.inr <| included_refl
      focus
        apply included_trans (vehicle_on_image included_refl r₂)
        apply union_included_iff.2 <| And.intro _ _
        focus
          apply included_trans θ_vehicle
          simp only [← Fintype.union_assoc, flush_union_left (𝒱 l₂)]
          rw [Fintype.union_assoc]
          apply included_union_iff.2 ∘ Or.inl <| included_refl
        focus
          simp only [← Fintype.union_assoc, ← flush_union_left (𝒱 r₂)]
          apply included_union_iff.2 ∘ Or.inr <| included_refl
    focus
      let ⟨ x, hx ⟩ := (not_one_iff_modifying θ).1 h
      let not_in_r₁ := vanishing_on_term θ_vanishing hx r₁
      let not_in_r₂ := vanishing_on_term θ_vanishing hx r₂
      let not_in_lhs : ¬ x ∈ (𝒱 (r₁ • θ) ∪ 𝒱 (r₂ • θ) : Fintype β) :=
        λ h => match (Fintype.mem_union_iff _ _ _).1 h with
          | Or.inl h => not_in_r₁ h
          | Or.inr h => not_in_r₂ h
      let in_rhs : x ∈ (𝒱 (Term.Cons l₁ r₁) ∪ 𝒱 (Term.Cons l₂ r₂) : Fintype β) := by
        simp only [vehicle_cons, ← Fintype.union_assoc, flush_union_left (𝒱 l₂)]
        rw [Fintype.union_assoc]
        apply (Fintype.mem_union_iff _ _ _).2 ∘ Or.inl
        apply mem_iff_singleton_included.2
        apply included_trans _ θ_carrier
        apply mem_iff_singleton_included.1
        exact carrier_spec.2 hx
      exact different_if_not_same_element not_in_lhs in_rhs

private def robinsonR (x : Term α β × Term α β)
  (rh : ∀ y, rel.rel y x → P y) : P x := match x with
  | (Term.Cons l₁ r₁, Term.Cons l₂ r₂) =>
    match rh (l₁, l₂) (decr_left _ _ _ _) with
    | Or.inl h => by
      apply Or.inl
      rw [stangers_iff_no_unifier]
      rw [stangers_iff_no_unifier] at h
      intro θ h'
      apply h θ
      simp only [subst_cons] at h'
      apply Term.noConfusion h'
      exact λ h _ => h
    | Or.inr ⟨ θ, θ_mgu, θ_vehicle, θ_vanishing, θ_carrier ⟩ =>
      match rh (r₁ • θ, r₂ • θ) (by apply decr_right <;> assumption) with
      | Or.inl h => by
        apply Or.inl
        rw [stangers_iff_no_unifier]
        rw [stangers_iff_no_unifier] at h
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
      | Or.inr ⟨ φ, φ_mgu, φ_vehicle, φ_vanishing, φ_carrier ⟩ => by
        apply Or.inr
        apply Exists.intro (θ * φ)
        apply And.intro _ _
        focus
          exact cons_mgu θ_mgu φ_mgu
        focus
          exact ⟨ cons_vehicle_in θ_vehicle φ_vehicle,
            cons_vanishing θ_vehicle φ_vehicle θ_vanishing φ_vanishing,
            cons_carrier_in θ_vehicle φ_vehicle θ_vanishing φ_vanishing
              θ_carrier φ_carrier ⟩
  | (Term.Var x, Term.Var y) => by
    byCases p : x = y
    focus
      apply Or.inr ∘ Exists.intro 1
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
        exact empty_included _
      focus
        exact λ h => False.elim (h rfl)
      focus
        rw [is_one_iff_empty_carrier.1 rfl]
        apply empty_included _
    focus
      apply Or.inr ∘ Exists.intro (Subst.elementary p)
      apply And.intro (mgu_of_unifies_and_most_general _ _)
        (And.intro _ (And.intro _ _))
      focus
        rw [Subst.elementary_spec₁ p, Subst.elementary_spec₂ p]
        exact Ne.symm p
      focus
        intro θ hθ
        apply Exists.intro θ
        apply Subst.ext.2
        intro z
        rw [← RAction.smul_mul]
        byCases p : z = x
        focus
          rw [p, hθ, Subst.elementary_spec₁]
        focus
          rw [Subst.elementary_spec₂]
          exact p
      focus
        rw [vehicle_elementary]
        apply included_union_iff.2 (Or.inr included_refl)
      focus
        exact elementary_vanishing
      focus
        rw [elementary_carrier]
        exact included_union_iff.2 (Or.inl included_refl)
  | (Term.Cst a, Term.Cst b) => by
    admit -- Same as (Term.Var x, Term.Var y) ?
  | _ => sorry

/-
-- robinson._unary is undefined :'(
def robinson (u v : Term α β) : Option (Subst α β) := match (u, v) with
  | (Term.Cons l₁ r₁, Term.Cons l₂ r₂) =>
    if let some θ := robinson l₁ l₂ then
      if let some φ := robinson (r₁ • θ) (r₂ • θ) then
        some (θ * φ)
      else none
    else none
  | _ => none
termination_by sorry
decreasing_by sorry -/

end
