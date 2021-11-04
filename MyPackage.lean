
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

def subst_cons {u v : Term α β} {θ : Subst α β} :
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

private def robinsonR (x : Term α β × Term α β)
  (rh : ∀ y, rel.rel y x → P y) : P x := match x with
  | (Term.Cons l₁ r₁, Term.Cons l₂ r₂) =>
    let p := show rel.rel (l₁, l₂) (Term.Cons l₁ r₁, Term.Cons l₂ r₂) by
      simp [rel, invImage, InvImage]
      apply lex_of_le_and_lt
      focus
        simp [invImage, InvImage, Fintype.included_wfRel]
        -- Some calculations to do...
        admit
      focus
        exact Prod.RProd.intro (depth_decr_l _ _) (depth_decr_l _ _)
    match rh (l₁, l₂) p with
    | Or.inl h => by
      apply Or.inl
      admit
    | Or.inr ⟨ θ, θ_mgu, hθ ⟩ =>
      let p := show rel.rel (r₁ • θ, r₂ • θ) (Term.Cons l₁ r₁, Term.Cons l₂ r₂) by
        byCases h : θ = 1
        focus
          rw [h, RAction.smul_one, RAction.smul_one]
          apply lex_of_le_and_lt
          focus
            -- Same calculations as above...
            admit
          focus
            exact Prod.RProd.intro (depth_decr_r _ _) (depth_decr_r _ _)
        focus
          admit
      match rh (r₁ • θ, r₂ • θ) p with
      | Or.inl h => by
        apply Or.inl
        admit
      | Or.inr ⟨ φ, φ_mgu, hφ ⟩ => by
        apply Or.inr
        apply Exists.intro (θ * φ)
        apply And.intro
        focus
          exact cons_mgu θ_mgu φ_mgu
        focus
          exact ⟨ cons_vehicle_in hθ.1 hφ.1,
            cons_vanishing hθ.1 hφ.1 hθ.2 hφ.2 ⟩
  | (Term.Var x, Term.Var y) => by
    byCases p : x = y
    focus
      apply Or.inr ∘ Exists.intro 1
      rw [p]
      apply And.intro
      focus
        simp [is_mgu]
        funext x
        apply propext
        simp [unifiers, generated_by]
        admit
      focus
        apply And.intro
        focus
          admit
        focus
          exact λ h => False.elim (h rfl)
    focus
      admit
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
