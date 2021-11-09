
import MyPackage.Base
import MyPackage.Notation

open Classical

section /- Miscellaneous basic definitions and theorems -/

def contrapose {p q : Prop} : (p → q) → (¬ q → ¬ p) := λ h₁ h₂ h₃ => h₂ (h₁ h₃)

theorem or_assoc {p q r : Prop} : (p ∨ q) ∨ r ↔ p ∨ q ∨ r := Iff.intro
  (λ h => by cases h with
    | inl h => cases h <;> simp_all
    | inr h => simp_all)
  (λ h => by cases h with
    | inl h => simp_all
    | inr h => cases h <;> simp_all)

theorem Prod.eq {α : Type u} {a b c d : α} (h₁ : a = c) (h₂ : b = d) :
  (a, b) = (c, d) := h₁ ▸ h₂ ▸ rfl

theorem Nat.le_of_le_of_le {a b c d : Nat} (h : a ≤ b) (h' : c ≤ d) : a + c ≤ b + d :=
  Nat.le_trans (Nat.add_le_add_left h' _) (Nat.add_le_add_right h _)

theorem Nat.add_ne_zero_of_r_ne_zero {a b : Nat} (h : b ≠ 0) : a + b ≠ 0 :=
  λ h' => match b with
  | 0 => h rfl
  | b + 1 => succ_ne_zero (a + b) h'

theorem Nat.add_ne_zero_of_l_ne_zero {a b : Nat} (h : a ≠ 0) : a + b ≠ 0 := by
  rw [Nat.add_comm]
  exact add_ne_zero_of_r_ne_zero h

theorem Nat.one_le_of_ne_zero {a : Nat} (h : a ≠ 0) : 1 ≤ a := match a with
  | 0 => False.elim <| h rfl
  | a + 1 => Nat.succ_le_succ (Nat.zero_le _)

theorem Nat.not_lt_self (a : Nat) : ¬ a < a := by
  intro h
  induction a with
  | zero => simp [Nat.lt] at h
  | succ a rh => exact rh <| Nat.lt_of_succ_lt_succ h

theorem Nat.ne_of_lt {a b : Nat} (h : a < b) : a ≠ b := by
  intro h'
  rw [h'] at h
  exact not_lt_self _ h

def List.mem (a : α) : (l : List α) → Prop
  | [] => False
  | x :: t => a = x ∨ mem a t

theorem List.mem_append {α : Type u} {x : α} {l₁ l₂ : List α} :
  List.mem x (List.append l₁ l₂) ↔ List.mem x l₁ ∨ List.mem x l₂ := by
  apply Iff.intro
  focus
    induction l₁ with
    | nil => simp [List.append]; exact Or.inr
    | cons y t =>
      byCases h' : x = y
      <;> simp [h', List.append, List.mem]
      <;> assumption
  focus
    intro h
    induction l₁ with
    | nil => simp_all [List.mem, List.append]
    | cons y t t_h =>
      match h with
      | Or.inl h =>
        byCases h' : x = y <;> simp [h', List.append, List.mem]
        simp [h', List.mem] at h
        exact t_h <| Or.inl h
      | Or.inr h =>
        simp [List.append, List.mem]
        apply Or.inr <| t_h <| Or.inr h

-- Replace this theorem with `List.mem_map_iff_image` ?
theorem List.mem_map {α β : Type u} {x : α} {f : α → β} {l : List α} :
  List.mem x l → List.mem (f x) (List.map f l) := by induction l with
  | nil => simp [List.mem]
  | cons y t h =>
    simp [List.mem]
    intro h'
    match h' with
    | Or.inl _ => apply Or.inl ∘ congrArg _; assumption
    | Or.inr h' => apply Or.inr ∘ h; assumption

theorem List.mem_map_iff_image {α β : Type u} {y : β} {f : α → β} {l : List α} :
  List.mem y (List.map f l) ↔ ∃ x, List.mem x l ∧ y = f x := by
  apply Iff.intro
  focus
    induction l with
    | nil => simp [List.mem]
    | cons x t rh =>
      intro h
      byCases p : y = f x
      focus
        exact ⟨ x, by simp [List.mem, p] ⟩
      focus
        let ⟨ z, h ⟩ := rh (by simp [List.mem, p] at h; assumption)
        apply Exists.intro z
        exact ⟨ Or.inr h.1, h.2 ⟩
  focus
    exact λ ⟨ x, ⟨ h₁, h₂ ⟩ ⟩ => h₂ ▸ List.mem_map h₁

theorem List.filter_eq {α : Type u} {f : α → Bool} {l : List α} {x : α} :
  filter f (x :: l) = if f x then x :: filter f l else filter f l := by
  admit

theorem List.mem_filter {α : Type u} {f : α → Bool} {l : List α} {x : α} :
  List.mem x (List.filter f l) ↔ List.mem x l ∧ f x := by
  induction l with
  | nil => simp [mem]
  | cons y t rh =>
    byCases p : f y
    focus
      byCases p' : x = y
      focus
        rw [p']
        rw [p'] at rh
        rw [List.filter_eq]
        simp [mem, filter, filterAux, p]
      focus
        rw [List.filter_eq]
        simp only [p, mem, p', false_or]
        rw [← rh]
        simp [mem]
    focus
      have p : f y = false := eq_false_of_ne_true p
      apply Iff.intro
      focus
        intro h
        suffices p : mem x (filter f t) ∧ x ≠ y by
          simp [mem, p, rh.1 p.1]
        apply And.intro
        focus
          simp_all [mem, filter, filterAux]
        focus
          suffices h : f x by
            intro h'
            rw [h'] at h
            apply Bool.noConfusion (Eq.trans p.symm h)
          simp_all [mem, filter, filterAux]
      focus
        simp [mem, filter, filterAux, p]
        intro ⟨ hl, hr ⟩
        apply rh.2 (And.intro _ hr)
        cases hl with
        | inl hl =>
          rw [hl] at hr
          apply Bool.noConfusion (Eq.trans p.symm hr)
        | inr hl => exact hl

def List.included {α : Type u} (l₁ l₂ : List α) :=
  ∀ a, List.mem a l₁ → List.mem a l₂

def List.concat_map {α β : Type u} (f : α → List β) : List α → List β
| [] => []
| x :: t => List.append (f x) (concat_map f t)

end

section Algebra /- Some algebraic notions -/
/- (at the time of writing, mathlib4 isn't ready so we need to redefine everything.) -/

universe u

class One (α : Type u) where
  one : α

instance (α : Type u) [One α] : OfNat α (nat_lit 1) where
  ofNat := One.one

class Monoid (α : Type u) extends Mul α, One α where
  mul_assoc (f g h : α) : f * g * h = f * (g * h)
  one_mul (f : α) : 1 * f = f
  mul_one (f : α) : f * 1 = f

class RAction (χ : Type u) (α : Type u) [Monoid α] extends RSMul χ α where
  smul_one (x : χ) : x • (1 : α) = x
  smul_mul (x : χ) (a b : α) : (x • a) • b = x • (a * b)

instance self_action (α : Type u) [Monoid α] : RAction α α where
  smul := Mul.mul
  smul_one := Monoid.mul_one
  smul_mul := Monoid.mul_assoc

instance square_monoid (α : Type u) [m : Monoid α] : Monoid (α × α) where
  one := ⟨ 1, 1 ⟩
  mul := λ (a₁, a₂) (b₁, b₂) => (a₁ * b₁, a₂ * b₂)
  one_mul := by intro (_, _); apply Prod.eq <;> exact m.one_mul _
  mul_one := by intro (_, _); apply Prod.eq <;> exact m.mul_one _
  mul_assoc := by intro (_, _) (_, _) (_, _); apply Prod.eq <;> exact m.mul_assoc _ _ _

instance square_action (χ α : Type u) [m : Monoid α] [a : RAction χ α] :
  RAction (χ × χ) (α × α) where
  smul := λ (x₁, x₂) (a₁, a₂) => (x₁ • a₁, x₂ • a₂)
  smul_one := by intro (_, _); apply Prod.eq <;> exact a.smul_one _
  smul_mul := by
    intro (_, _) (_, _) (_, _)
    apply Prod.eq <;> exact a.smul_mul _ _ _

end Algebra

section Fintype

private instance oid (α : Type u) : Setoid (List α) where
  r l₁ l₂ := ∀ a, List.mem a l₁ ↔ List.mem a l₂
  iseqv := {
    refl := by intros; simp_all
    symm := by intros; simp_all
    trans := by intros; simp_all
  }

def Fintype (α : Type u) := Quotient (oid α)

variable {α : Type u}

namespace Fintype

def mem : Fintype α → α → Prop := Quotient.lift (flip List.mem) <| by
  intro _ _ h
  funext a
  exact propext <| h a

instance : HasMem α (Fintype α) where
  mem a x := Fintype.mem x a

def mk (l : List α) : Fintype α := Quotient.mk l

theorem mem_mk_iff {l : List α} {x : α} : x ∈ Fintype.mk l ↔ List.mem x l := by
  suffices h : (Fintype.mem <| Fintype.mk l) = flip List.mem l by
    apply (λ {p q : Prop} (h : p = q) => show p ↔ q by simp_all)
    let h' := congrFun h x
    simp [flip] at h'
    rw [← h']
    rfl
  rfl

def empty : Fintype α := mk []

instance : EmptyCollection (Fintype α) where
  emptyCollection := empty

theorem not_empty_iff (a : α) : ¬ a ∈ (∅ : Fintype α) := by
  suffices p : ¬ a ∈ (mk [] : Fintype α) by assumption
  rw [mem_mk_iff]
  intro _; assumption

theorem ext {x y : Fintype α} : x = y ↔ ∀ a : α, a ∈ x ↔ a ∈ y := by
  apply @Quotient.inductionOn₂ _ _ _ _
    (λ x y : Fintype α => x = y ↔ ∀ a : α, a ∈ x ↔ a ∈ y) _ _
  intro l₁ l₂
  apply Iff.intro
  focus
    intro h _
    rw [h]
    exact Iff.intro id id
  focus
    exact λ h => Quotient.sound h

def union : Fintype α → Fintype α → Fintype α := Quotient.lift₂
  (λ l₁ l₂ => Fintype.mk (List.append l₁ l₂)) <| by
  intro _ _ _ _ h₁ h₂
  apply Quotient.sound
  intro a
  simp [List.mem_append, h₁ a, h₂ a]

instance : HasUnion (Fintype α) where
  union := Fintype.union

theorem spec (l₁ l₂ : List α) (a : α) :
  (a ∈ (Fintype.mk l₁) ∪ (Fintype.mk l₂)) = List.mem a (List.append l₁ l₂) := rfl

theorem mem_union_iff (x y : Fintype α) (a : α) : a ∈ x ∪ y ↔ a ∈ x ∨ a ∈ y := by
  suffices h : ∀ l₁ l₂, a ∈ (mk l₁) ∪ (mk l₂) ↔ a ∈ (mk l₁) ∨ a ∈ (mk l₂)
  from @Quotient.inductionOn₂ _ _ _ _ (λ x y : Fintype α => a ∈ x ∪ y ↔ a ∈ x ∨ a ∈ y) x y h
  intro l₁ l₂
  -- I'm not really convinced by the look of this proof :/
  rw [show (a ∈ (Fintype.mk l₁) ∪ (Fintype.mk l₂)) = List.mem a (List.append l₁ l₂) from rfl,
    List.mem_append]
  simp [Fintype.mem_mk_iff]

theorem union_assoc (x y z : Fintype α) : x ∪ y ∪ z = x ∪ (y ∪ z) := by
  suffices h : ∀ l₁ l₂ l₃ : List α, (mk l₁) ∪ (mk l₂) ∪ (mk l₃)
    = (mk l₁) ∪ ((mk l₂) ∪ (mk l₃))
    --why can't I `apply Quotient.inductionOn₃ x y z` ?
  from @Quotient.inductionOn₃ _ _ _ _ _ _
      (λ x y z : Fintype α => x ∪ y ∪ z = x ∪ (y ∪ z)) x y z h
  intro l₁ l₂ l₃
  apply Quotient.sound
  intro _
  simp [List.mem_append]
  exact or_assoc

def without [∀ (a : α) (x : Fintype α), Decidable (a ∈ x)] : Fintype α → Fintype α → Fintype α :=
  Quotient.lift (λ l x => mk <| List.filter (λ a => ¬ a ∈ x) l) <| by
  intro l₁ l₂ h
  funext a
  rw [Fintype.ext]
  intro x
  suffices p : ∀ l₁ l₂ (x : α), (List.mem x l₁ → List.mem x l₂) →
    List.mem x (List.filter (λ b => ¬ b ∈ a) l₁)
    → List.mem x (List.filter (λ b => ¬ b ∈ a) l₂) by
    apply Iff.intro
    focus
      apply p
      rw [h]
      exact id
    focus
      apply p
      rw [h]
      exact id
  simp only [List.mem_filter]
  intro l₁ l₂ x h ⟨ hl, hr ⟩
  exact ⟨ (h hl), hr ⟩

instance [∀ (a : α) (x : Fintype α), Decidable (a ∈ x)] : HasWithout (Fintype α) where
  without := without

def included (x y : Fintype α) := ∀ a : α, a ∈ x → a ∈ y

instance : HasIncluded (Fintype α) where
  included := included

theorem included_refl {a : Fintype α} : a ⊆ a := λ _ => id

theorem included_trans {a b c : Fintype α} (h : a ⊆ b) (h' : b ⊆ c) : a ⊆ c := λ _ => h' _ ∘ h _

theorem not_mem_empty (a : α) : ¬ a ∈ (∅ : Fintype α) := by
  suffices p : ¬ a ∈ (mk [] : Fintype α) from p
  rw [mem_mk_iff]
  simp [List.mem]

theorem empty_included (a : Fintype α) : ∅ ⊆ a := λ _ => False.elim ∘ not_mem_empty _

theorem union_on_included {a b c d : Fintype α}
  (h₁ : a ⊆ b) (h₂ : c ⊆ d) : a ∪ c ⊆ b ∪ d := by
  intro x
  simp only [mem_union_iff]
  exact λ h => match h with
  | Or.inl h => Or.inl <| h₁ _ h
  | Or.inr h => Or.inr <| h₂ _ h

theorem union_included_iff {a b c : Fintype α} : a ∪ b ⊆ c ↔ a ⊆ c ∧ b ⊆ c := by
  apply Iff.intro
  focus
    intro h
    apply And.intro
      <;> apply included_trans _ h
      <;> intro x h
      <;> rw [mem_union_iff]
    apply Or.inl; assumption
    apply Or.inr; assumption
  focus
    intro h x
    rw [mem_union_iff]
    exact λ h' => match h' with
    | Or.inl h' => h.1 _ h'
    | Or.inr h' => h.2 _ h'

theorem included_union_l {a c : Fintype α} (b : Fintype α) (h : a ⊆ c) : a ⊆ b ∪ c := by
  intro x h'
  rw [mem_union_iff]
  exact Or.inr <| h _ h'

theorem included_union_r {a b : Fintype α} (c : Fintype α) (h : a ⊆ b) : a ⊆ b ∪ c := by
  intro x h'
  rw [mem_union_iff]
  exact Or.inl <| h _ h'

theorem not_mem_of_superset_not_mem {x y : Fintype α} {a : α} (h : x ⊆ y) :
  ¬ a ∈ y → ¬ a ∈ x := contrapose (h _)

theorem mem_iff_singleton_included {x : Fintype α} {a : α} : a ∈ x ↔ (Fintype.mk [a]) ⊆ x := by
  apply Iff.intro
  focus
    intro h y h'
    suffices p : y = a by rw [p]; exact h
    simp_all [mem_mk_iff, List.mem]
  focus
    intro h
    specialize h a
    simp_all [mem_mk_iff, List.mem]

theorem mem_without_iff {x y : Fintype α} {a : α} : a ∈ x \ y ↔ a ∈ x ∧ ¬ a ∈ y := by
  apply @Quotient.inductionOn _ _
    (λ x : Fintype α => a ∈ x \ y ↔ a ∈ x ∧ ¬ a ∈ y) x
  intro l
  suffices p : a ∈ mk l \ y ↔
    List.mem a (List.filter (λ b => ¬ b ∈ y) l) by
    simp only [mk] at p
    rw [p]
    rw [List.mem_filter, show Quotient.mk l = mk l from rfl, mem_mk_iff]
    rw [show decide ¬ a ∈ y = true ↔ ¬ a ∈ y from Iff.intro of_decide_eq_true decide_eq_true]
    exact Iff.intro id id
  exact Iff.intro id id

theorem not_mem_iff_in_without {x : Fintype α} {a : α} :
  ¬ a ∈ x ↔ x ⊆ x \ Fintype.mk [a] := by
  apply @Quotient.inductionOn _ _
    (λ x : Fintype α => ¬ a ∈ x ↔ x ⊆ x \ Fintype.mk [a]) x
  intro l
  simp only [mem_mk_iff, HasIncluded.included, included]
  apply Iff.intro
  focus
    intro h b h'
    suffices p : List.mem b (List.filter (λ c => ¬ c ∈ mk [a]) l) from p
    rw [List.mem_filter]
    apply And.intro h'
    apply decide_eq_true
    intro h''
    apply h
    suffices p : a = b by rw [p]; exact h'
    simp_all [mem_mk_iff, List.mem]
  focus
    intro h h'
    specialize h a h'
    suffices p : List.mem a (List.filter (λ c => ¬ c ∈ mk [a]) l) by
      rw [List.mem_filter] at p
      apply of_decide_eq_true p.2
      simp [mem_mk_iff, List.mem]
    exact h

theorem included_without_of_included {a b: Fintype α} (c : Fintype α) (h : a ⊆ b) :
  a \ c ⊆ b \ c := by
  intro x
  simp only [mem_without_iff]
  exact λ ⟨ hl, hr ⟩ => And.intro (h _ hl) hr

theorem union_comm (a b : Fintype α) : a ∪ b = b ∪ a := by
  rw [ext]
  intro x
  simp only [mem_union_iff]
  apply Iff.intro
    <;> intro h
    <;> cases h
    <;> first
      | apply Or.inl; assumption
      | apply Or.inr; assumption

theorem union_idempotent (a : Fintype α) : a ∪ a = a := by
  rw [ext]
  intro x
  rw [mem_union_iff]
  apply Iff.intro
  intro h; cases h <;> assumption
  exact λ h => Or.inl h

theorem different_if_not_same_element {x y : Fintype β} {a : β} (h₁ : ¬ a ∈ x) (h₂ : a ∈ y) : x ≠ y := by
  intro h
  rw [ext] at h
  exact h₁ <| (h a).2 h₂

def image {β : Type u} (f : α → Fintype β) : Fintype α → Fintype β :=
  Quotient.lift (λ l => List.foldr (λ a x => f a ∪ x) ∅ l) <| by
  admit -- Prove each is included in the other ?

theorem in_image_of_is_image {β : Type u} {f : α → Fintype β} {a : α}
  {x : Fintype α} (h : a ∈ x) : f a ⊆ image f x := sorry

theorem image_in_of_all_in {β : Type u} {f : α → Fintype β} {x : Fintype α}
  {A : Fintype β} (h : ∀ a, a ∈ x → f a ⊆ A) : image f x ⊆ A := by
  admit

theorem mem_image_iff {β : Type u} {f : α → Fintype β} {x : Fintype α} {b : β} :
  b ∈ image f x ↔ ∃ a, a ∈ x ∧ b ∈ f a := sorry

def included_wfRel : WellFoundedRelation (Fintype α) where
  rel x y := included x y ∧ x ≠ y
  wf := by
    admit

end Fintype

end Fintype

section Finite /- A small theory of finite types -/

def finite (α : Type u) := ∃ l : List α, ∀ a : α, List.mem a l

section Subtypes /- First off, two theorems about finite types
                    with respect to subtypes. -/

theorem subtype_finite {α : Type u} (h : finite α) (P : α → Prop) : finite {a // P a} := by
  let ⟨ l, p₁ ⟩ := h
  apply Exists.intro (List.filterMap (λ a =>
    if h : P a then Option.some ⟨ a, h ⟩ else Option.none) l)
  intro ⟨ a, p₂ ⟩
  specialize p₁ a
  induction l with
  | nil => exact p₁
  | cons x t rh =>
    match p₁ with
    | Or.inl p₁ =>
      conv => rhs; rw [← p₁]
      simp [List.filterMap, List.mem, p₂]
    | Or.inr p₁ => byCases h : P x
      <;> simp [h, List.filterMap, List.mem, p₂, rh p₁]

theorem finite_of_full_subtype_finite {α : Type u} {P : α → Prop}
  (full : ∀ a, P a) (h : finite {a // P a}) : finite α := by
  let ⟨ l, p₁ ⟩ := h
  apply Exists.intro (List.map (λ ⟨ a, _ ⟩ => a) l)
  intro a
  let a' : {a // P a} := ⟨ a, full a ⟩
  specialize p₁ a'
  induction l with
  | nil => exact p₁
  | cons x t rh =>
    match x with
    | ⟨ x, _ ⟩ =>
      byCases p : a = x
      focus
        apply Or.inl; assumption
      focus
        simp [List.mem, p] at p₁
        apply Or.inr ∘ rh
        assumption

end Subtypes

section Functions /- Now, finite types with respect to functions -/

theorem image_finite {α β : Type u} (h : finite α) (f : α → β) : finite {b // ∃ a, b = f a} := by
  let ⟨ l, p₁ ⟩ := h
  apply Exists.intro (List.map (λ a => ⟨ f a, ⟨ a, rfl ⟩ ⟩) l)
  intro ⟨ b, ⟨ a, p₂ ⟩ ⟩
  specialize p₁ a
  induction l with
  | nil => exact p₁
  | cons x t h =>
    simp [List.map, List.mem]
    exact match p₁ with
    | Or.inl p₁ => p₁ ▸ Or.inl p₂
    | Or.inr p₁ => Or.inr <| h p₁

/- The three following declarations are private as they are completely ad-hoc.
   They are only meant to be used in the next theorem.
   It is possible to turn them into a general notion,
   but this is not my intention at the moment. -/
private def sec {α β : Type u} (f : α → β) (b : {b // ∃ a, b = f a}) : α := b.2.1

private def sec_image {α β : Type u} (f : α → β) : ∀ (b : {b // ∃ a, b = f a}), f (sec f b) = b := by
  intro ⟨ b, ⟨ a, h ⟩ ⟩
  simp [sec]
  conv => rhs; rw [h]

private def sec_codomain_full {α β : Type u} (f : α → β) (inj : ∀ x y, f x = f y → x = y)
  (a : α) : ∃ b, a = sec f b := by
  apply Exists.intro (⟨ f a, ⟨ a, rfl ⟩ ⟩)
  apply inj
  rw [sec_image f _]

theorem invimage_finite_of_inj {α β : Type u} (h : finite β)
  {f : α → β} (inj : ∀ x y, f x = f y → x = y) : finite α :=
  finite_of_full_subtype_finite
    (sec_codomain_full f inj)
    (image_finite (subtype_finite h (λ b => ∃ a, b = f a)) (sec f))

end Functions

section Sums /- Sums of finite types -/

theorem sum_finite {α β : Type u} (h₁ : finite α) (h₂ : finite β) : finite (α ⊕ β) := by
  apply Exists.intro (List.append (List.map Sum.inl h₁.1) (List.map Sum.inr h₂.1))
  intro x
  rw [List.mem_append]
  exact match x with
  | Sum.inl a => Or.inl <| List.mem_map <| h₁.2 a
  | Sum.inr b => Or.inr <| List.mem_map <| h₂.2 b

end Sums

end Finite
