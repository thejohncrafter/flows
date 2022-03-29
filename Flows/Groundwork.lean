/-
Copyright (c) 2021-2022 Julien Marquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Marquet
-/

import MyPackage.Base
import MyPackage.Notation

open Classical

section /- Miscellaneous basic definitions and theorems -/

def contrapose {p q : Prop} : (p → q) → (¬ q → ¬ p) := λ h₁ h₂ h₃ => h₂ (h₁ h₃)

theorem or_comm {P Q : Prop} : P ∨ Q ↔ Q ∨ P := by
  apply Iff.intro <;> intro h <;> cases h
    <;> first
    | apply Or.inl; assumption
    | apply Or.inr; assumption

theorem or_assoc {p q r : Prop} : (p ∨ q) ∨ r ↔ p ∨ q ∨ r := Iff.intro
  (λ h => by cases h with
    | inl h => cases h <;> simp_all
    | inr h => simp_all)
  (λ h => by cases h with
    | inl h => simp_all
    | inr h => cases h <;> simp_all)

theorem Prod.eq {α : Type u} {a b c d : α} (h₁ : a = c) (h₂ : b = d) :
  (a, b) = (c, d) := h₁ ▸ h₂ ▸ rfl

theorem Nat.eq_of_le_of_le {a b : Nat} (h : a ≤ b) (h' : b ≤ a) : a = b :=
  match Nat.eq_or_lt_of_le h with
  | Or.inl p => p
  | Or.inr p => False.elim <| Nat.not_le_of_gt p h'

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

theorem Nat.lt_of_not_le {a b : Nat} (h : ¬ a ≤ b) : b < a :=
  match Nat.lt_or_ge b a with
  | Or.inl h' => h'
  | Or.inr h' => False.elim <| h h'

theorem Nat.succ_pred_of_nonzero {n : Nat} (h : n ≠ 0) : succ (pred n) = n := by
  revert h
  cases n with
  | zero => simp
  | succ n => intro; rfl

theorem Nat.lt_pred_of_succ_lt {n m : Nat} (h : succ n < m) : n < pred m := by
  apply lt_of_succ_lt_succ
  rw [succ_pred_of_nonzero]
  exact h
  intro h'
  rw [h'] at h
  exact not_lt_zero _ h

theorem Nat.zero_lt_sub {n m : Nat} (h : n < m) : 0 < m - n := by
  suffices p : ∀ k, n + k < m → k < m - n from p 0 h
  suffices p : ∀ k, n < m → n + k < m → k < m - n from λ _ => p _ h
  induction n with
  | zero => intro k _ h; rw [Nat.zero_add] at h; exact h
  | succ n rh =>
    intro k h h'
    rw [sub_succ]
    rw [succ_add] at h'
    exact lt_pred_of_succ_lt <| rh (lt_of_succ_lt h) (succ k) (lt_of_succ_lt h) h'

theorem Nat.sub_add_self {n m : Nat} (h : m ≤ n) : n - m + m = n := by
  induction m with
  | zero => rfl
  | succ m rh =>
    rw [add_succ, sub_succ, ← succ_add]
    by_cases p : n - m = 0
    focus
      have p' := zero_lt_sub h
      rw [p] at p'
      exact False.elim <| Nat.not_lt_self _ p'
    focus
      rw [succ_pred_of_nonzero p]
      apply rh
      exact Nat.le_of_lt <| Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h

theorem Nat.lt_of_add_lt_add {n m : Nat} (k : Nat) (h : n + k < m + k) : n < m := by
  induction k with
  | zero => exact h
  | succ k rh =>
    apply rh ∘ lt_of_succ_lt_succ
    simp_all [add_succ]

def List.mem (a : α) : (l : List α) → Prop
  | [] => False
  | x :: t => a = x ∨ mem a t

theorem List.mem_append {α : Type u} {x : α} {l₁ l₂ : List α} :
  List.mem x (l₁ ++ l₂) ↔ List.mem x l₁ ∨ List.mem x l₂ := by
  apply Iff.intro
  focus
    induction l₁ with
    | nil => simp [List.append]; exact Or.inr
    | cons y t =>
      by_cases h' : x = y
      <;> simp [h', List.append, List.mem]
      <;> assumption
  focus
    intro h
    induction l₁ with
    | nil => simp_all [List.mem, List.append]
    | cons y t t_h =>
      match h with
      | Or.inl h =>
        by_cases h' : x = y <;> simp [h', List.append, List.mem]
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
      by_cases p : y = f x
      focus
        exact ⟨ x, by simp [List.mem, p] ⟩
      focus
        let ⟨ z, h ⟩ := rh (by simp [List.mem, p] at h; assumption)
        apply Exists.intro z
        exact ⟨ Or.inr h.1, h.2 ⟩
  focus
    exact λ ⟨ x, ⟨ h₁, h₂ ⟩ ⟩ => h₂ ▸ List.mem_map h₁

private def internal (p : α → Bool) : List α → List α → List α
  | [],    rs => rs
  | a::as, rs => match p a with
     | true  => internal p as (a::rs)
     | false => internal p as rs

private theorem append_eq (a : α) (l : List α) : a :: l = [a] ++ l := rfl

private theorem append_eq' (l : List α) : l ++ [] = l := by
  induction l with
  | nil => rfl
  | cons a l rh => rw [append_eq, List.append_assoc, rh]

private theorem internal_eq₁ (p : α → Bool) (as rs : List α) :
  internal p as rs = internal p as [] ++ rs := by
  induction as generalizing rs with
  | nil => rfl
  | cons a as rh =>
    simp only [internal]
    cases p a <;> simp only [rh rs, rh (a :: rs), rh [a]]
    rw [append_eq a rs, ← List.append_assoc]

private theorem internal_eq₂ (p : α → Bool) (as rs : List α) (a : α) :
  internal p (a :: as) rs = internal p []
    (internal p as [] ++ (if p a then [a] else []) ++ rs) := by
  induction as generalizing a rs with
  | nil =>
    simp only [internal]
    cases p a <;> simp
  | cons b as rh =>
    simp only [internal]
    cases h : p a <;> cases p b <;> conv => simp_match; simp_match
      <;> simp only [if_pos, if_neg]
      <;> simp only [internal_eq₁ _ _ rs, internal_eq₁ _ _ [b],
        internal_eq₁ _ _ (b :: rs), internal_eq₁ _ _ (a :: rs),
        internal_eq₁ _ _ (b :: a :: rs)]
      <;> simp only [append_eq a rs, append_eq b rs, append_eq b ([a] ++ rs)]
      <;> simp only [← List.append_assoc, append_eq']

private theorem List.filterAux_eq₁ (p : α → Bool) (as rs : List α) :
  filterAux p as rs = reverse (internal p as rs) := by
  induction as generalizing rs with
  | nil => rfl
  | cons a as rha =>
    induction rs
      <;> simp only [filterAux, internal]
      <;> cases p a <;> simp [rha]

private theorem List.filterAux_eq₂ (p : α → Bool) (as : List α) (a : α) :
  filterAux p (a :: as) [] = (if p a then [a] else []) ++ reverse (internal p as []) := by
  suffices h : filterAux p (a :: as) [] =
    reverse (internal p as [] ++ (if p a then [a] else [])) by
    rw [reverse_append] at h
    revert h
    cases p a <;> conv => simp_match <;> simp only [if_pos, if_neg]
      <;> exact id
  rw [filterAux_eq₁]
  simp only [internal]
  cases p a <;> conv => simp_match <;> simp only [if_pos, if_neg, internal_eq₁ _ _ [a]]
    <;> simp [append_eq', if_pos]

theorem List.filter_eq {α : Type u} {f : α → Bool} {l : List α} {a : α} :
  filter f (a :: l) = if f a then a :: filter f l else filter f l := by
  simp only [filter]
  rw [filterAux_eq₂, filterAux_eq₁]
  cases f a <;> simp only [if_pos, if_neg]
  rfl
  rw [← append_eq]

theorem List.mem_filter {α : Type u} {f : α → Bool} {l : List α} {x : α} :
  List.mem x (List.filter f l) ↔ List.mem x l ∧ f x := by
  induction l with
  | nil => simp [mem]
  | cons y t rh =>
    by_cases p : f y
    focus
      by_cases p' : x = y
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

theorem List.length_filter (l : List α) (f : α → Bool) :
  List.length (List.filter f l) ≤ List.length l := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a t rh =>
    rw [List.filter_eq]
    by_cases p : f a = true
    exact if_pos p ▸ Nat.succ_le_succ rh
    exact if_neg p ▸ Nat.le_trans rh (Nat.le_of_lt <| Nat.lt_succ_self _)

private def strong_induction_length {α : Type u} {C : List α → Prop} (a : List α)
  (step : ∀ (x : List α),
    (∀ (y : List α), List.length y < List.length x → C y) → C x) : C a :=
  (measure List.length).wf.induction _ step

theorem List.filter_mem_length_le {l : List α} {a : α} (h : List.mem a l) :
  List.length (List.filter (λ b => b ≠ a) l) + 1 ≤ List.length l := by
  induction l using strong_induction_length with
  | step l rh =>
    cases l with
    | nil => exact False.elim h
    | cons b t =>
      rw [List.filter_eq]
      by_cases p : decide (b ≠ a) = true
      focus
        rw [if_pos p]
        apply Nat.succ_le_succ
        apply rh _ (Nat.lt_succ_self _)
        exact match h with
        | Or.inl h => False.elim <| (of_decide_eq_true p).symm h
        | Or.inr h => h
      focus
        rw [if_neg p]
        exact Nat.succ_le_succ <| List.length_filter _ _

def List.included {α : Type u} (l₁ l₂ : List α) :=
  ∀ a, List.mem a l₁ → List.mem a l₂

def List.concat_map {α β : Type u} (f : α → List β) : List α → List β
| [] => []
| x :: t => List.append (f x) (concat_map f t)

end

section /- Let's define the minimim of a nonempty set in `ℕ`... -/

set_option codegen false

private theorem rev_bounded_wf (M : Nat) : WellFounded λ m n => n < m ∧ n ≤ M ∧ m ≤ M := by
  suffices p : WellFounded λ m n => M - m < M - n ∧ n ≤ M ∧ m ≤ M by
    apply Subrelation.wf _ p
    intro m n ⟨ h, nM, mM ⟩
    apply And.intro _ ⟨ nM, mM ⟩
    apply Nat.lt_of_add_lt_add (n + m)
    conv => lhs; rw [Nat.add_comm n m, ← Nat.add_assoc]
    rw [← Nat.add_assoc]
    rw [Nat.sub_add_self nM, Nat.sub_add_self mM]
    exact Nat.add_lt_add_left h _
  suffices p : WellFounded λ m n : Nat => m < n by
    let p := InvImage.wf (λ n => M - n) p
    apply Subrelation.wf _ p
    intro m n ⟨ h, _, _ ⟩
    simp only [InvImage]
    exact h
  have p : (λ m n : Nat => m < n) = Nat.lt := by funext _ _; rfl
  rw [p]
  exact Nat.lt_wfRel.wf

def set_min (P : Nat → Prop) (h : ∃ n, P n) : Nat :=
  go 0
  where
    P' := λ n => ∃ k, k ≤ n ∧ P k
    goF (n : Nat) (f : (m : Nat) → ¬ (∃ k, k ≤ n ∧ P k) ∧ m = n + 1 → Nat) : Nat :=
      if h : ∃ k, k ≤ n ∧ P k then n else f (n + 1) ⟨ h, rfl ⟩
    go := @WellFounded.fix Nat (λ _ => Nat) _ (match h with
      | ⟨ M, hM ⟩ => by
        suffices p : WellFounded λ m n => m = n + 1 ∧ m ≤ M by
          apply Subrelation.wf _ p
          intro n m ⟨ p, h ⟩
          apply And.intro h
          apply byContradiction
          intro h'
          apply p ⟨ M, _, hM ⟩
          have h' := Nat.lt_of_not_le h'
          rw [h] at h'
          exact Nat.le_of_lt_succ h'
        suffices p : WellFounded λ m n => n < m ∧ n ≤ M ∧ m ≤ M by
          apply Subrelation.wf _ p
          intro n m ⟨ h, h' ⟩
          apply And.intro _ (And.intro _ h')
          focus
            rw [h]
            exact Nat.lt_succ_self _
          focus
            apply Nat.le_trans (Nat.le_of_lt <| Nat.lt_succ_self m)
            rw [← Nat.add_one, ← h]
            exact h'
        exact rev_bounded_wf _
        ) goF

private theorem go_eq (P : Nat → Prop) (h : ∃ n, P n) (n : Nat) (h' : ∀ k, k < n → ¬ P k) :
  set_min.go P h n = if P n then n else set_min.go P h (n + 1) := by
  simp only [set_min.go]
  rw [WellFounded.fix_eq]
  simp only [set_min.goF]
  suffices p : (∃ k, k ≤ n ∧ P k) = P n by rw [p]; rfl
  apply propext
  apply Iff.intro _ λ h => ⟨ n, Nat.le_refl _, h ⟩
  focus
    intro ⟨ k, h₁, h₂ ⟩
    suffices p : k = n by rw [p.symm]; exact h₂
    exact match Nat.eq_or_lt_of_le h₁ with
    | Or.inl h => h
    | Or.inr h => False.elim <| h' k h h₂

private theorem go_eq₂ (P : Nat → Prop) (h : ∃ n, P n) {M : Nat}
  (h' : ∀ n, n < M → ¬ P n) : set_min P h = set_min.go P h M := by
  simp only [set_min]
  induction M with
  | zero => rfl
  | succ M rh =>
    suffices p : ∀ n, n < M → ¬ P n by
      rw [rh p]
      rw [go_eq _ _ _ p]
      simp [h' M (Nat.lt_succ_self _)]
    exact λ _ h => h' _ <| Nat.lt_trans h (Nat.lt_succ_self _)

private theorem go_spec (P : Nat → Prop) (h : ∃ n, P n) (m : Nat)
  (h' : m ≤ set_min P h) : ∀ n, n < m → ¬ P n := by
  induction m with
  | zero => intro; simp [Nat.not_lt_zero]
  | succ k rh =>
    intro n
    intro h₁
    have p : k < set_min P h := h'
    specialize rh (Nat.le_of_lt p)
    rw [go_eq₂ _ _ rh, go_eq _ _ k rh] at p
    suffices p' : ¬ P k by
      match Nat.eq_or_lt_of_le <| Nat.le_of_lt_succ h₁ with
      | Or.inl h₁ => rw [h₁]; exact p'
      | Or.inr h₁ => exact rh _ h₁
    by_cases p' : P k
    focus
      apply False.elim ∘ Nat.not_lt_self k
      simp_all [p']
    focus
      exact p'

theorem eq_set_min (P : Nat → Prop) (h : ∃ n, P n) {M : Nat}
  (h₁ : P M) (h₂ : ∀ n, n < M → ¬ P n) : M = set_min P h := by
  rw [go_eq₂ _ _ h₂, go_eq _ _ _ h₂]
  simp [h₁]

theorem rev_induction (M : Nat) {C : Nat → Prop} (n : Nat)
  (ind : ∀ m, (∀ n, m < n ∧ m ≤ M ∧ n ≤ M → C n) → C m) : C n :=
  (rev_bounded_wf M).induction n ind

theorem set_min_spec₀ (P : Nat → Prop) (h : ∃ n, P n) {m : Nat}
  (h' : ∀ n, n < m → ¬ P n) : m ≤ set_min P h := match h with
  | ⟨ M, hM ⟩ => by
    apply @rev_induction M (λ m => (∀ n, n < m → ¬ P n) → m ≤ set_min P h) m _ h'
    intro m rh h'
    rw [go_eq₂ P h h', go_eq P h _ h']
    by_cases p : P m
    focus
      simp [p, Nat.le_refl]
    focus
      rw [show (if P m then m else set_min.go P h (m + 1))
        = set_min.go P h (m + 1) by simp [p]]
      apply Nat.le_trans (Nat.le_of_lt <| Nat.lt_succ_self m)
      suffices p : ∀ n, n < m + 1 → ¬ P n by
        rw [← go_eq₂ P h p]
        apply rh _ _ p
        apply And.intro (Nat.lt_succ_self m)
        suffices p : m + 1 ≤ M from
          And.intro (Nat.le_trans (Nat.le_of_lt <| Nat.lt_succ_self _) p) p
        match Nat.lt_or_ge M (m + 1) with
        | Or.inl p' =>
          apply False.elim
          match Nat.eq_or_lt_of_le <| Nat.le_of_lt_succ p' with
          | Or.inl p' =>
            apply p m <| Nat.lt_succ_self _
            rw [← p']
            exact hM
          | Or.inr p' => exact h' _ p' hM
        | Or.inr p' => exact p'
      intro n h
      match Nat.eq_or_lt_of_le <| Nat.le_of_lt_succ h with
      | Or.inl p' => rw [p']; exact p
      | Or.inr p' => exact h' _ p'

theorem set_min_spec₁ (P : Nat → Prop) (h : ∃ n, P n) : P (set_min P h) := by
  apply byContradiction
  intro h'
  suffices p : set_min P h + 1 ≤ set_min P h from Nat.not_lt_self _ p
  apply set_min_spec₀
  intro n h''
  exact match Nat.eq_or_lt_of_le <| Nat.le_of_lt_succ h'' with
  | Or.inl h'' => h'' ▸ h'
  | Or.inr h'' => go_spec P h (n + 1) h'' _ (Nat.lt_succ_self _)

theorem set_min_spec₂ (P : Nat → Prop) (h : ∃ n, P n) : ∀ n, P n → set_min P h ≤ n := by
  intro n h'
  match Nat.lt_or_ge n (set_min P h) with
  | Or.inl p =>
    apply False.elim ∘ (λ p' : ¬ P n => p' h')
    exact go_spec P h (n + 1) p _ (Nat.lt_succ_self n)
  | Or.inr p => exact p

theorem set_min_le_of_included {P Q : Nat → Prop} (hP : ∃ n, P n) (hQ : ∃ n, Q n)
  (h : ∀ n, P n → Q n) : set_min Q hQ ≤ set_min P hP := by
  apply set_min_spec₀
  intro n h' p
  apply Nat.not_lt_self _ ∘ Nat.lt_of_lt_of_le h'
  apply set_min_spec₂
  exact h _ p

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

def mk (l : List α) : Fintype α := Quotient.mk' l

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
  have p := h₁ a
  simp [List.mem_append, h₁ a, h₂ a]

instance : HasUnion (Fintype α) where
  union := Fintype.union

theorem union_spec (l₁ l₂ : List α) : Fintype.mk l₁ ∪ Fintype.mk l₂ = mk (List.append l₁ l₂) := rfl

theorem mem_union_iff (x y : Fintype α) (a : α) : a ∈ x ∪ y ↔ a ∈ x ∨ a ∈ y := by
  suffices h : ∀ l₁ l₂, a ∈ (mk l₁) ∪ (mk l₂) ↔ a ∈ (mk l₁) ∨ a ∈ (mk l₂)
  from @Quotient.inductionOn₂ _ _ _ _ (λ x y : Fintype α => a ∈ x ∪ y ↔ a ∈ x ∨ a ∈ y) x y h
  intro l₁ l₂
  -- I'm not really convinced by the look of this proof :/
  rw [show (a ∈ (Fintype.mk l₁) ∪ (Fintype.mk l₂)) = List.mem a (List.append l₁ l₂) from rfl]
  simp [List.mem_append, Fintype.mem_mk_iff]

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
    simp only [mk, Quotient.mk'] at p
    rw [p]
    rw [List.mem_filter, show Quotient.mk _ l = mk l from rfl, mem_mk_iff]
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

private theorem mem_image_fold {β : Type u} (f : α → Fintype β) (l₁ : List α) (a : α)
  (h : List.mem a l₁) : f a ⊆ (List.foldr (λ a x => f a ∪ x) ∅ l₁) := by
  induction l₁ with
  | nil => apply False.elim h
  | cons x t rh =>
    simp only [List.foldr]
    by_cases p : a = x
    focus
      rw [p]
      exact included_union_r _ included_refl
    focus
      apply included_union_l
      apply rh
      simp_all [List.mem]

def image {β : Type u} (f : α → Fintype β) : Fintype α → Fintype β :=
  Quotient.lift (λ l => List.foldr (λ a x => f a ∪ x) ∅ l) <| by
  suffices p : ∀ l₁ l₂, (∀ a, List.mem a l₁ → List.mem a l₂) →
    List.foldr (λ a x => f a ∪ x) ∅ l₁ ⊆ List.foldr (λ a x => f a ∪ x) ∅ l₂ by
    intro l₁ l₂ h
    rw [ext]
    intro a
    apply Iff.intro (p l₁ l₂ _ _) (p l₂ l₁ _ _) <;> first
      | intro b
        rw [h]
        exact id
  intro l₁ l₂ h
  induction l₁ with
  | nil => exact empty_included _
  | cons x t rh =>
    apply union_included_iff.2 (And.intro _ _)
    focus
      apply mem_image_fold
      apply h
      simp [List.mem]
    focus
      apply rh
      intro a h'
      apply h
      simp [List.mem, h']

theorem in_image_of_is_image {β : Type u} {f : α → Fintype β} {a : α}
  {x : Fintype α} : a ∈ x → f a ⊆ image f x := by
  apply @Quotient.inductionOn _ _ (λ x : Fintype α => a ∈ x → f a ⊆ image f x) x
  intro l
  apply mem_image_fold

theorem image_in_of_all_in {β : Type u} {f : α → Fintype β} {x : Fintype α}
  {A : Fintype β} : (∀ a, a ∈ x → f a ⊆ A) → image f x ⊆ A := by
  apply @Quotient.inductionOn _ _
    (λ x : Fintype α => (∀ a, a ∈ x → f a ⊆ A) → image f x ⊆ A) x
  intro l h
  induction l with
  | nil => exact empty_included _
  | cons x t rh =>
    apply union_included_iff.2 (And.intro _ _)
    focus
      apply h
      suffices p : x ∈ mk (x :: t) from p
      simp [mem_mk_iff, List.mem]
    focus
      exact rh <| λ a h' => h _ <| Or.inr h'

theorem mem_image_iff {β : Type u} {f : α → Fintype β} {x : Fintype α} {b : β} :
  b ∈ image f x ↔ ∃ a, a ∈ x ∧ b ∈ f a := by
  apply Iff.intro
  focus
    intro h
    apply byContradiction
    intro h'
    have h'' : ∀ a, a ∈ x → f a ⊆ image f x \ mk [b] := by
      intro a h
      apply included_trans _
        (included_without_of_included (mk [b]) (in_image_of_is_image h))
      rw [← not_mem_iff_in_without]
      intro h''
      exact h' ⟨ a, h, h'' ⟩
    suffices p : ¬ b ∈ image f x from p h
    rw [not_mem_iff_in_without]
    exact image_in_of_all_in h''
  focus
    intro ⟨ a, h, h' ⟩
    rw [mem_iff_singleton_included]
    apply included_trans _ (in_image_of_is_image h)
    rw [← mem_iff_singleton_included]
    exact h'

section Size

set_option codegen false in
def size (x : Fintype α) := set_min
  (λ n => ∃ l, n = List.length l ∧ x ⊆ mk l) <| by
  apply @Quotient.inductionOn _ _
    (λ x : Fintype α => ∃ n, ∃ l, n = List.length l ∧ x ⊆ mk l)
  exact λ l => ⟨ List.length l, l, rfl, λ _ => id ⟩

theorem size_spec (x : Fintype α) : ∃ l, size x = List.length l ∧ x ⊆ mk l :=
  set_min_spec₁ (λ n => ∃ l, n = List.length l ∧ ∀ a : α, a ∈ x → List.mem a l) _

theorem size_mk_le (l : List α) : size (mk l) ≤ List.length l :=
  set_min_spec₂ _ _ _ ⟨ l, rfl, λ _ => id ⟩

theorem size_le_of_included {x y : Fintype α} (h : x ⊆ y) : size x ≤ size y := by
  apply set_min_le_of_included ⟨ size y, size_spec y ⟩ ⟨ size x, size_spec x ⟩
  intro n ⟨ l, l_length, hl ⟩
  let ⟨ l', l'_length, hl' ⟩ := size_spec x
  apply Exists.intro l
  apply And.intro l_length
  intro a h'
  exact hl a <| h a h'

theorem length_le_size {x : Fintype α} {l : List α} (h : x ⊆ mk l) :
  size x ≤ List.length l :=
  Nat.le_trans (size_le_of_included h) (size_mk_le _)

theorem le_size_of_all_le_length {x : Fintype α} {n : Nat}
  (h : ∀ l : List α, x ⊆ mk l → n ≤ List.length l) : n ≤ size x := by
  have ⟨ l', l'_length, h' ⟩ := size_spec x
  rw [l'_length]
  exact h _ h'

theorem length_le_of_included {x : Fintype α} {l : List α} (h : x ⊆ mk l) :
  size x ≤ List.length l :=
  Nat.le_trans (size_le_of_included h) (size_mk_le l)

theorem size_union_not_contained_le {x : Fintype α} {l : List α} {a : α}
  (h₁ : mk [a] ∪ x ⊆ mk l) (h₂ : ¬ a ∈ x) : size x + 1 ≤ List.length l := by
  have p : List.mem a l := by
    rw [union_included_iff] at h₁
    apply h₁.1
    simp [mem_mk_iff, List.mem]
  apply Nat.le_trans _ (List.filter_mem_length_le p)
  apply Nat.add_le_add_right
  apply length_le_of_included
  intro b h'
  rw [mem_mk_iff, List.mem_filter]
  apply And.intro
  focus
    exact h₁ _ ∘ (mem_union_iff _ _ _).2 ∘ Or.inr <| h'
  focus
    apply decide_eq_true
    intro h
    apply h₂
    rw [← h]
    exact h'

theorem size_succ_of_union_not_included {x : Fintype α} {a : α} (h : ¬ a ∈ x) :
  size (mk [a] ∪ x) = size x + 1 := by
  apply Nat.eq_of_le_of_le
  focus
    have ⟨ l, l_length, hl ⟩ := size_spec x
    rw [l_length]
    have p : mk [a] ∪ x ⊆ mk [a] ∪ mk l := by
      apply union_included_iff.2 (And.intro _ _)
      exact included_union_r _ included_refl
      exact included_union_l _ hl
    apply Nat.le_trans (size_le_of_included p)
    rw [union_spec]
    apply Nat.le_trans (size_mk_le _)
    exact Nat.le_refl _
  focus
    exact le_size_of_all_le_length <| λ l h' => Nat.le_trans
      (size_union_not_contained_le h' h)
      (Nat.le_refl _)

theorem eq_of_contained_of_same_size {x y : Fintype α} (h : x ⊆ y)
  (h' : size x = size y) : x = y := by
  rw [ext]
  intro a
  apply Iff.intro (h a)
  intro a_in_y
  apply byContradiction
  intro p
  suffices p : size x < size y from Nat.ne_of_lt p h'
  have p' : mk [a] ∪ x ⊆ y := by
    intro b h'
    match (mem_union_iff _ _ _).1 h' with
    | Or.inl h' =>
      suffices p : b = a by rw [p]; exact a_in_y
      simp_all [mem_mk_iff, List.mem]
    | Or.inr h' => exact h _ h'
  apply Nat.lt_of_lt_of_le _ (size_le_of_included p')
  rw [size_succ_of_union_not_included p]
  exact Nat.lt_succ_self _

end Size

def included_wfRel : WellFoundedRelation (Fintype α) where
  rel x y := x ⊆ y ∧ x ≠ y
  wf := by
    apply @Subrelation.wf _ (measure size).rel _ _
    focus
      exact (measure size).wf
    focus
      intro x y ⟨ h, h' ⟩
      suffices p : size x < size y from p
      apply Nat.lt_of_le_of_ne (size_le_of_included h)
      intro h''
      exact h' <| eq_of_contained_of_same_size h h''

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
      rw [← p₁]
      simp [List.filterMap, List.mem, p₂]
    | Or.inr p₁ => by_cases h : P x
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
      by_cases p : a = x
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
private noncomputable def sec {α β : Type u} (f : α → β) (b : {b // ∃ a, b = f a}) : α :=
  @epsilon _ (nonempty_of_exists b.2) (λ a => b = f a)

private def sec_image {α β : Type u} (f : α → β) : ∀ (b : {b // ∃ a, b = f a}), f (sec f b) = b := by
  intro ⟨ b, p@⟨ a, h ⟩ ⟩
  simp [sec]
  rw [← epsilon_spec p]

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
  let ⟨ l₁, h₁ ⟩ := h₁
  let ⟨ l₂, h₂ ⟩ := h₂
  apply Exists.intro (List.map Sum.inl l₁ ++ List.map Sum.inr l₂)
  intro x
  rw [List.mem_append]
  exact match x with
  | Sum.inl a => Or.inl <| List.mem_map <| h₁ a
  | Sum.inr b => Or.inr <| List.mem_map <| h₂ b

end Sums

end Finite
