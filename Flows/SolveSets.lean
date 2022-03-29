/-
Copyright (c) 2021-2022 Julien Marquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Marquet
-/

import Lean.Elab.Tactic.Basic

import Flows.Groundwork

open Lean Parser.Tactic Elab Elab.Tactic Meta

-- From mathlib4
namespace Lean.Expr
/-- If the expression is a constant, return that name. Otherwise return `Name.anonymous`. -/
def constName (e : Expr) : Name :=
e.constName?.getD Name.anonymous

/-- Return the function (name) and arguments of an application. -/
def getAppFnArgs (e : Expr) : Name × Array Expr :=
  Expr.withApp e λ e a => (e.constName, a)

end Lean.Expr
-- End of copied block

namespace Tactic.SolveSet

section Lemmas

variable {α : Type u}

def general_union (l : List (Fintype α)) : Fintype α := List.foldl HasUnion.union ∅ l

theorem in_singleton (a : Fintype α) : a ⊆ general_union [a] :=
  Fintype.included_union_l _ Fintype.included_refl

theorem included_of_included_l (a b c : Fintype α) (h : a ⊆ b) : a ⊆ b ∪ c := sorry
theorem included_of_included_r (a b c : Fintype α) (h : a ⊆ c) : a ⊆ b ∪ c := sorry

theorem union_included (a b c : Fintype α) (h : a ⊆ c) (h' : b ⊆ c) : a ∪ b ⊆ c := sorry

end Lemmas

structure Cache :=
  α : Expr
  univ : Level

structure State :=
  atoms : Array Expr := #[]
  numAtoms : Nat := 0

inductive SetExpr : Type :=
  | void
  | atom (i : Nat)
  | union (l : SetExpr) (r : SetExpr)

instance : Inhabited SetExpr := Inhabited.mk (SetExpr.void)

abbrev SolveM := ReaderT Cache <| StateRefT State MetaM

def SolveM.run (ty : Expr) (m : SolveM α) : MetaM α := do
  let Level.succ u _ ← getLevel ty | throwError "fail"
  (m {α := ty, univ := u }).run' {}

def mkApp (f : Name) (args : Array Expr) : SolveM Expr := do
  let c ← read
  pure $ mkAppN (mkConst f [c.univ]) (#[c.α] ++ args)

def addAtom (e : Expr) : SolveM Nat := do
  let c ← get
  for i in [:c.numAtoms] do
    if ← isDefEq e c.atoms[i] then
      return i
  modify λ c => { c with atoms := c.atoms.push e, numAtoms := c.numAtoms + 1 }
  return c.numAtoms

def getAtomIndex (e : Expr) : SolveM Nat := do
  let c ← get
  for i in [:c.numAtoms] do
    if ← isDefEq e c.atoms[i] then
      return i
  throwError "Atom not found -- this is a bug"

def isAtom (e : Expr) : SolveM Bool := do
  let c ← get
  for i in [:c.numAtoms] do
    if ← isDefEq e c.atoms[i] then
      return true
  return false

def getAtom (i : Nat) : SolveM Expr := do
  let c ← get
  return c.atoms[i]

-- Assumes l and r are ordered according to their first coordinate
partial def concat_map_assocs (l r : List (Nat × Expr)) (f g : Nat → Expr → SolveM Expr) :
  SolveM (List (Nat × Expr)) := go l r [] >>= pure ∘ List.reverse
  where go l r acc :
    SolveM (List (Nat × Expr)) := match (l, r) with
    | ([], []) => pure acc
    | ([], (j, eᵣ) :: r') => do go [] r' <| (j, ← g j eᵣ) :: acc
    | ((i, eₗ) :: l', []) => do go l' [] <| (i, ← f i eₗ) :: acc
    | ((i, eₗ) :: l', (j, eᵣ) :: r') =>
      if i < j then do go l' r <| (i, ← f i eₗ) :: acc
      else if i == j then do go l' r' <| (i, ← f i eₗ) :: acc
      else do go l r' <| (j, ← g j eᵣ) :: acc

partial def atomize (e : Expr) : SolveM (List (Nat × Expr)) :=
  match e.getAppFnArgs with
  | (``EmptyCollection.emptyCollection, #[_, _]) => pure []
  | (``HasUnion.union, #[_, _, eₗ, eᵣ]) => do
    let ml ← atomize eₗ
    let mr ← atomize eᵣ
    let process_l i included : SolveM Expr := do
        let a ← getAtom i
        mkApp ``included_of_included_l #[a, eₗ, eᵣ, included]
    let process_r j included : SolveM Expr := do
        let a ← getAtom j
        mkApp ``included_of_included_r #[a, eₗ, eᵣ, included]
    return (← concat_map_assocs ml mr process_l process_r)
  | _ => do
    let i ← addAtom e
    return [(i, ← mkApp ``Fintype.included_refl #[e])]

partial def prove_included (atomics : Array Expr) (l r : Expr) : SolveM Expr :=
  go l r
  where go l r : SolveM Expr := match l.getAppFnArgs with
    | (``EmptyCollection.emptyCollection, #[_, _]) =>
      mkApp ``Fintype.empty_included #[r]
    | (``HasUnion.union, #[_, _, eₗ, eᵣ]) => do
      let pₗ ← go eₗ r
      let pᵣ ← go eᵣ r
      mkApp ``union_included #[eₗ, eᵣ, r, pₗ, pᵣ]
    | _ => do
      let i ← getAtomIndex l
      pure atomics[i]

partial def check_atoms (e : Expr) : SolveM Bool :=
  match e.getAppFnArgs with
  | (``EmptyCollection.emptyCollection, #[_, _]) => pure true
  | (``HasUnion.union, #[_, _, eₗ, eᵣ]) => do
    return (← check_atoms eₗ) && (← check_atoms eᵣ)
  | _ => isAtom e

def solve_sets (l r : Expr) : SolveM Expr := do
  let atoms := Array.mk
    <| List.map (λ x => x.2)
    <| ← atomize r
  if !(← check_atoms l) then
    throwError "Some atomic formulas on the left aren't included in the right"
  let p ← prove_included atoms l r
  return p

elab "solve_sets " : tactic => liftMetaMAtMain λ g => do
  match (← instantiateMVars (← getMVarDecl g).type).getAppFnArgs with
  | (``HasIncluded.included, #[ty, _, l, r]) =>
    let ty ← match ty.getAppFnArgs with
    | (``Fintype, #[a]) => pure a
    | _ => throwError "Expected Fintype"
    let p ← (solve_sets l r).run ty
    assignExprMVar g p
  | _ => throwError "solve_sets failed, expected an inclusion"

set_option trace.Elab.debug true in
def ex₁ (a b c : Fintype α) : ∅ ∪ b ∪ a ⊆ a ∪ ∅ ∪ b := by solve_sets

end Tactic.SolveSet
