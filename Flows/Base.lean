/-
Copyright (c) 2021 Julien Marquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Marquet
-/

import Lean

class RSMul (χ α : Type u) where
  smul : χ → α → χ

class HasMem (χ α : Type u) where
  mem : χ → α → Prop

class HasUnion (α : Type u) where
  union : α → α → α

class HasIncluded (α : Type u) where
  included : α → α → Prop

class HasWithout (α : Type u) where
  without : α → α → α

class HasVehicle (α β : Type u) where
  vehicle : α → β
