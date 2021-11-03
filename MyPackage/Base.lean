
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
  without : α → α → Prop

class HasVehicle (α β : Type u) where
  vehicle : α → β
