/-
Copyright (c) 2021 Julien Marquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Marquet
-/

import MyPackage.Base

infix:70 " • " => RSMul.smul
infix:50 " ∈ " => HasMem.mem
infixl:60 " ∪ " => HasUnion.union
infix:50 " ⊆ " => HasIncluded.included
infixl:65 " \\ " => HasWithout.without
notation:max "𝒱 " a:arg => HasVehicle.vehicle a
