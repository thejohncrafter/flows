
import MyPackage.Base

infix:70 " • " => RSMul.smul
infix:50 " ∈ " => HasMem.mem
infixl:60 " ∪ " => HasUnion.union
infix:50 " ⊆ " => HasIncluded.included
infixl:65 " \\ " => HasWithout.without
notation:max "𝒱 " a:arg => HasVehicle.vehicle a
