module lineale-morphism where

open import level
open import lineale

record LM {ℓ : Level}{L₁ L₂ : Set ℓ} (pL₁ : Lineale L₁)(pL₂ : Lineale L₂) : Set (lsuc ℓ) where
 field
   func : L₁ → L₂
   p : ∀{x y : L₁} → rel (proset (mproset pL₁)) x y → rel (proset (mproset pL₂)) (func x) (func y)

