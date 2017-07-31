module atl-lineale where

open import empty
open import unit
open import eq
open import functions

-----------------------------------------------------------------------
-- The lineale 3                                                     --
-----------------------------------------------------------------------

data Three : Set where
  zero : Three
  half : Three
  one : Three

infix 3 _≤₃_

_≤₃_ : Three → Three → Set
half ≤₃ zero = ⊥
one ≤₃ zero = ⊥
one ≤₃ half = ⊥
_ ≤₃ _ = ⊤

_⊙₃_ : Three → Three → Three
one ⊙₃ one = one
half ⊙₃ half = half
half ⊙₃ one = one
one ⊙₃ half = one
_ ⊙₃ _ = zero

_▷₃_ : Three → Three → Three
half ▷₃ half = half
half ▷₃ one = one
one ▷₃ half = half
one ▷₃ one = one
_ ▷₃ _ = zero

infix 4 _⊔₃_

_⊔₃_ : Three → Three → Three
half ⊔₃ half = half
half ⊔₃ one = half
one ⊔₃ half = half
one ⊔₃ one = one
_ ⊔₃ _ = zero
  
unit₃ = half
  
_⊸₃_ : Three → Three → Three
half ⊸₃ zero = zero
half ⊸₃ half = half
one ⊸₃ zero = zero
one ⊸₃ half = zero
_ ⊸₃ _ = one
  
_↼₃_ : Three → Three → Three
zero ↼₃ half = zero
zero ↼₃ one = zero
half ↼₃ half = half
half ↼₃ one = half
_ ↼₃ _ = one

_⇀₃_ : Three → Three → Three
half ⇀₃ zero = zero
one ⇀₃ zero = zero
one ⇀₃ half = zero
_ ⇀₃ _ = one

record Three-Morphism : Set where
  constructor TMor
  field
    func : Three → Three
    monotone-pf : ∀{x y : Three} → x ≤₃ y → (func x) ≤₃ (func y)

three-morph-comp : Three-Morphism → Three-Morphism → Three-Morphism
three-morph-comp (TMor m₁ pm₁) (TMor m₂ pm₂) = TMor (m₂ ∘ m₁) pf
 where
   pf : {x y : Three} → x ≤₃ y → (m₂ ∘ m₁) x ≤₃ (m₂ ∘ m₁) y
   pf {x}{y} p = pm₂ (pm₁ p)
