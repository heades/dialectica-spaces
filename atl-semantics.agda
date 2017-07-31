module atl-semantics where

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
zero ⊙₃ zero = half
zero ⊙₃ half = half
half ⊙₃ zero = half
half ⊙₃ half = half
_ ⊙₃ _ = one

_▷₃_ : Three → Three → Three
zero ▷₃ one = one
half ▷₃ one = one
one ▷₃ one = one
_ ▷₃ _ = half

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

