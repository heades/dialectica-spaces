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

_⊗₃_ : Three → Three → Three
half ⊗₃ half = half
half ⊗₃ one = one
one ⊗₃ half = one
one ⊗₃ one = one
_ ⊗₃ _ = zero

I₃ : Three
I₃ = half

_⊸₃_ : Three → Three → Three
half ⊸₃ zero = zero
one ⊸₃ zero = zero
one ⊸₃ half = zero
half ⊸₃ half = half
_ ⊸₃ _ = one

_⊙₃_ : Three → Three → Three
half ⊙₃ half = half
half ⊙₃ one = half
one ⊙₃ half = half
one ⊙₃ one = half
_ ⊙₃ _ = zero

_▷₃_ : Three → Three → Three
half ▷₃ one = half
one ▷₃ half = half
half ▷₃ half = half
one ▷₃ one = half
zero ▷₃ zero = zero
one ▷₃ zero = half
half ▷₃ zero = half
_ ▷₃ _ = zero

_⇀₃_ : Three → Three → Three
half ⇀₃ zero = zero
one ⇀₃ zero = zero
zero ⇀₃ zero = zero
_ ⇀₃ _ = one

infix 4 _⊔₃_

_⊔₃_ : Three → Three → Three
half ⊔₃ half = half
half ⊔₃ one = half
one ⊔₃ half = half
one ⊔₃ one = one
_ ⊔₃ _ = zero

unit₃ = half

