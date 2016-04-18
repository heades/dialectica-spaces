-----------------------------------------------------------------------
-- Definitions of concrete colineales.                               --
-----------------------------------------------------------------------

module concrete-colineales where

open import prelude
open import colineale

-----------------------------------------------------------------------
-- The lineale 3                                                     --
-----------------------------------------------------------------------

data Three : Set where
  zero : Three
  half : Three
  one : Three

_≤3_ : Three → Three → Set
half ≤3 zero = ⊥
one ≤3 zero = ⊥
one ≤3 half = ⊥
_ ≤3 _ = ⊤


isProset3 : Proset Three
isProset3 = MkProset _≤3_ (λ {a} → aux₁ {a}) (λ{a b c} → aux₂ {a}{b}{c})
 where
   aux₁ : {a : Three} → a ≤3 a
   aux₁ {zero} = triv
   aux₁ {half} = triv
   aux₁ {one} = triv   

   aux₂ : {a b c : Three} → a ≤3 b → b ≤3 c → a ≤3 c
   aux₂ {zero} {zero} {zero} p₁ p₂ = triv
   aux₂ {zero} {zero} {half} p₁ p₂ = triv
   aux₂ {zero} {zero} {one} p₁ p₂ = triv
   aux₂ {zero} {half} {zero} p₁ p₂ = triv
   aux₂ {zero} {half} {half} p₁ p₂ = triv
   aux₂ {zero} {half} {one} p₁ p₂ = triv
   aux₂ {zero} {one} {zero} p₁ p₂ = triv
   aux₂ {zero} {one} {half} p₁ p₂ = triv
   aux₂ {zero} {one} {one} p₁ p₂ = triv
   aux₂ {half} {zero} {zero} p₁ p₂ = p₁
   aux₂ {half} {zero} {half} p₁ p₂ = triv
   aux₂ {half} {zero} {one} p₁ p₂ = triv
   aux₂ {half} {half} {zero} p₁ p₂ = p₂
   aux₂ {half} {half} {half} p₁ p₂ = triv
   aux₂ {half} {half} {one} p₁ p₂ = triv
   aux₂ {half} {one} {zero} p₁ p₂ = p₂
   aux₂ {half} {one} {half} p₁ p₂ = triv
   aux₂ {half} {one} {one} p₁ p₂ = triv
   aux₂ {one} {zero} {zero} p₁ p₂ = p₁
   aux₂ {one} {zero} {half} p₁ p₂ = p₁
   aux₂ {one} {zero} {one} p₁ p₂ = triv
   aux₂ {one} {half} {zero} p₁ p₂ = p₂
   aux₂ {one} {half} {half} p₁ p₂ = p₁
   aux₂ {one} {half} {one} p₁ p₂ = p₂
   aux₂ {one} {one} {zero} p₁ p₂ = p₂
   aux₂ {one} {one} {half} p₁ p₂ = p₂
   aux₂ {one} {one} {one} p₁ p₂ = triv


-- Now we define the three element proper colineale; co-intuitionistic and
-- linear:

_⊕3_ : Three → Three → Three
zero ⊕3 zero = zero
zero ⊕3 one = one
one ⊕3 zero = one
one ⊕3 one = one
zero ⊕3 half = zero
half ⊕3 zero = zero
half ⊕3 half = half
half ⊕3 one = one
one ⊕3 half = one

symm3 : {a b : Three} → a ⊕3 b ≡ b ⊕3 a
symm3 {zero} {zero} = refl
symm3 {zero} {half} = refl
symm3 {zero} {one} = refl
symm3 {half} {zero} = refl
symm3 {half} {half} = refl
symm3 {half} {one} = refl
symm3 {one} {zero} = refl
symm3 {one} {half} = refl
symm3 {one} {one} = refl

isMonProset3 : MonProset Three
isMonProset3 = MkMonProset _⊕3_ half isProset3 (λ {a b c} → assoc3 {a}{b}{c}) left-ident3 right-ident3 (λ {a b} → symm3 {a}{b}) (λ {a b} → comp3 {a}{b})
 where
   assoc3 : {a b c : Three} → a ⊕3 (b ⊕3 c) ≡ (a ⊕3 b) ⊕3 c
   assoc3 {zero} {zero} {zero} = refl
   assoc3 {zero} {zero} {half} = refl
   assoc3 {zero} {zero} {one} = refl
   assoc3 {zero} {half} {zero} = refl
   assoc3 {zero} {half} {half} = refl
   assoc3 {zero} {half} {one} = refl
   assoc3 {zero} {one} {zero} = refl
   assoc3 {zero} {one} {half} = refl
   assoc3 {zero} {one} {one} = refl
   assoc3 {half} {zero} {zero} = refl
   assoc3 {half} {zero} {half} = refl
   assoc3 {half} {zero} {one} = refl
   assoc3 {half} {half} {zero} = refl
   assoc3 {half} {half} {half} = refl
   assoc3 {half} {half} {one} = refl
   assoc3 {half} {one} {zero} = refl
   assoc3 {half} {one} {half} = refl
   assoc3 {half} {one} {one} = refl
   assoc3 {one} {zero} {zero} = refl
   assoc3 {one} {zero} {half} = refl
   assoc3 {one} {zero} {one} = refl
   assoc3 {one} {half} {zero} = refl
   assoc3 {one} {half} {half} = refl
   assoc3 {one} {half} {one} = refl
   assoc3 {one} {one} {zero} = refl
   assoc3 {one} {one} {half} = refl
   assoc3 {one} {one} {one} = refl

   left-ident3 : {a : Three} → half ⊕3 a ≡ a
   left-ident3 {zero} = refl
   left-ident3 {half} = refl
   left-ident3 {one} = refl

   right-ident3 : {a : Three} → a ⊕3 half ≡ a
   right-ident3 {zero} = refl
   right-ident3 {half} = refl
   right-ident3 {one} = refl   

   comp3 : {a b : Three} → a ≤3 b → {c : Three} → (a ⊕3 c) ≤3 (b ⊕3 c)
   comp3 {zero} {zero} x {zero} = triv
   comp3 {zero} {zero} x {half} = triv
   comp3 {zero} {zero} x {one} = triv
   comp3 {zero} {half} x {zero} = triv
   comp3 {zero} {half} x {half} = triv
   comp3 {zero} {half} x {one} = triv
   comp3 {zero} {one} x {zero} = triv
   comp3 {zero} {one} x {half} = triv
   comp3 {zero} {one} x {one} = triv
   comp3 {half} {zero} x {zero} = triv
   comp3 {half} {zero} x {half} = x
   comp3 {half} {zero} x {one} = triv
   comp3 {half} {half} x {zero} = triv
   comp3 {half} {half} x {half} = triv
   comp3 {half} {half} x {one} = triv
   comp3 {half} {one} x {zero} = triv
   comp3 {half} {one} x {half} = triv
   comp3 {half} {one} x {one} = triv
   comp3 {one} {zero} x {zero} = x
   comp3 {one} {zero} x {half} = x
   comp3 {one} {zero} x {one} = triv
   comp3 {one} {half} x {zero} = x
   comp3 {one} {half} x {half} = x
   comp3 {one} {half} x {one} = triv
   comp3 {one} {one} x {zero} = triv
   comp3 {one} {one} x {half} = triv
   comp3 {one} {one} x {one} = triv

_-_ : Three → Three → Three
zero - zero = zero
zero - one = one
one - zero = zero
one - one = zero
half - zero = one
zero - half = one
half - one = one
half - half = half
one - half = one

isColineale3 : Colineale Three
isColineale3 = MkColineale isMonProset3 _-_ aux₁ (λ {a b c} → aux₂ {a}{b}{c})
 where
  aux₁ : (a b : Three) → b ≤3 (a ⊕3 (a - b))
  aux₁ zero zero = triv
  aux₁ zero half = triv
  aux₁ zero one = triv
  aux₁ half zero = triv
  aux₁ half half = triv
  aux₁ half one = triv
  aux₁ one zero = triv
  aux₁ one half = triv
  aux₁ one one = triv

  aux₂ : {a b c : Three} → (b - c) ≤3 a → c ≤3 (a ⊕3 b)
  aux₂ {zero} {zero} {zero} x = triv
  aux₂ {zero} {zero} {half} x = x
  aux₂ {zero} {zero} {one} x = x
  aux₂ {zero} {half} {zero} x = triv
  aux₂ {zero} {half} {half} x = x
  aux₂ {zero} {half} {one} x = x
  aux₂ {zero} {one} {zero} x = triv
  aux₂ {zero} {one} {half} x = triv
  aux₂ {zero} {one} {one} x = triv
  aux₂ {half} {zero} {zero} x = triv
  aux₂ {half} {zero} {half} x = x
  aux₂ {half} {zero} {one} x = x
  aux₂ {half} {half} {zero} x = triv
  aux₂ {half} {half} {half} x = triv
  aux₂ {half} {half} {one} x = x
  aux₂ {half} {one} {zero} x = triv
  aux₂ {half} {one} {half} x = triv
  aux₂ {half} {one} {one} x = triv
  aux₂ {one} {zero} {zero} x = triv
  aux₂ {one} {zero} {half} x = triv
  aux₂ {one} {zero} {one} x = triv
  aux₂ {one} {half} {zero} x = triv
  aux₂ {one} {half} {half} x = triv
  aux₂ {one} {half} {one} x = triv
  aux₂ {one} {one} {zero} x = triv
  aux₂ {one} {one} {half} x = triv
  aux₂ {one} {one} {one} x = triv
