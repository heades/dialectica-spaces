----------------------------------------------------------------
-- This module defines Biclosed Posets which are essentially  --
-- non-commutative lineales with two implications.            --
----------------------------------------------------------------
module biclosed-poset where

open import prelude

record Poset {ℓ : Level}(A : Set ℓ) : Set (lsuc ℓ) where
 constructor MkPoset
 field
   rel : A → A → Set
   prefl : ∀{a : A} → rel a a
   ptrans : ∀{a b c : A} → rel a b → rel b c → rel a c
   pasymm : ∀{a b c : A} → rel a b → rel b a → a ≡ b

open Poset public

-- Ordered Non-commutative Monoid:
record ONCMonoid {ℓ : Level}(P : Set ℓ) : Set (lsuc ℓ) where
 constructor MkONCMonoid
 field
   mul : P → P → P
   unit : P
   
   poset : Poset P
   assoc : ∀{a b c : P} → mul a (mul b c) ≡ mul (mul a b) c
   left-ident : ∀{a : P} → mul unit a ≡ a
   right-ident : ∀{a : P} → mul a unit ≡ a
   compat-l : ∀{a b : P} → (rel poset) a b → (∀{c : P} → (rel poset) (mul c a) (mul c b))
   compat-r : ∀{a b : P} → (rel poset) a b → (∀{c : P} → (rel poset) (mul a c) (mul b c))

open ONCMonoid public

record BiclosedPoset {ℓ : Level}(L : Set ℓ) : Set (lsuc ℓ) where
 constructor MkLineale
 field
   oncMonoid : ONCMonoid L
   l-imp : L → L → L -- a ⇀ b = l-imp a b
   r-imp : L → L → L -- b ↼ a = r-imp b a
   
   l-rlcomp : (a b : L) → (rel (poset oncMonoid)) ((mul oncMonoid) a (l-imp a b)) b
   l-adj : {a b y : L} → (rel (poset oncMonoid)) (mul oncMonoid a y) b → (rel (poset oncMonoid)) y (l-imp a b)

   r-rlcomp : (a b : L) → (rel (poset oncMonoid)) ((mul oncMonoid) (r-imp b a) a) b
   r-adj : {a b y : L} → (rel (poset oncMonoid)) (mul oncMonoid y a) b → (rel (poset oncMonoid)) y (r-imp b a)

open BiclosedPoset public