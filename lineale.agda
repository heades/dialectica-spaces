-----------------------------------------------------------------------
-- The definition of lineales. They are used to enforce the weak     --
-- adjunction condition on arrows in dialectica categories.          --
-- Lineales are due to Martin Hyland and Valeria de Paiva:           --
--   http://www.cs.bham.ac.uk/~vdp/publications/Lineales91.pdf       --
-----------------------------------------------------------------------

module lineale where

open import prelude

record Proset {ℓ : Level}(A : Set ℓ) : Set (lsuc ℓ) where
 constructor MkProset
 field
   rel : A → A → Set
   prefl : ∀{a : A} → rel a a
   ptrans : ∀{a b c : A} → rel a b → rel b c → rel a c

open Proset public

record MonProset {ℓ : Level}(P : Set ℓ) : Set (lsuc ℓ) where
 constructor MkMonProset
 field
   mul : P → P → P
   unit : P
   
   proset : Proset P
   assoc : ∀{a b c : P} → mul a (mul b c) ≡ mul (mul a b) c
   left-ident : ∀{a : P} → mul unit a ≡ a
   right-ident : ∀{a : P} → mul a unit ≡ a
   symm : ∀{a b : P} → mul a b ≡ mul b a
   compat : ∀{a b : P} → (rel proset) a b → (∀{c : P} → (rel proset) (mul a c) (mul b c))

open MonProset public

record Lineale {ℓ : Level}(L : Set ℓ) : Set (lsuc ℓ) where
 constructor MkLineale
 field
   mproset : MonProset L
   l-imp : L → L → L
   
   rlcomp : (a b : L) → (rel (proset mproset)) ((mul mproset) a (l-imp a b)) b
   adj : {a b y : L} → (rel (proset mproset)) (mul mproset a y) b → (rel (proset mproset)) y (l-imp a b)

open Lineale public

record Full-Lineale {ℓ : Level}(L : Set ℓ) : Set (lsuc ℓ) where
 constructor MkFLineale    
 field
   lineale : Lineale L
   
   par : L → L → L
   empty : L

   f-assoc : ∀{a b c} → par a (par b c) ≡ par (par a b) c
   f-symm  : ∀{a b} → par a b ≡ par b a
   f-compat : ∀{a b} → (rel (proset (mproset lineale))) a b → (∀{c : L} → (rel (proset (mproset lineale))) (par a c) (par b c))    
   f-left-ident : ∀{a} → par a empty ≡ a
   f-right-ident : ∀{a} → par empty a ≡ a

   f-left-absorp : ∀{a b c} → (rel (proset (mproset lineale))) (mul (mproset lineale) (par a b) c) (par a (mul (mproset lineale) b c))
   f-right-absorp : ∀{a b c} → (rel (proset (mproset lineale))) (mul (mproset lineale) a (par b c)) (par (mul (mproset lineale) a b) c)

record Add-Lineale {ℓ : Level}(L : Set ℓ) : Set (lsuc ℓ) where
 constructor MkALineale    
 field
   a-lineale : Lineale L

   add : L → L → L
   add-unit : L

   a-assoc : ∀{a b c} → add a (add b c) ≡ add (add a b) c
   a-symm  : ∀{a b} → add a b ≡ add b a
   a-compat : ∀{a b} → (rel (proset (mproset a-lineale))) a b → (∀{c : L} → (rel (proset (mproset a-lineale))) (add a c) (add b c))    
   a-left-ident : ∀{a} → add a add-unit ≡ a
   a-right-ident : ∀{a} → add add-unit a ≡ a

   a-inj₁ : ∀{a b} → (rel (proset (mproset a-lineale))) a (add a b)
   a-inj₂ : ∀{a b} → (rel (proset (mproset a-lineale))) b (add a b)
   a-cop : ∀{a b c} → (rel (proset (mproset a-lineale))) a c → (rel (proset (mproset a-lineale))) b c → (rel (proset (mproset a-lineale))) (add a b) c
   a-unit-least : ∀{a} → (rel (proset (mproset a-lineale))) add-unit a

open Add-Lineale public
   
