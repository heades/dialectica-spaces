-----------------------------------------------------------------------
-- The definition of lineales. They are used to enforce the weak     --
-- adjunction condition on arrows in dialectica categories.          --
-- Lineales are due to Martin Hyland and Valeria de Paiva:           --
--   http://www.cs.bham.ac.uk/~vdp/publications/Lineales91.pdf       --
-----------------------------------------------------------------------

module colineale where

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
   par : P → P → P
   unit : P
   
   proset : Proset P
   assoc : ∀{a b c : P} → par a (par b c) ≡ par (par a b) c
   left-ident : ∀{a : P} → par unit a ≡ a
   right-ident : ∀{a : P} → par a unit ≡ a
   symm : ∀{a b : P} → par a b ≡ par b a
   compat : ∀{a b : P} → (rel proset) a b → (∀{c : P} → (rel proset) (par a c) (par b c))

open MonProset public

record Colineale {ℓ : Level}(L : Set ℓ) : Set (lsuc ℓ) where
 constructor MkColineale
 field
   mproset : MonProset L
   l-coimp : L → L → L
   
   rlcomp : (a b : L) → (rel (proset mproset)) b ((par mproset) a (l-coimp a b))
   coadj : {a b c : L} → (rel (proset mproset)) (l-coimp b c) a → (rel (proset mproset)) c (par mproset a b)

open Colineale public
