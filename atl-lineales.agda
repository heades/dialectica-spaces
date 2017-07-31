module ATLL where

open import empty
open import unit
open import eq

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

_⊗3_ : Three → Three → Three
zero ⊗3 zero = zero
zero ⊗3 one = zero
one ⊗3 zero = zero
one ⊗3 one = one
zero ⊗3 half = zero
half ⊗3 zero = zero
half ⊗3 half = half
half ⊗3 one = one
one ⊗3 half = one

symm3 : {a b : Three} → a ⊗3 b ≡ b ⊗3 a
symm3 {zero} {zero} = refl
symm3 {zero} {half} = refl
symm3 {zero} {one} = refl
symm3 {half} {zero} = refl
symm3 {half} {half} = refl
symm3 {half} {one} = refl
symm3 {one} {zero} = refl
symm3 {one} {half} = refl
symm3 {one} {one} = refl

assoc3 : {a b c : Three} → a ⊗3 (b ⊗3 c) ≡ (a ⊗3 b) ⊗3 c
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

left-ident3 : {a : Three} → half ⊗3 a ≡ a
left-ident3 {zero} = refl
left-ident3 {half} = refl
left-ident3 {one} = refl

right-ident3 : {a : Three} → a ⊗3 half ≡ a
right-ident3 {zero} = refl
right-ident3 {half} = refl
right-ident3 {one} = refl

comp3 : {a b : Three} → a ≤3 b → {c : Three} → (a ⊗3 c) ≤3 (b ⊗3 c)
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
comp3 {half} {zero} x {one} = x
comp3 {half} {half} x {zero} = triv
comp3 {half} {half} x {half} = triv
comp3 {half} {half} x {one} = triv
comp3 {half} {one} x {zero} = triv
comp3 {half} {one} x {half} = triv
comp3 {half} {one} x {one} = triv
comp3 {one} {zero} x {zero} = triv
comp3 {one} {zero} x {half} = x
comp3 {one} {zero} x {one} = x
comp3 {one} {half} x {zero} = triv
comp3 {one} {half} x {half} = x
comp3 {one} {half} x {one} = triv
comp3 {one} {one} x {zero} = triv
comp3 {one} {one} x {half} = triv
comp3 {one} {one} x {one} = triv

land : Three → Three → Three
land half half = half
land half one = one
land one half = half
land one one = one
land _ _ = zero

land-assoc : {a b c : Three} → land a (land b c) ≡ land (land a b) c
land-assoc {zero} {zero} {zero} = refl
land-assoc {zero} {zero} {half} = refl
land-assoc {zero} {zero} {one} = refl
land-assoc {zero} {half} {zero} = refl
land-assoc {zero} {half} {half} = refl
land-assoc {zero} {half} {one} = refl
land-assoc {zero} {one} {zero} = refl
land-assoc {zero} {one} {half} = refl
land-assoc {zero} {one} {one} = refl
land-assoc {half} {zero} {zero} = refl
land-assoc {half} {zero} {half} = refl
land-assoc {half} {zero} {one} = refl
land-assoc {half} {half} {zero} = refl
land-assoc {half} {half} {half} = refl
land-assoc {half} {half} {one} = refl
land-assoc {half} {one} {zero} = refl
land-assoc {half} {one} {half} = refl
land-assoc {half} {one} {one} = refl
land-assoc {one} {zero} {zero} = refl
land-assoc {one} {zero} {half} = refl
land-assoc {one} {zero} {one} = refl
land-assoc {one} {half} {zero} = refl
land-assoc {one} {half} {half} = refl
land-assoc {one} {half} {one} = refl
land-assoc {one} {one} {zero} = refl
land-assoc {one} {one} {half} = refl
land-assoc {one} {one} {one} = refl

land-func : {a b c d : Three} → a ≤3 c → b ≤3 d → (land a b) ≤3 (land c d)
land-func {zero} {zero} {zero} {zero} p1 p2 = triv
land-func {zero} {zero} {zero} {half} p1 p2 = triv
land-func {zero} {zero} {zero} {one} p1 p2 = triv
land-func {zero} {zero} {half} {zero} p1 p2 = triv
land-func {zero} {zero} {half} {half} p1 p2 = triv
land-func {zero} {zero} {half} {one} p1 p2 = triv
land-func {zero} {zero} {one} {zero} p1 p2 = triv
land-func {zero} {zero} {one} {half} p1 p2 = triv
land-func {zero} {zero} {one} {one} p1 p2 = triv
land-func {zero} {half} {zero} {zero} p1 p2 = triv
land-func {zero} {half} {zero} {half} p1 p2 = triv
land-func {zero} {half} {zero} {one} p1 p2 = triv
land-func {zero} {half} {half} {zero} p1 p2 = triv
land-func {zero} {half} {half} {half} p1 p2 = triv
land-func {zero} {half} {half} {one} p1 p2 = triv
land-func {zero} {half} {one} {zero} p1 p2 = triv
land-func {zero} {half} {one} {half} p1 p2 = triv
land-func {zero} {half} {one} {one} p1 p2 = triv
land-func {zero} {one} {zero} {zero} p1 p2 = triv
land-func {zero} {one} {zero} {half} p1 p2 = triv
land-func {zero} {one} {zero} {one} p1 p2 = triv
land-func {zero} {one} {half} {zero} p1 p2 = triv
land-func {zero} {one} {half} {half} p1 p2 = triv
land-func {zero} {one} {half} {one} p1 p2 = triv
land-func {zero} {one} {one} {zero} p1 p2 = triv
land-func {zero} {one} {one} {half} p1 p2 = triv
land-func {zero} {one} {one} {one} p1 p2 = triv
land-func {half} {zero} {zero} {zero} p1 p2 = triv
land-func {half} {zero} {zero} {half} p1 p2 = triv
land-func {half} {zero} {zero} {one} p1 p2 = triv
land-func {half} {zero} {half} {zero} p1 p2 = triv
land-func {half} {zero} {half} {half} p1 p2 = triv
land-func {half} {zero} {half} {one} p1 p2 = triv
land-func {half} {zero} {one} {zero} p1 p2 = triv
land-func {half} {zero} {one} {half} p1 p2 = triv
land-func {half} {zero} {one} {one} p1 p2 = triv
land-func {half} {half} {zero} {zero} p1 p2 = p1
land-func {half} {half} {zero} {half} p1 p2 = p1
land-func {half} {half} {zero} {one} p1 p2 = p1
land-func {half} {half} {half} {zero} p1 ()
land-func {half} {half} {half} {half} p1 p2 = triv
land-func {half} {half} {half} {one} p1 p2 = triv
land-func {half} {half} {one} {zero} p1 p2 = p2
land-func {half} {half} {one} {half} p1 p2 = triv
land-func {half} {half} {one} {one} p1 p2 = triv
land-func {half} {one} {zero} {zero} p1 p2 = p1
land-func {half} {one} {zero} {half} p1 p2 = p1
land-func {half} {one} {zero} {one} p1 p2 = p1
land-func {half} {one} {half} {zero} p1 p2 = p2
land-func {half} {one} {half} {half} p1 p2 = p2
land-func {half} {one} {half} {one} p1 p2 = triv
land-func {half} {one} {one} {zero} p1 p2 = p2
land-func {half} {one} {one} {half} p1 p2 = p2
land-func {half} {one} {one} {one} p1 p2 = triv
land-func {one} {zero} {zero} {zero} p1 p2 = triv
land-func {one} {zero} {zero} {half} p1 p2 = triv
land-func {one} {zero} {zero} {one} p1 p2 = triv
land-func {one} {zero} {half} {zero} p1 p2 = triv
land-func {one} {zero} {half} {half} p1 p2 = triv
land-func {one} {zero} {half} {one} p1 p2 = triv
land-func {one} {zero} {one} {zero} p1 p2 = triv
land-func {one} {zero} {one} {half} p1 p2 = triv
land-func {one} {zero} {one} {one} p1 p2 = triv
land-func {one} {half} {zero} {zero} p1 p2 = p1
land-func {one} {half} {zero} {half} p1 p2 = p1
land-func {one} {half} {zero} {one} p1 p2 = p1
land-func {one} {half} {half} {zero} p1 p2 = p1
land-func {one} {half} {half} {half} p1 p2 = triv
land-func {one} {half} {half} {one} p1 p2 = triv
land-func {one} {half} {one} {zero} p1 p2 = p2
land-func {one} {half} {one} {half} p1 p2 = triv
land-func {one} {half} {one} {one} p1 p2 = triv
land-func {one} {one} {zero} {zero} p1 p2 = p1
land-func {one} {one} {zero} {half} p1 p2 = p1
land-func {one} {one} {zero} {one} p1 p2 = p1
land-func {one} {one} {half} {zero} p1 p2 = p1
land-func {one} {one} {half} {half} p1 p2 = p1
land-func {one} {one} {half} {one} p1 p2 = triv
land-func {one} {one} {one} {zero} p1 p2 = p2
land-func {one} {one} {one} {half} p1 p2 = p2
land-func {one} {one} {one} {one} p1 p2 = triv

lchoice : Three → Three → Three
lchoice half half = half
lchoice half one = half
lchoice one half = half
lchoice one one = one
lchoice _ _ = zero

lchoice-contract1 : ∀{a} → (lchoice a a) ≤3 a
lchoice-contract1 {zero} = triv
lchoice-contract1 {half} = triv
lchoice-contract1 {one} = triv

lchoice-contract2 : ∀{a} → a ≤3 (lchoice a a)
lchoice-contract2 {zero} = triv
lchoice-contract2 {half} = triv
lchoice-contract2 {one} = triv

-- Fails:
-- lchoice-u : ∀{x a b} → x ≤3 a → x ≤3 b → x ≤3 lchoice a b

lchoice-prod1 : ∀{a b} → lchoice a b ≤3 a
lchoice-prod1 {zero} {zero} = triv
lchoice-prod1 {zero} {half} = triv
lchoice-prod1 {zero} {one} = triv
lchoice-prod1 {half} {zero} = triv
lchoice-prod1 {half} {half} = triv
lchoice-prod1 {half} {one} = triv
lchoice-prod1 {one} {zero} = triv
lchoice-prod1 {one} {half} = triv
lchoice-prod1 {one} {one} = triv

lchoice-prod2 : ∀{a b} → lchoice a b ≤3 b
lchoice-prod2 {zero} {zero} = triv
lchoice-prod2 {zero} {half} = triv
lchoice-prod2 {zero} {one} = triv
lchoice-prod2 {half} {zero} = triv
lchoice-prod2 {half} {half} = triv
lchoice-prod2 {half} {one} = triv
lchoice-prod2 {one} {zero} = triv
lchoice-prod2 {one} {half} = triv
lchoice-prod2 {one} {one} = triv

lchoice-sym : ∀{a b} → lchoice a b ≤3 lchoice b a
lchoice-sym {zero} {zero} = triv
lchoice-sym {zero} {half} = triv
lchoice-sym {zero} {one} = triv
lchoice-sym {half} {zero} = triv
lchoice-sym {half} {half} = triv
lchoice-sym {half} {one} = triv
lchoice-sym {one} {zero} = triv
lchoice-sym {one} {half} = triv
lchoice-sym {one} {one} = triv

seq-over-lchoice1 : ∀{a b c} → lchoice (land a b) (land a c) ≤3 land a (lchoice b c)
seq-over-lchoice1 {zero} {zero} {zero} = triv
seq-over-lchoice1 {zero} {zero} {half} = triv
seq-over-lchoice1 {zero} {zero} {one} = triv
seq-over-lchoice1 {zero} {half} {zero} = triv
seq-over-lchoice1 {zero} {half} {half} = triv
seq-over-lchoice1 {zero} {half} {one} = triv
seq-over-lchoice1 {zero} {one} {zero} = triv
seq-over-lchoice1 {zero} {one} {half} = triv
seq-over-lchoice1 {zero} {one} {one} = triv
seq-over-lchoice1 {half} {zero} {zero} = triv
seq-over-lchoice1 {half} {zero} {half} = triv
seq-over-lchoice1 {half} {zero} {one} = triv
seq-over-lchoice1 {half} {half} {zero} = triv
seq-over-lchoice1 {half} {half} {half} = triv
seq-over-lchoice1 {half} {half} {one} = triv
seq-over-lchoice1 {half} {one} {zero} = triv
seq-over-lchoice1 {half} {one} {half} = triv
seq-over-lchoice1 {half} {one} {one} = triv
seq-over-lchoice1 {one} {zero} {zero} = triv
seq-over-lchoice1 {one} {zero} {half} = triv
seq-over-lchoice1 {one} {zero} {one} = triv
seq-over-lchoice1 {one} {half} {zero} = triv
seq-over-lchoice1 {one} {half} {half} = triv
seq-over-lchoice1 {one} {half} {one} = triv
seq-over-lchoice1 {one} {one} {zero} = triv
seq-over-lchoice1 {one} {one} {half} = triv
seq-over-lchoice1 {one} {one} {one} = triv

seq-over-lchoice2 : ∀{a b c} → land a (lchoice b c) ≤3 lchoice (land a b) (land a c)
seq-over-lchoice2 {zero} {zero} {zero} = triv
seq-over-lchoice2 {zero} {zero} {half} = triv
seq-over-lchoice2 {zero} {zero} {one} = triv
seq-over-lchoice2 {zero} {half} {zero} = triv
seq-over-lchoice2 {zero} {half} {half} = triv
seq-over-lchoice2 {zero} {half} {one} = triv
seq-over-lchoice2 {zero} {one} {zero} = triv
seq-over-lchoice2 {zero} {one} {half} = triv
seq-over-lchoice2 {zero} {one} {one} = triv
seq-over-lchoice2 {half} {zero} {zero} = triv
seq-over-lchoice2 {half} {zero} {half} = triv
seq-over-lchoice2 {half} {zero} {one} = triv
seq-over-lchoice2 {half} {half} {zero} = triv
seq-over-lchoice2 {half} {half} {half} = triv
seq-over-lchoice2 {half} {half} {one} = triv
seq-over-lchoice2 {half} {one} {zero} = triv
seq-over-lchoice2 {half} {one} {half} = triv
seq-over-lchoice2 {half} {one} {one} = triv
seq-over-lchoice2 {one} {zero} {zero} = triv
seq-over-lchoice2 {one} {zero} {half} = triv
seq-over-lchoice2 {one} {zero} {one} = triv
seq-over-lchoice2 {one} {half} {zero} = triv
seq-over-lchoice2 {one} {half} {half} = triv
seq-over-lchoice2 {one} {half} {one} = triv
seq-over-lchoice2 {one} {one} {zero} = triv
seq-over-lchoice2 {one} {one} {half} = triv
seq-over-lchoice2 {one} {one} {one} = triv

seq-over-lchoice3 : ∀{a b c} → lchoice (land b a) (land c a) ≤3 land (lchoice b c) a
seq-over-lchoice3 {zero} {zero} {zero} = triv
seq-over-lchoice3 {zero} {zero} {half} = triv
seq-over-lchoice3 {zero} {zero} {one} = triv
seq-over-lchoice3 {zero} {half} {zero} = triv
seq-over-lchoice3 {zero} {half} {half} = triv
seq-over-lchoice3 {zero} {half} {one} = triv
seq-over-lchoice3 {zero} {one} {zero} = triv
seq-over-lchoice3 {zero} {one} {half} = triv
seq-over-lchoice3 {zero} {one} {one} = triv
seq-over-lchoice3 {half} {zero} {zero} = triv
seq-over-lchoice3 {half} {zero} {half} = triv
seq-over-lchoice3 {half} {zero} {one} = triv
seq-over-lchoice3 {half} {half} {zero} = triv
seq-over-lchoice3 {half} {half} {half} = triv
seq-over-lchoice3 {half} {half} {one} = triv
seq-over-lchoice3 {half} {one} {zero} = triv
seq-over-lchoice3 {half} {one} {half} = triv
seq-over-lchoice3 {half} {one} {one} = triv
seq-over-lchoice3 {one} {zero} {zero} = triv
seq-over-lchoice3 {one} {zero} {half} = triv
seq-over-lchoice3 {one} {zero} {one} = triv
seq-over-lchoice3 {one} {half} {zero} = triv
seq-over-lchoice3 {one} {half} {half} = triv
seq-over-lchoice3 {one} {half} {one} = triv
seq-over-lchoice3 {one} {one} {zero} = triv
seq-over-lchoice3 {one} {one} {half} = triv
seq-over-lchoice3 {one} {one} {one} = triv

seq-over-lchoice4 : ∀{a b c} → land (lchoice b c) a ≤3 lchoice (land b a) (land c a)
seq-over-lchoice4 {zero} {zero} {zero} = triv
seq-over-lchoice4 {zero} {zero} {half} = triv
seq-over-lchoice4 {zero} {zero} {one} = triv
seq-over-lchoice4 {zero} {half} {zero} = triv
seq-over-lchoice4 {zero} {half} {half} = triv
seq-over-lchoice4 {zero} {half} {one} = triv
seq-over-lchoice4 {zero} {one} {zero} = triv
seq-over-lchoice4 {zero} {one} {half} = triv
seq-over-lchoice4 {zero} {one} {one} = triv
seq-over-lchoice4 {half} {zero} {zero} = triv
seq-over-lchoice4 {half} {zero} {half} = triv
seq-over-lchoice4 {half} {zero} {one} = triv
seq-over-lchoice4 {half} {half} {zero} = triv
seq-over-lchoice4 {half} {half} {half} = triv
seq-over-lchoice4 {half} {half} {one} = triv
seq-over-lchoice4 {half} {one} {zero} = triv
seq-over-lchoice4 {half} {one} {half} = triv
seq-over-lchoice4 {half} {one} {one} = triv
seq-over-lchoice4 {one} {zero} {zero} = triv
seq-over-lchoice4 {one} {zero} {half} = triv
seq-over-lchoice4 {one} {zero} {one} = triv
seq-over-lchoice4 {one} {half} {zero} = triv
seq-over-lchoice4 {one} {half} {half} = triv
seq-over-lchoice4 {one} {half} {one} = triv
seq-over-lchoice4 {one} {one} {zero} = triv
seq-over-lchoice4 {one} {one} {half} = triv
seq-over-lchoice4 {one} {one} {one} = triv

para-over-lchoice1 : ∀{a b c} → (lchoice (a ⊗3 b) (a ⊗3 c)) ≤3 (a ⊗3 (lchoice b c))
para-over-lchoice1 {zero} {zero} {zero} = triv
para-over-lchoice1 {zero} {zero} {half} = triv
para-over-lchoice1 {zero} {zero} {one} = triv
para-over-lchoice1 {zero} {half} {zero} = triv
para-over-lchoice1 {zero} {half} {half} = triv
para-over-lchoice1 {zero} {half} {one} = triv
para-over-lchoice1 {zero} {one} {zero} = triv
para-over-lchoice1 {zero} {one} {half} = triv
para-over-lchoice1 {zero} {one} {one} = triv
para-over-lchoice1 {half} {zero} {zero} = triv
para-over-lchoice1 {half} {zero} {half} = triv
para-over-lchoice1 {half} {zero} {one} = triv
para-over-lchoice1 {half} {half} {zero} = triv
para-over-lchoice1 {half} {half} {half} = triv
para-over-lchoice1 {half} {half} {one} = triv
para-over-lchoice1 {half} {one} {zero} = triv
para-over-lchoice1 {half} {one} {half} = triv
para-over-lchoice1 {half} {one} {one} = triv
para-over-lchoice1 {one} {zero} {zero} = triv
para-over-lchoice1 {one} {zero} {half} = triv
para-over-lchoice1 {one} {zero} {one} = triv
para-over-lchoice1 {one} {half} {zero} = triv
para-over-lchoice1 {one} {half} {half} = triv
para-over-lchoice1 {one} {half} {one} = triv
para-over-lchoice1 {one} {one} {zero} = triv
para-over-lchoice1 {one} {one} {half} = triv
para-over-lchoice1 {one} {one} {one} = triv

para-over-lchoice2 : ∀{a b c} → (a ⊗3 (lchoice b c)) ≤3 (lchoice (a ⊗3 b) (a ⊗3 c))
para-over-lchoice2 {zero} {zero} {zero} = triv
para-over-lchoice2 {zero} {zero} {half} = triv
para-over-lchoice2 {zero} {zero} {one} = triv
para-over-lchoice2 {zero} {half} {zero} = triv
para-over-lchoice2 {zero} {half} {half} = triv
para-over-lchoice2 {zero} {half} {one} = triv
para-over-lchoice2 {zero} {one} {zero} = triv
para-over-lchoice2 {zero} {one} {half} = triv
para-over-lchoice2 {zero} {one} {one} = triv
para-over-lchoice2 {half} {zero} {zero} = triv
para-over-lchoice2 {half} {zero} {half} = triv
para-over-lchoice2 {half} {zero} {one} = triv
para-over-lchoice2 {half} {half} {zero} = triv
para-over-lchoice2 {half} {half} {half} = triv
para-over-lchoice2 {half} {half} {one} = triv
para-over-lchoice2 {half} {one} {zero} = triv
para-over-lchoice2 {half} {one} {half} = triv
para-over-lchoice2 {half} {one} {one} = triv
para-over-lchoice2 {one} {zero} {zero} = triv
para-over-lchoice2 {one} {zero} {half} = triv
para-over-lchoice2 {one} {zero} {one} = triv
para-over-lchoice2 {one} {half} {zero} = triv
para-over-lchoice2 {one} {half} {half} = triv
para-over-lchoice2 {one} {half} {one} = triv
para-over-lchoice2 {one} {one} {zero} = triv
para-over-lchoice2 {one} {one} {half} = triv
para-over-lchoice2 {one} {one} {one} = triv
