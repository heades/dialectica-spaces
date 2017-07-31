module atl-semantics-thms where

open import prelude
open import atl-semantics

not-same-half-one : half ≡ one → ⊥ {lzero}
not-same-half-one ()

not-same-half-zero : half ≡ zero → ⊥ {lzero}
not-same-half-zero ()

▷₃-sym : (∀{a b} → (a ▷₃ b) ≡ (b ▷₃ a)) → ⊥ {lzero}
▷₃-sym p with p {one}{half}
... | ic = not-same-half-one ic   

symm₃ : {a b : Three} → a ⊙₃ b ≡ b ⊙₃ a
symm₃ {zero} {zero} = refl
symm₃ {zero} {half} = refl
symm₃ {zero} {one} = refl
symm₃ {half} {zero} = refl
symm₃ {half} {half} = refl
symm₃ {half} {one} = refl
symm₃ {one} {zero} = refl
symm₃ {one} {half} = refl
symm₃ {one} {one} = refl

assoc₃ : {a b c : Three} → (a ⊙₃ b) ⊙₃ c ≡ a ⊙₃ (b ⊙₃ c)
assoc₃ {zero} {zero} {zero} = refl
assoc₃ {zero} {zero} {half} = refl
assoc₃ {zero} {zero} {one} = refl
assoc₃ {zero} {half} {zero} = refl
assoc₃ {zero} {half} {half} = refl
assoc₃ {zero} {half} {one} = refl
assoc₃ {zero} {one} {zero} = refl
assoc₃ {zero} {one} {half} = refl
assoc₃ {zero} {one} {one} = refl
assoc₃ {half} {zero} {zero} = refl
assoc₃ {half} {zero} {half} = refl
assoc₃ {half} {zero} {one} = refl
assoc₃ {half} {half} {zero} = refl
assoc₃ {half} {half} {half} = refl
assoc₃ {half} {half} {one} = refl
assoc₃ {half} {one} {zero} = refl
assoc₃ {half} {one} {half} = refl
assoc₃ {half} {one} {one} = refl
assoc₃ {one} {zero} {zero} = refl
assoc₃ {one} {zero} {half} = refl
assoc₃ {one} {zero} {one} = refl
assoc₃ {one} {half} {zero} = refl
assoc₃ {one} {half} {half} = refl
assoc₃ {one} {half} {one} = refl
assoc₃ {one} {one} {zero} = refl
assoc₃ {one} {one} {half} = refl
assoc₃ {one} {one} {one} = refl

-- left-ident₃ : {a : Three} → half ⊙₃ a ≡ a
-- left-ident₃ {zero} = refl
-- left-ident₃ {half} = refl
-- left-ident₃ {one} = refl

-- right-ident₃ : {a : Three} → a ⊙₃ half ≡ a
-- right-ident₃ {zero} = refl
-- right-ident₃ {half} = refl
-- right-ident₃ {one} = refl

comp₃ : {a b : Three} → a ≤₃ b → {c : Three} → (a ⊙₃ c) ≤₃ (b ⊙₃ c)
comp₃ {zero} {zero} x {zero} = triv
comp₃ {zero} {zero} x {half} = triv
comp₃ {zero} {zero} x {one} = triv
comp₃ {zero} {half} x {zero} = triv
comp₃ {zero} {half} x {half} = triv
comp₃ {zero} {half} x {one} = triv
comp₃ {zero} {one} x {zero} = triv
comp₃ {zero} {one} x {half} = triv
comp₃ {zero} {one} x {one} = triv
comp₃ {half} {zero} x {zero} = triv
comp₃ {half} {zero} x {half} = triv
comp₃ {half} {zero} x {one} = triv
comp₃ {half} {half} x {zero} = triv
comp₃ {half} {half} x {half} = triv
comp₃ {half} {half} x {one} = triv
comp₃ {half} {one} x {zero} = triv
comp₃ {half} {one} x {half} = triv
comp₃ {half} {one} x {one} = triv
comp₃ {one} {zero} x {zero} = x
comp₃ {one} {zero} x {half} = x
comp₃ {one} {zero} x {one} = triv
comp₃ {one} {half} x {zero} = x
comp₃ {one} {half} x {half} = x
comp₃ {one} {half} x {one} = triv
comp₃ {one} {one} x {zero} = triv
comp₃ {one} {one} x {half} = triv
comp₃ {one} {one} x {one} = triv

land-assoc : {a b c : Three} →  a ▷₃ (b ▷₃ c) ≡ (a ▷₃ b) ▷₃ c
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

land-func : {a b c d : Three} → a ≤₃ c → b ≤₃ d → (a ⊙₃ b) ≤₃ (c ⊙₃ d)
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
land-func {zero} {one} {zero} {zero} p1 p2 = p2
land-func {zero} {one} {zero} {half} p1 p2 = p2
land-func {zero} {one} {zero} {one} p1 p2 = triv
land-func {zero} {one} {half} {zero} p1 p2 = p2
land-func {zero} {one} {half} {half} p1 p2 = p2
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
land-func {half} {half} {zero} {zero} p1 p2 = triv
land-func {half} {half} {zero} {half} p1 p2 = triv
land-func {half} {half} {zero} {one} p1 p2 = triv
land-func {half} {half} {half} {zero} p1 ()
land-func {half} {half} {half} {half} p1 p2 = triv
land-func {half} {half} {half} {one} p1 p2 = triv
land-func {half} {half} {one} {zero} p1 p2 = triv
land-func {half} {half} {one} {half} p1 p2 = triv
land-func {half} {half} {one} {one} p1 p2 = triv
land-func {half} {one} {zero} {zero} p1 p2 = p1
land-func {half} {one} {zero} {half} p1 p2 = p1
land-func {half} {one} {zero} {one} p1 p2 = triv
land-func {half} {one} {half} {zero} p1 p2 = p2
land-func {half} {one} {half} {half} p1 p2 = p2
land-func {half} {one} {half} {one} p1 p2 = triv
land-func {half} {one} {one} {zero} p1 p2 = triv
land-func {half} {one} {one} {half} p1 p2 = triv
land-func {half} {one} {one} {one} p1 p2 = triv
land-func {one} {zero} {zero} {zero} p1 p2 = p1
land-func {one} {zero} {zero} {half} p1 p2 = p1
land-func {one} {zero} {zero} {one} p1 p2 = triv
land-func {one} {zero} {half} {zero} p1 p2 = p1
land-func {one} {zero} {half} {half} p1 p2 = p1
land-func {one} {zero} {half} {one} p1 p2 = triv
land-func {one} {zero} {one} {zero} p1 p2 = triv
land-func {one} {zero} {one} {half} p1 p2 = triv
land-func {one} {zero} {one} {one} p1 p2 = triv
land-func {one} {half} {zero} {zero} p1 p2 = p1
land-func {one} {half} {zero} {half} p1 p2 = p1
land-func {one} {half} {zero} {one} p1 p2 = triv
land-func {one} {half} {half} {zero} p1 p2 = p1
land-func {one} {half} {half} {half} p1 p2 = p1
land-func {one} {half} {half} {one} p1 p2 = triv
land-func {one} {half} {one} {zero} p1 p2 = triv
land-func {one} {half} {one} {half} p1 p2 = triv
land-func {one} {half} {one} {one} p1 p2 = triv
land-func {one} {one} {zero} {zero} p1 p2 = p1
land-func {one} {one} {zero} {half} p1 p2 = p1
land-func {one} {one} {zero} {one} p1 p2 = triv
land-func {one} {one} {half} {zero} p1 p2 = p1
land-func {one} {one} {half} {half} p1 p2 = p1
land-func {one} {one} {half} {one} p1 p2 = triv
land-func {one} {one} {one} {zero} p1 p2 = triv
land-func {one} {one} {one} {half} p1 p2 = triv
land-func {one} {one} {one} {one} p1 p2 = triv

lchoice-assoc₃ : ∀{a b c} → ((a ⊔₃ b) ⊔₃ c) ≡ (a ⊔₃ (b ⊔₃ c))
lchoice-assoc₃ {zero} {zero} {zero} = refl
lchoice-assoc₃ {zero} {zero} {half} = refl
lchoice-assoc₃ {zero} {zero} {one} = refl
lchoice-assoc₃ {zero} {half} {zero} = refl
lchoice-assoc₃ {zero} {half} {half} = refl
lchoice-assoc₃ {zero} {half} {one} = refl
lchoice-assoc₃ {zero} {one} {zero} = refl
lchoice-assoc₃ {zero} {one} {half} = refl
lchoice-assoc₃ {zero} {one} {one} = refl
lchoice-assoc₃ {half} {zero} {zero} = refl
lchoice-assoc₃ {half} {zero} {half} = refl
lchoice-assoc₃ {half} {zero} {one} = refl
lchoice-assoc₃ {half} {half} {zero} = refl
lchoice-assoc₃ {half} {half} {half} = refl
lchoice-assoc₃ {half} {half} {one} = refl
lchoice-assoc₃ {half} {one} {zero} = refl
lchoice-assoc₃ {half} {one} {half} = refl
lchoice-assoc₃ {half} {one} {one} = refl
lchoice-assoc₃ {one} {zero} {zero} = refl
lchoice-assoc₃ {one} {zero} {half} = refl
lchoice-assoc₃ {one} {zero} {one} = refl
lchoice-assoc₃ {one} {half} {zero} = refl
lchoice-assoc₃ {one} {half} {half} = refl
lchoice-assoc₃ {one} {half} {one} = refl
lchoice-assoc₃ {one} {one} {zero} = refl
lchoice-assoc₃ {one} {one} {half} = refl
lchoice-assoc₃ {one} {one} {one} = refl

lchoice-contract : ∀{a} → (a ⊔₃ a) ≡ a
lchoice-contract {zero} = refl
lchoice-contract {half} = refl
lchoice-contract {one} = refl

-- Fails:
-- lchoice-u : ∀{x a b} → x ≤₃ a → x ≤₃ b → x ≤₃ lchoice a b

lchoice-prod1 : ∀{a b} → a ⊔₃ b ≤₃ a
lchoice-prod1 {zero} {zero} = triv
lchoice-prod1 {zero} {half} = triv
lchoice-prod1 {zero} {one} = triv
lchoice-prod1 {half} {zero} = triv
lchoice-prod1 {half} {half} = triv
lchoice-prod1 {half} {one} = triv
lchoice-prod1 {one} {zero} = triv
lchoice-prod1 {one} {half} = triv
lchoice-prod1 {one} {one} = triv

lchoice-prod2 : ∀{a b} → a ⊔₃ b ≤₃ b
lchoice-prod2 {zero} {zero} = triv
lchoice-prod2 {zero} {half} = triv
lchoice-prod2 {zero} {one} = triv
lchoice-prod2 {half} {zero} = triv
lchoice-prod2 {half} {half} = triv
lchoice-prod2 {half} {one} = triv
lchoice-prod2 {one} {zero} = triv
lchoice-prod2 {one} {half} = triv
lchoice-prod2 {one} {one} = triv

lchoice-sym : ∀{a b} → (a ⊔₃ b) ≡ (b ⊔₃ a)
lchoice-sym {zero} {zero} = refl
lchoice-sym {zero} {half} = refl
lchoice-sym {zero} {one} = refl
lchoice-sym {half} {zero} = refl
lchoice-sym {half} {half} = refl
lchoice-sym {half} {one} = refl
lchoice-sym {one} {zero} = refl
lchoice-sym {one} {half} = refl
lchoice-sym {one} {one} = refl

seq-over-lchoice : ∀{a b c} → ((a ▷₃ b) ⊔₃ (a ▷₃ c)) ≡ (a ▷₃ (b ⊔₃ c))
seq-over-lchoice {zero} {zero} {zero} = refl
seq-over-lchoice {zero} {zero} {half} = refl
seq-over-lchoice {zero} {zero} {one} = refl
seq-over-lchoice {zero} {half} {zero} = refl
seq-over-lchoice {zero} {half} {half} = refl
seq-over-lchoice {zero} {half} {one} = refl
seq-over-lchoice {zero} {one} {zero} = refl
seq-over-lchoice {zero} {one} {half} = refl
seq-over-lchoice {zero} {one} {one} = refl
seq-over-lchoice {half} {zero} {zero} = refl
seq-over-lchoice {half} {zero} {half} = refl
seq-over-lchoice {half} {zero} {one} = refl
seq-over-lchoice {half} {half} {zero} = refl
seq-over-lchoice {half} {half} {half} = refl
seq-over-lchoice {half} {half} {one} = refl
seq-over-lchoice {half} {one} {zero} = refl
seq-over-lchoice {half} {one} {half} = refl
seq-over-lchoice {half} {one} {one} = refl
seq-over-lchoice {one} {zero} {zero} = refl
seq-over-lchoice {one} {zero} {half} = refl
seq-over-lchoice {one} {zero} {one} = refl
seq-over-lchoice {one} {half} {zero} = refl
seq-over-lchoice {one} {half} {half} = refl
seq-over-lchoice {one} {half} {one} = refl
seq-over-lchoice {one} {one} {zero} = refl
seq-over-lchoice {one} {one} {half} = refl
seq-over-lchoice {one} {one} {one} = refl

seq-over-lchoice2 : ∀{a b c} → ((b ▷₃ a) ⊔₃ (c ▷₃ a)) ≡ ((b ⊔₃ c) ▷₃ a)
seq-over-lchoice2 {zero} {zero} {zero} = refl
seq-over-lchoice2 {zero} {zero} {half} = refl
seq-over-lchoice2 {zero} {zero} {one} = refl
seq-over-lchoice2 {zero} {half} {zero} = refl
seq-over-lchoice2 {zero} {half} {half} = refl
seq-over-lchoice2 {zero} {half} {one} = refl
seq-over-lchoice2 {zero} {one} {zero} = refl
seq-over-lchoice2 {zero} {one} {half} = refl
seq-over-lchoice2 {zero} {one} {one} = refl
seq-over-lchoice2 {half} {zero} {zero} = refl
seq-over-lchoice2 {half} {zero} {half} = refl
seq-over-lchoice2 {half} {zero} {one} = refl
seq-over-lchoice2 {half} {half} {zero} = refl
seq-over-lchoice2 {half} {half} {half} = refl
seq-over-lchoice2 {half} {half} {one} = refl
seq-over-lchoice2 {half} {one} {zero} = refl
seq-over-lchoice2 {half} {one} {half} = refl
seq-over-lchoice2 {half} {one} {one} = refl
seq-over-lchoice2 {one} {zero} {zero} = refl
seq-over-lchoice2 {one} {zero} {half} = refl
seq-over-lchoice2 {one} {zero} {one} = refl
seq-over-lchoice2 {one} {half} {zero} = refl
seq-over-lchoice2 {one} {half} {half} = refl
seq-over-lchoice2 {one} {half} {one} = refl
seq-over-lchoice2 {one} {one} {zero} = refl
seq-over-lchoice2 {one} {one} {half} = refl
seq-over-lchoice2 {one} {one} {one} = refl

para-over-lchoice : ∀{a b c} → ((a ⊙₃ b) ⊔₃ (a ⊙₃ c)) ≡ (a ⊙₃ (b ⊔₃ c))
para-over-lchoice {zero} {zero} {zero} = refl
para-over-lchoice {zero} {zero} {half} = refl
para-over-lchoice {zero} {zero} {one} = refl
para-over-lchoice {zero} {half} {zero} = refl
para-over-lchoice {zero} {half} {half} = refl
para-over-lchoice {zero} {half} {one} = refl
para-over-lchoice {zero} {one} {zero} = refl
para-over-lchoice {zero} {one} {half} = refl
para-over-lchoice {zero} {one} {one} = refl
para-over-lchoice {half} {zero} {zero} = refl
para-over-lchoice {half} {zero} {half} = refl
para-over-lchoice {half} {zero} {one} = refl
para-over-lchoice {half} {half} {zero} = refl
para-over-lchoice {half} {half} {half} = refl
para-over-lchoice {half} {half} {one} = refl
para-over-lchoice {half} {one} {zero} = refl
para-over-lchoice {half} {one} {half} = refl
para-over-lchoice {half} {one} {one} = refl
para-over-lchoice {one} {zero} {zero} = refl
para-over-lchoice {one} {zero} {half} = refl
para-over-lchoice {one} {zero} {one} = refl
para-over-lchoice {one} {half} {zero} = refl
para-over-lchoice {one} {half} {half} = refl
para-over-lchoice {one} {half} {one} = refl
para-over-lchoice {one} {one} {zero} = refl
para-over-lchoice {one} {one} {half} = refl
para-over-lchoice {one} {one} {one} = refl

para-over-lchoice2 : ∀{a b c} → ((a ⊙₃ c) ⊔₃ (b ⊙₃ c)) ≡ ((a ⊔₃ b) ⊙₃ c)
para-over-lchoice2 {zero} {zero} {zero} = refl
para-over-lchoice2 {zero} {zero} {half} = refl
para-over-lchoice2 {zero} {zero} {one} = refl
para-over-lchoice2 {zero} {half} {zero} = refl
para-over-lchoice2 {zero} {half} {half} = refl
para-over-lchoice2 {zero} {half} {one} = refl
para-over-lchoice2 {zero} {one} {zero} = refl
para-over-lchoice2 {zero} {one} {half} = refl
para-over-lchoice2 {zero} {one} {one} = refl
para-over-lchoice2 {half} {zero} {zero} = refl
para-over-lchoice2 {half} {zero} {half} = refl
para-over-lchoice2 {half} {zero} {one} = refl
para-over-lchoice2 {half} {half} {zero} = refl
para-over-lchoice2 {half} {half} {half} = refl
para-over-lchoice2 {half} {half} {one} = refl
para-over-lchoice2 {half} {one} {zero} = refl
para-over-lchoice2 {half} {one} {half} = refl
para-over-lchoice2 {half} {one} {one} = refl
para-over-lchoice2 {one} {zero} {zero} = refl
para-over-lchoice2 {one} {zero} {half} = refl
para-over-lchoice2 {one} {zero} {one} = refl
para-over-lchoice2 {one} {half} {zero} = refl
para-over-lchoice2 {one} {half} {half} = refl
para-over-lchoice2 {one} {half} {one} = refl
para-over-lchoice2 {one} {one} {zero} = refl
para-over-lchoice2 {one} {one} {half} = refl
para-over-lchoice2 {one} {one} {one} = refl

trans₃ : {a b c : Three} → a ≤₃ b → b ≤₃ c → a ≤₃ c
trans₃ {zero} {zero} {zero} p1 p2 = triv
trans₃ {zero} {zero} {half} p1 p2 = triv
trans₃ {zero} {zero} {one} p1 p2 = triv
trans₃ {zero} {half} {zero} p1 p2 = triv
trans₃ {zero} {half} {half} p1 p2 = triv
trans₃ {zero} {half} {one} p1 p2 = triv
trans₃ {zero} {one} {zero} p1 p2 = triv
trans₃ {zero} {one} {half} p1 p2 = triv
trans₃ {zero} {one} {one} p1 p2 = triv
trans₃ {half} {zero} {zero} p1 p2 = p1
trans₃ {half} {zero} {half} p1 p2 = triv
trans₃ {half} {zero} {one} p1 p2 = triv
trans₃ {half} {half} {zero} p1 p2 = p2
trans₃ {half} {half} {half} p1 p2 = triv
trans₃ {half} {half} {one} p1 p2 = triv
trans₃ {half} {one} {zero} p1 p2 = p2
trans₃ {half} {one} {half} p1 p2 = triv
trans₃ {half} {one} {one} p1 p2 = triv
trans₃ {one} {zero} {zero} p1 p2 = p1
trans₃ {one} {zero} {half} p1 p2 = p1
trans₃ {one} {zero} {one} p1 p2 = triv
trans₃ {one} {half} {zero} p1 p2 = p1
trans₃ {one} {half} {half} p1 p2 = p1
trans₃ {one} {half} {one} p1 p2 = triv
trans₃ {one} {one} {zero} p1 p2 = p2
trans₃ {one} {one} {half} p1 p2 = p2
trans₃ {one} {one} {one} p1 p2 = triv
  
compat₃ : {a b : Three} → a ≤₃ b → {c : Three} → (a ⊙₃ c) ≤₃ (b ⊙₃ c)
compat₃ {zero} {zero} p {zero} = triv
compat₃ {zero} {zero} p {half} = triv
compat₃ {zero} {zero} p {one} = triv
compat₃ {zero} {half} p {zero} = triv
compat₃ {zero} {half} p {half} = triv
compat₃ {zero} {half} p {one} = triv
compat₃ {zero} {one} p {zero} = triv
compat₃ {zero} {one} p {half} = triv
compat₃ {zero} {one} p {one} = triv
compat₃ {half} {zero} p {zero} = triv
compat₃ {half} {zero} p {half} = triv
compat₃ {half} {zero} p {one} = triv
compat₃ {half} {half} p {zero} = triv
compat₃ {half} {half} p {half} = triv
compat₃ {half} {half} p {one} = triv
compat₃ {half} {one} p {zero} = triv
compat₃ {half} {one} p {half} = triv
compat₃ {half} {one} p {one} = triv
compat₃ {one} {zero} p {zero} = p
compat₃ {one} {zero} p {half} = p
compat₃ {one} {zero} p {one} = triv
compat₃ {one} {half} p {zero} = p
compat₃ {one} {half} p {half} = p
compat₃ {one} {half} p {one} = triv
compat₃ {one} {one} p {zero} = triv
compat₃ {one} {one} p {half} = triv
compat₃ {one} {one} p {one} = triv

adj₃ : {a b y : Three} → (a ⊙₃ y) ≤₃ b → y ≤₃ (a ⊸₃ b)
adj₃ {zero} {zero} {zero} p = triv
adj₃ {zero} {zero} {half} p = triv
adj₃ {zero} {zero} {one} p = triv
adj₃ {zero} {half} {zero} p = triv
adj₃ {zero} {half} {half} p = triv
adj₃ {zero} {half} {one} p = triv
adj₃ {zero} {one} {zero} p = triv
adj₃ {zero} {one} {half} p = triv
adj₃ {zero} {one} {one} p = triv
adj₃ {half} {zero} {zero} p = triv
adj₃ {half} {zero} {half} ()
adj₃ {half} {zero} {one} ()
adj₃ {half} {half} {zero} p = triv
adj₃ {half} {half} {half} p = triv
adj₃ {half} {half} {one} ()
adj₃ {half} {one} {zero} p = triv
adj₃ {half} {one} {half} p = triv
adj₃ {half} {one} {one} p = triv
adj₃ {one} {zero} {zero} p = triv
adj₃ {one} {zero} {half} ()
adj₃ {one} {zero} {one} ()
adj₃ {one} {half} {zero} p = triv
adj₃ {one} {half} {half} ()
adj₃ {one} {half} {one} ()
adj₃ {one} {one} {zero} p = triv
adj₃ {one} {one} {half} p = triv
adj₃ {one} {one} {one} p = triv

-- adj₃-inv : {a b y : Three} → y ≤₃ (a ⊸₃ b) → (a ⊙₃ y) ≤₃ b
-- adj₃-inv {zero} {zero} {zero} p = triv
-- adj₃-inv {zero} {zero} {half} p = triv
-- adj₃-inv {zero} {zero} {one} p = triv
-- adj₃-inv {zero} {half} {zero} p = triv
-- adj₃-inv {zero} {half} {half} p = triv
-- adj₃-inv {zero} {half} {one} p = triv
-- adj₃-inv {zero} {one} {zero} p = triv
-- adj₃-inv {zero} {one} {half} p = triv
-- adj₃-inv {zero} {one} {one} p = triv
-- adj₃-inv {half} {zero} {zero} p = triv
-- adj₃-inv {half} {zero} {half} p = p
-- adj₃-inv {half} {zero} {one} p = p
-- adj₃-inv {half} {half} {zero} p = triv
-- adj₃-inv {half} {half} {half} p = triv
-- adj₃-inv {half} {half} {one} p = p
-- adj₃-inv {half} {one} {zero} p = triv
-- adj₃-inv {half} {one} {half} p = triv
-- adj₃-inv {half} {one} {one} p = triv
-- adj₃-inv {one} {zero} {zero} p = triv
-- adj₃-inv {one} {zero} {half} p = p
-- adj₃-inv {one} {zero} {one} p = p
-- adj₃-inv {one} {half} {zero} p = triv
-- adj₃-inv {one} {half} {half} p = p
-- adj₃-inv {one} {half} {one} p = p
-- adj₃-inv {one} {one} {zero} p = triv
-- adj₃-inv {one} {one} {half} p = triv
-- adj₃-inv {one} {one} {one} p = triv

l-adj₃ : {a b y : Three} → (a ▷₃ y) ≤₃ b → y ≤₃ (b ↼₃ a)
l-adj₃ {zero} {zero} {zero} p = triv
l-adj₃ {zero} {zero} {half} p = triv
l-adj₃ {zero} {zero} {one} p = triv
l-adj₃ {zero} {half} {zero} p = triv
l-adj₃ {zero} {half} {half} p = triv
l-adj₃ {zero} {half} {one} p = triv
l-adj₃ {zero} {one} {zero} p = triv
l-adj₃ {zero} {one} {half} p = triv
l-adj₃ {zero} {one} {one} p = triv
l-adj₃ {half} {zero} {zero} p = triv
l-adj₃ {half} {zero} {half} ()
l-adj₃ {half} {zero} {one} ()
l-adj₃ {half} {half} {zero} p = triv
l-adj₃ {half} {half} {half} p = triv
l-adj₃ {half} {half} {one} ()
l-adj₃ {half} {one} {zero} p = triv
l-adj₃ {half} {one} {half} p = triv
l-adj₃ {half} {one} {one} p = triv
l-adj₃ {one} {zero} {zero} p = triv
l-adj₃ {one} {zero} {half} ()
l-adj₃ {one} {zero} {one} ()
l-adj₃ {one} {half} {zero} p = triv
l-adj₃ {one} {half} {half} p = triv
l-adj₃ {one} {half} {one} ()
l-adj₃ {one} {one} {zero} p = triv
l-adj₃ {one} {one} {half} p = triv
l-adj₃ {one} {one} {one} p = triv

-- l-adj₃-inv : {a b y : Three} → y ≤₃ (b ↼₃ a) → (a ▷₃ y) ≤₃ b
-- l-adj₃-inv {zero} {zero} {zero} p = triv
-- l-adj₃-inv {zero} {zero} {half} p = triv
-- l-adj₃-inv {zero} {zero} {one} p = triv
-- l-adj₃-inv {zero} {half} {zero} p = triv
-- l-adj₃-inv {zero} {half} {half} p = triv
-- l-adj₃-inv {zero} {half} {one} p = triv
-- l-adj₃-inv {zero} {one} {zero} p = triv
-- l-adj₃-inv {zero} {one} {half} p = triv
-- l-adj₃-inv {zero} {one} {one} p = triv
-- l-adj₃-inv {half} {zero} {zero} p = triv
-- l-adj₃-inv {half} {zero} {half} p = p
-- l-adj₃-inv {half} {zero} {one} p = p
-- l-adj₃-inv {half} {half} {zero} p = triv
-- l-adj₃-inv {half} {half} {half} p = triv
-- l-adj₃-inv {half} {half} {one} p = p
-- l-adj₃-inv {half} {one} {zero} p = triv
-- l-adj₃-inv {half} {one} {half} p = triv
-- l-adj₃-inv {half} {one} {one} p = triv
-- l-adj₃-inv {one} {zero} {zero} p = triv
-- l-adj₃-inv {one} {zero} {half} p = p 
-- l-adj₃-inv {one} {zero} {one} p = p
-- l-adj₃-inv {one} {half} {zero} p = triv
-- l-adj₃-inv {one} {half} {half} p = triv
-- l-adj₃-inv {one} {half} {one} p = p
-- l-adj₃-inv {one} {one} {zero} p = triv
-- l-adj₃-inv {one} {one} {half} p = triv
-- l-adj₃-inv {one} {one} {one} p = triv

r-adj₃ : {a b y : Three} → (y ▷₃ a) ≤₃ b → y ≤₃ (a ⇀₃ b)
r-adj₃ {zero} {zero} {zero} p = triv
r-adj₃ {zero} {zero} {half} p = triv
r-adj₃ {zero} {zero} {one} p = triv
r-adj₃ {zero} {half} {zero} p = triv
r-adj₃ {zero} {half} {half} p = triv 
r-adj₃ {zero} {half} {one} p = triv
r-adj₃ {zero} {one} {zero} p = triv
r-adj₃ {zero} {one} {half} p = triv
r-adj₃ {zero} {one} {one} p = triv
r-adj₃ {half} {zero} {zero} p = triv
r-adj₃ {half} {zero} {half} p = p 
r-adj₃ {half} {zero} {one} p = p
r-adj₃ {half} {half} {zero} p = triv
r-adj₃ {half} {half} {half} p = triv
r-adj₃ {half} {half} {one} p = triv
r-adj₃ {half} {one} {zero} p = triv
r-adj₃ {half} {one} {half} p = triv
r-adj₃ {half} {one} {one} p = triv
r-adj₃ {one} {zero} {zero} p = triv
r-adj₃ {one} {zero} {half} p = p 
r-adj₃ {one} {zero} {one} p = p
r-adj₃ {one} {half} {zero} p = triv
r-adj₃ {one} {half} {half} p = p
r-adj₃ {one} {half} {one} p = p
r-adj₃ {one} {one} {zero} p = triv
r-adj₃ {one} {one} {half} p = triv
r-adj₃ {one} {one} {one} p = triv

-- r-adj₃-inv : {a b y : Three} → y ≤₃ (a ⇀₃ b) → (y ▷₃ a) ≤₃ b
-- r-adj₃-inv {zero} {zero} {zero} p = triv
-- r-adj₃-inv {zero} {zero} {half} p = triv
-- r-adj₃-inv {zero} {zero} {one} p = triv
-- r-adj₃-inv {zero} {half} {zero} p = triv
-- r-adj₃-inv {zero} {half} {half} p = triv
-- r-adj₃-inv {zero} {half} {one} p = triv
-- r-adj₃-inv {zero} {one} {zero} p = triv
-- r-adj₃-inv {zero} {one} {half} p = triv
-- r-adj₃-inv {zero} {one} {one} p = triv
-- r-adj₃-inv {half} {zero} {zero} p = triv
-- r-adj₃-inv {half} {zero} {half} p = p
-- r-adj₃-inv {half} {zero} {one} p = p
-- r-adj₃-inv {half} {half} {zero} p = triv
-- r-adj₃-inv {half} {half} {half} p = triv
-- r-adj₃-inv {half} {half} {one} p = triv
-- r-adj₃-inv {half} {one} {zero} p = triv
-- r-adj₃-inv {half} {one} {half} p = triv
-- r-adj₃-inv {half} {one} {one} p = triv
-- r-adj₃-inv {one} {zero} {zero} p = triv
-- r-adj₃-inv {one} {zero} {half} p = p
-- r-adj₃-inv {one} {zero} {one} p = p
-- r-adj₃-inv {one} {half} {zero} p = triv
-- r-adj₃-inv {one} {half} {half} p = p
-- r-adj₃-inv {one} {half} {one} p = p
-- r-adj₃-inv {one} {one} {zero} p = triv
-- r-adj₃-inv {one} {one} {half} p = triv
-- r-adj₃-inv {one} {one} {one} p = triv
