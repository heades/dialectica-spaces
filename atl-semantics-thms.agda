module atl-semantics-thms where

open import prelude
open import atl-semantics

not-same-half-one : half ≡ one → ⊥ {lzero}
not-same-half-one ()

not-same-half-zero : half ≡ zero → ⊥ {lzero}
not-same-half-zero ()

not-same-zero-one : zero ≡ one → ⊥ {lzero}
not-same-zero-one ()

refl₃ : {a : Three} → a ≤₃ a
refl₃ {zero} = triv
refl₃ {half} = triv
refl₃ {one} = triv

▷₃-sym : (∀{a b} → (a ▷₃ b) ≡ (b ▷₃ a)) → ⊥ {lzero}
▷₃-sym p = not-same-half-zero (p {half}{zero})

▷₃-contract : (∀{a} → (a ▷₃ a) ≡ a) → ⊥ {lzero}
▷₃-contract p = not-same-half-one (p {one})

⊙₃-contract : (∀{a} → (a ⊙₃ a) ≡ a) → ⊥ {lzero}
⊙₃-contract p = not-same-half-one (p {one})

iso₃ : ∀{a b} → a ≤₃ b → b ≤₃ a → a ≡ b
iso₃ {zero} {zero} p₁ p₂ = refl
iso₃ {zero} {half} p1 ()
iso₃ {zero} {one} p₁ ()
iso₃ {half} {zero} () p₂
iso₃ {half} {half} p₁ p₂ = refl
iso₃ {half} {one} p₁ ()
iso₃ {one} {zero} () p₂
iso₃ {one} {half} () p₂
iso₃ {one} {one} p₁ p₂ = refl

iso₃-inv : ∀{a b} → a ≡ b → ((a ≤₃ b) × (b ≤₃ a))
iso₃-inv {zero} {zero} p = triv , triv
iso₃-inv {zero} {half} ()
iso₃-inv {zero} {one} ()
iso₃-inv {half} {zero} ()
iso₃-inv {half} {half} p = triv , triv
iso₃-inv {half} {one} ()
iso₃-inv {one} {zero} ()
iso₃-inv {one} {half} ()
iso₃-inv {one} {one} p = triv , triv

⊙₃-zero : {x : Three} → x ⊙₃ zero ≤₃ zero
⊙₃-zero {zero} = triv
⊙₃-zero {half} = triv
⊙₃-zero {one} = triv

⊙₃-sym : {a b : Three} → a ⊙₃ b ≡ b ⊙₃ a
⊙₃-sym {zero} {zero} = refl
⊙₃-sym {zero} {half} = refl
⊙₃-sym {zero} {one} = refl
⊙₃-sym {half} {zero} = refl
⊙₃-sym {half} {half} = refl
⊙₃-sym {half} {one} = refl
⊙₃-sym {one} {zero} = refl
⊙₃-sym {one} {half} = refl
⊙₃-sym {one} {one} = refl

⊙₃-assoc : {a b c : Three} → (a ⊙₃ b) ⊙₃ c ≡ a ⊙₃ (b ⊙₃ c)
⊙₃-assoc {zero} {zero} {zero} = refl
⊙₃-assoc {zero} {zero} {half} = refl
⊙₃-assoc {zero} {zero} {one} = refl
⊙₃-assoc {zero} {half} {zero} = refl
⊙₃-assoc {zero} {half} {half} = refl
⊙₃-assoc {zero} {half} {one} = refl
⊙₃-assoc {zero} {one} {zero} = refl
⊙₃-assoc {zero} {one} {half} = refl
⊙₃-assoc {zero} {one} {one} = refl
⊙₃-assoc {half} {zero} {zero} = refl
⊙₃-assoc {half} {zero} {half} = refl
⊙₃-assoc {half} {zero} {one} = refl
⊙₃-assoc {half} {half} {zero} = refl
⊙₃-assoc {half} {half} {half} = refl
⊙₃-assoc {half} {half} {one} = refl
⊙₃-assoc {half} {one} {zero} = refl
⊙₃-assoc {half} {one} {half} = refl
⊙₃-assoc {half} {one} {one} = refl
⊙₃-assoc {one} {zero} {zero} = refl
⊙₃-assoc {one} {zero} {half} = refl
⊙₃-assoc {one} {zero} {one} = refl
⊙₃-assoc {one} {half} {zero} = refl
⊙₃-assoc {one} {half} {half} = refl
⊙₃-assoc {one} {half} {one} = refl
⊙₃-assoc {one} {one} {zero} = refl
⊙₃-assoc {one} {one} {half} = refl
⊙₃-assoc {one} {one} {one} = refl

⊙₃-func : {a b c d : Three} → a ≤₃ c → b ≤₃ d → (a ⊙₃ b) ≤₃ (c ⊙₃ d)
⊙₃-func {zero} {zero} {zero} {zero} p₁ p₂ = triv
⊙₃-func {zero} {zero} {zero} {half} p₁ p₂ = triv
⊙₃-func {zero} {zero} {zero} {one} p₁ p₂ = triv
⊙₃-func {zero} {zero} {half} {zero} p₁ p₂ = triv
⊙₃-func {zero} {zero} {half} {half} p₁ p₂ = triv
⊙₃-func {zero} {zero} {half} {one} p₁ p₂ = triv
⊙₃-func {zero} {zero} {one} {zero} p₁ p₂ = triv
⊙₃-func {zero} {zero} {one} {half} p₁ p₂ = triv
⊙₃-func {zero} {zero} {one} {one} p₁ p₂ = triv
⊙₃-func {zero} {half} {zero} {zero} p₁ p₂ = triv
⊙₃-func {zero} {half} {zero} {half} p₁ p₂ = triv
⊙₃-func {zero} {half} {zero} {one} p₁ p₂ = triv
⊙₃-func {zero} {half} {half} {zero} p₁ p₂ = triv
⊙₃-func {zero} {half} {half} {half} p₁ p₂ = triv
⊙₃-func {zero} {half} {half} {one} p₁ p₂ = triv
⊙₃-func {zero} {half} {one} {zero} p₁ p₂ = triv
⊙₃-func {zero} {half} {one} {half} p₁ p₂ = triv
⊙₃-func {zero} {half} {one} {one} p₁ p₂ = triv
⊙₃-func {zero} {one} {zero} {zero} p₁ p₂ = triv
⊙₃-func {zero} {one} {zero} {half} p₁ p₂ = triv
⊙₃-func {zero} {one} {zero} {one} p₁ p₂ = triv
⊙₃-func {zero} {one} {half} {zero} p₁ p₂ = triv
⊙₃-func {zero} {one} {half} {half} p₁ p₂ = triv
⊙₃-func {zero} {one} {half} {one} p₁ p₂ = triv
⊙₃-func {zero} {one} {one} {zero} p₁ p₂ = triv
⊙₃-func {zero} {one} {one} {half} p₁ p₂ = triv
⊙₃-func {zero} {one} {one} {one} p₁ p₂ = triv
⊙₃-func {half} {zero} {zero} {zero} p₁ p₂ = triv
⊙₃-func {half} {zero} {zero} {half} p₁ p₂ = triv
⊙₃-func {half} {zero} {zero} {one} p₁ p₂ = triv
⊙₃-func {half} {zero} {half} {zero} p₁ p₂ = triv
⊙₃-func {half} {zero} {half} {half} p₁ p₂ = triv
⊙₃-func {half} {zero} {half} {one} p₁ p₂ = triv
⊙₃-func {half} {zero} {one} {zero} p₁ p₂ = triv
⊙₃-func {half} {zero} {one} {half} p₁ p₂ = triv
⊙₃-func {half} {zero} {one} {one} p₁ p₂ = triv
⊙₃-func {half} {half} {zero} {zero} () ()
⊙₃-func {half} {half} {zero} {half} () p₂
⊙₃-func {half} {half} {zero} {one} () p₂
⊙₃-func {half} {half} {half} {zero} p₁ ()
⊙₃-func {half} {half} {half} {half} p₁ p₂ = triv
⊙₃-func {half} {half} {half} {one} p₁ p₂ = triv
⊙₃-func {half} {half} {one} {zero} p₁ ()
⊙₃-func {half} {half} {one} {half} p₁ p₂ = triv
⊙₃-func {half} {half} {one} {one} p₁ p₂ = triv
⊙₃-func {half} {one} {zero} {zero} () ()
⊙₃-func {half} {one} {zero} {half} () ()
⊙₃-func {half} {one} {zero} {one} () p₂
⊙₃-func {half} {one} {half} {zero} p₁ ()
⊙₃-func {half} {one} {half} {half} p₁ ()
⊙₃-func {half} {one} {half} {one} p₁ p₂ = triv
⊙₃-func {half} {one} {one} {zero} p₁ ()
⊙₃-func {half} {one} {one} {half} p₁ p₂ = triv
⊙₃-func {half} {one} {one} {one} p₁ p₂ = triv
⊙₃-func {one} {zero} {zero} {zero} p₁ p₂ = triv
⊙₃-func {one} {zero} {zero} {half} p₁ p₂ = triv
⊙₃-func {one} {zero} {zero} {one} p₁ p₂ = triv
⊙₃-func {one} {zero} {half} {zero} p₁ p₂ = triv
⊙₃-func {one} {zero} {half} {half} p₁ p₂ = triv
⊙₃-func {one} {zero} {half} {one} p₁ p₂ = triv
⊙₃-func {one} {zero} {one} {zero} p₁ p₂ = triv
⊙₃-func {one} {zero} {one} {half} p₁ p₂ = triv
⊙₃-func {one} {zero} {one} {one} p₁ p₂ = triv
⊙₃-func {one} {half} {zero} {zero} () ()
⊙₃-func {one} {half} {zero} {half} () p₂
⊙₃-func {one} {half} {zero} {one} () p₂
⊙₃-func {one} {half} {half} {zero} () p₂
⊙₃-func {one} {half} {half} {half} () p₂
⊙₃-func {one} {half} {half} {one} () p₂
⊙₃-func {one} {half} {one} {zero} p₁ ()
⊙₃-func {one} {half} {one} {half} p₁ p₂ = triv
⊙₃-func {one} {half} {one} {one} p₁ p₂ = triv
⊙₃-func {one} {one} {zero} {zero} () ()
⊙₃-func {one} {one} {zero} {half} () ()
⊙₃-func {one} {one} {zero} {one} () p₂
⊙₃-func {one} {one} {half} {zero} () ()
⊙₃-func {one} {one} {half} {half} () ()
⊙₃-func {one} {one} {half} {one} () p₂
⊙₃-func {one} {one} {one} {zero} p₁ ()
⊙₃-func {one} {one} {one} {half} p₁ p₂ = triv
⊙₃-func {one} {one} {one} {one} p₁ p₂ = triv

⊙₃-comp : {a b : Three} → a ≤₃ b → {c : Three} → (a ⊙₃ c) ≤₃ (b ⊙₃ c)
⊙₃-comp {zero} {zero} x {zero} = triv
⊙₃-comp {zero} {zero} x {half} = triv
⊙₃-comp {zero} {zero} x {one} = triv
⊙₃-comp {zero} {half} x {zero} = triv
⊙₃-comp {zero} {half} x {half} = triv
⊙₃-comp {zero} {half} x {one} = triv
⊙₃-comp {zero} {one} x {zero} = triv
⊙₃-comp {zero} {one} x {half} = triv
⊙₃-comp {zero} {one} x {one} = triv
⊙₃-comp {half} {zero} x {zero} = triv
⊙₃-comp {half} {zero} () {half}
⊙₃-comp {half} {zero} x {one} = x
⊙₃-comp {half} {half} x {zero} = triv
⊙₃-comp {half} {half} x {half} = triv
⊙₃-comp {half} {half} x {one} = triv
⊙₃-comp {half} {one} x {zero} = triv
⊙₃-comp {half} {one} x {half} = triv
⊙₃-comp {half} {one} x {one} = triv
⊙₃-comp {one} {zero} x {zero} = triv
⊙₃-comp {one} {zero} x {half} = x
⊙₃-comp {one} {zero} x {one} = x
⊙₃-comp {one} {half} x {zero} = triv
⊙₃-comp {one} {half} x {half} = triv
⊙₃-comp {one} {half} x {one} = triv
⊙₃-comp {one} {one} x {zero} = triv
⊙₃-comp {one} {one} x {half} = triv
⊙₃-comp {one} {one} x {one} = triv

▷₃-assoc : {a b c : Three} →  a ▷₃ (b ▷₃ c) ≡ (a ▷₃ b) ▷₃ c
▷₃-assoc {zero} {zero} {zero} = refl
▷₃-assoc {zero} {zero} {half} = refl
▷₃-assoc {zero} {zero} {one} = refl
▷₃-assoc {zero} {half} {zero} = refl
▷₃-assoc {zero} {half} {half} = refl
▷₃-assoc {zero} {half} {one} = refl
▷₃-assoc {zero} {one} {zero} = refl
▷₃-assoc {zero} {one} {half} = refl
▷₃-assoc {zero} {one} {one} = refl
▷₃-assoc {half} {zero} {zero} = refl
▷₃-assoc {half} {zero} {half} = refl
▷₃-assoc {half} {zero} {one} = refl
▷₃-assoc {half} {half} {zero} = refl
▷₃-assoc {half} {half} {half} = refl
▷₃-assoc {half} {half} {one} = refl
▷₃-assoc {half} {one} {zero} = refl 
▷₃-assoc {half} {one} {half} = refl
▷₃-assoc {half} {one} {one} = refl
▷₃-assoc {one} {zero} {zero} = refl
▷₃-assoc {one} {zero} {half} = refl
▷₃-assoc {one} {zero} {one} = refl
▷₃-assoc {one} {half} {zero} = refl
▷₃-assoc {one} {half} {half} = refl
▷₃-assoc {one} {half} {one} = refl
▷₃-assoc {one} {one} {zero} = refl
▷₃-assoc {one} {one} {half} = refl
▷₃-assoc {one} {one} {one} = refl

▷₃-func : {a b c d : Three} → a ≤₃ c → b ≤₃ d → (a ▷₃ b) ≤₃ (c ▷₃ d)
▷₃-func {zero} {zero} {zero} {zero} p1 p2 = triv
▷₃-func {zero} {zero} {zero} {half} p1 p2 = triv
▷₃-func {zero} {zero} {zero} {one} p1 p2 = triv
▷₃-func {zero} {zero} {half} {zero} p1 p2 = triv
▷₃-func {zero} {zero} {half} {half} p1 p2 = triv
▷₃-func {zero} {zero} {half} {one} p1 p2 = triv
▷₃-func {zero} {zero} {one} {zero} p1 p2 = triv
▷₃-func {zero} {zero} {one} {half} p1 p2 = triv
▷₃-func {zero} {zero} {one} {one} p1 p2 = triv
▷₃-func {zero} {half} {zero} {zero} p1 p2 = triv
▷₃-func {zero} {half} {zero} {half} p1 p2 = triv
▷₃-func {zero} {half} {zero} {one} p1 p2 = triv
▷₃-func {zero} {half} {half} {zero} p1 p2 = triv
▷₃-func {zero} {half} {half} {half} p1 p2 = triv
▷₃-func {zero} {half} {half} {one} p1 p2 = triv
▷₃-func {zero} {half} {one} {zero} p1 p2 = triv
▷₃-func {zero} {half} {one} {half} p1 p2 = triv
▷₃-func {zero} {half} {one} {one} p1 p2 = triv
▷₃-func {zero} {one} {zero} {zero} p1 p2 = triv
▷₃-func {zero} {one} {zero} {half} p1 p2 = triv
▷₃-func {zero} {one} {zero} {one} p1 p2 = triv
▷₃-func {zero} {one} {half} {zero} p1 p2 = triv
▷₃-func {zero} {one} {half} {half} p1 p2 = triv
▷₃-func {zero} {one} {half} {one} p1 p2 = triv
▷₃-func {zero} {one} {one} {zero} p1 p2 = triv
▷₃-func {zero} {one} {one} {half} p1 p2 = triv
▷₃-func {zero} {one} {one} {one} p1 p2 = triv
▷₃-func {half} {zero} {zero} {zero} () p2
▷₃-func {half} {zero} {zero} {half} () p2
▷₃-func {half} {zero} {zero} {one} () p2
▷₃-func {half} {zero} {half} {zero} p1 p2 = triv
▷₃-func {half} {zero} {half} {half} p1 p2 = triv
▷₃-func {half} {zero} {half} {one} p1 p2 = triv
▷₃-func {half} {zero} {one} {zero} p1 p2 = triv
▷₃-func {half} {zero} {one} {half} p1 p2 = triv
▷₃-func {half} {zero} {one} {one} p1 p2 = triv
▷₃-func {half} {half} {zero} {zero} () ()
▷₃-func {half} {half} {zero} {half} () p2
▷₃-func {half} {half} {zero} {one} () p2
▷₃-func {half} {half} {half} {zero} p1 ()
▷₃-func {half} {half} {half} {half} p1 p2 = triv
▷₃-func {half} {half} {half} {one} p1 p2 = triv
▷₃-func {half} {half} {one} {zero} p1 ()
▷₃-func {half} {half} {one} {half} p1 p2 = triv
▷₃-func {half} {half} {one} {one} p1 p2 = triv
▷₃-func {half} {one} {zero} {zero} p1 p2 = p1
▷₃-func {half} {one} {zero} {half} p1 p2 = p1
▷₃-func {half} {one} {zero} {one} () p2
▷₃-func {half} {one} {half} {zero} p1 p2 = triv
▷₃-func {half} {one} {half} {half} p1 ()
▷₃-func {half} {one} {half} {one} p1 p2 = triv
▷₃-func {half} {one} {one} {zero} p1 p2 = triv
▷₃-func {half} {one} {one} {half} p1 p2 = triv
▷₃-func {half} {one} {one} {one} p1 p2 = triv
▷₃-func {one} {zero} {zero} {zero} () p2
▷₃-func {one} {zero} {zero} {half} () p2
▷₃-func {one} {zero} {zero} {one} () p2
▷₃-func {one} {zero} {half} {zero} p1 p2 = triv
▷₃-func {one} {zero} {half} {half} p1 p2 = triv
▷₃-func {one} {zero} {half} {one} p1 p2 = triv
▷₃-func {one} {zero} {one} {zero} p1 p2 = triv
▷₃-func {one} {zero} {one} {half} p1 p2 = triv
▷₃-func {one} {zero} {one} {one} p1 p2 = triv
▷₃-func {one} {half} {zero} {zero} p1 p2 = p1
▷₃-func {one} {half} {zero} {half} p1 p2 = p1
▷₃-func {one} {half} {zero} {one} p1 p2 = p1
▷₃-func {one} {half} {half} {zero} p1 p2 = triv
▷₃-func {one} {half} {half} {half} p1 p2 = triv
▷₃-func {one} {half} {half} {one} p1 p2 = triv
▷₃-func {one} {half} {one} {zero} p1 p2 = triv
▷₃-func {one} {half} {one} {half} p1 p2 = triv
▷₃-func {one} {half} {one} {one} p1 p2 = triv
▷₃-func {one} {one} {zero} {zero} p1 p2 = p1
▷₃-func {one} {one} {zero} {half} p1 p2 = p1
▷₃-func {one} {one} {zero} {one} p1 p2 = p1
▷₃-func {one} {one} {half} {zero} p1 p2 = triv
▷₃-func {one} {one} {half} {half} p1 p2 = triv
▷₃-func {one} {one} {half} {one} p1 p2 = triv
▷₃-func {one} {one} {one} {zero} p1 p2 = triv
▷₃-func {one} {one} {one} {half} p1 p2 = triv
▷₃-func {one} {one} {one} {one} p1 p2 = triv

▷₃-zero : ∀{x} → (zero ▷₃ x) ≤₃ zero
▷₃-zero {zero} = triv
▷₃-zero {half} = triv
▷₃-zero {one} = triv

⊔₃-assoc₃ : ∀{a b c} → ((a ⊔₃ b) ⊔₃ c) ≡ (a ⊔₃ (b ⊔₃ c))
⊔₃-assoc₃ {zero} {zero} {zero} = refl
⊔₃-assoc₃ {zero} {zero} {half} = refl
⊔₃-assoc₃ {zero} {zero} {one} = refl
⊔₃-assoc₃ {zero} {half} {zero} = refl
⊔₃-assoc₃ {zero} {half} {half} = refl
⊔₃-assoc₃ {zero} {half} {one} = refl
⊔₃-assoc₃ {zero} {one} {zero} = refl
⊔₃-assoc₃ {zero} {one} {half} = refl
⊔₃-assoc₃ {zero} {one} {one} = refl
⊔₃-assoc₃ {half} {zero} {zero} = refl
⊔₃-assoc₃ {half} {zero} {half} = refl
⊔₃-assoc₃ {half} {zero} {one} = refl
⊔₃-assoc₃ {half} {half} {zero} = refl
⊔₃-assoc₃ {half} {half} {half} = refl
⊔₃-assoc₃ {half} {half} {one} = refl
⊔₃-assoc₃ {half} {one} {zero} = refl
⊔₃-assoc₃ {half} {one} {half} = refl
⊔₃-assoc₃ {half} {one} {one} = refl
⊔₃-assoc₃ {one} {zero} {zero} = refl
⊔₃-assoc₃ {one} {zero} {half} = refl
⊔₃-assoc₃ {one} {zero} {one} = refl
⊔₃-assoc₃ {one} {half} {zero} = refl
⊔₃-assoc₃ {one} {half} {half} = refl
⊔₃-assoc₃ {one} {half} {one} = refl
⊔₃-assoc₃ {one} {one} {zero} = refl
⊔₃-assoc₃ {one} {one} {half} = refl
⊔₃-assoc₃ {one} {one} {one} = refl

⊔₃-func : {a b c d : Three} → a ≤₃ c → b ≤₃ d → (a ⊔₃ b) ≤₃ (c ⊔₃ d)
⊔₃-func {zero} {zero} {zero} {zero} p₁ p₂ = triv
⊔₃-func {zero} {zero} {zero} {half} p₁ p₂ = triv
⊔₃-func {zero} {zero} {zero} {one} p₁ p₂ = triv
⊔₃-func {zero} {zero} {half} {zero} p₁ p₂ = triv
⊔₃-func {zero} {zero} {half} {half} p₁ p₂ = triv
⊔₃-func {zero} {zero} {half} {one} p₁ p₂ = triv
⊔₃-func {zero} {zero} {one} {zero} p₁ p₂ = triv
⊔₃-func {zero} {zero} {one} {half} p₁ p₂ = triv
⊔₃-func {zero} {zero} {one} {one} p₁ p₂ = triv
⊔₃-func {zero} {half} {zero} {zero} p₁ p₂ = triv
⊔₃-func {zero} {half} {zero} {half} p₁ p₂ = triv
⊔₃-func {zero} {half} {zero} {one} p₁ p₂ = triv
⊔₃-func {zero} {half} {half} {zero} p₁ p₂ = triv
⊔₃-func {zero} {half} {half} {half} p₁ p₂ = triv
⊔₃-func {zero} {half} {half} {one} p₁ p₂ = triv
⊔₃-func {zero} {half} {one} {zero} p₁ p₂ = triv
⊔₃-func {zero} {half} {one} {half} p₁ p₂ = triv
⊔₃-func {zero} {half} {one} {one} p₁ p₂ = triv
⊔₃-func {zero} {one} {zero} {zero} p₁ p₂ = triv
⊔₃-func {zero} {one} {zero} {half} p₁ p₂ = triv
⊔₃-func {zero} {one} {zero} {one} p₁ p₂ = triv
⊔₃-func {zero} {one} {half} {zero} p₁ p₂ = triv
⊔₃-func {zero} {one} {half} {half} p₁ p₂ = triv
⊔₃-func {zero} {one} {half} {one} p₁ p₂ = triv
⊔₃-func {zero} {one} {one} {zero} p₁ p₂ = triv
⊔₃-func {zero} {one} {one} {half} p₁ p₂ = triv
⊔₃-func {zero} {one} {one} {one} p₁ p₂ = triv
⊔₃-func {half} {zero} {zero} {zero} p₁ p₂ = triv
⊔₃-func {half} {zero} {zero} {half} p₁ p₂ = triv
⊔₃-func {half} {zero} {zero} {one} p₁ p₂ = triv
⊔₃-func {half} {zero} {half} {zero} p₁ p₂ = triv
⊔₃-func {half} {zero} {half} {half} p₁ p₂ = triv
⊔₃-func {half} {zero} {half} {one} p₁ p₂ = triv
⊔₃-func {half} {zero} {one} {zero} p₁ p₂ = triv
⊔₃-func {half} {zero} {one} {half} p₁ p₂ = triv
⊔₃-func {half} {zero} {one} {one} p₁ p₂ = triv
⊔₃-func {half} {half} {zero} {zero} () ()
⊔₃-func {half} {half} {zero} {half} () p₂
⊔₃-func {half} {half} {zero} {one} () p₂
⊔₃-func {half} {half} {half} {zero} p₁ ()
⊔₃-func {half} {half} {half} {half} p₁ p₂ = triv
⊔₃-func {half} {half} {half} {one} p₁ p₂ = triv
⊔₃-func {half} {half} {one} {zero} p₁ ()
⊔₃-func {half} {half} {one} {half} p₁ p₂ = triv
⊔₃-func {half} {half} {one} {one} p₁ p₂ = triv
⊔₃-func {half} {one} {zero} {zero} () ()
⊔₃-func {half} {one} {zero} {half} () ()
⊔₃-func {half} {one} {zero} {one} () p₂ 
⊔₃-func {half} {one} {half} {zero} p₁ ()
⊔₃-func {half} {one} {half} {half} p₁ p₂ = triv
⊔₃-func {half} {one} {half} {one} p₁ p₂ = triv
⊔₃-func {half} {one} {one} {zero} p₁ ()
⊔₃-func {half} {one} {one} {half} p₁ p₂ = triv
⊔₃-func {half} {one} {one} {one} p₁ p₂ = triv
⊔₃-func {one} {zero} {zero} {zero} p₁ p₂ = triv
⊔₃-func {one} {zero} {zero} {half} p₁ p₂ = triv
⊔₃-func {one} {zero} {zero} {one} p₁ p₂ = triv
⊔₃-func {one} {zero} {half} {zero} p₁ p₂ = triv
⊔₃-func {one} {zero} {half} {half} p₁ p₂ = triv
⊔₃-func {one} {zero} {half} {one} p₁ p₂ = triv
⊔₃-func {one} {zero} {one} {zero} p₁ p₂ = triv
⊔₃-func {one} {zero} {one} {half} p₁ p₂ = triv
⊔₃-func {one} {zero} {one} {one} p₁ p₂ = triv
⊔₃-func {one} {half} {zero} {zero} () ()
⊔₃-func {one} {half} {zero} {half} () p₂
⊔₃-func {one} {half} {zero} {one} () p₂
⊔₃-func {one} {half} {half} {zero} () ()
⊔₃-func {one} {half} {half} {half} p₁ p₂ = triv
⊔₃-func {one} {half} {half} {one} p₁ p₂ = triv
⊔₃-func {one} {half} {one} {zero} p₁ ()
⊔₃-func {one} {half} {one} {half} p₁ p₂ = triv
⊔₃-func {one} {half} {one} {one} p₁ p₂ = triv
⊔₃-func {one} {one} {zero} {zero} () ()
⊔₃-func {one} {one} {zero} {half} () ()
⊔₃-func {one} {one} {zero} {one} () p₂
⊔₃-func {one} {one} {half} {zero} () ()
⊔₃-func {one} {one} {half} {half} () ()
⊔₃-func {one} {one} {half} {one} () p₂
⊔₃-func {one} {one} {one} {zero} p₁ ()
⊔₃-func {one} {one} {one} {half} p₁ ()
⊔₃-func {one} {one} {one} {one} p₁ p₂ = triv

⊔₃-contract : ∀{a} → (a ⊔₃ a) ≡ a
⊔₃-contract {zero} = refl
⊔₃-contract {half} = refl
⊔₃-contract {one} = refl

⊔₃-prod1 : ∀{a b} → a ⊔₃ b ≤₃ a
⊔₃-prod1 {zero} {zero} = triv
⊔₃-prod1 {zero} {half} = triv
⊔₃-prod1 {zero} {one} = triv
⊔₃-prod1 {half} {zero} = triv
⊔₃-prod1 {half} {half} = triv
⊔₃-prod1 {half} {one} = triv
⊔₃-prod1 {one} {zero} = triv
⊔₃-prod1 {one} {half} = triv
⊔₃-prod1 {one} {one} = triv

⊔₃-prod2 : ∀{a b} → a ⊔₃ b ≤₃ b
⊔₃-prod2 {zero} {zero} = triv
⊔₃-prod2 {zero} {half} = triv
⊔₃-prod2 {zero} {one} = triv
⊔₃-prod2 {half} {zero} = triv
⊔₃-prod2 {half} {half} = triv
⊔₃-prod2 {half} {one} = triv
⊔₃-prod2 {one} {zero} = triv
⊔₃-prod2 {one} {half} = triv
⊔₃-prod2 {one} {one} = triv

⊔₃-sym : ∀{a b} → (a ⊔₃ b) ≡ (b ⊔₃ a)
⊔₃-sym {zero} {zero} = refl
⊔₃-sym {zero} {half} = refl
⊔₃-sym {zero} {one} = refl
⊔₃-sym {half} {zero} = refl
⊔₃-sym {half} {half} = refl
⊔₃-sym {half} {one} = refl
⊔₃-sym {one} {zero} = refl
⊔₃-sym {one} {half} = refl
⊔₃-sym {one} {one} = refl

seq-over-⊔₃ : ∀{a b c} → ((a ▷₃ b) ⊔₃ (a ▷₃ c)) ≡ (a ▷₃ (b ⊔₃ c))
seq-over-⊔₃ {zero} {zero} {zero} = refl
seq-over-⊔₃ {zero} {zero} {half} = refl
seq-over-⊔₃ {zero} {zero} {one} = refl
seq-over-⊔₃ {zero} {half} {zero} = refl
seq-over-⊔₃ {zero} {half} {half} = refl
seq-over-⊔₃ {zero} {half} {one} = refl
seq-over-⊔₃ {zero} {one} {zero} = refl
seq-over-⊔₃ {zero} {one} {half} = refl
seq-over-⊔₃ {zero} {one} {one} = refl
seq-over-⊔₃ {half} {zero} {zero} = refl
seq-over-⊔₃ {half} {zero} {half} = refl
seq-over-⊔₃ {half} {zero} {one} = refl
seq-over-⊔₃ {half} {half} {zero} = refl
seq-over-⊔₃ {half} {half} {half} = refl
seq-over-⊔₃ {half} {half} {one} = refl
seq-over-⊔₃ {half} {one} {zero} = refl
seq-over-⊔₃ {half} {one} {half} = refl
seq-over-⊔₃ {half} {one} {one} = refl
seq-over-⊔₃ {one} {zero} {zero} = refl
seq-over-⊔₃ {one} {zero} {half} = refl
seq-over-⊔₃ {one} {zero} {one} = refl
seq-over-⊔₃ {one} {half} {zero} = refl
seq-over-⊔₃ {one} {half} {half} = refl
seq-over-⊔₃ {one} {half} {one} = refl
seq-over-⊔₃ {one} {one} {zero} = refl
seq-over-⊔₃ {one} {one} {half} = refl
seq-over-⊔₃ {one} {one} {one} = refl

seq-over-⊔₃2 : ∀{a b c} → ((b ▷₃ a) ⊔₃ (c ▷₃ a)) ≡ ((b ⊔₃ c) ▷₃ a)
seq-over-⊔₃2 {zero} {zero} {zero} = refl
seq-over-⊔₃2 {zero} {zero} {half} = refl
seq-over-⊔₃2 {zero} {zero} {one} = refl
seq-over-⊔₃2 {zero} {half} {zero} = refl
seq-over-⊔₃2 {zero} {half} {half} = refl
seq-over-⊔₃2 {zero} {half} {one} = refl
seq-over-⊔₃2 {zero} {one} {zero} = refl
seq-over-⊔₃2 {zero} {one} {half} = refl
seq-over-⊔₃2 {zero} {one} {one} = refl
seq-over-⊔₃2 {half} {zero} {zero} = refl
seq-over-⊔₃2 {half} {zero} {half} = refl
seq-over-⊔₃2 {half} {zero} {one} = refl
seq-over-⊔₃2 {half} {half} {zero} = refl
seq-over-⊔₃2 {half} {half} {half} = refl
seq-over-⊔₃2 {half} {half} {one} = refl
seq-over-⊔₃2 {half} {one} {zero} = refl
seq-over-⊔₃2 {half} {one} {half} = refl
seq-over-⊔₃2 {half} {one} {one} = refl
seq-over-⊔₃2 {one} {zero} {zero} = refl
seq-over-⊔₃2 {one} {zero} {half} = refl
seq-over-⊔₃2 {one} {zero} {one} = refl
seq-over-⊔₃2 {one} {half} {zero} = refl
seq-over-⊔₃2 {one} {half} {half} = refl
seq-over-⊔₃2 {one} {half} {one} = refl
seq-over-⊔₃2 {one} {one} {zero} = refl
seq-over-⊔₃2 {one} {one} {half} = refl
seq-over-⊔₃2 {one} {one} {one} = refl

para-over-⊔₃ : ∀{a b c} → ((a ⊙₃ b) ⊔₃ (a ⊙₃ c)) ≡ (a ⊙₃ (b ⊔₃ c))
para-over-⊔₃ {zero} {zero} {zero} = refl
para-over-⊔₃ {zero} {zero} {half} = refl
para-over-⊔₃ {zero} {zero} {one} = refl
para-over-⊔₃ {zero} {half} {zero} = refl
para-over-⊔₃ {zero} {half} {half} = refl
para-over-⊔₃ {zero} {half} {one} = refl
para-over-⊔₃ {zero} {one} {zero} = refl
para-over-⊔₃ {zero} {one} {half} = refl
para-over-⊔₃ {zero} {one} {one} = refl
para-over-⊔₃ {half} {zero} {zero} = refl
para-over-⊔₃ {half} {zero} {half} = refl
para-over-⊔₃ {half} {zero} {one} = refl
para-over-⊔₃ {half} {half} {zero} = refl
para-over-⊔₃ {half} {half} {half} = refl
para-over-⊔₃ {half} {half} {one} = refl
para-over-⊔₃ {half} {one} {zero} = refl
para-over-⊔₃ {half} {one} {half} = refl
para-over-⊔₃ {half} {one} {one} = refl
para-over-⊔₃ {one} {zero} {zero} = refl
para-over-⊔₃ {one} {zero} {half} = refl
para-over-⊔₃ {one} {zero} {one} = refl
para-over-⊔₃ {one} {half} {zero} = refl
para-over-⊔₃ {one} {half} {half} = refl
para-over-⊔₃ {one} {half} {one} = refl
para-over-⊔₃ {one} {one} {zero} = refl
para-over-⊔₃ {one} {one} {half} = refl
para-over-⊔₃ {one} {one} {one} = refl

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

⊙₃-over-⊔₃ : ∀{a b c} → ((a ⊙₃ b) ⊔₃ (a ⊙₃ c)) ≡ (a ⊙₃ (b ⊔₃ c))
⊙₃-over-⊔₃ {zero} {zero} {zero} = refl
⊙₃-over-⊔₃ {zero} {zero} {half} = refl
⊙₃-over-⊔₃ {zero} {zero} {one} = refl
⊙₃-over-⊔₃ {zero} {half} {zero} = refl
⊙₃-over-⊔₃ {zero} {half} {half} = refl
⊙₃-over-⊔₃ {zero} {half} {one} = refl
⊙₃-over-⊔₃ {zero} {one} {zero} = refl
⊙₃-over-⊔₃ {zero} {one} {half} = refl
⊙₃-over-⊔₃ {zero} {one} {one} = refl
⊙₃-over-⊔₃ {half} {zero} {zero} = refl
⊙₃-over-⊔₃ {half} {zero} {half} = refl
⊙₃-over-⊔₃ {half} {zero} {one} = refl
⊙₃-over-⊔₃ {half} {half} {zero} = refl
⊙₃-over-⊔₃ {half} {half} {half} = refl
⊙₃-over-⊔₃ {half} {half} {one} = refl
⊙₃-over-⊔₃ {half} {one} {zero} = refl
⊙₃-over-⊔₃ {half} {one} {half} = refl
⊙₃-over-⊔₃ {half} {one} {one} = refl
⊙₃-over-⊔₃ {one} {zero} {zero} = refl
⊙₃-over-⊔₃ {one} {zero} {half} = refl
⊙₃-over-⊔₃ {one} {zero} {one} = refl
⊙₃-over-⊔₃ {one} {half} {zero} = refl
⊙₃-over-⊔₃ {one} {half} {half} = refl
⊙₃-over-⊔₃ {one} {half} {one} = refl
⊙₃-over-⊔₃ {one} {one} {zero} = refl
⊙₃-over-⊔₃ {one} {one} {half} = refl
⊙₃-over-⊔₃ {one} {one} {one} = refl

λ₃ : {a : Three} → (a ⊗₃ I₃) ≤₃ a
λ₃ {zero} = triv
λ₃ {half} = triv
λ₃ {one} = triv

λ₃-inv : {a : Three} → a ≤₃ (a ⊗₃ I₃)
λ₃-inv {zero} = triv
λ₃-inv {half} = triv
λ₃-inv {one} = triv

ρ₃ : {a : Three} → (I₃ ⊗₃ a) ≤₃ a
ρ₃ {zero} = triv
ρ₃ {half} = triv
ρ₃ {one} = triv

ρ₃-inv : {a : Three} → a ≤₃ (I₃ ⊗₃ a)
ρ₃-inv {zero} = triv
ρ₃-inv {half} = triv
ρ₃-inv {one} = triv

β₃ : {a b : Three} → (a ⊗₃ b) ≡ (b ⊗₃ a)
β₃ {zero} {zero} = refl
β₃ {zero} {half} = refl
β₃ {zero} {one} = refl
β₃ {half} {zero} = refl
β₃ {half} {half} = refl
β₃ {half} {one} = refl
β₃ {one} {zero} = refl
β₃ {one} {half} = refl
β₃ {one} {one} = refl

α₃ : {a b c : Three} → (a ⊗₃ b) ⊗₃ c ≡ a ⊗₃ (b ⊗₃ c)
α₃ {zero} {zero} {zero} = refl
α₃ {zero} {zero} {half} = refl
α₃ {zero} {zero} {one} = refl
α₃ {zero} {half} {zero} = refl
α₃ {zero} {half} {half} = refl
α₃ {zero} {half} {one} = refl
α₃ {zero} {one} {zero} = refl
α₃ {zero} {one} {half} = refl
α₃ {zero} {one} {one} = refl
α₃ {half} {zero} {zero} = refl
α₃ {half} {zero} {half} = refl
α₃ {half} {zero} {one} = refl
α₃ {half} {half} {zero} = refl
α₃ {half} {half} {half} = refl
α₃ {half} {half} {one} = refl
α₃ {half} {one} {zero} = refl
α₃ {half} {one} {half} = refl
α₃ {half} {one} {one} = refl
α₃ {one} {zero} {zero} = refl
α₃ {one} {zero} {half} = refl
α₃ {one} {zero} {one} = refl
α₃ {one} {half} {zero} = refl
α₃ {one} {half} {half} = refl
α₃ {one} {half} {one} = refl
α₃ {one} {one} {zero} = refl
α₃ {one} {one} {half} = refl
α₃ {one} {one} {one} = refl

⊗₃-func : {a b c d : Three} → a ≤₃ c → b ≤₃ d → (a ⊗₃ b) ≤₃ (c ⊗₃ d)
⊗₃-func {zero} {zero} {zero} {zero} p₁ p₂ = triv
⊗₃-func {zero} {zero} {zero} {half} p₁ p₂ = triv
⊗₃-func {zero} {zero} {zero} {one} p₁ p₂ = triv
⊗₃-func {zero} {zero} {half} {zero} p₁ p₂ = triv
⊗₃-func {zero} {zero} {half} {half} p₁ p₂ = triv
⊗₃-func {zero} {zero} {half} {one} p₁ p₂ = triv
⊗₃-func {zero} {zero} {one} {zero} p₁ p₂ = triv
⊗₃-func {zero} {zero} {one} {half} p₁ p₂ = triv
⊗₃-func {zero} {zero} {one} {one} p₁ p₂ = triv
⊗₃-func {zero} {half} {zero} {zero} p₁ p₂ = triv
⊗₃-func {zero} {half} {zero} {half} p₁ p₂ = triv
⊗₃-func {zero} {half} {zero} {one} p₁ p₂ = triv
⊗₃-func {zero} {half} {half} {zero} p₁ p₂ = triv
⊗₃-func {zero} {half} {half} {half} p₁ p₂ = triv
⊗₃-func {zero} {half} {half} {one} p₁ p₂ = triv
⊗₃-func {zero} {half} {one} {zero} p₁ p₂ = triv
⊗₃-func {zero} {half} {one} {half} p₁ p₂ = triv
⊗₃-func {zero} {half} {one} {one} p₁ p₂ = triv
⊗₃-func {zero} {one} {zero} {zero} p₁ p₂ = triv
⊗₃-func {zero} {one} {zero} {half} p₁ p₂ = triv
⊗₃-func {zero} {one} {zero} {one} p₁ p₂ = triv
⊗₃-func {zero} {one} {half} {zero} p₁ p₂ = triv
⊗₃-func {zero} {one} {half} {half} p₁ p₂ = triv
⊗₃-func {zero} {one} {half} {one} p₁ p₂ = triv
⊗₃-func {zero} {one} {one} {zero} p₁ p₂ = triv
⊗₃-func {zero} {one} {one} {half} p₁ p₂ = triv
⊗₃-func {zero} {one} {one} {one} p₁ p₂ = triv
⊗₃-func {half} {zero} {zero} {zero} p₁ p₂ = triv
⊗₃-func {half} {zero} {zero} {half} p₁ p₂ = triv
⊗₃-func {half} {zero} {zero} {one} p₁ p₂ = triv
⊗₃-func {half} {zero} {half} {zero} p₁ p₂ = triv
⊗₃-func {half} {zero} {half} {half} p₁ p₂ = triv
⊗₃-func {half} {zero} {half} {one} p₁ p₂ = triv
⊗₃-func {half} {zero} {one} {zero} p₁ p₂ = triv
⊗₃-func {half} {zero} {one} {half} p₁ p₂ = triv
⊗₃-func {half} {zero} {one} {one} p₁ p₂ = triv
⊗₃-func {half} {half} {zero} {zero} () ()
⊗₃-func {half} {half} {zero} {half} () p₂
⊗₃-func {half} {half} {zero} {one} () p₂
⊗₃-func {half} {half} {half} {zero} p₁ ()
⊗₃-func {half} {half} {half} {half} p₁ p₂ = triv
⊗₃-func {half} {half} {half} {one} p₁ p₂ = triv
⊗₃-func {half} {half} {one} {zero} p₁ ()
⊗₃-func {half} {half} {one} {half} p₁ p₂ = triv
⊗₃-func {half} {half} {one} {one} p₁ p₂ = triv
⊗₃-func {half} {one} {zero} {zero} () ()
⊗₃-func {half} {one} {zero} {half} () ()
⊗₃-func {half} {one} {zero} {one} () p₂
⊗₃-func {half} {one} {half} {zero} p₁ ()
⊗₃-func {half} {one} {half} {half} p₁ ()
⊗₃-func {half} {one} {half} {one} p₁ p₂ = triv
⊗₃-func {half} {one} {one} {zero} p₁ ()
⊗₃-func {half} {one} {one} {half} p₁ p₂ = triv
⊗₃-func {half} {one} {one} {one} p₁ p₂ = triv
⊗₃-func {one} {zero} {zero} {zero} p₁ p₂ = triv
⊗₃-func {one} {zero} {zero} {half} p₁ p₂ = triv
⊗₃-func {one} {zero} {zero} {one} p₁ p₂ = triv
⊗₃-func {one} {zero} {half} {zero} p₁ p₂ = triv
⊗₃-func {one} {zero} {half} {half} p₁ p₂ = triv
⊗₃-func {one} {zero} {half} {one} p₁ p₂ = triv
⊗₃-func {one} {zero} {one} {zero} p₁ p₂ = triv
⊗₃-func {one} {zero} {one} {half} p₁ p₂ = triv
⊗₃-func {one} {zero} {one} {one} p₁ p₂ = triv
⊗₃-func {one} {half} {zero} {zero} () ()
⊗₃-func {one} {half} {zero} {half} () p₂
⊗₃-func {one} {half} {zero} {one} () p₂
⊗₃-func {one} {half} {half} {zero} () p₂
⊗₃-func {one} {half} {half} {half} () p₂
⊗₃-func {one} {half} {half} {one} () p₂
⊗₃-func {one} {half} {one} {zero} p₁ ()
⊗₃-func {one} {half} {one} {half} p₁ p₂ = triv
⊗₃-func {one} {half} {one} {one} p₁ p₂ = triv
⊗₃-func {one} {one} {zero} {zero} () ()
⊗₃-func {one} {one} {zero} {half} () ()
⊗₃-func {one} {one} {zero} {one} () p₂
⊗₃-func {one} {one} {half} {zero} () ()
⊗₃-func {one} {one} {half} {half} () ()
⊗₃-func {one} {one} {half} {one} () p₂
⊗₃-func {one} {one} {one} {zero} p₁ ()
⊗₃-func {one} {one} {one} {half} p₁ p₂ = triv
⊗₃-func {one} {one} {one} {one} p₁ p₂ = triv

⊗₃-comp : {a b : Three} → a ≤₃ b → {c : Three} → (a ⊗₃ c) ≤₃ (b ⊗₃ c)
⊗₃-comp {zero} {zero} p {zero} = triv
⊗₃-comp {zero} {zero} p {half} = triv
⊗₃-comp {zero} {zero} p {one} = triv
⊗₃-comp {zero} {half} p {zero} = triv
⊗₃-comp {zero} {half} p {half} = triv
⊗₃-comp {zero} {half} p {one} = triv
⊗₃-comp {zero} {one} p {zero} = triv
⊗₃-comp {zero} {one} p {half} = triv
⊗₃-comp {zero} {one} p {one} = triv
⊗₃-comp {half} {zero} p {zero} = triv
⊗₃-comp {half} {zero} () {half}
⊗₃-comp {half} {zero} () {one}
⊗₃-comp {half} {half} p {zero} = triv
⊗₃-comp {half} {half} p {half} = triv
⊗₃-comp {half} {half} p {one} = triv
⊗₃-comp {half} {one} p {zero} = triv
⊗₃-comp {half} {one} p {half} = triv
⊗₃-comp {half} {one} p {one} = triv
⊗₃-comp {one} {zero} p {zero} = triv
⊗₃-comp {one} {zero} () {half}
⊗₃-comp {one} {zero} () {one}
⊗₃-comp {one} {half} p {zero} = triv
⊗₃-comp {one} {half} () {half}
⊗₃-comp {one} {half} p {one} = triv
⊗₃-comp {one} {one} p {zero} = triv
⊗₃-comp {one} {one} p {half} = triv
⊗₃-comp {one} {one} p {one} = triv

⊗₃-contract : {a : Three} → (a ⊗₃ a) ≡ a
⊗₃-contract {zero} = refl
⊗₃-contract {half} = refl
⊗₃-contract {one} = refl

⊗₃-adj : {a b y : Three} → (a ⊗₃ y) ≤₃ b → y ≤₃ (a ⊸₃ b)
⊗₃-adj {zero} {zero} {zero} p = triv
⊗₃-adj {zero} {zero} {half} p = triv
⊗₃-adj {zero} {zero} {one} p = triv
⊗₃-adj {zero} {half} {zero} p = triv
⊗₃-adj {zero} {half} {half} p = triv
⊗₃-adj {zero} {half} {one} p = triv
⊗₃-adj {zero} {one} {zero} p = triv
⊗₃-adj {zero} {one} {half} p = triv
⊗₃-adj {zero} {one} {one} p = triv
⊗₃-adj {half} {zero} {zero} p = triv
⊗₃-adj {half} {zero} {half} ()
⊗₃-adj {half} {zero} {one} ()
⊗₃-adj {half} {half} {zero} p = triv
⊗₃-adj {half} {half} {half} p = triv
⊗₃-adj {half} {half} {one} ()
⊗₃-adj {half} {one} {zero} p = triv
⊗₃-adj {half} {one} {half} p = triv
⊗₃-adj {half} {one} {one} p = triv
⊗₃-adj {one} {zero} {zero} p = triv
⊗₃-adj {one} {zero} {half} ()
⊗₃-adj {one} {zero} {one} ()
⊗₃-adj {one} {half} {zero} p = triv
⊗₃-adj {one} {half} {half} ()
⊗₃-adj {one} {half} {one} ()
⊗₃-adj {one} {one} {zero} p = triv
⊗₃-adj {one} {one} {half} p = triv
⊗₃-adj {one} {one} {one} p = triv

⊗₃-adj-inv : {a b y : Three} → y ≤₃ (a ⊸₃ b) → (y ⊗₃ a) ≤₃ b
⊗₃-adj-inv {zero} {zero} {zero} p = triv
⊗₃-adj-inv {zero} {zero} {half} p = triv
⊗₃-adj-inv {zero} {zero} {one} p = triv
⊗₃-adj-inv {zero} {half} {zero} p = triv
⊗₃-adj-inv {zero} {half} {half} p = triv
⊗₃-adj-inv {zero} {half} {one} p = triv
⊗₃-adj-inv {zero} {one} {zero} p = triv
⊗₃-adj-inv {zero} {one} {half} p = triv
⊗₃-adj-inv {zero} {one} {one} p = triv
⊗₃-adj-inv {half} {zero} {zero} p = triv
⊗₃-adj-inv {half} {zero} {half} ()
⊗₃-adj-inv {half} {zero} {one} ()
⊗₃-adj-inv {half} {half} {zero} p = triv
⊗₃-adj-inv {half} {half} {half} p = triv
⊗₃-adj-inv {half} {half} {one} ()
⊗₃-adj-inv {half} {one} {zero} p = triv
⊗₃-adj-inv {half} {one} {half} p = triv
⊗₃-adj-inv {half} {one} {one} p = triv
⊗₃-adj-inv {one} {zero} {zero} p = triv
⊗₃-adj-inv {one} {zero} {half} ()
⊗₃-adj-inv {one} {zero} {one} ()
⊗₃-adj-inv {one} {half} {zero} p = triv
⊗₃-adj-inv {one} {half} {half} ()
⊗₃-adj-inv {one} {half} {one} ()
⊗₃-adj-inv {one} {one} {zero} p = triv
⊗₃-adj-inv {one} {one} {half} p = triv
⊗₃-adj-inv {one} {one} {one} p = triv

⊗₃-app : {a b : Three} → ((a ⊸₃ b) ⊗₃ a) ≤₃ b
⊗₃-app {a}{b} = ⊗₃-adj-inv {a} {b} {a ⊸₃ b} (refl₃ {a ⊸₃ b})

point₃ : ∀{a b} → I₃ ≤₃ (a ⊸₃ b) → a ≤₃ b
point₃ {a}{b} p with ⊗₃-adj-inv {a}{b}{I₃} p | ρ₃-inv {a}
... | r₁ | r₂ =  trans₃ {a}{I₃ ⊗₃ a}{b} r₂ r₁
