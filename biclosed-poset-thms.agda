module biclosed-poset-thms where

open import biclosed-poset

bp-mul-funct : ∀{ℓ}{M : Set ℓ}{p : ONCMonoid M}{a c b d : M}
  → (rel (poset p)) a c
  → (rel (poset p)) b d
  → (rel (poset p)) (mul p a b) (mul p c d)
bp-mul-funct {_}{P}{MkONCMonoid _⊗_ ut (MkPoset _≤_ r t n) asc li ri cp-l cp-r}{a}{c}{b}{d} p₁ p₂ =
  let p₃ = cp-r p₁ {b}
      p₄ = cp-l p₂ {c}
   in t p₃ p₄
