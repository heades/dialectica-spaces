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

l-imp-funct : ∀{ℓ}{L : Set ℓ}{p : BiclosedPoset L}{c a b d : L}
  → (rel (poset (oncMonoid p))) c a
  → (rel (poset (oncMonoid p))) b d
  → (rel (poset (oncMonoid p))) (r-imp p a b) (r-imp p c d)
l-imp-funct {p = MkBiclosedPoset
            (MkONCMonoid _⊗_ I
            (MkPoset _≤_ prefl ptrans pasymm) assoc left-ident right-ident compat-l compat-r)
            _⇀_ _↼_ _ _ _ _ _ _ r-rlcomp r-adj l-rlcomp l-adj}{c}{a}{b}{d} p₁ p₂
  = let x = compat-r p₁ {a ⇀ b}
        y = ptrans x (r-rlcomp a b)
        z = ptrans y p₂
     in r-adj z

r-imp-funct : ∀{ℓ}{L : Set ℓ}{p : BiclosedPoset L}{c a b d : L}
  → (rel (poset (oncMonoid p))) c a
  → (rel (poset (oncMonoid p))) b d
  → (rel (poset (oncMonoid p))) (l-imp p b a) (l-imp p d c)
r-imp-funct {p = MkBiclosedPoset
            (MkONCMonoid _⊗_ I
            (MkPoset _≤_ prefl ptrans pasymm) assoc left-ident right-ident compat-l compat-r)
            _⇀_ _↼_ _ _ _ _ _ _ l-rlcomp l-adj r-rlcomp r-adj}{c}{a}{b}{d} p₁ p₂
  = let x = compat-l p₁ {b ↼ a}
        y = ptrans x (r-rlcomp a b)
        z = ptrans y p₂
     in r-adj z
