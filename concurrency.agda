open import prelude
open import lineale
open import concrete-lineales

module concurrency where

open Add-Lineale
open import DialSets Three isALineale3

module local-defs where
  l-pf : Lineale Three
  l-pf = a-lineale isALineale3
  
  _≤L_ : Three → Three → Set
  x ≤L y = (rel (proset (mproset l-pf))) x y

  reflL = prefl (proset (mproset l-pf))

open local-defs

_⊕ᵣ_ : ∀{Y U X V : Set} → (U → X → Three) → (V → Y → Three) → ((Y → U) × (X → V) → X × Y → Three)
α ⊕ᵣ β = λ x y → lor (α (fst x (snd y)) (fst y)) (β (snd x (fst y)) (snd y))

_⊕ₒ_ : Obj → Obj → Obj
(U , X , α) ⊕ₒ (V , Y , β) = ((Y → U) × (X → V)) , (X × Y) , (α ⊕ᵣ β)

seq-rel : ∀{U X V Y : Set} → (U → X → Three) → (V → Y → Three) → (U × V) → (X × Y) → Three
seq-rel α β (u , v) (x , y) = land (α u x) (β v y)

_▻_ : Obj → Obj → Obj
(U , X , α) ▻ (V , Y , β) = (U × V) , (X × Y) , seq-rel α β

seq-func : {A B C D : Obj} → Hom A C → Hom B D → Hom (A ▻ B) (C ▻ D)
seq-func {U , X , α} {V , Y , β} {W , Z , γ} {M , T , φ} (f , F , p1) (g , G , p2) = (prod-func f g) , (prod-func F G , (λ {u : U × V}{y : Z × T} → aux {u}{y}))
 where
   prod-func : {U V W M : Set} → (U → W) → (V → M) → U × V → W × M
   prod-func f g ( u , v ) = (f u , g v)

   aux : {u : U × V} {y : Z × T} → seq-rel α β u (prod-func F G y) ≤L seq-rel γ φ (prod-func f g u) y
   aux {u , v}{z , t} = land-func {α u (F z)} {β v (G t)} {γ (f u) z} {φ (g v) t} p1 p2

weak-dist-par-seq-aux₁ : {U Z V Y W X : Set} → U × (Z → V) × (Y → W) → (Z → U × V) × (X × Y → W)
weak-dist-par-seq-aux₁ {U} {Z} {V} {Y} {W} {X} (u , f , g) = (λ z → u , f z) , (λ p' → g (snd p'))

weak-dist-par-seq-aux₂ : {X Y Z : Set} → (X × Y) × Z → X × Y × Z
weak-dist-par-seq-aux₂ {X} {Y} {Z} ((x , y) , z) = x , (y , z)

weak-dist₁-par-seq : {A B C : Obj} → Hom (A ▻ (B ⊕ₒ C)) ((A ▻ B) ⊕ₒ C)
weak-dist₁-par-seq {U , X , α}{V , Y , β}{W , Z , γ} = weak-dist-par-seq-aux₁ , weak-dist-par-seq-aux₂ , (λ {u} → cond {u})
 where
  cond : {u : U × (Z → V) × (Y → W)} {y : (X × Y) × Z} →
      seq-rel α (β ⊕ᵣ γ) u (weak-dist-par-seq-aux₂ y) ≤3 (seq-rel α β ⊕ᵣ γ) (weak-dist-par-seq-aux₁ u) y
  cond {u , f , g} {(x , y) , z} with (α u x)
  cond {u , f , g} {(x , y) , z} | zero with β (f z) y | γ (g y) z
  cond {u , f , g} {(x , y) , z} | zero | zero | zero = triv
  cond {u , f , g} {(x , y) , z} | zero | zero | half = triv
  cond {u , f , g} {(x , y) , z} | zero | zero | one = triv
  cond {u , f , g} {(x , y) , z} | zero | half | zero = triv
  cond {u , f , g} {(x , y) , z} | zero | half | half = triv
  cond {u , f , g} {(x , y) , z} | zero | half | one = triv
  cond {u , f , g} {(x , y) , z} | zero | one | zero = triv
  cond {u , f , g} {(x , y) , z} | zero | one | half = triv
  cond {u , f , g} {(x , y) , z} | zero | one | one = triv
  cond {u , f , g} {(x , y) , z} | half with β (f z) y | γ (g y) z
  cond {u , f , g} {(x , y) , z} | half | zero | zero = triv
  cond {u , f , g} {(x , y) , z} | half | zero | half = triv
  cond {u , f , g} {(x , y) , z} | half | zero | one = triv
  cond {u , f , g} {(x , y) , z} | half | half | zero = triv
  cond {u , f , g} {(x , y) , z} | half | half | half = triv
  cond {u , f , g} {(x , y) , z} | half | half | one = triv
  cond {u , f , g} {(x , y) , z} | half | one | zero = triv
  cond {u , f , g} {(x , y) , z} | half | one | half = triv
  cond {u , f , g} {(x , y) , z} | half | one | one = triv
  cond {u , f , g} {(x , y) , z} | one with β (f z) y | γ (g y) z
  cond {u , f , g} {(x , y) , z} | one | zero | zero = triv
  cond {u , f , g} {(x , y) , z} | one | zero | half = triv
  cond {u , f , g} {(x , y) , z} | one | zero | one = triv
  cond {u , f , g} {(x , y) , z} | one | half | zero = triv
  cond {u , f , g} {(x , y) , z} | one | half | half = triv
  cond {u , f , g} {(x , y) , z} | one | half | one = triv
  cond {u , f , g} {(x , y) , z} | one | one | zero = triv
  cond {u , f , g} {(x , y) , z} | one | one | half = triv
  cond {u , f , g} {(x , y) , z} | one | one | one = triv

weak-dist₂-par-seq-aux₁ : {Y U X V W Z : Set} → ((Y → U) × (X → V)) × W → (Y × Z → U) × (X → V × W)
weak-dist₂-par-seq-aux₁ ((f , g) , w) = (λ p → f (fst p)) , (λ x → (g x) , w)

weak-dist₂-par-seq-aux₂ : {X Y Z : Set} → X × Y × Z → (X × Y) × Z
weak-dist₂-par-seq-aux₂ {X} {Y} {Z} (x , y , z) = (x , y) , z

-- Fails:
-- Hom (A ▻ (B + C)) ((A ▻ B) + C)
-- Hom ((A + B) ▻ C) ((A ▻ C) + (B ▻ C))
-- Hom (A + A) A

choice-seq-dist-aux₁ : {U V W : Set} → Σ (U ⊎ V) (λ x → W) → Σ U (λ x → W) ⊎ Σ V (λ x → W)
choice-seq-dist-aux₁ (inj₁ x , b) = inj₁ (x , b)
choice-seq-dist-aux₁ (inj₂ y , b) = inj₂ (y , b)

choice-seq-dist-aux₂ : {X Z Y : Set} → Σ X (λ x → Z) ⊎ Σ Y (λ x → Z) → Σ (X ⊎ Y) (λ x → Z)
choice-seq-dist-aux₂ (inj₁ (a , b)) = inj₁ a , b
choice-seq-dist-aux₂ (inj₂ (a , b)) = inj₂ a , b

choice-seq-dist : {A B C : Obj} → Hom ((A ⊔ₒ B) ▻ C) ((A ▻ C) ⊔ₒ (B ▻ C))
choice-seq-dist {U , X , α}{V , Y , β}{W , Z , γ} = choice-seq-dist-aux₁ , choice-seq-dist-aux₂ , (λ {u y} → cond {u}{y})
 where
  cond : {u : Σ (U ⊎ V) (λ x → W)}
      {y : Σ X (λ x → Z) ⊎ Σ Y (λ x → Z)} →
      seq-rel (chooseᵣ α β) γ u (choice-seq-dist-aux₂ y)
      ≤3
      chooseᵣ(seq-rel α γ) (seq-rel β γ) (choice-seq-dist-aux₁ u) y
  cond {inj₁ u , w} {inj₁ (a , b)} = {!!}
  cond {inj₁ u , w} {inj₂ (a , b)} = triv
  cond {inj₂ u , w} {inj₁ (a , b)} = triv
  cond {inj₂ u , w} {inj₂ (a , b)} = {!!}

choice-seq-dist-inv-aux₁ : {U W V : Set} → Σ U (λ x → W) ⊎ Σ V (λ x → W) → Σ (U ⊎ V) (λ x → W)
choice-seq-dist-inv-aux₁ (inj₁ (a , b)) = inj₁ a , b
choice-seq-dist-inv-aux₁ (inj₂ (a , b)) = inj₂ a , b

choice-seq-dist-inv-aux₂ : {X Y Z : Set} → Σ (X ⊎ Y) (λ x → Z) → Σ X (λ x → Z) ⊎ Σ Y (λ x → Z)
choice-seq-dist-inv-aux₂ (inj₁ x , z) = inj₁ (x , z)
choice-seq-dist-inv-aux₂ (inj₂ y , z) = inj₂ (y , z)
  
choice-seq-dist-inv : {A B C : Obj} → Hom ((A ▻ C) ⊔ₒ (B ▻ C)) ((A ⊔ₒ B) ▻ C)
choice-seq-dist-inv {U , X , α}{V , Y , β}{W , Z , γ} = choice-seq-dist-inv-aux₁ , choice-seq-dist-inv-aux₂ , (λ {u y} → cond {u}{y})
 where  
  cond : {u : Σ U (λ x → W) ⊎ Σ V (λ x → W)}
      {y : Σ (X ⊎ Y) (λ x → Z)} →
      chooseᵣ (seq-rel α γ) (seq-rel β γ) u (choice-seq-dist-inv-aux₂ y)
      ≤3
      seq-rel
      (chooseᵣ α β) γ (choice-seq-dist-inv-aux₁ u) y
  cond {inj₁ (a , b)} {inj₁ x , y} = reflL {land (α a x) (γ b y)}
  cond {inj₁ (a , b)} {inj₂ x , y} = triv
  cond {inj₂ (a , b)} {inj₁ x , y} = triv
  cond {inj₂ (a , b)} {inj₂ x , y} = reflL {land (β a x) (γ b y)}

-- choice-seq-dist-iso₁ : {A B C : Obj} → choice-seq-dist {A}{B}{C} ○ choice-seq-dist-inv ≡h id {(choose A B) ▻ C}
-- choice-seq-dist-iso₁ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux₁ , ext-set aux₂
--   where
--     aux₁ : {a : Σ (U ⊎ V) (λ x → W)} → choice-seq-dist-inv-aux₁ (choice-seq-dist-aux₁ a) ≡ a
--     aux₁ {inj₁ x , b} = refl
--     aux₁ {inj₂ y , b} = refl

--     aux₂ : {a : Σ (X ⊎ Y) (λ x → Z)} → choice-seq-dist-aux₂ (choice-seq-dist-inv-aux₂ a) ≡ a
--     aux₂ {inj₁ x , b} = refl
--     aux₂ {inj₂ y , b} = refl

-- choice-seq-dist-iso₂ : {A B C : Obj} → choice-seq-dist-inv {A}{B}{C} ○ choice-seq-dist ≡h id {choose (A ▻ C) (B ▻ C)}
-- choice-seq-dist-iso₂ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux₁ , ext-set aux₂
--  where
--    aux₁ : {a : Σ U (λ x → W) ⊎ Σ V (λ x → W)} → choice-seq-dist-aux₁ (choice-seq-dist-inv-aux₁ a) ≡ a
--    aux₁ {inj₁ (a , b)} = refl
--    aux₁ {inj₂ (a , b)} = refl

--    aux₂ : {a : Σ X (λ x → Z) ⊎ Σ Y (λ x → Z)} → choice-seq-dist-inv-aux₂ (choice-seq-dist-aux₂ a) ≡ a
--    aux₂ {inj₁ (a , b)} = refl
--    aux₂ {inj₂ (a , b)} = refl

⊙-rel : ∀{U X V Y : Set} → (U → X → Three) → (V → Y → Three) → (U × V) → (X × Y) → Three
⊙-rel α β (u , v) (x , y) = (α u x) ⊗3 (β v y)

_⊙_ : Obj → Obj → Obj
(U , X , α) ⊙ (V , Y , β) = (U × V) , (X × Y) , ⊙-rel α β

_⊸ᵣ_ : ∀{U V X Y : Set} → (U → X → Three) → (V → Y → Three) → ((U → V) × (Y → X)) → U × Y → Three
_⊸ᵣ_ α β (f , g) (u , y) = (α u (g y)) ⊸₃ (β (f u) y)

_⊸_ : Obj → Obj → Obj
(U , X , α) ⊸ (V , Y , β) = ((U → V) × (Y → X)) , (U × Y) , (α ⊸ᵣ β)

curry₃ : {a b c : Three} → (a ⊗3 b) ≤3 c → a ≤3 (b ⊸₃ c)
curry₃ {zero} {zero} {zero} p = triv
curry₃ {zero} {zero} {half} p = triv
curry₃ {zero} {zero} {one} p = triv
curry₃ {zero} {half} {zero} p = triv
curry₃ {zero} {half} {half} p = triv
curry₃ {zero} {half} {one} p = triv
curry₃ {zero} {one} {zero} p = triv
curry₃ {zero} {one} {half} p = triv
curry₃ {zero} {one} {one} p = triv
curry₃ {half} {zero} {zero} p = triv
curry₃ {half} {zero} {half} p = triv
curry₃ {half} {zero} {one} p = triv
curry₃ {half} {half} {zero} p = p
curry₃ {half} {half} {half} p = triv
curry₃ {half} {half} {one} p = triv
curry₃ {half} {one} {zero} p = p
curry₃ {half} {one} {half} p = p
curry₃ {half} {one} {one} p = triv
curry₃ {one} {zero} {zero} p = triv
curry₃ {one} {zero} {half} p = triv
curry₃ {one} {zero} {one} p = triv
curry₃ {one} {half} {zero} p = p
curry₃ {one} {half} {half} p = p
curry₃ {one} {half} {one} p = triv
curry₃ {one} {one} {zero} p = p
curry₃ {one} {one} {half} p = p
curry₃ {one} {one} {one} p = triv

curry-inv₃ : {a b c : Three} → a ≤3 (b ⊸₃ c) → (a ⊗3 b) ≤3 c
curry-inv₃ {zero} {zero} {zero} p = triv
curry-inv₃ {zero} {zero} {half} p = triv
curry-inv₃ {zero} {zero} {one} p = triv
curry-inv₃ {zero} {half} {zero} p = triv
curry-inv₃ {zero} {half} {half} p = triv
curry-inv₃ {zero} {half} {one} p = triv
curry-inv₃ {zero} {one} {zero} p = triv
curry-inv₃ {zero} {one} {half} p = triv
curry-inv₃ {zero} {one} {one} p = triv
curry-inv₃ {half} {zero} {zero} p = triv
curry-inv₃ {half} {zero} {half} p = triv
curry-inv₃ {half} {zero} {one} p = triv
curry-inv₃ {half} {half} {zero} p = p
curry-inv₃ {half} {half} {half} p = triv
curry-inv₃ {half} {half} {one} p = triv
curry-inv₃ {half} {one} {zero} p = p
curry-inv₃ {half} {one} {half} p = p
curry-inv₃ {half} {one} {one} p = triv
curry-inv₃ {one} {zero} {zero} p = triv
curry-inv₃ {one} {zero} {half} p = triv
curry-inv₃ {one} {zero} {one} p = triv
curry-inv₃ {one} {half} {zero} p = p
curry-inv₃ {one} {half} {half} p = p
curry-inv₃ {one} {half} {one} p = triv
curry-inv₃ {one} {one} {zero} p = p
curry-inv₃ {one} {one} {half} p = p
curry-inv₃ {one} {one} {one} p = triv

curr : {X A B : Obj} → Hom (X ⊙ A) B → Hom X (A ⊸ B)
curr {U , X , α}{V , Y , β}{Z , W , γ} (f , F , pf) = (λ u → (λ v → f (u , v)) , (λ w → snd (F w))) , ((λ p → fst (F (snd p))) , (λ {u} {y} → aux {u}{y}))
 where
   aux : {u : U} {y : V × W} → α u (fst (F (snd y))) ≤3 (β ⊸ᵣ γ) ((λ v → f (u , v)) , (λ w → snd (F w))) y
   aux {u}{v , w} with pf {u , v}{w}
   ... | pf' with F w
   ... | x , y with α u x | β v y | γ (f (u , v)) w   
   ... | a | b | c = curry₃ {a}{b}{c} pf'

curr-inv : {X A B : Obj} → Hom X (A ⊸ B) → Hom (X ⊙ A) B
curr-inv {U , X , α}{V , Y , β}{Z , W , γ} (f , F , pf) = (λ p → fst (f (fst p)) (snd p)) , ({!!} , {!!})

-- Fails:
-- Hom C A → Hom D B → Hom (C ⊙ D) (A ⊔ₒ B), implies if ⊔ₒ was right operator on the right, then left-rule for ⊙ and ▻ would fail.
-- Hom A C → Hom B D → Hom (A ⊔ₒ B) (C ⊙ D)
-- Hom (A ▻ (B ⊕ₒ C)) ((A ▻ B) ⊕ₒ (A ▻ C))
-- Hom (A ▻ (B + C)) ((A ▻ B) + (A ▻ C))
-- Hom A C → Hom B D → Hom (A ⊔ₒ B) (C ⊕ₒ D)
-- Hom ((C ⊕ₒ A) ⊔ₒ (B ⊕ₒ D)) ((C ⊕ₒ (A ⊔ₒ B)) ⊕ₒ D)
--
-- Works:
-- postulate choice-func : {A B C D : Obj} → Hom (C ⊙ A) E → Hom (D ⊙ B) F → Hom (A ⊔ₒ B) (C ⊔ₒ D)

choice-para-dist-aux₁ : {U V W : Set} → Σ (U ⊎ V) (λ x → W) → Σ U (λ x → W) ⊎ Σ V (λ x → W)
choice-para-dist-aux₁ (inj₁ a , b) = inj₁ (a , b)
choice-para-dist-aux₁ (inj₂ a , b) = inj₂ (a , b)

choice-para-dist-aux₂ : {X Y Z : Set} → Σ X (λ x → Z) ⊎ Σ Y (λ x → Z) → Σ (X ⊎ Y) (λ x → Z)
choice-para-dist-aux₂ (inj₁ (a , b)) = inj₁ a , b  
choice-para-dist-aux₂ (inj₂ (a , b)) = inj₂ a , b

choice-para-dist : {A B C : Obj} → Hom ((A ⊔ₒ B) ⊙ C) ((A ⊙ C) ⊔ₒ (B ⊙ C))
choice-para-dist {U , X , α}{V , Y , β}{W , Z , γ} = choice-para-dist-aux₁ , choice-para-dist-aux₂ , (λ {u y} → cond {u}{y})
 where
  cond : {u : Σ (U ⊎ V) (λ x → W)}
      {y : Σ X (λ x → Z) ⊎ Σ Y (λ x → Z)} →
      ⊙-rel
      (chooseᵣ α β)
      γ u (choice-para-dist-aux₂ y)
      ≤3
      chooseᵣ (⊙-rel α γ) (⊙-rel β γ) (choice-para-dist-aux₁ u) y
  cond {inj₁ a , b} {inj₁ (x , y)} = reflL {α a x ⊗3 γ b y}
  cond {inj₁ a , b} {inj₂ (x , y)} with γ b y
  cond {inj₁ a , b} {inj₂ (x , y)} | zero = triv
  cond {inj₁ a , b} {inj₂ (x , y)} | half = triv
  cond {inj₁ a , b} {inj₂ (x , y)} | one = triv
  cond {inj₂ a , b} {inj₁ (x , y)} with γ b y
  cond {inj₂ a , b} {inj₁ (x , y)} | zero = triv
  cond {inj₂ a , b} {inj₁ (x , y)} | half = triv
  cond {inj₂ a , b} {inj₁ (x , y)} | one = triv
  cond {inj₂ a , b} {inj₂ (x , y)} = reflL {β a x ⊗3 γ b y}

choice-para-dist-inv-aux₁ : {U V W : Set} → Σ U (λ x → W) ⊎ Σ V (λ x → W) → Σ (U ⊎ V) (λ x → W)
choice-para-dist-inv-aux₁ (inj₁ (a , b)) = inj₁ a , b
choice-para-dist-inv-aux₁ (inj₂ (a , b)) = inj₂ a , b

choice-para-dist-inv-aux₂ : {X Y Z : Set} → Σ (X ⊎ Y) (λ x → Z) → Σ X (λ x → Z) ⊎ Σ Y (λ x → Z)
choice-para-dist-inv-aux₂ (inj₁ a , b) = inj₁ (a , b)
choice-para-dist-inv-aux₂ (inj₂ a , b) = inj₂ (a , b)
  
choice-para-dist-inv : {A B C : Obj} → Hom ((A ⊙ C) ⊔ₒ (B ⊙ C)) ((A ⊔ₒ B) ⊙ C)
choice-para-dist-inv {U , X , α}{V , Y , β}{W , Z , γ} = choice-para-dist-inv-aux₁ , (choice-para-dist-inv-aux₂ , (λ {u y} → cond {u}{y}))
 where
   cond : {u : Σ U (λ x → W) ⊎ Σ V (λ x → W)}
      {y : Σ (X ⊎ Y) (λ x → Z)} →
       chooseᵣ (⊙-rel α γ) (⊙-rel β γ) u (choice-para-dist-inv-aux₂ y)
      ≤3
      ⊙-rel
      (chooseᵣ α β)
      γ (choice-para-dist-inv-aux₁ u) y
   cond {inj₁ (a , b)} {inj₁ x , y} = reflL {α a x ⊗3 γ b y}
   cond {inj₁ (a , b)} {inj₂ x , y} = triv
   cond {inj₂ (a , b)} {inj₁ x , y} = triv
   cond {inj₂ (a , b)} {inj₂ x , y} = reflL {β a x ⊗3 γ b y}

choice-para-dist-iso₁ : {A B C : Obj} → choice-para-dist {A}{B}{C} ○ choice-para-dist-inv ≡h id {(A ⊔ₒ B) ⊙ C}
choice-para-dist-iso₁ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux₁ , ext-set aux₂
 where
   aux₁ : {a : Σ (U ⊎ V) (λ x → W)} → choice-para-dist-inv-aux₁ (choice-para-dist-aux₁ a) ≡ a
   aux₁ {inj₁ x , b} = refl
   aux₁ {inj₂ y , b} = refl

   aux₂ : {a : Σ (X ⊎ Y) (λ x → Z)} → choice-para-dist-aux₂ (choice-para-dist-inv-aux₂ a) ≡ a
   aux₂ {inj₁ x , b} = refl
   aux₂ {inj₂ y , b} = refl

choice-para-dist-iso₂ : {A B C : Obj} → choice-para-dist-inv {A}{B}{C} ○ choice-para-dist ≡h id {(A ⊙ C) ⊔ₒ (B ⊙ C)}
choice-para-dist-iso₂ {U , X , α}{V , Y , β}{W , Z , γ} = (ext-set aux₁) , ext-set aux₂
 where
   aux₁ : {a : Σ U (λ x → W) ⊎ Σ V (λ x → W)} → choice-para-dist-aux₁ (choice-para-dist-inv-aux₁ a) ≡ a
   aux₁ {inj₁ (a , b)} = refl
   aux₁ {inj₂ (a , b)} = refl

   aux₂ : {a : Σ X (λ x → Z) ⊎ Σ Y (λ x → Z)} → choice-para-dist-inv-aux₂ (choice-para-dist-aux₂ a) ≡ a
   aux₂ {inj₁ (a , b)} = refl
   aux₂ {inj₂ (a , b)} = refl

para-sym : {A B : Obj} → Hom (A ⊙ B) (B ⊙ A)
para-sym {U , X , α}{V , Y , β} = twist-× , twist-× , (λ {u x} → cond {u}{x})
 where
  cond : {u : Σ U (λ x → V)} {y : Σ Y (λ x → X)} → ⊙-rel α β u (twist-× y) ≤3 ⊙-rel β α (twist-× u) y
  cond {u , v}{y , x} rewrite symm3 {α u x}{β v y} = reflL {β v y ⊗3 α u x}

-- Doesn't hold:
-- Hom (A ▻ (B ⊙ C)) ((A ▻ B) ⊙ (A ▻ C))
-- Hom ((A ▻ B) ⊙ (A ▻ C)) (A ▻ (B ⊙ C))
-- Hom (((A ▻ B) ⊙ (A ▻ C)) ⊙ ((D ▻ F) ⊙ (E ▻ F))) ((A ▻ (B ⊙ C)) ⊙ ((D ⊙ E) ▻ F))

