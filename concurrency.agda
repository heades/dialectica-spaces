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

_⊗_ = _⊗ₒ_

seq-rel : ∀{U X V Y : Set} → (U → X → Three) → (V → Y → Three) → (U × V) → (X × Y) → Three
seq-rel α β (u , v) (x , y) = land (α u x) (β v y)

_▻_ : Obj → Obj → Obj
(U , X , α) ▻ (V , Y , β) = (U × V) , (X × Y) , seq-rel α β

choice-seq-dist-aux₁ : {U V W : Set} → Σ (U ⊎ V) (λ x → W) → Σ U (λ x → W) ⊎ Σ V (λ x → W)
choice-seq-dist-aux₁ (inj₁ x , b) = inj₁ (x , b)
choice-seq-dist-aux₁ (inj₂ y , b) = inj₂ (y , b)

choice-seq-dist-aux₂ : {X Z Y : Set} → Σ X (λ x → Z) ⊎ Σ Y (λ x → Z) → Σ (X ⊎ Y) (λ x → Z)
choice-seq-dist-aux₂ (inj₁ (a , b)) = inj₁ a , b
choice-seq-dist-aux₂ (inj₂ (a , b)) = inj₂ a , b

choice-seq-dist : {A B C : Obj} → Hom ((choose A B) ▻ C) (choose (A ▻ C) (B ▻ C))
choice-seq-dist {U , X , α}{V , Y , β}{W , Z , γ} = choice-seq-dist-aux₁ , choice-seq-dist-aux₂ , (λ {u y} → cond {u}{y})
 where
  cond : {u : Σ (U ⊎ V) (λ x → W)}
      {y : Σ X (λ x → Z) ⊎ Σ Y (λ x → Z)} →
      seq-rel (chooseᵣ α β) γ u (choice-seq-dist-aux₂ y)
      ≤3
      chooseᵣ(seq-rel α γ) (seq-rel β γ) (choice-seq-dist-aux₁ u) y
  cond {inj₁ x , c} {inj₁ (a , b)} = reflL {land (α x a) (γ c b)}
  cond {inj₁ x , c} {inj₂ (a , b)} = land-proj₁ {zero}{γ c b}
  cond {inj₂ x , c} {inj₁ (a , b)} = land-proj₁ {zero}{γ c b}
  cond {inj₂ x , c} {inj₂ (a , b)} = reflL {land (β x a)(γ c b)}

choice-seq-dist-inv-aux₁ : {U W V : Set} → Σ U (λ x → W) ⊎ Σ V (λ x → W) → Σ (U ⊎ V) (λ x → W)
choice-seq-dist-inv-aux₁ (inj₁ (a , b)) = inj₁ a , b
choice-seq-dist-inv-aux₁ (inj₂ (a , b)) = inj₂ a , b

choice-seq-dist-inv-aux₂ : {X Y Z : Set} → Σ (X ⊎ Y) (λ x → Z) → Σ X (λ x → Z) ⊎ Σ Y (λ x → Z)
choice-seq-dist-inv-aux₂ (inj₁ x , z) = inj₁ (x , z)
choice-seq-dist-inv-aux₂ (inj₂ y , z) = inj₂ (y , z)
  
choice-seq-dist-inv : {A B C : Obj} → Hom (choose (A ▻ C) (B ▻ C)) ((choose A B) ▻ C)
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

choice-seq-dist-iso₁ : {A B C : Obj} → choice-seq-dist {A}{B}{C} ○ choice-seq-dist-inv ≡h id {(choose A B) ▻ C}
choice-seq-dist-iso₁ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux₁ , ext-set aux₂
  where
    aux₁ : {a : Σ (U ⊎ V) (λ x → W)} → choice-seq-dist-inv-aux₁ (choice-seq-dist-aux₁ a) ≡ a
    aux₁ {inj₁ x , b} = refl
    aux₁ {inj₂ y , b} = refl

    aux₂ : {a : Σ (X ⊎ Y) (λ x → Z)} → choice-seq-dist-aux₂ (choice-seq-dist-inv-aux₂ a) ≡ a
    aux₂ {inj₁ x , b} = refl
    aux₂ {inj₂ y , b} = refl

choice-seq-dist-iso₂ : {A B C : Obj} → choice-seq-dist-inv {A}{B}{C} ○ choice-seq-dist ≡h id {choose (A ▻ C) (B ▻ C)}
choice-seq-dist-iso₂ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux₁ , ext-set aux₂
 where
   aux₁ : {a : Σ U (λ x → W) ⊎ Σ V (λ x → W)} → choice-seq-dist-aux₁ (choice-seq-dist-inv-aux₁ a) ≡ a
   aux₁ {inj₁ (a , b)} = refl
   aux₁ {inj₂ (a , b)} = refl

   aux₂ : {a : Σ X (λ x → Z) ⊎ Σ Y (λ x → Z)} → choice-seq-dist-inv-aux₂ (choice-seq-dist-aux₂ a) ≡ a
   aux₂ {inj₁ (a , b)} = refl
   aux₂ {inj₂ (a , b)} = refl

⊙-rel : ∀{U X V Y : Set} → (U → X → Three) → (V → Y → Three) → (U × V) → (X × Y) → Three
⊙-rel α β (u , v) (x , y) = (α u x) ⊗3 (β v y)

_⊙_ : Obj → Obj → Obj
(U , X , α) ⊙ (V , Y , β) = (U × V) , (X × Y) , ⊙-rel α β

choice-para-dist : {A B C : Obj} → Hom ((choose A B) ⊙ C) (choose (A ⊙ C) (B ⊙ C))
choice-para-dist {U , X , α}{V , Y , β}{W , Z , γ} = aux₁ , aux₂ , (λ {u y} → cond {u}{y})
 where
  aux₁ : Σ (U ⊎ V) (λ x → W) → Σ U (λ x → W) ⊎ Σ V (λ x → W)
  aux₁ (inj₁ a , b) = inj₁ (a , b)
  aux₁ (inj₂ a , b) = inj₂ (a , b)

  aux₂ : Σ X (λ x → Z) ⊎ Σ Y (λ x → Z) → Σ (X ⊎ Y) (λ x → Z)
  aux₂ (inj₁ (a , b)) = inj₁ a , b  
  aux₂ (inj₂ (a , b)) = inj₂ a , b

  cond : {u : Σ (U ⊎ V) (λ x → W)}
      {y : Σ X (λ x → Z) ⊎ Σ Y (λ x → Z)} →
      ⊙-rel
      (chooseᵣ α β)
      γ u (aux₂ y)
      ≤3
      chooseᵣ (⊙-rel α γ) (⊙-rel β γ) (aux₁ u) y
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
