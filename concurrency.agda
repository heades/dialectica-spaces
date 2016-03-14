open import prelude
open import lineale

module concurrency {ℓ : Level}(L : Set ℓ) (fl-pf : Add-Lineale L) where

open Add-Lineale
open import DialSets L (lineale fl-pf)

module concurrency-local-defs where
 ∅ : L
 ∅ = add-unit fl-pf

 _≤L_ = rel (proset (mproset (lineale fl-pf)))
 reflL = prefl (proset (mproset (lineale fl-pf)))

open concurrency-local-defs

-- Parallel composition: coproduct

+-ident : Obj
+-ident = ⊥ , ⊤ , (λ x y → ∅)

+-cond : ∀{U V X Y : Set ℓ} → (U → X → L) → (V → Y → L) → U ⊎ V → X × Y → L
+-cond α β (inj₁ u) (x , y) = α u x
+-cond α β (inj₂ v) (x , y) = β v y

_+_ : Obj → Obj → Obj
(U , X , α) + (V , Y , β) = (U ⊎ V) , (X × Y) , +-cond α β

+-terminalₐ : ∀{A} → Hom +-ident A
+-terminalₐ {U , X , α} = (λ x → ⊥-elim {ℓ} x) , (λ x → triv) , (λ {u y} → cond {u}{y})
 where
   cond : {u : ⊥ {ℓ}} {y : X} → ∅ ≤L (α (⊥-elim u) y)
   cond {u}{x} = ⊥-elim {ℓ} u

+-inj₁ : ∀{A B} → Hom A (A + B)
+-inj₁ {U , X , α}{V , Y , β} = inj₁ , (fst , (λ {u y} → cond {u}{y}))
 where
  cond : {u : U} {y : Σ X (λ x → Y)} →
       (α u (fst y)) ≤L (+-cond α β (inj₁ u) y)
  cond {y = a , b} = reflL

+-inj₂ : ∀{A B} → Hom B (A + B)
+-inj₂ {U , X , α}{V , Y , β} = inj₂ , snd , (λ {u y} → cond {u}{y})
 where
   cond : {u : V} {y : Σ X (λ x → Y)} →
      rel (proset (mproset (lineale fl-pf))) (β u (snd y))
      (+-cond α β (inj₂ u) y)
   cond {u}{x , y} = reflL

+-ar : ∀{A B C} → (f : Hom A C) → (g : Hom B C) → Hom (A + B) C
+-ar {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁) (g , G , p₂) = ⊎-ar f g , trans-× F G , (λ {u y} → cond {u}{y})
 where
   cond : {u : U ⊎ V} {y : Z} → (+-cond α β u (F y , G y)) ≤L (γ (⊎-ar f g u) y)
   cond {inj₁ u}{z} = p₁
   cond {inj₂ v}{z} = p₂

+-diag₁ : ∀{A B C} → (f : Hom A C) → (g : Hom B C) → +-inj₁ ○ (+-ar f g) ≡h f
+-diag₁ {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁) (g , G , p₂) = refl , refl

+-diag₂ : ∀{A B C} → (f : Hom A C) → (g : Hom B C) → +-inj₂ ○ (+-ar f g) ≡h g
+-diag₂ {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁) (g , G , p₂) = refl , refl

J : Obj
J = (⊥ , ⊥ , (λ x y → ∅))

-- We show enough to see that choice is symmetric monoidal, but we can
-- easily see that all of the symmetric monoidal properties of
-- disjoint union will lift up to the dialectica space.  Notice that
-- it is not, however, a coproduct.
chooseᵣ : {U V X Y : Set ℓ} → (U → X → L) → (V → Y → L) → U ⊎ V → X ⊎ Y → L
chooseᵣ α β (inj₁ x) (inj₁ y) = α x y
chooseᵣ α β (inj₁ x) (inj₂ y) = ∅
chooseᵣ α β (inj₂ x) (inj₁ y) = ∅
chooseᵣ α β (inj₂ x) (inj₂ y) = β x y

choose : Obj → Obj → Obj
choose (U , X , α) (V , Y , β) = (U ⊎ V) , (X ⊎ Y) , chooseᵣ α β

choose-assoc : ∀{A B C} → Hom (choose A (choose B C)) (choose (choose A B) C)
choose-assoc {U , X , α}{V , Y , β}{W , Z , γ} = ⊎-assoc , ⊎-assoc-inv , (λ {x y} → cond {x}{y})
 where
  cond : {u : U ⊎ V ⊎ W} {y : (X ⊎ Y) ⊎ Z} →      
      (chooseᵣ α (chooseᵣ β γ) u (⊎-assoc-inv y)) ≤L (chooseᵣ (chooseᵣ α β) γ (⊎-assoc u) y)
  cond {inj₁ x} {inj₁ (inj₁ y)} = reflL
  cond {inj₁ x} {inj₁ (inj₂ y)} = reflL
  cond {inj₁ x} {inj₂ y} = reflL
  cond {inj₂ (inj₁ x)} {inj₁ (inj₁ y)} = reflL
  cond {inj₂ (inj₁ x)} {inj₁ (inj₂ y)} = reflL
  cond {inj₂ (inj₁ x)} {inj₂ y} = reflL
  cond {inj₂ (inj₂ x)} {inj₁ (inj₁ y)} = reflL
  cond {inj₂ (inj₂ x)} {inj₁ (inj₂ y)} = reflL
  cond {inj₂ (inj₂ x)} {inj₂ y} = reflL

choose-assoc-inv : ∀{A B C} → Hom (choose (choose A B) C) (choose A (choose B C))
choose-assoc-inv {U , X , α}{V , Y , β}{W , Z , γ} = ⊎-assoc-inv , ⊎-assoc , (λ {u y} → cond {u}{y})
 where
   cond : {u : (U ⊎ V) ⊎ W} {y : X ⊎ Y ⊎ Z} →
     (chooseᵣ (chooseᵣ α β) γ u (⊎-assoc y)) ≤L (chooseᵣ α (chooseᵣ β γ) (⊎-assoc-inv u) y)
   cond {inj₁ (inj₁ x)} {inj₁ y} = reflL
   cond {inj₁ (inj₁ x)} {inj₂ (inj₁ y)} = reflL
   cond {inj₁ (inj₁ x)} {inj₂ (inj₂ y)} = reflL
   cond {inj₁ (inj₂ x)} {inj₁ y} = reflL
   cond {inj₁ (inj₂ x)} {inj₂ (inj₁ y)} = reflL
   cond {inj₁ (inj₂ x)} {inj₂ (inj₂ y)} = reflL
   cond {inj₂ x} {inj₁ y} = reflL
   cond {inj₂ x} {inj₂ (inj₁ y)} = reflL
   cond {inj₂ x} {inj₂ (inj₂ y)} = reflL

choose-assoc-iso₁ : ∀{A B C} → choose-assoc {A}{B}{C} ○ choose-assoc-inv ≡h id
choose-assoc-iso₁ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set ⊎-assoc-iso₁ , ext-set ⊎-assoc-iso₁

choose-assoc-iso₂ : ∀{A B C} → choose-assoc-inv {A}{B}{C} ○ choose-assoc ≡h id
choose-assoc-iso₂ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set ⊎-assoc-iso₂ , ext-set ⊎-assoc-iso₂

choose-sym : ∀{A B} → Hom (choose A B) (choose B A)
choose-sym {U , X , α}{V , Y , β} = ⊎-sym , ⊎-sym , (λ {u y} → cond {u}{y})
 where
   cond : {u : U ⊎ V} {y : Y ⊎ X} → (chooseᵣ α β u (⊎-sym y)) ≤L (chooseᵣ β α (⊎-sym u) y)
   cond {inj₁ x} {inj₁ y} = reflL
   cond {inj₁ x} {inj₂ y} = reflL
   cond {inj₂ x} {inj₁ y} = reflL
   cond {inj₂ x} {inj₂ y} = reflL

choose-left-ident : ∀{A} → Hom (choose J A) A
choose-left-ident {U , X , α} = ⊎-left-ident , ⊎-left-ident-inv , (λ {u y} → cond {u}{y})
 where
  cond : {u : ⊥ ⊎ U} {y : X} →
      (chooseᵣ {⊥ {ℓ}}{U}{⊥ {ℓ}} (λ x y₁ → ∅) α u (inj₂ y)) ≤L (α (⊎-left-ident u) y)
  cond {inj₁ u}{x} = ⊥-elim {ℓ} u
  cond {inj₂ u}{x} = reflL

choose-left-ident-inv : ∀{A} → Hom A (choose J A)
choose-left-ident-inv {U , X , α} = ⊎-left-ident-inv , ⊎-left-ident , ((λ {u y} → cond {u}{y}))
 where
  cond : {u : U} {y : ⊥ ⊎ X} →
      (α u (⊎-left-ident y)) ≤L (chooseᵣ {⊥ {ℓ}} (λ x y₁ → ∅) α (inj₂ u) y)
  cond {y = inj₁ x} = ⊥-elim {ℓ} x
  cond {y = inj₂ y} = reflL

choose-left-ident-iso₁ : ∀{A} → choose-left-ident {A} ○ choose-left-ident-inv ≡h id
choose-left-ident-iso₁ {U , X , α} = ext-set ⊎-left-ident-iso₁ , ext-set ⊎-left-ident-iso₁

choose-left-ident-iso₂ : ∀{A} → choose-left-ident-inv {A} ○ choose-left-ident ≡h id
choose-left-ident-iso₂ {U , X , α} = ext-set ⊎-left-ident-iso₂ , ext-set ⊎-left-ident-iso₂

choose-right-ident : ∀{A} → Hom (choose A J) A
choose-right-ident {U , X , α} = ⊎-right-ident , ⊎-right-ident-inv , (λ {u y} → cond {u}{y})
 where
  cond : {u : U ⊎ ⊥} {y : X} →      
      (chooseᵣ {U}{⊥ {ℓ}}{X}{⊥ {ℓ}} α (λ x y₁ → ∅) u (inj₁ y)) ≤L (α (⊎-right-ident u) y)
  cond {inj₁ x} = reflL
  cond {inj₂ y} = ⊥-elim {ℓ} y

choose-right-ident-inv : ∀{A} → Hom A (choose A J)
choose-right-ident-inv {U , X , α} = ⊎-right-ident-inv , ⊎-right-ident , (λ {u y} → cond {u}{y})
 where
  cond : {u : U} {y : X ⊎ ⊥} →
      (α u (⊎-right-ident y)) ≤L (chooseᵣ {_}{⊥ {ℓ}} α (λ x y₁ → ∅) (inj₁ u) y)
  cond {y = inj₁ x} = reflL
  cond {y = inj₂ y} = ⊥-elim {ℓ} y

choose-right-ident-iso₁ : ∀{A} → choose-right-ident {A} ○ choose-right-ident-inv ≡h id
choose-right-ident-iso₁ {U , X , α} = ext-set ⊎-right-ident-iso₁ , ext-set ⊎-right-ident-iso₁

choose-right-ident-iso₂ : ∀{A} → choose-right-ident-inv {A} ○ choose-right-ident ≡h id
choose-right-ident-iso₂ {U , X , α} = ext-set ⊎-right-ident-iso₂ , ext-set ⊎-right-ident-iso₂

choose-+-dist : ∀{A B C : Obj} → Hom ((choose A C) + (choose B C)) ((choose A B) + C) 
choose-+-dist {U , X , α}{V , Y , β}{W , Z , γ} = aux₁ , aux₂ , (λ {u y} → cond {u}{y})
 where
  aux₁ : (U ⊎ W) ⊎ V ⊎ W → (U ⊎ V) ⊎ W
  aux₁ (inj₁ (inj₁ x)) = inj₁ (inj₁ x)
  aux₁ (inj₁ (inj₂ y)) = inj₂ y
  aux₁ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
  aux₁ (inj₂ (inj₂ y)) = inj₂ y

  aux₂ : Σ (X ⊎ Y) (λ x → Z) → Σ (X ⊎ Z) (λ x → Y ⊎ Z)
  aux₂ (inj₁ x , b) = inj₁ x , inj₂ b
  aux₂ (inj₂ y , b) = inj₂ b , inj₁ y

  cond : {u : (U ⊎ W) ⊎ V ⊎ W} {y : Σ (X ⊎ Y) (λ x → Z)} →
      (+-cond (chooseᵣ α γ) (chooseᵣ β γ) u (aux₂ y)) ≤L
      (+-cond (chooseᵣ α β) γ (aux₁ u) y)
  cond {inj₁ (inj₁ x)} {inj₁ x₁ , b} = reflL
  cond {inj₁ (inj₁ x)} {inj₂ y , b} = reflL
  cond {inj₁ (inj₂ x)} {inj₁ x₁ , b} = a-unit-least fl-pf
  cond {inj₁ (inj₂ x)} {inj₂ y , b} = reflL
  cond {inj₂ (inj₁ x)} {inj₁ x₁ , b} = reflL
  cond {inj₂ (inj₁ x)} {inj₂ y , b} = reflL
  cond {inj₂ (inj₂ x)} {inj₁ x₁ , b} = reflL
  cond {inj₂ (inj₂ x)} {inj₂ y , b} = a-unit-least fl-pf

choose-contract : ∀{A : Obj} → Hom (choose A A) A
choose-contract {U , X , α} = aux₁ , inj₁ , (λ {u y} → cond {u}{y})
 where
  aux₁ : U ⊎ U → U
  aux₁ (inj₁ x) = x
  aux₁ (inj₂ y) = y

  cond : {u : U ⊎ U} {y : X} → (chooseᵣ α α u (inj₁ y)) ≤L (α (aux₁ u) y)
  cond {inj₁ u}{x} = reflL
  cond {inj₂ u}{x} = a-unit-least fl-pf
