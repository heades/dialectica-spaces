-----------------------------------------------------------------------
-- The definition of the dialectica category GC on Sets              --
-- parameterized by an arbitrary lineale.  GC is described in        --
-- Valeria de Paiva's thesis:                                        --
--   http://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-213.pdf          --
-----------------------------------------------------------------------
module ATL-Dialectica where

open import prelude
open import atl-semantics
open import atl-semantics-thms

-----------------------------------------------------------------------
-- We have a category                                                --
-----------------------------------------------------------------------

-- The objects:
Obj : Set₁
Obj = Σ[ U ∈ Set ] (Σ[ X ∈ Set ] (U → X → Three))

obj-fst : Obj → Set
obj-fst (U , X , α) = U

obj-snd : Obj → Set
obj-snd (U , X , α) = X
  
-- The morphisms:
Hom : Obj → Obj → Set
Hom (U , X , α) (V , Y , β) =
  Σ[ f ∈ (U → V) ]
    (Σ[ F ∈ (Y → X) ] (∀{u : U}{y : Y} → α u (F y) ≤₃ β (f u) y))

-- Composition:
comp : {A B C : Obj} → Hom A B → Hom B C → Hom A C
comp {(U , X , α)} {(V , Y , β)} {(W , Z , γ)} (f , F , p₁) (g , G , p₂) =
  (g ∘ f , F ∘ G , cond)
  where
   cond : {u : U} {y : Z} → (α u (F (G y))) ≤₃ (γ (g (f u)) y)
   cond {u}{z} = trans₃ {α u (F (G z))}{β (f u) (G z)} {γ (g (f u)) z} p₁ p₂

infixl 5 _○_

_○_ = comp

-- The contravariant hom-functor:
Homₐ :  {A' A B B' : Obj} → Hom A' A → Hom B B' → Hom A B → Hom A' B'
Homₐ f h g = comp f (comp g h)

-- The identity function:
id : {A : Obj} → Hom A A 
id {(U , V , α)} = (id-set , id-set , (λ {u} {y} → refl₃ {α u y}))

-- In this formalization we will only worry about proving that the
-- data of morphisms are equivalent, and not worry about the morphism
-- conditions.  This will make proofs shorter and faster.
--
-- If we have parallel morphisms (f,F) and (g,G) in which we know that
-- f = g and F = G, then the condition for (f,F) will imply the
-- condition of (g,G) and vice versa.  Thus, we can safly ignore it.
infix 4 _≡h_

_≡h_ : {A B : Obj} → (f g : Hom A B) → Set
_≡h_ {(U , X , α)}{(V , Y , β)} (f , F , p₁) (g , G , p₂) = f ≡ g × F ≡ G

≡h-refl : {A B : Obj}{f : Hom A B} → f ≡h f
≡h-refl {U , X , α}{V , Y , β}{f , F , _} = refl , refl

≡h-trans : ∀{A B}{f g h : Hom A B} → f ≡h g → g ≡h h → f ≡h h
≡h-trans {U , X , α}{V , Y , β}{f , F , _}{g , G , _}{h , H , _} (p₁ , p₂) (p₃ , p₄) rewrite p₁ | p₂ | p₃ | p₄ = refl , refl

≡h-sym : ∀{A B}{f g : Hom A B} → f ≡h g → g ≡h f
≡h-sym {U , X , α}{V , Y , β}{f , F , _}{g , G , _} (p₁ , p₂) rewrite p₁ | p₂ = refl , refl

≡h-subst-○ : ∀{A B C}{f₁ f₂ : Hom A B}{g₁ g₂ : Hom B C}{j : Hom A C}
  → f₁ ≡h f₂
  → g₁ ≡h g₂
  → f₂ ○ g₂ ≡h j
  → f₁ ○ g₁ ≡h j
≡h-subst-○ {U , X , α}
           {V , Y , β}
           {W , Z , γ}
           {f₁ , F₁ , _}
           {f₂ , F₂ , _}
           {g₁ , G₁ , _}
           {g₂ , G₂ , _}
           {j , J , _}
           (p₅ , p₆) (p₇ , p₈) (p₉ , p₁₀) rewrite p₅ | p₆ | p₇ | p₈ | p₉ | p₁₀ = refl , refl

○-assoc : ∀{A B C D}{f : Hom A B}{g : Hom B C}{h : Hom C D}
  → f ○ (g ○ h) ≡h (f ○ g) ○ h
○-assoc {U , X , α}{V , Y , β}{W , Z , γ}{S , T , ι}
        {f , F , _}{g , G , _}{h , H , _} = refl , refl

○-idl : ∀{A B}{f : Hom A B} → id ○ f ≡h f
○-idl {U , X , _}{V , Y , _}{f , F , _} = refl , refl

○-idr : ∀{A B}{f : Hom A B} → f ○ id ≡h f
○-idr {U , X , _}{V , Y , _}{f , F , _} = refl , refl

_⊙ᵣ_ : ∀{U X V Y : Set} → (U → X → Three) → (V → Y → Three) → ((U × V) → (X × Y) → Three)
_⊙ᵣ_ α β (u , v) (x , y) = (α u x) ⊙₃ (β v y)

_⊙_ : (A B : Obj) → Obj
(U , X , α) ⊙ (V , Y , β) = ((U × V) , (X × Y) , α ⊙ᵣ β)
  
_⊙ₐ_ : {A B C D : Obj} → Hom A C → Hom B D → Hom (A ⊙ B) (C ⊙ D)
_⊙ₐ_ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)}{(S , T , δ)} (f , F , p₁) (g , G , p₂) = ⟨ f , g ⟩ , func-× F G , (λ {p₁}{p₂} → cond {p₁}{p₂})
 where
   cond : {u : U × V} {y : Z × T} → (α ⊙ᵣ β) u (func-× F G y) ≤₃ (γ ⊙ᵣ δ) (⟨ f , g ⟩ u) y
   cond {u , v}{z , t} with p₁ {u}{z} | p₂ {v}{t}
   ... | r₁ | r₂ = ⊙₃-func {α u (F z)}{β v (G t)}{γ (f u) z}{δ (g v) t} r₁ r₂

⊙-α : {A B C : Obj} → Hom ((A ⊙ B) ⊙ C) (A ⊙ (B ⊙ C))
⊙-α {U , X , α}{V , Y , β}{W , Z , γ} = lr-assoc-× , (rl-assoc-× , (λ {p₁}{p₂} → cond {p₁}{p₂}))
 where
   cond : {u : (U × V) × W} {y : X × Y × Z} → ((α ⊙ᵣ β) ⊙ᵣ γ) u (rl-assoc-× y) ≤₃ (α ⊙ᵣ (β ⊙ᵣ γ)) (lr-assoc-× u) y
   cond {(u , v) , w}{x , y , z} = fst (iso₃-inv (⊙₃-assoc {α u x}{β v y}{γ w z}))

⊙-β : {A B : Obj} → Hom (A ⊙ B) (B ⊙ A)
⊙-β {U , X , α}{V , Y , β} = twist-× , (twist-× , (λ {p₁}{p₂} → cond {p₁}{p₂}))
 where
  cond : {u : U × V} {y : Y × X} → (α ⊙ᵣ β) u (twist-× y) ≤₃ (β ⊙ᵣ α) (twist-× u) y
  cond {u , v}{y , x} = fst (iso₃-inv (⊙₃-sym {α u x}{β v y}))

_▷ᵣ_ : ∀{U X V Y : Set} → (U → X → Three) → (V → Y → Three) → (U × V) → (X × Y) → Three
_▷ᵣ_ α β (u , v) (x , y) = (α u x) ▷₃ (β v y)

_▷_ : Obj → Obj → Obj
(U , X , α) ▷ (V , Y , β) = (U × V) , (X × Y) , α ▷ᵣ β

_▷ₐ_ : {A B C D : Obj} → Hom A C → Hom B D → Hom (A ▷ B) (C ▷ D)
_▷ₐ_ {U , X , α} {V , Y , β} {W , Z , γ} {M , T , φ} (f , F , p1) (g , G , p2) = (prod-func f g) , (prod-func F G , (λ {u : U × V}{y : Z × T} → aux {u}{y}))
 where
   prod-func : {U V W M : Set} → (U → W) → (V → M) → U × V → W × M
   prod-func f g ( u , v ) = (f u , g v)

   aux : {u : U × V} {y : Z × T} → _▷ᵣ_ α β u (prod-func F G y) ≤₃ _▷ᵣ_ γ φ (prod-func f g u) y
   aux {u , v}{z , t} = ▷₃-func {α u (F z)}{β v (G t)}{γ (f u) z}{φ (g v) t} (p1 {u}{z}) (p2 {v}{t})

▷-α : {A B C : Obj} → Hom ((A ▷ B) ▷ C) (A ▷ (B ▷ C))
▷-α {U , X , α}{V , Y , β}{W , Z , γ} = lr-assoc-× , (rl-assoc-× , (λ {p₁}{p₂} → cond {p₁}{p₂}))
 where
   cond : {u : (U × V) × W} {y : X × Y × Z} → ((α ▷ᵣ β) ▷ᵣ γ) u (rl-assoc-× y) ≤₃ (α ▷ᵣ (β ▷ᵣ γ)) (lr-assoc-× u) y
   cond {(u , v) , w}{x , y , z} = snd (iso₃-inv (▷₃-assoc {α u x}{β v y}{γ w z}))

_⊔ᵣ_ : {U V X Y : Set} → (U → X → Three) → (V → Y → Three) → U ⊎ V → X ⊎ Y → Three
_⊔ᵣ_ α β (inj₁ u) (inj₁ x) = α u x
_⊔ᵣ_ α β (inj₁ u) (inj₂ y) = zero
_⊔ᵣ_ α β (inj₂ v) (inj₁ x) = zero
_⊔ᵣ_ α β (inj₂ v) (inj₂ y) = β v y

_⊔ₒ_ : Obj → Obj → Obj
_⊔ₒ_ (U , X , α) (V , Y , β) = (U ⊎ V) , (X ⊎ Y) , α ⊔ᵣ β

_⊔ₐ_ : {A C B D : Obj} → Hom A C → Hom B D → Hom (A ⊔ₒ B) (C ⊔ₒ D)
_⊔ₐ_ {U , X , α} {V , Y , β} {W , Z , γ} {R , S , φ} (f , F , F-pf) (g , G , G-pf) = ⊎-map f g , (⊎-map F G , (λ {u}{v} → cond {u}{v}))
 where
   cond : {u : U ⊎ W} {y : Y ⊎ S} → (α ⊔ᵣ γ) u (⊎-map F G y) ≤₃ (β ⊔ᵣ φ) (⊎-map f g u) y
   cond {inj₁ u} {inj₁ y} = F-pf
   cond {inj₁ u} {inj₂ s} = triv
   cond {inj₂ w} {inj₁ y} = triv
   cond {inj₂ w} {inj₂ s} = G-pf
   
choose-assoc : ∀{A B C} → Hom (A ⊔ₒ (B ⊔ₒ C)) ((A ⊔ₒ B) ⊔ₒ C)
choose-assoc {U , X , α}{V , Y , β}{W , Z , γ} = ⊎-assoc , ⊎-assoc-inv , (λ {x y} → cond {x}{y})
 where
  cond : {u : U ⊎ V ⊎ W} {y : (X ⊎ Y) ⊎ Z} →      
      (_⊔ᵣ_ α (_⊔ᵣ_ β γ) u (⊎-assoc-inv y)) ≤₃ (_⊔ᵣ_ (α ⊔ᵣ β) γ (⊎-assoc u) y)
  cond {inj₁ x} {inj₁ (inj₁ y)} = refl₃ {α x y}
  cond {inj₁ x} {inj₁ (inj₂ y)} = triv
  cond {inj₁ x} {inj₂ y} = triv
  cond {inj₂ (inj₁ x)} {inj₁ (inj₁ y)} = triv
  cond {inj₂ (inj₁ x)} {inj₁ (inj₂ y)} = refl₃ {β x y}
  cond {inj₂ (inj₁ x)} {inj₂ y} = triv
  cond {inj₂ (inj₂ x)} {inj₁ (inj₁ y)} = triv
  cond {inj₂ (inj₂ x)} {inj₁ (inj₂ y)} = triv
  cond {inj₂ (inj₂ x)} {inj₂ y} = refl₃ {γ x y}

choose-assoc-inv : ∀{A B C} → Hom ((A ⊔ₒ B) ⊔ₒ C) (A ⊔ₒ (B ⊔ₒ C))
choose-assoc-inv {U , X , α}{V , Y , β}{W , Z , γ} = ⊎-assoc-inv , ⊎-assoc , (λ {u y} → cond {u}{y})
 where
   cond : {u : (U ⊎ V) ⊎ W} {y : X ⊎ Y ⊎ Z} →
     (_⊔ᵣ_ (_⊔ᵣ_ α β) γ u (⊎-assoc y)) ≤₃ (_⊔ᵣ_ α (_⊔ᵣ_ β γ) (⊎-assoc-inv u) y)
   cond {inj₁ (inj₁ x)} {inj₁ y} = refl₃ {α x y}
   cond {inj₁ (inj₁ x)} {inj₂ (inj₁ y)} = triv
   cond {inj₁ (inj₁ x)} {inj₂ (inj₂ y)} = triv
   cond {inj₁ (inj₂ x)} {inj₁ y} = triv
   cond {inj₁ (inj₂ x)} {inj₂ (inj₁ y)} = refl₃ {β x y}
   cond {inj₁ (inj₂ x)} {inj₂ (inj₂ y)} = triv
   cond {inj₂ x} {inj₁ y} = triv
   cond {inj₂ x} {inj₂ (inj₁ y)} = triv
   cond {inj₂ x} {inj₂ (inj₂ y)} = refl₃ {γ x y}

choose-assoc-iso₁ : ∀{A B C} → choose-assoc {A}{B}{C} ○ choose-assoc-inv ≡h id
choose-assoc-iso₁ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set ⊎-assoc-iso₁ , ext-set ⊎-assoc-iso₁

choose-assoc-iso₂ : ∀{A B C} → choose-assoc-inv {A}{B}{C} ○ choose-assoc ≡h id
choose-assoc-iso₂ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set ⊎-assoc-iso₂ , ext-set ⊎-assoc-iso₂

choose-sym : ∀{A B} → Hom (A ⊔ₒ B) (B ⊔ₒ A)
choose-sym {U , X , α}{V , Y , β} = ⊎-sym , ⊎-sym , (λ {u y} → cond {u}{y})
 where
   cond : {u : U ⊎ V} {y : Y ⊎ X} → (_⊔ᵣ_ α β u (⊎-sym y)) ≤₃ (_⊔ᵣ_ β α (⊎-sym u) y)
   cond {inj₁ x} {inj₁ y} = triv
   cond {inj₁ x} {inj₂ y} = refl₃ {α x y}
   cond {inj₂ x} {inj₁ y} = refl₃ {β x y}
   cond {inj₂ x} {inj₂ y} = triv

choose-contract : ∀{A : Obj} → Hom (A ⊔ₒ A) A
choose-contract {U , X , α} = aux₁ , inj₁ , (λ {u y} → cond {u}{y})
 where
  aux₁ : U ⊎ U → U
  aux₁ (inj₁ x) = x
  aux₁ (inj₂ y) = y

  cond : {u : U ⊎ U} {y : X} → (_⊔ᵣ_ α α u (inj₁ y)) ≤₃ (α (aux₁ u) y)
  cond {inj₁ u}{x} = refl₃ {α u x}
  cond {inj₂ u}{x} = triv

choice-seq-dist-aux₁ : {U V W : Set} → Σ (U ⊎ V) (λ x → W) → Σ U (λ x → W) ⊎ Σ V (λ x → W)
choice-seq-dist-aux₁ (inj₁ x , b) = inj₁ (x , b)
choice-seq-dist-aux₁ (inj₂ y , b) = inj₂ (y , b)

choice-seq-dist-aux₂ : {X Z Y : Set} → Σ X (λ x → Z) ⊎ Σ Y (λ x → Z) → Σ (X ⊎ Y) (λ x → Z)
choice-seq-dist-aux₂ (inj₁ (a , b)) = inj₁ a , b
choice-seq-dist-aux₂ (inj₂ (a , b)) = inj₂ a , b

choice-seq-dist : {A B C : Obj} → Hom ((A ⊔ₒ B) ▷ C) ((A ▷ C) ⊔ₒ (B ▷ C))
choice-seq-dist {U , X , α}{V , Y , β}{W , Z , γ} = choice-seq-dist-aux₁ , choice-seq-dist-aux₂ , (λ {u y} → cond {u}{y})
 where
  cond : {u : Σ (U ⊎ V) (λ x → W)}
      {y : Σ X (λ x → Z) ⊎ Σ Y (λ x → Z)} →
      _▷ᵣ_ (_⊔ᵣ_ α β) γ u (choice-seq-dist-aux₂ y)
      ≤₃
      _⊔ᵣ_ (_▷ᵣ_ α γ) (_▷ᵣ_ β γ) (choice-seq-dist-aux₁ u) y
  cond {inj₁ u , w} {inj₁ (a , b)} = refl₃ {α u a ▷₃ γ w b}
  cond {inj₁ u , w} {inj₂ (a , b)} = ▷₃-zero {γ w b}
  cond {inj₂ u , w} {inj₁ (a , b)} = ▷₃-zero {γ w b}
  cond {inj₂ u , w} {inj₂ (a , b)} = refl₃ {β u a ▷₃ γ w b}

choice-seq-dist-inv-aux₁ : {U W V : Set} → Σ U (λ x → W) ⊎ Σ V (λ x → W) → Σ (U ⊎ V) (λ x → W)
choice-seq-dist-inv-aux₁ (inj₁ (a , b)) = inj₁ a , b
choice-seq-dist-inv-aux₁ (inj₂ (a , b)) = inj₂ a , b

choice-seq-dist-inv-aux₂ : {X Y Z : Set} → Σ (X ⊎ Y) (λ x → Z) → Σ X (λ x → Z) ⊎ Σ Y (λ x → Z)
choice-seq-dist-inv-aux₂ (inj₁ x , z) = inj₁ (x , z)
choice-seq-dist-inv-aux₂ (inj₂ y , z) = inj₂ (y , z)
  
choice-seq-dist-inv : {A B C : Obj} → Hom ((A ▷ C) ⊔ₒ (B ▷ C)) ((A ⊔ₒ B) ▷ C)
choice-seq-dist-inv {U , X , α}{V , Y , β}{W , Z , γ} = choice-seq-dist-inv-aux₁ , choice-seq-dist-inv-aux₂ , (λ {u y} → cond {u}{y})
 where  
  cond : {u : Σ U (λ x → W) ⊎ Σ V (λ x → W)}
      {y : Σ (X ⊎ Y) (λ x → Z)} →
      _⊔ᵣ_ (_▷ᵣ_ α γ) (_▷ᵣ_ β γ) u (choice-seq-dist-inv-aux₂ y)
      ≤₃
      _▷ᵣ_
      (_⊔ᵣ_ α β) γ (choice-seq-dist-inv-aux₁ u) y
  cond {inj₁ (a , b)} {inj₁ x , y} = refl₃ {α a x ▷₃ γ b y}
  cond {inj₁ (a , b)} {inj₂ x , y} = triv
  cond {inj₂ (a , b)} {inj₁ x , y} = triv
  cond {inj₂ (a , b)} {inj₂ x , y} = refl₃ {β a x ▷₃ γ b y}

choice-seq-dist-iso₁ : {A B C : Obj} → choice-seq-dist {A}{B}{C} ○ choice-seq-dist-inv ≡h id {(A ⊔ₒ B) ▷ C}
choice-seq-dist-iso₁ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux₁ , ext-set aux₂
  where
    aux₁ : {a : Σ (U ⊎ V) (λ x → W)} → choice-seq-dist-inv-aux₁ (choice-seq-dist-aux₁ a) ≡ a
    aux₁ {inj₁ x , b} = refl
    aux₁ {inj₂ y , b} = refl

    aux₂ : {a : Σ (X ⊎ Y) (λ x → Z)} → choice-seq-dist-aux₂ (choice-seq-dist-inv-aux₂ a) ≡ a
    aux₂ {inj₁ x , b} = refl
    aux₂ {inj₂ y , b} = refl

choice-seq-dist-iso₂ : {A B C : Obj} → choice-seq-dist-inv {A}{B}{C} ○ choice-seq-dist ≡h id {(A ▷ C) ⊔ₒ (B ▷ C)}
choice-seq-dist-iso₂ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux₁ , ext-set aux₂
 where
   aux₁ : {a : Σ U (λ x → W) ⊎ Σ V (λ x → W)} → choice-seq-dist-aux₁ (choice-seq-dist-inv-aux₁ a) ≡ a
   aux₁ {inj₁ (a , b)} = refl
   aux₁ {inj₂ (a , b)} = refl

   aux₂ : {a : Σ X (λ x → Z) ⊎ Σ Y (λ x → Z)} → choice-seq-dist-inv-aux₂ (choice-seq-dist-aux₂ a) ≡ a
   aux₂ {inj₁ (a , b)} = refl
   aux₂ {inj₂ (a , b)} = refl

choice-para-distr-aux₁ : {U V W : Set} → (U ⊎ V) × W → U × W ⊎ V × W
choice-para-distr-aux₁ {U} {V} {W} (inj₁ u , w) = inj₁ (u , w)
choice-para-distr-aux₁ {U} {V} {W} (inj₂ v , w) = inj₂ (v , w)

choice-para-distr-aux₂ : {X Z Y : Set} → X × Z ⊎ Y × Z → (X ⊎ Y) × Z
choice-para-distr-aux₂ {X} {Z} {Y} (inj₁ (x , z)) = inj₁ x , z
choice-para-distr-aux₂ {X} {Z} {Y} (inj₂ (y , z)) = inj₂ y , z

choice-para-distr : {A B C : Obj} → Hom ((A ⊔ₒ B) ⊙ C) ((A ⊙ C) ⊔ₒ (B ⊙ C))
choice-para-distr {U , X , α}{V , Y , β}{W , Z , γ} = choice-para-distr-aux₁ , (choice-para-distr-aux₂ , (λ {u y} → cond {u}{y}))
 where
  cond : {u : (U ⊎ V) × W} {y : X × Z ⊎ Y × Z} → ((α ⊔ᵣ β) ⊙ᵣ γ) u (choice-para-distr-aux₂ y) ≤₃ ((α ⊙ᵣ γ) ⊔ᵣ (β ⊙ᵣ γ)) (choice-para-distr-aux₁ u) y
  cond {inj₁ u , w} {inj₁ (x , z)} =  refl₃ {α u x ⊙₃ γ w z} 
  cond {inj₁ u , w} {inj₂ (y , z)} = triv
  cond {inj₂ v , w} {inj₁ (x , z)} = triv
  cond {inj₂ v , w} {inj₂ (y , z)} = refl₃ {β v y ⊙₃ γ w z}

choice-para-distr-inv-aux₁ : {U W V : Set} → U × W ⊎ V × W → (U ⊎ V) × W
choice-para-distr-inv-aux₁ {U} {W} {V} (inj₁ (u , w)) = (inj₁ u) , w
choice-para-distr-inv-aux₁ {U} {W} {V} (inj₂ (v , w)) = (inj₂ v) , w

choice-para-distr-inv-aux₂ : {X Y Z : Set} → (X ⊎ Y) × Z → X × Z ⊎ Y × Z
choice-para-distr-inv-aux₂ {X} {Y} {Z} (inj₁ x , z) = inj₁ (x , z)
choice-para-distr-inv-aux₂ {X} {Y} {Z} (inj₂ y , z) = inj₂ (y , z)

choice-para-distr-inv : {A B C : Obj} → Hom ((A ⊙ C) ⊔ₒ (B ⊙ C)) ((A ⊔ₒ B) ⊙ C)
choice-para-distr-inv {U , X , α}{V , Y , β}{W , Z , γ} = choice-para-distr-inv-aux₁ , (choice-para-distr-inv-aux₂ , (λ {u y} → cond {u}{y}))
 where
   cond : {u : U × W ⊎ V × W} {y : (X ⊎ Y) × Z} → ((α ⊙ᵣ γ) ⊔ᵣ (β ⊙ᵣ γ)) u (choice-para-distr-inv-aux₂ y) ≤₃ ((α ⊔ᵣ β) ⊙ᵣ γ) (choice-para-distr-inv-aux₁ u) y
   cond {inj₁ (u , w)} {inj₁ x , z} = refl₃ {α u x ⊙₃ γ w z} 
   cond {inj₁ (v , w)} {inj₂ y , z} = triv
   cond {inj₂ (u , w)} {inj₁ x , z} = triv
   cond {inj₂ (v , w)} {inj₂ y , z} = refl₃ {β v y ⊙₃ γ w z}

choice-para-distr-iso₁ : {A B C : Obj} → choice-para-distr {A}{B}{C} ○ choice-para-distr-inv {A}{B}{C} ≡h id {(A ⊔ₒ B) ⊙ C}
choice-para-distr-iso₁ {U , X , α}{V , Y , β}{W , Z , γ} = (ext-set aux₁) , ext-set aux₂
 where
  aux₁ : {a : (U ⊎ V) × W} → (choice-para-distr-inv-aux₁ ∘ choice-para-distr-aux₁) a ≡ id-set a
  aux₁ {inj₁ u , w} = refl
  aux₁ {inj₂ v , w} = refl

  aux₂ : {a : (X ⊎ Y) × Z} → (choice-para-distr-aux₂ ∘ choice-para-distr-inv-aux₂) a ≡ id-set a
  aux₂ {inj₁ x , z} = refl
  aux₂ {inj₂ y , z} = refl

choice-para-distr-iso₂ : {A B C : Obj} → choice-para-distr-inv {A}{B}{C} ○ choice-para-distr {A}{B}{C} ≡h id {(A ⊙ C) ⊔ₒ (B ⊙ C)}
choice-para-distr-iso₂ {U , X , α}{V , Y , β}{W , Z , γ} = (ext-set aux₁) , ext-set aux₂
 where
  aux₁ : {a : U × W ⊎ V × W} → (choice-para-distr-aux₁ ∘ choice-para-distr-inv-aux₁) a ≡ id-set a
  aux₁ {inj₁ (u , w)} = refl
  aux₁ {inj₂ (v , w)} = refl

  aux₂ : {a : X × Z ⊎ Y × Z} → (choice-para-distr-inv-aux₂ ∘ choice-para-distr-aux₂) a ≡ id-set a
  aux₂ {inj₁ (x , z)} = refl
  aux₂ {inj₂ (y , z)} = refl

choice-para-distr-nat : {A A' B B' C C' : Obj}
  → (f : Hom A A')
  → (g : Hom B B')
  → (h : Hom C C')
  → ((f ⊔ₐ g) ⊙ₐ h) ○ choice-para-distr {A'}{B'}{C'} ≡h choice-para-distr {A}{B}{C} ○ ((f ⊙ₐ h) ⊔ₐ (g ⊙ₐ h))
choice-para-distr-nat {U , X , α}{U' , X' , α'}{V , Y , β}{V' , Y' , β'}{W , Z , γ}{W' , Z' , γ'} (f , F , F-pf) (g , G , G-pf) (h , H , H-pf) = (ext-set aux₁) , ext-set (λ {a} → aux₂ {a})
 where
  aux₁ : {a : (U ⊎ V) × W} → (choice-para-distr-aux₁ ∘ ⟨ ⊎-map f g , h ⟩) a ≡ (⊎-map ⟨ f , h ⟩ ⟨ g , h ⟩ ∘ choice-para-distr-aux₁) a
  aux₁ {inj₁ u , w} = refl
  aux₁ {inj₂ v , w} = refl

  aux₂ : {a : X' × Z' ⊎ Y' × Z'} → (func-× (⊎-map F G) H ∘ choice-para-distr-aux₂) a ≡ (choice-para-distr-aux₂ ∘ ⊎-map (func-× F H) (func-× G H)) a
  aux₂ {inj₁ (x' , z')} = refl
  aux₂ {inj₂ (y' , z')} = refl

choice-para-distl-aux₁ : {U V W : Set} → U × (V ⊎ W) → U × V ⊎ U × W
choice-para-distl-aux₁ {U} {V} {W} (u , inj₁ v) = inj₁ (u , v)
choice-para-distl-aux₁ {U} {V} {W} (u , inj₂ w) = inj₂ (u , w)

choice-para-distl-aux₂ : {X Y Z : Set} → X × Y ⊎ X × Z → X × (Y ⊎ Z)
choice-para-distl-aux₂ {X} {Y} {Z} (inj₁ (x , y)) = x , inj₁ y
choice-para-distl-aux₂ {X} {Y} {Z} (inj₂ (x , z)) = x , inj₂ z

choice-para-distl : {A B C : Obj} → Hom (A ⊙ (B ⊔ₒ C)) ((A ⊙ B) ⊔ₒ (A ⊙ C))
choice-para-distl {U , X , α}{V , Y , β}{W , Z , γ} = choice-para-distl-aux₁ , (choice-para-distl-aux₂ , (λ {u}{v} → cond {u}{v}))
 where
   cond : {u : U × (V ⊎ W)} {y : X × Y ⊎ X × Z} → (α ⊙ᵣ (β ⊔ᵣ γ)) u (choice-para-distl-aux₂ y) ≤₃ ((α ⊙ᵣ β) ⊔ᵣ (α ⊙ᵣ γ)) (choice-para-distl-aux₁ u) y
   cond {u , inj₁ v} {inj₁ (x , y)} = refl₃ {α u x ⊙₃ β v y}
   cond {u , inj₁ v} {inj₂ (x , z)} = ⊙₃-zero {α u x}
   cond {u , inj₂ w} {inj₁ (x , y)} = ⊙₃-zero {α u x}
   cond {u , inj₂ w} {inj₂ (x , z)} = refl₃ {α u x ⊙₃ γ w z}

choice-seq-distl : {A B C : Obj} → Hom (A ▷ (B ⊔ₒ C)) ((A ▷ B) ⊔ₒ (A ▷ C))
choice-seq-distl {U , X , α}{V , Y , β}{W , Z , γ} = choice-para-distl-aux₁ , (choice-para-distl-aux₂ , {!!})
 where
   cond : {u : U × (V ⊎ W)} {y : X × Y ⊎ X × Z} → (α ▷ᵣ (β ⊔ᵣ γ)) u (choice-para-distl-aux₂ y) ≤₃ ((α ▷ᵣ β) ⊔ᵣ (α ▷ᵣ γ)) (choice-para-distl-aux₁ u) y
   cond {u , inj₁ v} {inj₁ (x , y)} = refl₃ {α u x ▷₃ β v y}
   cond {u , inj₁ v} {inj₂ (x , z)} = {!!}
   cond {u , inj₂ w} {inj₁ (x , y)} = {!!}
   cond {u , inj₂ w} {inj₂ (x , z)} = refl₃ {α u x ▷₃ γ w z}

{-
-- -----------------------------------------------------------------------
-- -- The SMCC Structure                                                --
-- -----------------------------------------------------------------------

-- -- The tensor functor: ⊗
-- _⊗ᵣ_ : ∀{U X V Y : Set ℓ} → (U → X → L) → (V → Y → L) → ((U × V) → ((V → X) × (U → Y)) → L)
-- _⊗ᵣ_ α β (u , v) (f , g) = (α u (f v)) ⊗L (β v (g u))

-- _⊗ₒ_ : (A B : Obj) → Obj
-- (U , X , α) ⊗ₒ (V , Y , β) = ((U × V) , ((V → X) × (U → Y)) , α ⊗ᵣ β)


-- F⊗ : ∀{S Z W T V X U Y : Set ℓ}{f : U → W}{F : Z → X}{g : V → S}{G : T → Y} → (S → Z) × (W → T) → (V → X) × (U → Y)
-- F⊗ {f = f}{F}{g}{G} (h₁ , h₂) = (λ v → F(h₁ (g v))) , (λ u → G(h₂ (f u)))
  
-- _⊗ₐ_ : {A B C D : Obj} → Hom A C → Hom B D → Hom (A ⊗ₒ B) (C ⊗ₒ D)
-- _⊗ₐ_ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)}{(S , T , δ)} (f , F , p₁) (g , G , p₂) = ⟨ f , g ⟩ , F⊗ {f = f}{F}{g}{G} , (λ {u y} → cond {u}{y})
--  where
--   cond : {u : Σ U (λ x → V)} {y : Σ (S → Z) (λ x → W → T)} →
--       ((α ⊗ᵣ β) u (F⊗ {f = f}{F}{g}{G} y)) ≤L ((γ ⊗ᵣ δ) (⟨ f , g ⟩ u) y)
--   cond {u , v}{h , j} = l-mul-funct {p = mproset l-pf} (p₁ {u}{h (g v)}) (p₂ {v}{j (f u)}) 


-- -- The unit for tensor:
-- ι : ⊤ {ℓ} → ⊤ {ℓ} → L
-- ι triv triv = unitL

-- I : Obj
-- I = (⊤ , ⊤ , ι)

-- -- The left-unitor:   
-- λ⊗ : ∀{A : Obj} → Hom (I ⊗ₒ A) A
-- λ⊗ {(U , X , α)} = snd , (λ x → (λ _ → triv) , (λ _ → x)) , (λ {u y} → cond {u}{y})
--  where
--   cond : {u : Σ ⊤ (λ x → U)} {y : X} →
--       ((ι ⊗ᵣ α) u ((λ _ → triv) , (λ _ → y))) ≤L (α (snd u) y)
--   cond {triv , u}{x} rewrite left-identL {α u x} = reflL


-- λ⁻¹⊗ : ∀{A : Obj} → Hom A (I ⊗ₒ A)
-- λ⁻¹⊗ {(U , X , α)} = (λ u → triv , u) , ((λ x → snd x triv) , (λ {u y} → cond {u}{y}))
--  where
--   cond : {u : U} {y : Σ (U → ⊤) (λ x → ⊤ → X)} →
--     (α u (snd y triv)) ≤L ((ι ⊗ᵣ α) (triv , u) y)
--   cond {u}{t₁ , t₂} with t₂ triv | t₁ u
--   ... | x | triv rewrite left-identL {α u x} = reflL


-- -- The right-unitor:
-- ρ⊗ : ∀{A : Obj} → Hom (A ⊗ₒ I) A
-- ρ⊗ {(U , X , α)} = fst , (λ x → (λ x₁ → x) , (λ x₁ → triv)) , (λ {u y} → cond {u}{y})
--  where
--   cond : {u : Σ U (λ x → ⊤)} {y : X} →
--       ((α ⊗ᵣ ι) u ((λ x₁ → y) , (λ x₁ → triv))) ≤L (α (fst u) y)
--   cond {u , triv}{x} rewrite right-identL {α u x} = reflL


-- ρ⊗-inv : ∀{A : Obj} → Hom A (A ⊗ₒ I)
-- ρ⊗-inv {(U , X , α)} = (λ x → x , triv) , (λ x → fst x triv) , (λ {u y} → cond {u}{y})
--  where
--   cond : {u : U} {y : Σ (⊤ → X) (λ x → U → ⊤)} →
--        (α u (fst y triv)) ≤L ((α ⊗ᵣ ι) (u , triv) y)
--   cond {u}{t₁ , t₂} with t₁ triv | t₂ u
--   ... | x | triv rewrite right-identL {α u x} = reflL

-- -- Symmetry:
-- β⊗ : ∀{A B : Obj} → Hom (A ⊗ₒ B) (B ⊗ₒ A)
-- β⊗ {(U , X , α)}{(V , Y , β)} = twist-× , twist-× , (λ {u y} → cond {u}{y})
--  where
--    cond : {u : Σ U (λ x → V)} {y : Σ (U → Y) (λ x → V → X)} →
--         ((α ⊗ᵣ β) u (twist-× y)) ≤L ((β ⊗ᵣ α) (twist-× u) y)
--    cond {u , v}{t₁ , t₂} rewrite symmL {(α u (t₂ v))} {(β v (t₁ u))} = reflL

-- -- The associator:
-- α⊗-inv : ∀{A B C : Obj} → Hom (A ⊗ₒ (B ⊗ₒ C)) ((A ⊗ₒ B) ⊗ₒ C)
-- α⊗-inv {(U , X , α)}{(V , Y , β)}{(W , Z , γ)} = rl-assoc-× , Fα-inv , (λ {u y} → cond {u}{y})
--  where
--    Fα-inv : (W → (V → X) × (U → Y)) × (U × V → Z) → (V × W → X) × (U → (W → Y) × (V → Z))
--    Fα-inv = (λ p → (λ p' → fst ((fst p) (snd p')) (fst p')) , (λ u → (λ w → snd (fst p w) u) , (λ v → (snd p) (u , v))))
--    cond : {u : Σ U (λ x → Σ V (λ x₁ → W))}
--       {y : Σ (W → Σ (V → X) (λ x → U → Y)) (λ x → Σ U (λ x₁ → V) → Z)} →        
--       ((α ⊗ᵣ (β ⊗ᵣ γ)) u
--        ((λ p' → fst (fst y (snd p')) (fst p')) ,
--         (λ u₁ → (λ w → snd (fst y w) u₁) , (λ v → snd y (u₁ , v)))))
--         ≤L
--       (((α ⊗ᵣ β) ⊗ᵣ γ) (rl-assoc-× u) y)
--    cond {u , (v , w)}{t₁ , t₂} with t₁ w | t₂ (u , v)
--    ... | t₃ , t₄ | z rewrite assocL {(α u (t₃ v))}{(β v (t₄ u))}{(γ w z)} = reflL

-- Fα : ∀{V W X Y U V Z : Set ℓ} → Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z))
--        → Σ (W → Σ (V → X) (λ x → U → Y)) (λ x → Σ U (λ x₁ → V) → Z)
-- Fα (f ,  g) = (λ x → (λ x₁ → f ((x₁ , x))) , (λ x₁ → fst (g x₁) x)) , (λ x → snd (g (fst x)) (snd x))


-- α⊗ : ∀{A B C : Obj} → Hom ((A ⊗ₒ B) ⊗ₒ C) (A ⊗ₒ (B ⊗ₒ C)) 
-- α⊗ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)} = (lr-assoc-× , Fα {V} , (λ {u y} → cond {u}{y}))
--  where
--   cond : {u : Σ (Σ U (λ x → V)) (λ x → W)}
--       {y : Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z))} →
--       (((α ⊗ᵣ β) ⊗ᵣ γ) u (Fα {V} y)) ≤L ((α ⊗ᵣ (β ⊗ᵣ γ)) (lr-assoc-× u) y)
--   cond {(u , v) , w}{t₁ , t₂} with t₂ u
--   ... | t₃ , t₄ rewrite sym (assocL {(α u (t₁ (v , w)))}{(β v (t₃ w))}{(γ w (t₄ v))}) = reflL


-- α⊗-id₁ : ∀{A B C} → (α⊗ {A}{B}{C}) ○ α⊗-inv ≡h id
-- α⊗-id₁ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux , ext-set aux'
--  where
--    aux : {a : Σ (Σ U (λ x → V)) (λ x → W)} → rl-assoc-× (lr-assoc-× a) ≡ a
--    aux {(u , v) , w} = refl

--    aux' : {a : Σ (W → Σ (V → X) (λ x → U → Y)) (λ x → Σ U (λ x₁ → V) → Z)}
--      → ((λ x → (λ x₁ → fst (fst a x) x₁) , (λ x₁ → snd (fst a x) x₁)) , (λ x → snd a (fst x , snd x))) ≡ a
--    aux' {j₁ , j₂} = eq-× (ext-set aux'') (ext-set aux''')
--     where
--       aux'' : {a : W} → (fst (j₁ a) , snd (j₁ a)) ≡ j₁ a
--       aux'' {w} with j₁ w
--       ... | h₁ , h₂ = refl

--       aux''' : {a : Σ U (λ x₁ → V)} → j₂ (fst a , snd a) ≡ j₂ a
--       aux''' {u , v} = refl

-- α⊗-id₂ : ∀{A B C} → (α⊗-inv {A}{B}{C}) ○ α⊗ ≡h id
-- α⊗-id₂ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux , ext-set aux'
--  where
--    aux : {a : Σ U (λ x → Σ V (λ x₁ → W))} → lr-assoc-× (rl-assoc-× a) ≡ a
--    aux {u , (v , w)} = refl
--    aux' : {a
--        : Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z))} →
--       ((λ p' → fst (fst (Fα {V} {W} {X} {Y} {U} {V} {Z} a) (snd p')) (fst p')) ,
--        (λ u → (λ w → snd (fst (Fα {V} {W} {X} {Y} {U} {V} {Z} a) w) u) , (λ v → snd (Fα {V} {W} {X} {Y} {U} {V} {Z} a) (u , v))))
--       ≡ a
--    aux' {j₁ , j₂} = eq-× (ext-set aux'') (ext-set aux''')
--      where
--        aux'' : {a : Σ V (λ x → W)} → j₁ (fst a , snd a) ≡ j₁ a
--        aux'' {v , w} = refl
--        aux''' : {a : U} → ((λ w → fst (j₂ a) w) , (λ v → snd (j₂ a) v)) ≡ j₂ a
--        aux''' {u} with j₂ u
--        ... | h₁ , h₂ = refl


-- -- Internal hom:
-- ⊸-cond : ∀{U V X Y : Set ℓ} → (U → X → L) → (V → Y → L) → (U → V) × (Y → X) → U × Y → L
-- ⊸-cond α β (f , g) (u , y) = α u (g y) →L β (f u) y

-- _⊸ₒ_ : Obj → Obj → Obj
-- (U , X , α) ⊸ₒ (V , Y , β) = ((U → V) × (Y → X)) , (U × Y) , ⊸-cond α β


-- _⊸ₐ_ : {A B C D : Obj} → Hom C A → Hom B D → Hom (A ⊸ₒ B) (C ⊸ₒ D)
-- _⊸ₐ_ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)}{(S , T , δ)} (f , F , p₁) (g , G , p₂) =
--   h , H , (λ {u y} → cond {u}{y})
--   where
--    h : Σ (U → V) (λ x → Y → X) → Σ (W → S) (λ x → T → Z)
--    h (h₁ , h₂) = (λ w → g (h₁ (f w))) , (λ t → F (h₂ (G t)))
--    H : Σ W (λ x → T) → Σ U (λ x → Y)
--    H (w , t) = f w , G t
--    cond : {u : Σ (U → V) (λ x → Y → X)} {y : Σ W (λ x → T)} →
--         (⊸-cond α β u (H y)) ≤L (⊸-cond γ δ (h u) y)
--    cond {t₁ , t₂}{w , t} = l-imp-funct {p = l-pf} p₁ p₂


-- cur : {A B C : Obj}
--   → Hom (A ⊗ₒ B) C
--   → Hom A (B ⊸ₒ C)
-- cur {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁)
--   = (λ u → (λ v → f (u , v)) , (λ z → snd (F z) u)) , (λ p →  fst (F (snd p)) (fst p)) , (λ {u y} → cond {u}{y})
--  where
--    cond : {u : U} {y : Σ V (λ x → Z)} →
--       (α u (fst (F (snd y)) (fst y))) ≤L (⊸-cond β γ ((λ v → f (u , v)) , (λ z → snd (F z) u)) y)
--    cond {u}{v , z} with p₁ {u , v}{z}
--    ... | p₂ with F z
--    ... | t₁ , t₂ rewrite symmL {α u (t₁ v)}{β v (t₂ u)} = adjL p₂


-- cur-≡h : ∀{A B C}{f₁ f₂ : Hom (A ⊗ₒ B) C}
--   → f₁ ≡h f₂
--   → cur f₁ ≡h cur f₂
-- cur-≡h {U , X , α}{V , Y , β}{W , Z , γ}
--        {f₁ , F₁ , p₁}{f₂ , F₂ , p₂} (p₃ , p₄)
--        rewrite p₃ | p₄ = refl , refl


-- uncur : {A B C : Obj}
--   → Hom A (B ⊸ₒ C)
--   → Hom (A ⊗ₒ B) C
-- uncur {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁)
--   = (λ p → fst (f (fst p)) (snd p)) , (λ z → (λ v → F (v , z)) , (λ u → snd (f u) z)) , (λ {u y} → cond {u}{y})
--   where
--     cond : {u : Σ U (λ x → V)} {y : Z} →
--          ((α ⊗ᵣ β) u ((λ v → F (v , y)) , (λ u₁ → snd (f u₁) y))) ≤L (γ (fst (f (fst u)) (snd u)) y)
--     cond {u , v}{z} with p₁ {u}{v , z}
--     ... | p₂ with f u
--     ... | t₁ , t₂ rewrite symmL {(α u (F (v , z)))}{β v (t₂ z)} = adj-inv {r = l-pf} p₂


-- cur-uncur-bij₁ : ∀{A B C}{f : Hom (A ⊗ₒ B) C}
--   → uncur (cur f) ≡h f
-- cur-uncur-bij₁ {U , X , α}{V , Y , β}{W , Z , γ}{f , F , p₁} = ext-set aux₁ , ext-set aux₂
--  where
--    aux₁ : {a : Σ U (λ x → V)} → f (fst a , snd a) ≡ f a
--    aux₁ {u , v} = refl
   
--    aux₂ : {a : Z} → ((λ v → fst (F a) v) , (λ u → snd (F a) u)) ≡ F a
--    aux₂ {z} with F z
--    ... | j₁ , j₂ = refl

-- cur-uncur-bij₂ : ∀{A B C}{g : Hom A (B ⊸ₒ C)}
--   → cur (uncur g) ≡h g
-- cur-uncur-bij₂ {U , X , α}{V , Y , β}{W , Z , γ}{g , G , p₁} = ext-set aux₁ , ext-set aux₂
--  where
--    aux₁ : {a : U} → ((λ v → fst (g a) v) , (λ z → snd (g a) z)) ≡ g a
--    aux₁ {u} with g u
--    ... | (j₁ , j₂) = refl

--    aux₂ : {a : Σ V (λ x → Z)} → G (fst a , snd a) ≡ G a
--    aux₂ {v , z} = refl

-- -----------------------------------------------------------------------
-- -- Additives                                                         --
-- -----------------------------------------------------------------------

-- +-ident : Obj
-- +-ident = ⊥ , ⊤ , (λ x y → ∅)

-- +-cond : ∀{U V X Y : Set ℓ} → (U → X → L) → (V → Y → L) → U ⊎ V → X × Y → L
-- +-cond α β (inj₁ u) (x , y) = α u x
-- +-cond α β (inj₂ v) (x , y) = β v y

-- _+_ : Obj → Obj → Obj
-- (U , X , α) + (V , Y , β) = (U ⊎ V) , (X × Y) , +-cond α β

-- +-terminalₐ : ∀{A} → Hom +-ident A
-- +-terminalₐ {U , X , α} = (λ x → ⊥-elim {ℓ} x) , (λ x → triv) , (λ {u y} → cond {u}{y})
--  where
--    cond : {u : ⊥ {ℓ}} {y : X} → ∅ ≤L (α (⊥-elim u) y)
--    cond {u}{x} = ⊥-elim {ℓ} u

-- +-inj₁ : ∀{A B} → Hom A (A + B)
-- +-inj₁ {U , X , α}{V , Y , β} = inj₁ , (fst , (λ {u y} → cond {u}{y}))
--  where
--   cond : {u : U} {y : Σ X (λ x → Y)} →
--        (α u (fst y)) ≤L (+-cond α β (inj₁ u) y)
--   cond {y = a , b} = reflL

-- +-inj₂ : ∀{A B} → Hom B (A + B)
-- +-inj₂ {U , X , α}{V , Y , β} = inj₂ , snd , (λ {u y} → cond {u}{y})
--  where
--    cond : {u : V} {y : Σ X (λ x → Y)} →
--       (β u (snd y)) ≤L (+-cond α β (inj₂ u) y)
--    cond {u}{x , y} = reflL

-- +-ar : ∀{A B C} → (f : Hom A C) → (g : Hom B C) → Hom (A + B) C
-- +-ar {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁) (g , G , p₂) = ⊎-ar f g , trans-× F G , (λ {u y} → cond {u}{y})
--  where
--    cond : {u : U ⊎ V} {y : Z} → (+-cond α β u (F y , G y)) ≤L (γ (⊎-ar f g u) y)
--    cond {inj₁ u}{z} = p₁
--    cond {inj₂ v}{z} = p₂

-- +-diag₁ : ∀{A B C} → (f : Hom A C) → (g : Hom B C) → +-inj₁ ○ (+-ar f g) ≡h f
-- +-diag₁ {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁) (g , G , p₂) = refl , refl

-- +-diag₂ : ∀{A B C} → (f : Hom A C) → (g : Hom B C) → +-inj₂ ○ (+-ar f g) ≡h g
-- +-diag₂ {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁) (g , G , p₂) = refl , refl

-- -----------------------------------------------------------------------
-- -- The of-course exponential                                         --
-- -----------------------------------------------------------------------

-- !ₒ-cond : ∀{U X : Set ℓ}
--   → (U → X → L)
--   → U
--   → (U → X *)
--   → L
-- !ₒ-cond α u f =  foldr (λ a r → (α u a) ⊗L r) unitL (f u) 
   
-- !ₒ : Obj → Obj
-- !ₒ (U , X , α) = U , (U → X *) , !ₒ-cond α


-- !-cta : {V Y U X : Set ℓ}
--   → (Y → X)
--   → (U → V)
--   → (V → Y *)
--   → (U → X *)
-- !-cta F f g = λ u → list-funct F (g (f u))
      
-- !ₐ : {A B : Obj} → Hom A B → Hom (!ₒ A) (!ₒ B)
-- !ₐ {U , X , α}{V , Y , β} (f , F , p) = f , !-cta F f , (λ {u y} → cond {u} {y})
--  where
--    cond : {u : U} {y : V → 𝕃 Y} →        
--       (foldr (λ a y₁ → (α u a) ⊗L y₁) unitL (map F (y (f u))))
--       ≤L
--       (foldr (λ a y₁ → (β (f u) a) ⊗L y₁) unitL (y (f u)))
--    cond {u}{t} = aux {t (f u)}
--      where
--        aux : {l : 𝕃 Y} →
--          (foldr (λ a y →(α u a) ⊗L y) unitL
--          (map F l))
--          ≤L
--          (foldr (λ a y → (β (f u) a) ⊗L y) unitL l)
--        aux {[]} = reflL
--        aux {y :: ys} with aux {ys}
--        ... | IH = l-mul-funct {p = mproset l-pf} (p {u}{y}) IH

-- -- The unit of the comonad:
-- ε : ∀{A} → Hom (!ₒ A) A
-- ε {U , X , α} = id-set , (λ x y → [ x ]) , cond
--  where
--   cond : {u : U} {y : X} →      
--       ((α u y) ⊗L unitL) ≤L (α u y)
--   cond {u}{x} rewrite right-identL {α u x} = reflL

-- -- The duplicator of the comonad:
-- δ-cta : {U X : Set ℓ} → (U → 𝕃 (U → 𝕃 X)) → U → 𝕃 X
-- δ-cta g u = foldr (λ f rest → (f u) ++ rest) [] (g u)
  
-- δ : ∀{A} → Hom (!ₒ A) (!ₒ (!ₒ A))
-- δ {U , X , α} = id-set , δ-cta , (λ {u y} → cond {u}{y})
--   where
--    cond : {u : U} {y : U → 𝕃 (U → 𝕃 X)} →      
--       (foldr (λ a y₁ → (α u a) ⊗L y₁) unitL
--        (foldr (λ f → _++_ (f u)) [] (y u)))
--       ≤L
--       (foldr
--        (λ a y₁ →          
--           (foldr (λ a₁ y₂ → (α u a₁) ⊗L y₂)
--            unitL (a u))
--            ⊗L
--           y₁)
--        unitL (y u))
--    cond {u}{t} = aux {t u}
--     where
--      aux : {l : 𝕃 (U → 𝕃 X)} → rel (proset (mproset l-pf))
--       (foldr (λ a y → mul (mproset l-pf) (α u a) y) (unit (mproset l-pf))
--        (foldr (λ f → _++_ (f u)) [] l))
--       (foldr
--        (λ a y →
--           mul (mproset l-pf)
--           (foldr (λ a₁ y₁ → mul (mproset l-pf) (α u a₁) y₁)
--            (unit (mproset l-pf)) (a u))
--           y)
--        (unit (mproset l-pf)) l)      
--      aux {[]} = reflL
--      aux {t₁ :: ts} with aux {ts}
--      ... | IH with t₁ u
--      ... | [] rewrite left-identL {(foldr
--         (λ a → _⊗L_ (foldr (λ a₁ → _⊗L_ (α u a₁)) unitL (a u)))
--         unitL
--         ts)} = IH
--      ... | x :: xs rewrite
--            sym (foldr-monoid {l₁ = xs}{foldr (λ f → _++_ (f u)) [] ts}{_⊗L_}{α u}{unitL}{left-identL}{assocL})
--          | assocL {(α u x)}{(foldr (λ x₁ → mul (mproset l-pf) (α u x₁)) (unit (mproset l-pf)) xs)}{(foldr (λ x₁ → mul (mproset l-pf) (α u x₁)) (unit (mproset l-pf)) (foldr (λ f → _++_ (f u)) [] ts))}
--       = compat-sym {p = mproset l-pf} IH     

-- -- The proper diagrams:
-- comonand-diag₁ : ∀{A}
--   → (δ {A}) ○ (!ₐ (δ {A})) ≡h (δ {A}) ○ (δ { !ₒ A})
-- comonand-diag₁ {U , X , α} =
--   refl , ext-set (λ {a} → ext-set (λ {a₁} → aux {a₁}{a a₁}))
--  where
--    aux : ∀{a₁ : U}{l : 𝕃 (U → 𝕃 (U → 𝕃 X))} →
--       foldr (λ f → _++_ (f a₁)) []
--       (map (λ g u → foldr (λ f → _++_ (f u)) [] (g u)) l)
--       ≡
--       foldr (λ f → _++_ (f a₁)) [] (foldr (λ f → _++_ (f a₁)) [] l)
--    aux {a}{[]} = refl  
--    aux {a}{x :: l} rewrite
--      sym (foldr-append-fun {l₁ = x a}{foldr (λ f → _++_ (f a)) [] l}{a})
--      = cong2 {a = foldr (λ f → _++_ (f a)) [] (x a)}
--              _++_
--              refl
--              (aux {a}{l})

-- comonand-diag₂ : ∀{A}
--   → (δ {A}) ○ (ε { !ₒ A}) ≡h (δ {A}) ○ (!ₐ (ε {A}))
-- comonand-diag₂ {U , X , α} =
--   refl , ext-set (λ {f} → ext-set (λ {a} → aux {a}{f a}))
--  where
--   aux : ∀{a : U}{l : X *}
--     → l ++ [] ≡ foldr (λ f₁ → _++_ (f₁ a)) [] (map (λ x y → x :: []) l)
--   aux {a}{[]} = refl
--   aux {a}{x :: l} with aux {a}{l}
--   ... | IH rewrite ++[] l =
--     cong2 {a = x} {x} {l}
--           {foldr (λ f₁ → _++_ (f₁ a)) [] (map (λ x₁ y → x₁ :: []) l)} _::_ refl
--           IH

-- -----------------------------------------------------------------------
-- -- Experimental defintions                                           --
-- -----------------------------------------------------------------------

-- J : Obj
-- J = (⊥ , ⊥ , (λ x y → ∅))

-- -- We show enough to see that choice is symmetric monoidal, but we can
-- -- easily see that all of the symmetric monoidal properties of
-- -- disjoint union will lift up to the dialectica space.  Notice that
-- -- it is not, however, a coproduct.
-- _⊔ᵣ_ : {U V X Y : Set ℓ} → (U → X → L) → (V → Y → L) → U ⊎ V → X ⊎ Y → L
-- _⊔ᵣ_ α β (inj₁ x) (inj₁ y) = α x y
-- _⊔ᵣ_ α β (inj₁ x) (inj₂ y) = ∅
-- _⊔ᵣ_ α β (inj₂ x) (inj₁ y) = ∅
-- _⊔ᵣ_ α β (inj₂ x) (inj₂ y) = β x y

-- choose : Obj → Obj → Obj
-- choose (U , X , α) (V , Y , β) = (U ⊎ V) , (X ⊎ Y) , _⊔ᵣ_ α β

-- _⊔ₒ_ : Obj → Obj → Obj
-- x ⊔ₒ y = choose x y

-- choose-assoc : ∀{A B C} → Hom (choose A (choose B C)) (choose (choose A B) C)
-- choose-assoc {U , X , α}{V , Y , β}{W , Z , γ} = ⊎-assoc , ⊎-assoc-inv , (λ {x y} → cond {x}{y})
--  where
--   cond : {u : U ⊎ V ⊎ W} {y : (X ⊎ Y) ⊎ Z} →      
--       (_⊔ᵣ_ α (_⊔ᵣ_ β γ) u (⊎-assoc-inv y)) ≤L (_⊔ᵣ_ (_⊔ᵣ_ α β) γ (⊎-assoc u) y)
--   cond {inj₁ x} {inj₁ (inj₁ y)} = reflL
--   cond {inj₁ x} {inj₁ (inj₂ y)} = reflL
--   cond {inj₁ x} {inj₂ y} = reflL
--   cond {inj₂ (inj₁ x)} {inj₁ (inj₁ y)} = reflL
--   cond {inj₂ (inj₁ x)} {inj₁ (inj₂ y)} = reflL
--   cond {inj₂ (inj₁ x)} {inj₂ y} = reflL
--   cond {inj₂ (inj₂ x)} {inj₁ (inj₁ y)} = reflL
--   cond {inj₂ (inj₂ x)} {inj₁ (inj₂ y)} = reflL
--   cond {inj₂ (inj₂ x)} {inj₂ y} = reflL

-- choose-assoc-inv : ∀{A B C} → Hom (choose (choose A B) C) (choose A (choose B C))
-- choose-assoc-inv {U , X , α}{V , Y , β}{W , Z , γ} = ⊎-assoc-inv , ⊎-assoc , (λ {u y} → cond {u}{y})
--  where
--    cond : {u : (U ⊎ V) ⊎ W} {y : X ⊎ Y ⊎ Z} →
--      (_⊔ᵣ_ (_⊔ᵣ_ α β) γ u (⊎-assoc y)) ≤L (_⊔ᵣ_ α (_⊔ᵣ_ β γ) (⊎-assoc-inv u) y)
--    cond {inj₁ (inj₁ x)} {inj₁ y} = reflL
--    cond {inj₁ (inj₁ x)} {inj₂ (inj₁ y)} = reflL
--    cond {inj₁ (inj₁ x)} {inj₂ (inj₂ y)} = reflL
--    cond {inj₁ (inj₂ x)} {inj₁ y} = reflL
--    cond {inj₁ (inj₂ x)} {inj₂ (inj₁ y)} = reflL
--    cond {inj₁ (inj₂ x)} {inj₂ (inj₂ y)} = reflL
--    cond {inj₂ x} {inj₁ y} = reflL
--    cond {inj₂ x} {inj₂ (inj₁ y)} = reflL
--    cond {inj₂ x} {inj₂ (inj₂ y)} = reflL

-- choose-assoc-iso₁ : ∀{A B C} → choose-assoc {A}{B}{C} ○ choose-assoc-inv ≡h id
-- choose-assoc-iso₁ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set ⊎-assoc-iso₁ , ext-set ⊎-assoc-iso₁

-- choose-assoc-iso₂ : ∀{A B C} → choose-assoc-inv {A}{B}{C} ○ choose-assoc ≡h id
-- choose-assoc-iso₂ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set ⊎-assoc-iso₂ , ext-set ⊎-assoc-iso₂

-- choose-sym : ∀{A B} → Hom (choose A B) (choose B A)
-- choose-sym {U , X , α}{V , Y , β} = ⊎-sym , ⊎-sym , (λ {u y} → cond {u}{y})
--  where
--    cond : {u : U ⊎ V} {y : Y ⊎ X} → (_⊔ᵣ_ α β u (⊎-sym y)) ≤L (_⊔ᵣ_ β α (⊎-sym u) y)
--    cond {inj₁ x} {inj₁ y} = reflL
--    cond {inj₁ x} {inj₂ y} = reflL
--    cond {inj₂ x} {inj₁ y} = reflL
--    cond {inj₂ x} {inj₂ y} = reflL

-- choose-left-ident : ∀{A} → Hom (choose J A) A
-- choose-left-ident {U , X , α} = ⊎-left-ident , ⊎-left-ident-inv , (λ {u y} → cond {u}{y})
--  where
--   cond : {u : ⊥ ⊎ U} {y : X} →
--       (_⊔ᵣ_ {⊥ {ℓ}}{U}{⊥ {ℓ}} (λ x y₁ → ∅) α u (inj₂ y)) ≤L (α (⊎-left-ident u) y)
--   cond {inj₁ u}{x} = ⊥-elim {ℓ} u
--   cond {inj₂ u}{x} = reflL

-- choose-left-ident-inv : ∀{A} → Hom A (choose J A)
-- choose-left-ident-inv {U , X , α} = ⊎-left-ident-inv , ⊎-left-ident , ((λ {u y} → cond {u}{y}))
--  where
--   cond : {u : U} {y : ⊥ ⊎ X} →
--       (α u (⊎-left-ident y)) ≤L (_⊔ᵣ_ {⊥ {ℓ}} (λ x y₁ → ∅) α (inj₂ u) y)
--   cond {y = inj₁ x} = ⊥-elim {ℓ} x
--   cond {y = inj₂ y} = reflL

-- choose-left-ident-iso₁ : ∀{A} → choose-left-ident {A} ○ choose-left-ident-inv ≡h id
-- choose-left-ident-iso₁ {U , X , α} = ext-set ⊎-left-ident-iso₁ , ext-set ⊎-left-ident-iso₁

-- choose-left-ident-iso₂ : ∀{A} → choose-left-ident-inv {A} ○ choose-left-ident ≡h id
-- choose-left-ident-iso₂ {U , X , α} = ext-set ⊎-left-ident-iso₂ , ext-set ⊎-left-ident-iso₂

-- choose-right-ident : ∀{A} → Hom (choose A J) A
-- choose-right-ident {U , X , α} = ⊎-right-ident , ⊎-right-ident-inv , (λ {u y} → cond {u}{y})
--  where
--   cond : {u : U ⊎ ⊥} {y : X} →      
--       (_⊔ᵣ_ {U}{⊥ {ℓ}}{X}{⊥ {ℓ}} α (λ x y₁ → ∅) u (inj₁ y)) ≤L (α (⊎-right-ident u) y)
--   cond {inj₁ x} = reflL
--   cond {inj₂ y} = ⊥-elim {ℓ} y

-- choose-right-ident-inv : ∀{A} → Hom A (choose A J)
-- choose-right-ident-inv {U , X , α} = ⊎-right-ident-inv , ⊎-right-ident , (λ {u y} → cond {u}{y})
--  where
--   cond : {u : U} {y : X ⊎ ⊥} →
--       (α u (⊎-right-ident y)) ≤L (_⊔ᵣ_ {_}{⊥ {ℓ}} α (λ x y₁ → ∅) (inj₁ u) y)
--   cond {y = inj₁ x} = reflL
--   cond {y = inj₂ y} = ⊥-elim {ℓ} y

-- choose-right-ident-iso₁ : ∀{A} → choose-right-ident {A} ○ choose-right-ident-inv ≡h id
-- choose-right-ident-iso₁ {U , X , α} = ext-set ⊎-right-ident-iso₁ , ext-set ⊎-right-ident-iso₁

-- choose-right-ident-iso₂ : ∀{A} → choose-right-ident-inv {A} ○ choose-right-ident ≡h id
-- choose-right-ident-iso₂ {U , X , α} = ext-set ⊎-right-ident-iso₂ , ext-set ⊎-right-ident-iso₂

-- choose-+-dist : ∀{A B C : Obj} → Hom ((choose A C) + (choose B C)) ((choose A B) + C) 
-- choose-+-dist {U , X , α}{V , Y , β}{W , Z , γ} = aux₁ , aux₂ , (λ {u y} → cond {u}{y})
--  where
--   aux₁ : (U ⊎ W) ⊎ V ⊎ W → (U ⊎ V) ⊎ W
--   aux₁ (inj₁ (inj₁ x)) = inj₁ (inj₁ x)
--   aux₁ (inj₁ (inj₂ y)) = inj₂ y
--   aux₁ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
--   aux₁ (inj₂ (inj₂ y)) = inj₂ y

--   aux₂ : Σ (X ⊎ Y) (λ x → Z) → Σ (X ⊎ Z) (λ x → Y ⊎ Z)
--   aux₂ (inj₁ x , b) = inj₁ x , inj₂ b
--   aux₂ (inj₂ y , b) = inj₂ b , inj₁ y

--   cond : {u : (U ⊎ W) ⊎ V ⊎ W} {y : Σ (X ⊎ Y) (λ x → Z)} →
--       (+-cond (_⊔ᵣ_ α γ) (_⊔ᵣ_ β γ) u (aux₂ y)) ≤L
--       (+-cond (_⊔ᵣ_ α β) γ (aux₁ u) y)
--   cond {inj₁ (inj₁ x)} {inj₁ x₁ , b} = reflL
--   cond {inj₁ (inj₁ x)} {inj₂ y , b} = reflL
--   cond {inj₁ (inj₂ x)} {inj₁ x₁ , b} = a-unit-least al-pf
--   cond {inj₁ (inj₂ x)} {inj₂ y , b} = reflL
--   cond {inj₂ (inj₁ x)} {inj₁ x₁ , b} = reflL
--   cond {inj₂ (inj₁ x)} {inj₂ y , b} = reflL
--   cond {inj₂ (inj₂ x)} {inj₁ x₁ , b} = reflL
--   cond {inj₂ (inj₂ x)} {inj₂ y , b} = a-unit-least al-pf

-- choose-contract : ∀{A : Obj} → Hom (choose A A) A
-- choose-contract {U , X , α} = aux₁ , inj₁ , (λ {u y} → cond {u}{y})
--  where
--   aux₁ : U ⊎ U → U
--   aux₁ (inj₁ x) = x
--   aux₁ (inj₂ y) = y

--   cond : {u : U ⊎ U} {y : X} → (_⊔ᵣ_ α α u (inj₁ y)) ≤L (α (aux₁ u) y)
--   cond {inj₁ u}{x} = reflL
--   cond {inj₂ u}{x} = a-unit-least al-pf                

-}
