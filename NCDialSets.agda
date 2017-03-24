--------------------------------------------------------------------------------------------
-- The definition of the non-commutative dialectica category GC on Sets                   --
-- parameterized by an arbitrary bi-closed poset.  GC is described in                     --
-- Valeria de Paiva's thesis:                                                             --
--   http://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-213.pdf                               --
--                                                                                        --
-- This particular formalization is due to Valeria de Paiva:                              --
--    http://www.slideshare.net/valeria.depaiva/a-dialectica-model-of-the-lambek-calculus --
--------------------------------------------------------------------------------------------

open import prelude
open import biclosed-poset
open import biclosed-poset-thms 

module NCDialSets {ℓ : Level}(M : Set ℓ) (bp-pf : BiclosedPoset M) where

module NCDialSets-local-defs where
  -----------------------------------------------------------------------
  -- Initial local definitions to make reading types easier            --
  -----------------------------------------------------------------------
  _≤M_ : M → M → Set
  _≤M_ = (rel (poset (oncMonoid bp-pf)))

  {-# DISPLAY rel = _≤M_  #-}

  _⊗M_ : M → M → M
  _⊗M_ = mul (oncMonoid bp-pf)

  {-# DISPLAY mul = _⊗M_  #-}

  reflM : {a : M} → a ≤M a
  reflM {a} = prefl (poset (oncMonoid bp-pf))
  
  transM : {a b c : M} → a ≤M b → b ≤M c → a ≤M c
  transM p₁ p₂ = (ptrans (poset (oncMonoid bp-pf))) p₁ p₂
  
  compatM-r : {a : M} {b : M}
    → a ≤M b
    → {c : M}
    → (a ⊗M c) ≤M (b ⊗M c)          
  compatM-r p = compat-r (oncMonoid bp-pf) p

  compatM-l : {a : M} {b : M}
    → a ≤M b
    → {c : M}
    → (c ⊗M a) ≤M (c ⊗M b)          
  compatM-l p = compat-l (oncMonoid bp-pf) p
  
  unitM = unit (oncMonoid bp-pf)

  {-# DISPLAY unit = unitM  #-}
  
  left-identM : {a : M} → unitM ⊗M a ≡ a
  left-identM = left-ident (oncMonoid bp-pf)
  
  right-identM : {a : M} → a ⊗M unitM ≡ a
  right-identM = right-ident (oncMonoid bp-pf)
  
  assocM : {a b c : M} →
         a ⊗M (b ⊗M c) ≡ (a ⊗M b) ⊗M c
  assocM = assoc (oncMonoid bp-pf)
  
  _⇀M_ : M → M → M
  _⇀M_ = r-imp bp-pf

  {-# DISPLAY r-imp = _⇀M_  #-}

  _↼M_ : M → M → M
  _↼M_ = l-imp bp-pf

  {-# DISPLAY l-imp = _↼M_  #-}

  βM : M → M
  βM = exc bp-pf

  {-# DISPLAY exc = βM  #-}

  βM-compat : {a b : M} → a ≤M b → (βM a) ≤M (βM b)
  βM-compat = exc-compat bp-pf

  βM-min : {a : M} → (βM a) ≤M a
  βM-min = exc-min bp-pf

  βM-dup : {a : M} → (βM a) ≤M (βM (βM a))
  βM-dup = exc-dup bp-pf

  βM-sym-left : {a b : M} → ((βM a) ⊗M b) ≤M (b ⊗M (βM a))
  βM-sym-left = exc-sym-left bp-pf

  βM-sym-right : {a b : M} → (a ⊗M (βM b)) ≤M ((βM b) ⊗M a)
  βM-sym-right = exc-sym-right bp-pf

  l-adjM : {a b y : M}
    → (a ⊗M y) ≤M b
    → y ≤M (a ⇀M b)
  l-adjM p = r-adj bp-pf p

  r-adjM : {a b y : M}
    → (y ⊗M a) ≤M b
    → y ≤M (b ↼M a)
  r-adjM p = l-adj bp-pf p

  l-rlcompM : (a b : M) → (a ⊗M (a ⇀M b)) ≤M b
  l-rlcompM a b = r-rlcomp bp-pf a b

  r-rlcompM : (a b : M) → ((b ↼M a) ⊗M a) ≤M b
  r-rlcompM a b = l-rlcomp bp-pf a b

open NCDialSets-local-defs
  
-----------------------------------------------------------------------
-- We have a category                                                --
-----------------------------------------------------------------------

-- The objects:
Obj : Set (lsuc ℓ)
Obj = Σ[ U ∈ Set ℓ ] (Σ[ X ∈ Set ℓ ] (U → X → M))

obj-fst : Obj → Set ℓ
obj-fst (U , X , α) = U

obj-snd : Obj → Set ℓ
obj-snd (U , X , α) = X
  
-- The morphisms:
Hom : Obj → Obj → Set ℓ
Hom (U , X , α) (V , Y , β) =
  Σ[ f ∈ (U → V) ]
    (Σ[ F ∈ (Y → X) ] (∀{u : U}{y : Y} → α u (F y) ≤M β (f u) y))

-- Composition:
comp : {A B C : Obj} → Hom A B → Hom B C → Hom A C
comp {(U , X , α)} {(V , Y , β)} {(W , Z , γ)} (f , F , p₁) (g , G , p₂) =
  (g ∘ f , F ∘ G , cond)
  where
   cond : {u : U} {y : Z} → (α u (F (G y))) ≤M (γ (g (f u)) y)
   cond {u}{z} = transM (p₁ {u}{G z}) p₂ 

infixl 5 _○_

_○_ = comp

-- The contravariant hom-functor:
Homₐ :  {A' A B B' : Obj} → Hom A' A → Hom B B' → Hom A B → Hom A' B'
Homₐ f h g = comp f (comp g h)

-- The identity function:
id : {A : Obj} → Hom A A 
id {(U , V , α)} = (id-set , id-set , reflM)

-- In this formalization we will only worry about proving that the
-- data of morphisms are equivalent, and not worry about the morphism
-- conditions.  This will make proofs shorter and faster.
--
-- If we have parallel morphisms (f,F) and (g,G) in which we know that
-- f = g and F = G, then the condition for (f,F) will imply the
-- condition of (g,G) and vice versa.  Thus, we can safly ignore it.
infix 4 _≡h_

_≡h_ : {A B : Obj} → (f g : Hom A B) → Set ℓ
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


-----------------------------------------------------------------------
-- The MCC Structure                                                --
-----------------------------------------------------------------------

-- The tensor functor: ⊗
_⊗ᵣ_ : ∀{U X V Y : Set ℓ} → (U → X → M) → (V → Y → M) → ((U × V) → ((V → X) × (U → Y)) → M)
_⊗ᵣ_ α β (u , v) (f , g) = (α u (f v)) ⊗M (β v (g u))

_⊗ₒ_ : (A B : Obj) → Obj
(U , X , α) ⊗ₒ (V , Y , β) = ((U × V) , ((V → X) × (U → Y)) , α ⊗ᵣ β)

F⊗ : ∀{S Z W T V X U Y : Set ℓ}{f : U → W}{F : Z → X}{g : V → S}{G : T → Y} → (S → Z) × (W → T) → (V → X) × (U → Y)
F⊗ {f = f}{F}{g}{G} (h₁ , h₂) = (λ v → F(h₁ (g v))) , (λ u → G(h₂ (f u)))
  
_⊗ₐ_ : {A B C D : Obj} → Hom A C → Hom B D → Hom (A ⊗ₒ B) (C ⊗ₒ D)
_⊗ₐ_ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)}{(S , T , δ)} (f , F , p₁) (g , G , p₂) = ⟨ f , g ⟩ , F⊗ {f = f}{F}{g}{G} , (λ {u y} → cond {u}{y})
 where
  cond : {u : Σ U (λ x → V)} {y : Σ (S → Z) (λ x → W → T)} →
      ((α ⊗ᵣ β) u (F⊗ {f = f}{F}{g}{G} y)) ≤M ((γ ⊗ᵣ δ) (⟨ f , g ⟩ u) y)
  cond {u , v}{h , j} = bp-mul-funct {p = oncMonoid bp-pf} (p₁ {u}{h (g v)}) (p₂ {v}{j (f u)})

-- The unit for tensor:
ι : ⊤ {ℓ} → ⊤ {ℓ} → M
ι triv triv = unitM

I : Obj
I = (⊤ , ⊤ , ι)

-- The left-unitor:   
λ⊗ : ∀{A : Obj} → Hom (I ⊗ₒ A) A
λ⊗ {(U , X , α)} = snd , (λ x → (λ _ → triv) , (λ _ → x)) , (λ {u y} → cond {u}{y})
 where
  cond : {u : Σ ⊤ (λ x → U)} {y : X} →
      ((ι ⊗ᵣ α) u ((λ _ → triv) , (λ _ → y))) ≤M (α (snd u) y)
  cond {triv , u}{x} rewrite left-identM {α u x} = reflM


λ⁻¹⊗ : ∀{A : Obj} → Hom A (I ⊗ₒ A)
λ⁻¹⊗ {(U , X , α)} = (λ u → triv , u) , ((λ x → snd x triv) , (λ {u y} → cond {u}{y}))
 where
  cond : {u : U} {y : Σ (U → ⊤) (λ x → ⊤ → X)} →
    (α u (snd y triv)) ≤M ((ι ⊗ᵣ α) (triv , u) y)
  cond {u}{t₁ , t₂} with t₂ triv | t₁ u
  ... | x | triv rewrite left-identM {α u x} = reflM


-- The right-unitor:
ρ⊗ : ∀{A : Obj} → Hom (A ⊗ₒ I) A
ρ⊗ {(U , X , α)} = fst , (λ x → (λ x₁ → x) , (λ x₁ → triv)) , (λ {u y} → cond {u}{y})
 where
  cond : {u : Σ U (λ x → ⊤)} {y : X} →
      ((α ⊗ᵣ ι) u ((λ x₁ → y) , (λ x₁ → triv))) ≤M (α (fst u) y)
  cond {u , triv}{x} rewrite right-identM {α u x} = reflM


ρ⁼¹⊗ : ∀{A : Obj} → Hom A (A ⊗ₒ I)
ρ⁼¹⊗ {(U , X , α)} = (λ x → x , triv) , (λ x → fst x triv) , (λ {u y} → cond {u}{y})
 where
  cond : {u : U} {y : Σ (⊤ → X) (λ x → U → ⊤)} →
       (α u (fst y triv)) ≤M ((α ⊗ᵣ ι) (u , triv) y)
  cond {u}{t₁ , t₂} with t₁ triv | t₂ u
  ... | x | triv rewrite right-identM {α u x} = reflM

-- The associator:
α⁼¹⊗ : ∀{A B C : Obj} → Hom (A ⊗ₒ (B ⊗ₒ C)) ((A ⊗ₒ B) ⊗ₒ C)
α⁼¹⊗ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)} = rl-assoc-× , Fα-inv , (λ {u y} → cond {u}{y})
 where
   Fα-inv : (W → (V → X) × (U → Y)) × (U × V → Z) → (V × W → X) × (U → (W → Y) × (V → Z))
   Fα-inv = (λ p → (λ p' → fst ((fst p) (snd p')) (fst p')) , (λ u → (λ w → snd (fst p w) u) , (λ v → (snd p) (u , v))))
   cond : {u : Σ U (λ x → Σ V (λ x₁ → W))}
      {y : Σ (W → Σ (V → X) (λ x → U → Y)) (λ x → Σ U (λ x₁ → V) → Z)} →        
      ((α ⊗ᵣ (β ⊗ᵣ γ)) u
       ((λ p' → fst (fst y (snd p')) (fst p')) ,
        (λ u₁ → (λ w → snd (fst y w) u₁) , (λ v → snd y (u₁ , v)))))
        ≤M
      (((α ⊗ᵣ β) ⊗ᵣ γ) (rl-assoc-× u) y)
   cond {u , (v , w)}{t₁ , t₂} with t₁ w | t₂ (u , v)
   ... | t₃ , t₄ | z rewrite assocM {(α u (t₃ v))}{(β v (t₄ u))}{(γ w z)} = reflM

Fα : ∀{V W X Y U V Z : Set ℓ} → Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z))
       → Σ (W → Σ (V → X) (λ x → U → Y)) (λ x → Σ U (λ x₁ → V) → Z)
Fα (f ,  g) = (λ x → (λ x₁ → f ((x₁ , x))) , (λ x₁ → fst (g x₁) x)) , (λ x → snd (g (fst x)) (snd x))

α⊗ : ∀{A B C : Obj} → Hom ((A ⊗ₒ B) ⊗ₒ C) (A ⊗ₒ (B ⊗ₒ C)) 
α⊗ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)} = (lr-assoc-× , Fα {V} , (λ {u y} → cond {u}{y}))
 where
  cond : {u : Σ (Σ U (λ x → V)) (λ x → W)}
      {y : Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z))} →
      (((α ⊗ᵣ β) ⊗ᵣ γ) u (Fα {V} y)) ≤M ((α ⊗ᵣ (β ⊗ᵣ γ)) (lr-assoc-× u) y)
  cond {(u , v) , w}{t₁ , t₂} with t₂ u
  ... | t₃ , t₄ rewrite sym (assocM {(α u (t₁ (v , w)))}{(β v (t₃ w))}{(γ w (t₄ v))}) = reflM

α⊗-id₁ : ∀{A B C} → (α⊗ {A}{B}{C}) ○ α⁼¹⊗ ≡h id
α⊗-id₁ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux , ext-set aux'
 where
   aux : {a : Σ (Σ U (λ x → V)) (λ x → W)} → rl-assoc-× (lr-assoc-× a) ≡ a
   aux {(u , v) , w} = refl

   aux' : {a : Σ (W → Σ (V → X) (λ x → U → Y)) (λ x → Σ U (λ x₁ → V) → Z)}
     → ((λ x → (λ x₁ → fst (fst a x) x₁) , (λ x₁ → snd (fst a x) x₁)) , (λ x → snd a (fst x , snd x))) ≡ a
   aux' {j₁ , j₂} = eq-× (ext-set aux'') (ext-set aux''')
    where
      aux'' : {a : W} → (fst (j₁ a) , snd (j₁ a)) ≡ j₁ a
      aux'' {w} with j₁ w
      ... | h₁ , h₂ = refl

      aux''' : {a : Σ U (λ x₁ → V)} → j₂ (fst a , snd a) ≡ j₂ a
      aux''' {u , v} = refl

α⊗-id₂ : ∀{A B C} → (α⁼¹⊗ {A}{B}{C}) ○ α⊗ ≡h id
α⊗-id₂ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux , ext-set aux'
 where
   aux : {a : Σ U (λ x → Σ V (λ x₁ → W))} → lr-assoc-× (rl-assoc-× a) ≡ a
   aux {u , (v , w)} = refl
   aux' : {a
       : Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z))} →
      ((λ p' → fst (fst (Fα {V} {W} {X} {Y} {U} {V} {Z} a) (snd p')) (fst p')) ,
       (λ u → (λ w → snd (fst (Fα {V} {W} {X} {Y} {U} {V} {Z} a) w) u) , (λ v → snd (Fα {V} {W} {X} {Y} {U} {V} {Z} a) (u , v))))
      ≡ a
   aux' {j₁ , j₂} = eq-× (ext-set aux'') (ext-set aux''')
     where
       aux'' : {a : Σ V (λ x → W)} → j₁ (fst a , snd a) ≡ j₁ a
       aux'' {v , w} = refl
       aux''' : {a : U} → ((λ w → fst (j₂ a) w) , (λ v → snd (j₂ a) v)) ≡ j₂ a
       aux''' {u} with j₂ u
       ... | h₁ , h₂ = refl

-- Internal homs:

⇀-cond : ∀{U V X Y : Set ℓ} → (U → X → M) → (V → Y → M) → (U → V) × (Y → X) → U × Y → M
⇀-cond α β (f , g) (u , y) = α u (g y) ⇀M β (f u) y

_⇀ₒ_ : Obj → Obj → Obj
(U , X , α) ⇀ₒ (V , Y , β) = ((U → V) × (Y → X)) , (U × Y) , ⇀-cond α β

_⇀ₐ_ : {A B C D : Obj} → Hom C A → Hom B D → Hom (A ⇀ₒ B) (C ⇀ₒ D)
_⇀ₐ_ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)}{(S , T , δ)} (f , F , p₁) (g , G , p₂) =
  h , H , (λ {u y} → cond {u}{y})
  where
   h : Σ (U → V) (λ x → Y → X) → Σ (W → S) (λ x → T → Z)
   h (h₁ , h₂) = (λ w → g (h₁ (f w))) , (λ t → F (h₂ (G t)))
   H : Σ W (λ x → T) → Σ U (λ x → Y)
   H (w , t) = f w , G t
   cond : {u : Σ (U → V) (λ x → Y → X)} {y : Σ W (λ x → T)} →
        (⇀-cond α β u (H y)) ≤M (⇀-cond γ δ (h u) y)
   cond {t₁ , t₂}{w , t} = l-imp-funct {p = bp-pf} p₁ p₂

⇀-cur : {A B C : Obj}
  → Hom (B ⊗ₒ A) C
  → Hom A (B ⇀ₒ C)
⇀-cur {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁)
  = (λ u → (λ v → f (v , u)) , (λ z → fst (F z) u)) , (λ r → snd (F (snd r)) (fst r)) , (λ {u} {y} → cond {u}{y})
 where
   cond : {u : U} {y : V × Z} →
      α u (snd (F (snd y)) (fst y)) ≤M
      ⇀-cond β γ ((λ v → f (v , u)) , (λ z → fst (F z) u)) y
   cond {u}{v , z} with p₁ {v , u}{z}
   ... | p₂ with F z
   ... | t₁ , t₂ = l-adjM p₂

⇀-cur-≡h : ∀{A B C}{f₁ f₂ : Hom (A ⊗ₒ B) C}
  → f₁ ≡h f₂
  → ⇀-cur f₁ ≡h ⇀-cur f₂
⇀-cur-≡h {U , X , α}{V , Y , β}{W , Z , γ}
       {f₁ , F₁ , p₁}{f₂ , F₂ , p₂} (p₃ , p₄)
        rewrite p₃ | p₄ = refl , refl

⇀-uncur : {A B C : Obj}
  → Hom A (B ⇀ₒ C)
  → Hom (B ⊗ₒ A) C
⇀-uncur {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁)
  = (λ x → fst (f (snd x)) (fst x)) , (λ z → (λ u → snd (f u) z) , (λ v → F (v , z))) , (λ {u} {y} → cond {u}{y})
  where
    cond : {u : V × U} {y : Z} →
      (β ⊗ᵣ α) u ((λ u₁ → snd (f u₁) y) , (λ v → F (v , y))) ≤M
      γ (fst (f (snd u)) (fst u)) y
    cond {v , u}{z} with p₁ {u}{v , z}
    ... | p₂ with f u
    ... | t₁ , t₂ = let x = compatM-l p₂ {β v (t₂ z)}
                        y = l-rlcompM (β v (t₂ z))(γ (t₁ v) z)
                     in transM x y 

⇀-cur-uncur-bij₁ : ∀{A B C}{f : Hom (A ⊗ₒ B) C}
  → ⇀-uncur (⇀-cur f) ≡h f
⇀-cur-uncur-bij₁ {U , X , α}{V , Y , β}{W , Z , γ}{f , F , p₁} = ext-set aux₁ , ext-set aux₂
 where
   aux₁ : {a : Σ U (λ x → V)} → f (fst a , snd a) ≡ f a
   aux₁ {u , v} = refl
   
   aux₂ : {a : Z} → ((λ v → fst (F a) v) , (λ u → snd (F a) u)) ≡ F a
   aux₂ {z} with F z
   ... | j₁ , j₂ = refl

⇀-cur-uncur-bij₂ : ∀{A B C}{g : Hom A (B ⇀ₒ C)}
  → ⇀-cur (⇀-uncur g) ≡h g
⇀-cur-uncur-bij₂ {U , X , α}{V , Y , β}{W , Z , γ}{g , G , p₁} = ext-set aux₁ , ext-set aux₂
 where
   aux₁ : {a : U} → ((λ v → fst (g a) v) , (λ z → snd (g a) z)) ≡ g a
   aux₁ {u} with g u
   ... | (j₁ , j₂) = refl

   aux₂ : {a : Σ V (λ x → Z)} → G (fst a , snd a) ≡ G a
   aux₂ {v , z} = refl

↼-cond : ∀{U V X Y : Set ℓ} → (U → X → M) → (V → Y → M) → (U → V) × (Y → X) → U × Y → M
↼-cond α β (f , g) (u , y) = β (f u) y  ↼M α u (g y)

_↼ₒ_ : Obj → Obj → Obj
(V , Y , β) ↼ₒ (U , X , α) = ((U → V) × (Y → X)) , (U × Y) , ↼-cond α β

_↼ₐ_ : {A B C D : Obj} → Hom C A → Hom B D → Hom (B ↼ₒ A) (D ↼ₒ C)
_↼ₐ_ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)}{(S , T , δ)} (f , F , p₁) (g , G , p₂) =
  h , H , (λ {u y} → cond {u}{y})
  where
   h : Σ (U → V) (λ x → Y → X) → Σ (W → S) (λ x → T → Z)
   h (h₁ , h₂) = (λ w → g (h₁ (f w))) , (λ t → F (h₂ (G t)))
   H : Σ W (λ x → T) → Σ U (λ x → Y)
   H (w , t) = f w , G t
   cond : {u : (U → V) × (Y → X)} {y : W × T} → ↼-cond α β u (H y) ≤M ↼-cond γ δ (h u) y
   cond {t₁ , t₂}{w , t} = r-imp-funct {p = bp-pf} p₁ p₂

↼-cur : {A B C : Obj}
  → Hom (A ⊗ₒ B) C
  → Hom A (C ↼ₒ B)
↼-cur {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁)
  = (λ u → (λ v → f (u , v)) , (λ z → snd (F z) u) ) , (λ r → fst (F (snd r)) (fst r)) , (λ {u} {y} → cond {u}{y})
 where
   cond : {u : U} {y : V × Z} →
      α u (fst (F (snd y)) (fst y)) ≤M
      ↼-cond β γ ((λ v → f (u , v)) , (λ z → snd (F z) u)) y
   cond {u}{v , z} with p₁ {u , v}{z}
   ... | p₂ with F z
   ... | t₁ , t₂ = r-adjM p₂

↼-cur-≡h : ∀{A B C}{f₁ f₂ : Hom (A ⊗ₒ B) C}
  → f₁ ≡h f₂
  → ↼-cur f₁ ≡h ↼-cur f₂
↼-cur-≡h {U , X , α}{V , Y , β}{W , Z , γ}
       {f₁ , F₁ , p₁}{f₂ , F₂ , p₂} (p₃ , p₄)
        rewrite p₃ | p₄ = refl , refl

↼-uncur : {A B C : Obj}
  → Hom A (C ↼ₒ B)
  → Hom (A ⊗ₒ B) C
↼-uncur {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁)
 = (λ r → fst (f (fst r)) (snd r)) , (λ z → (λ v → F (v , z)) , (λ u → snd (f u) z)) , (λ {u} {y} → cond {u}{y})
  where
    cond : {u : U × V} {y : Z} →
      (α ⊗ᵣ β) u ((λ v → F (v , y)) , (λ u₁ → snd (f u₁) y)) ≤M
      γ (fst (f (fst u)) (snd u)) y
    cond {u , v}{z} with p₁ {u}{v , z}
    ... | p₂ with f u
    ... | t₁ , t₂ = let x = compatM-r p₂ {β v (t₂ z)}
                        y = r-rlcompM (β v (t₂ z))(γ (t₁ v) z)
                     in transM x y 

↼-cur-uncur-bij₁ : ∀{A B C}{f : Hom (A ⊗ₒ B) C}
  → ↼-uncur (↼-cur f) ≡h f
↼-cur-uncur-bij₁ {U , X , α}{V , Y , β}{W , Z , γ}{f , F , p₁} = ext-set aux₁ , ext-set aux₂
 where
   aux₁ : {a : Σ U (λ x → V)} → f (fst a , snd a) ≡ f a
   aux₁ {u , v} = refl
   
   aux₂ : {a : Z} → ((λ v → fst (F a) v) , (λ u → snd (F a) u)) ≡ F a
   aux₂ {z} with F z
   ... | j₁ , j₂ = refl

↼-cur-uncur-bij₂ : ∀{A B C}{g : Hom A (C ↼ₒ B)}
  → ↼-cur (↼-uncur g) ≡h g
↼-cur-uncur-bij₂ {U , X , α}{V , Y , β}{W , Z , γ}{g , G , p₁} = ext-set aux₁ , ext-set aux₂
 where
   aux₁ : {a : U} → ((λ v → fst (g a) v) , (λ z → snd (g a) z)) ≡ g a
   aux₁ {u} with g u
   ... | (j₁ , j₂) = refl

   aux₂ : {a : Σ V (λ x → Z)} → G (fst a , snd a) ≡ G a
   aux₂ {v , z} = refl

-----------------------------------------------------------------------
-- The exchange modality                                             --
-----------------------------------------------------------------------

κₒ : Obj → Obj
κₒ (U , X , α) = U , X , (λ u x → βM (α u x))

κₐ : {A B : Obj} → Hom A B → Hom (κₒ A) (κₒ B)
κₐ {U , X , α}{V , Y , β} (f , F , p) = f , F , βM-compat p

κε : ∀{A} → Hom (κₒ A) A
κε {U , X , α} = id-set , id-set , βM-min

κδ : ∀{A} → Hom (κₒ A) (κₒ (κₒ A))
κδ {U , X , α} = id-set , id-set , βM-dup

-- The proper diagrams:
κ-comonand-diag₁ : ∀{A}
  → (κδ {A}) ○ (κₐ (κδ {A})) ≡h (κδ {A}) ○ (κδ { κₒ A})
κ-comonand-diag₁ {U , X , α} = refl , refl

κ-comonand-diag₂ : ∀{A}
  → (κδ {A}) ○ (κε { κₒ A}) ≡h (κδ {A}) ○ (κₐ (κε {A}))
κ-comonand-diag₂ {U , X , α} = refl , refl

-- Symmetries:

β-left : ∀{A B} → Hom ((κₒ A) ⊗ₒ B) (B ⊗ₒ (κₒ A))
β-left {U , X , α}{V , Y , β} = twist-× , twist-× , (λ {u} {y} → aux {u}{y})
 where
  aux : {u : U × V} {y : (U → Y) × (V → X)} →
      ((λ u₁ x → βM (α u₁ x)) ⊗ᵣ β) u (twist-× y) ≤M
      (β ⊗ᵣ (λ u₁ x → βM (α u₁ x))) (twist-× u) y
  aux {u , v}{f , g} = βM-sym-left

β-right : ∀{A B} → Hom (A ⊗ₒ (κₒ B)) ((κₒ B) ⊗ₒ A)
β-right {U , X , α}{V , Y , β} = twist-× , twist-× , (λ {u} {y} → aux {u}{y})
 where
  aux : {u : U × V} {y : (U → Y) × (V → X)} →
      (α ⊗ᵣ (λ u₁ x → βM (β u₁ x))) u (twist-× y) ≤M
      ((λ u₁ x → βM (β u₁ x)) ⊗ᵣ α) (twist-× u) y
  aux {u , v}{f , g} = βM-sym-right

-----------------------------------------------------------------------
-- The of-course modality                                            --
-----------------------------------------------------------------------

!ₒ-cond : ∀{U X : Set ℓ}
  → (U → X → M)
  → U
  → (U → X *)
  → M
!ₒ-cond α u f =  foldr (λ a r → (α u a) ⊗M r) unitM (f u) 
   
!ₒ : Obj → Obj
!ₒ (U , X , α) = U , (U → X *) , !ₒ-cond α

!-cta : {V Y U X : Set ℓ}
  → (Y → X)
  → (U → V)
  → (V → Y *)
  → (U → X *)
!-cta F f g = λ u → list-funct F (g (f u))
      
!ₐ : {A B : Obj} → Hom A B → Hom (!ₒ A) (!ₒ B)
!ₐ {U , X , α}{V , Y , β} (f , F , p) = f , !-cta F f , (λ {u y} → cond {u} {y})
 where
   cond : {u : U} {y : V → 𝕃 Y} →        
      (foldr (λ a y₁ → (α u a) ⊗M y₁) unitM (map F (y (f u))))
      ≤M
      (foldr (λ a y₁ → (β (f u) a) ⊗M y₁) unitM (y (f u)))
   cond {u}{t} = aux {t (f u)}
     where
       aux : {l : 𝕃 Y} →
         (foldr (λ a y →(α u a) ⊗M y) unitM
         (map F l))
         ≤M
         (foldr (λ a y → (β (f u) a) ⊗M y) unitM l)
       aux {[]} = reflM
       aux {y :: ys} with aux {ys}
       ... | IH = bp-mul-funct {p = oncMonoid bp-pf} (p {u}{y}) IH

-- The unit of the comonad:
ε : ∀{A} → Hom (!ₒ A) A
ε {U , X , α} = id-set , (λ x y → [ x ]) , cond
 where
  cond : {u : U} {y : X} →      
      ((α u y) ⊗M unitM) ≤M (α u y)
  cond {u}{x} rewrite right-identM {α u x} = reflM

-- The duplicator of the comonad:
δ-cta : {U X : Set ℓ} → (U → 𝕃 (U → 𝕃 X)) → U → 𝕃 X
δ-cta g u = foldr (λ f rest → (f u) ++ rest) [] (g u)
  
δ : ∀{A} → Hom (!ₒ A) (!ₒ (!ₒ A))
δ {U , X , α} = id-set , δ-cta , (λ {u y} → cond {u}{y})
  where
   cond : {u : U} {y : U → 𝕃 (U → 𝕃 X)} →      
      (foldr (λ a y₁ → (α u a) ⊗M y₁) unitM
       (foldr (λ f → _++_ (f u)) [] (y u)))
      ≤M
      (foldr
       (λ a y₁ →          
          (foldr (λ a₁ y₂ → (α u a₁) ⊗M y₂)
           unitM (a u))
           ⊗M
          y₁)
       unitM (y u))
   cond {u}{t} = aux {t u}
    where
     aux : {l : 𝕃 (U → 𝕃 X)} →
         (foldr (λ a y → (α u a) ⊗M y) unitM (foldr (λ f → _++_ (f u)) [] l))
       ≤M
         (foldr
           (λ a y → (foldr (λ a₁ y₁ → (α u a₁) ⊗M y₁) unitM (a u)) ⊗M y)
           unitM l)
     aux {[]} = reflM
     aux {t₁ :: ts} with aux {ts}
     ... | IH with t₁ u
     ... | [] rewrite left-identM {(foldr
        (λ a → _⊗M_ (foldr (λ a₁ → _⊗M_ (α u a₁)) unitM (a u)))
        unitM
        ts)} = IH
     ... | x :: xs rewrite
           sym (foldr-monoid {l₁ = xs}{foldr (λ f → _++_ (f u)) [] ts}{_⊗M_}{α u}{unitM}{left-identM}{assocM})
         | assocM {(α u x)}{(foldr (λ x₁ → _⊗M_ (α u x₁)) unitM xs)}{(foldr (λ x₁ → _⊗M_ (α u x₁)) unitM (foldr (λ f → _++_ (f u)) [] ts))}
      = compatM-l IH {((α u x) ⊗M (foldr (λ x₁ → _⊗M_ (α u x₁)) unitM xs))}

-- The proper diagrams:
comonand-diag₁ : ∀{A}
  → (δ {A}) ○ (!ₐ (δ {A})) ≡h (δ {A}) ○ (δ { !ₒ A})
comonand-diag₁ {U , X , α} =
  refl , ext-set (λ {a} → ext-set (λ {a₁} → aux {a₁}{a a₁}))
 where
   aux : ∀{a₁ : U}{l : 𝕃 (U → 𝕃 (U → 𝕃 X))} →
      foldr (λ f → _++_ (f a₁)) []
      (map (λ g u → foldr (λ f → _++_ (f u)) [] (g u)) l)
      ≡
      foldr (λ f → _++_ (f a₁)) [] (foldr (λ f → _++_ (f a₁)) [] l)
   aux {a}{[]} = refl  
   aux {a}{x :: l} rewrite
     sym (foldr-append-fun {l₁ = x a}{foldr (λ f → _++_ (f a)) [] l}{a})
     = cong2 {a = foldr (λ f → _++_ (f a)) [] (x a)}
             _++_
             refl
             (aux {a}{l})

comonand-diag₂ : ∀{A}
  → (δ {A}) ○ (ε { !ₒ A}) ≡h (δ {A}) ○ (!ₐ (ε {A}))
comonand-diag₂ {U , X , α} =
  refl , ext-set (λ {f} → ext-set (λ {a} → aux {a}{f a}))
 where
  aux : ∀{a : U}{l : X *}
    → l ++ [] ≡ foldr (λ f₁ → _++_ (f₁ a)) [] (map (λ x y → x :: []) l)
  aux {a}{[]} = refl
  aux {a}{x :: l} with aux {a}{l}
  ... | IH rewrite ++[] l =
    cong2 {a = x} {x} {l}
          {foldr (λ f₁ → _++_ (f₁ a)) [] (map (λ x₁ y → x₁ :: []) l)} _::_ refl
          IH

