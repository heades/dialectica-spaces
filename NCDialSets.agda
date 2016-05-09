open import prelude
open import biclosed-poset
open import biclosed-poset-thms 

-----------------------------------------------------------------------
-- The definition of the dialectica category GC on Sets              --
-- parameterized by an arbitrary lineale.  GC is described in        --
-- Valeria de Paiva's thesis:                                        --
--   http://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-213.pdf          --
-----------------------------------------------------------------------
module NCDialSets {ℓ : Level}(M : Set ℓ) (bp-pf : BiclosedPoset M) where

module DialSets-local-defs where
  -----------------------------------------------------------------------
  -- Initial local definitions to make reading types easier            --
  -----------------------------------------------------------------------
  _≤M_ : M → M → Set
  x ≤M y = (rel (poset (oncMonoid bp-pf))) x y

  reflM : {a : M} → a ≤M a
  reflM = prefl (poset (oncMonoid bp-pf))
  
  transM : {a b c : M} → a ≤M b → b ≤M c → a ≤M c
  transM = ptrans (poset (oncMonoid bp-pf))
  
  compatM-r : {a : M} {b : M}
    → rel (poset (oncMonoid bp-pf)) a b
    → {c : M}
    → rel (poset (oncMonoid bp-pf)) (mul (oncMonoid bp-pf) a c) (mul (oncMonoid bp-pf) b c)
          
  compatM-r = compat-r (oncMonoid bp-pf)

  compatM-l : {a : M} {b : M}
    → rel (poset (oncMonoid bp-pf)) a b
    → {c : M}
    → rel (poset (oncMonoid bp-pf)) (mul (oncMonoid bp-pf) c a) (mul (oncMonoid bp-pf) c b)
          
  compatM-l = compat-l (oncMonoid bp-pf)
  
  _⊗M_ : M → M → M
  x ⊗M y = mul (oncMonoid bp-pf) x y
  
  unitM = unit (oncMonoid bp-pf)
  
  left-identM : {a : M} → mul (oncMonoid bp-pf) (unit (oncMonoid bp-pf)) a ≡ a
  left-identM = left-ident (oncMonoid bp-pf)
  
  right-identM : {a : M} → mul (oncMonoid bp-pf) a (unit (oncMonoid bp-pf)) ≡ a
  right-identM = right-ident (oncMonoid bp-pf)
  
  assocM : {a b c : M} →
         mul (oncMonoid bp-pf) a (mul (oncMonoid bp-pf) b c) ≡
         mul (oncMonoid bp-pf) (mul (oncMonoid bp-pf) a b) c
  assocM = assoc (oncMonoid bp-pf)
  
  _⇀M_ : M → M → M
  _⇀M_ = l-imp bp-pf

  _↼M_ : M → M → M
  _↼M_ = r-imp bp-pf
  
  l-adjM : {a b y : M} →
       rel (poset (oncMonoid bp-pf)) (mul (oncMonoid bp-pf) a y) b →
       rel (poset (oncMonoid bp-pf)) y (l-imp bp-pf a b)
  l-adjM = l-adj bp-pf

  r-adjM : {a b y : M} →
       rel (poset (oncMonoid bp-pf)) (mul (oncMonoid bp-pf) y a) b →
       rel (poset (oncMonoid bp-pf)) y (r-imp bp-pf b a)
  r-adjM = r-adj bp-pf

open DialSets-local-defs

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
-- The SMCC Structure                                                --
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


-- -- The unit for tensor:
-- ι : ⊤ {ℓ} → ⊤ {ℓ} → M
-- ι triv triv = unitM

-- I : Obj
-- I = (⊤ , ⊤ , ι)

-- -- The left-unitor:   
-- λ⊗ : ∀{A : Obj} → Hom (I ⊗ₒ A) A
-- λ⊗ {(U , X , α)} = snd , (λ x → (λ _ → triv) , (λ _ → x)) , (λ {u y} → cond {u}{y})
--  where
--   cond : {u : Σ ⊤ (λ x → U)} {y : X} →
--       ((ι ⊗ᵣ α) u ((λ _ → triv) , (λ _ → y))) ≤M (α (snd u) y)
--   cond {triv , u}{x} rewrite left-identM {α u x} = reflM


-- λ⁻¹⊗ : ∀{A : Obj} → Hom A (I ⊗ₒ A)
-- λ⁻¹⊗ {(U , X , α)} = (λ u → triv , u) , ((λ x → snd x triv) , (λ {u y} → cond {u}{y}))
--  where
--   cond : {u : U} {y : Σ (U → ⊤) (λ x → ⊤ → X)} →
--     (α u (snd y triv)) ≤M ((ι ⊗ᵣ α) (triv , u) y)
--   cond {u}{t₁ , t₂} with t₂ triv | t₁ u
--   ... | x | triv rewrite left-identM {α u x} = reflM


-- -- The right-unitor:
-- ρ⊗ : ∀{A : Obj} → Hom (A ⊗ₒ I) A
-- ρ⊗ {(U , X , α)} = fst , (λ x → (λ x₁ → x) , (λ x₁ → triv)) , (λ {u y} → cond {u}{y})
--  where
--   cond : {u : Σ U (λ x → ⊤)} {y : X} →
--       ((α ⊗ᵣ ι) u ((λ x₁ → y) , (λ x₁ → triv))) ≤M (α (fst u) y)
--   cond {u , triv}{x} rewrite right-identM {α u x} = reflM


-- ρ⊗-inv : ∀{A : Obj} → Hom A (A ⊗ₒ I)
-- ρ⊗-inv {(U , X , α)} = (λ x → x , triv) , (λ x → fst x triv) , (λ {u y} → cond {u}{y})
--  where
--   cond : {u : U} {y : Σ (⊤ → X) (λ x → U → ⊤)} →
--        (α u (fst y triv)) ≤M ((α ⊗ᵣ ι) (u , triv) y)
--   cond {u}{t₁ , t₂} with t₁ triv | t₂ u
--   ... | x | triv rewrite right-identM {α u x} = reflM

-- -- Symmetry:
-- β⊗ : ∀{A B : Obj} → Hom (A ⊗ₒ B) (B ⊗ₒ A)
-- β⊗ {(U , X , α)}{(V , Y , β)} = twist-× , twist-× , (λ {u y} → cond {u}{y})
--  where
--    cond : {u : Σ U (λ x → V)} {y : Σ (U → Y) (λ x → V → X)} →
--         ((α ⊗ᵣ β) u (twist-× y)) ≤M ((β ⊗ᵣ α) (twist-× u) y)
--    cond {u , v}{t₁ , t₂} rewrite symmM {(α u (t₂ v))} {(β v (t₁ u))} = reflM

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
--         ≤M
--       (((α ⊗ᵣ β) ⊗ᵣ γ) (rl-assoc-× u) y)
--    cond {u , (v , w)}{t₁ , t₂} with t₁ w | t₂ (u , v)
--    ... | t₃ , t₄ | z rewrite assocM {(α u (t₃ v))}{(β v (t₄ u))}{(γ w z)} = reflM

-- Fα : ∀{V W X Y U V Z : Set ℓ} → Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z))
--        → Σ (W → Σ (V → X) (λ x → U → Y)) (λ x → Σ U (λ x₁ → V) → Z)
-- Fα (f ,  g) = (λ x → (λ x₁ → f ((x₁ , x))) , (λ x₁ → fst (g x₁) x)) , (λ x → snd (g (fst x)) (snd x))


-- α⊗ : ∀{A B C : Obj} → Hom ((A ⊗ₒ B) ⊗ₒ C) (A ⊗ₒ (B ⊗ₒ C)) 
-- α⊗ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)} = (lr-assoc-× , Fα {V} , (λ {u y} → cond {u}{y}))
--  where
--   cond : {u : Σ (Σ U (λ x → V)) (λ x → W)}
--       {y : Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z))} →
--       (((α ⊗ᵣ β) ⊗ᵣ γ) u (Fα {V} y)) ≤M ((α ⊗ᵣ (β ⊗ᵣ γ)) (lr-assoc-× u) y)
--   cond {(u , v) , w}{t₁ , t₂} with t₂ u
--   ... | t₃ , t₄ rewrite sym (assocM {(α u (t₁ (v , w)))}{(β v (t₃ w))}{(γ w (t₄ v))}) = reflM


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
-- ⊸-cond : ∀{U V X Y : Set ℓ} → (U → X → M) → (V → Y → M) → (U → V) × (Y → X) → U × Y → M
-- ⊸-cond α β (f , g) (u , y) = α u (g y) →M β (f u) y

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
--         (⊸-cond α β u (H y)) ≤M (⊸-cond γ δ (h u) y)
--    cond {t₁ , t₂}{w , t} = l-imp-funct {p = bp-pf} p₁ p₂


-- cur : {A B C : Obj}
--   → Hom (A ⊗ₒ B) C
--   → Hom A (B ⊸ₒ C)
-- cur {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁)
--   = (λ u → (λ v → f (u , v)) , (λ z → snd (F z) u)) , (λ p →  fst (F (snd p)) (fst p)) , (λ {u y} → cond {u}{y})
--  where
--    cond : {u : U} {y : Σ V (λ x → Z)} →
--       (α u (fst (F (snd y)) (fst y))) ≤M (⊸-cond β γ ((λ v → f (u , v)) , (λ z → snd (F z) u)) y)
--    cond {u}{v , z} with p₁ {u , v}{z}
--    ... | p₂ with F z
--    ... | t₁ , t₂ rewrite symmM {α u (t₁ v)}{β v (t₂ u)} = adjM p₂


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
--          ((α ⊗ᵣ β) u ((λ v → F (v , y)) , (λ u₁ → snd (f u₁) y))) ≤M (γ (fst (f (fst u)) (snd u)) y)
--     cond {u , v}{z} with p₁ {u}{v , z}
--     ... | p₂ with f u
--     ... | t₁ , t₂ rewrite symmM {(α u (F (v , z)))}{β v (t₂ z)} = adj-inv {r = bp-pf} p₂


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

-- +-cond : ∀{U V X Y : Set ℓ} → (U → X → M) → (V → Y → M) → U ⊎ V → X × Y → M
-- +-cond α β (inj₁ u) (x , y) = α u x
-- +-cond α β (inj₂ v) (x , y) = β v y

-- _+_ : Obj → Obj → Obj
-- (U , X , α) + (V , Y , β) = (U ⊎ V) , (X × Y) , +-cond α β

-- +-terminalₐ : ∀{A} → Hom +-ident A
-- +-terminalₐ {U , X , α} = (λ x → ⊥-elim {ℓ} x) , (λ x → triv) , (λ {u y} → cond {u}{y})
--  where
--    cond : {u : ⊥ {ℓ}} {y : X} → ∅ ≤M (α (⊥-elim u) y)
--    cond {u}{x} = ⊥-elim {ℓ} u

-- +-inj₁ : ∀{A B} → Hom A (A + B)
-- +-inj₁ {U , X , α}{V , Y , β} = inj₁ , (fst , (λ {u y} → cond {u}{y}))
--  where
--   cond : {u : U} {y : Σ X (λ x → Y)} →
--        (α u (fst y)) ≤M (+-cond α β (inj₁ u) y)
--   cond {y = a , b} = reflM

-- +-inj₂ : ∀{A B} → Hom B (A + B)
-- +-inj₂ {U , X , α}{V , Y , β} = inj₂ , snd , (λ {u y} → cond {u}{y})
--  where
--    cond : {u : V} {y : Σ X (λ x → Y)} →
--       (β u (snd y)) ≤M (+-cond α β (inj₂ u) y)
--    cond {u}{x , y} = reflM

-- +-ar : ∀{A B C} → (f : Hom A C) → (g : Hom B C) → Hom (A + B) C
-- +-ar {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁) (g , G , p₂) = ⊎-ar f g , trans-× F G , (λ {u y} → cond {u}{y})
--  where
--    cond : {u : U ⊎ V} {y : Z} → (+-cond α β u (F y , G y)) ≤M (γ (⊎-ar f g u) y)
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
--   → (U → X → M)
--   → U
--   → (U → X *)
--   → M
-- !ₒ-cond α u f =  foldr (λ a r → (α u a) ⊗M r) unitM (f u) 
   
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
--       (foldr (λ a y₁ → (α u a) ⊗M y₁) unitM (map F (y (f u))))
--       ≤M
--       (foldr (λ a y₁ → (β (f u) a) ⊗M y₁) unitM (y (f u)))
--    cond {u}{t} = aux {t (f u)}
--      where
--        aux : {l : 𝕃 Y} →
--          (foldr (λ a y →(α u a) ⊗M y) unitM
--          (map F l))
--          ≤M
--          (foldr (λ a y → (β (f u) a) ⊗M y) unitM l)
--        aux {[]} = reflM
--        aux {y :: ys} with aux {ys}
--        ... | IH = l-mul-funct {p = oncMonoid bp-pf} (p {u}{y}) IH

-- -- The unit of the comonad:
-- ε : ∀{A} → Hom (!ₒ A) A
-- ε {U , X , α} = id-set , (λ x y → [ x ]) , cond
--  where
--   cond : {u : U} {y : X} →      
--       ((α u y) ⊗M unitM) ≤M (α u y)
--   cond {u}{x} rewrite right-identM {α u x} = reflM

-- -- The duplicator of the comonad:
-- δ-cta : {U X : Set ℓ} → (U → 𝕃 (U → 𝕃 X)) → U → 𝕃 X
-- δ-cta g u = foldr (λ f rest → (f u) ++ rest) [] (g u)
  
-- δ : ∀{A} → Hom (!ₒ A) (!ₒ (!ₒ A))
-- δ {U , X , α} = id-set , δ-cta , (λ {u y} → cond {u}{y})
--   where
--    cond : {u : U} {y : U → 𝕃 (U → 𝕃 X)} →      
--       (foldr (λ a y₁ → (α u a) ⊗M y₁) unitM
--        (foldr (λ f → _++_ (f u)) [] (y u)))
--       ≤M
--       (foldr
--        (λ a y₁ →          
--           (foldr (λ a₁ y₂ → (α u a₁) ⊗M y₂)
--            unitM (a u))
--            ⊗M
--           y₁)
--        unitM (y u))
--    cond {u}{t} = aux {t u}
--     where
--      aux : {l : 𝕃 (U → 𝕃 X)} → rel (poset (oncMonoid bp-pf))
--       (foldr (λ a y → mul (oncMonoid bp-pf) (α u a) y) (unit (oncMonoid bp-pf))
--        (foldr (λ f → _++_ (f u)) [] l))
--       (foldr
--        (λ a y →
--           mul (oncMonoid bp-pf)
--           (foldr (λ a₁ y₁ → mul (oncMonoid bp-pf) (α u a₁) y₁)
--            (unit (oncMonoid bp-pf)) (a u))
--           y)
--        (unit (oncMonoid bp-pf)) l)      
--      aux {[]} = reflM
--      aux {t₁ :: ts} with aux {ts}
--      ... | IH with t₁ u
--      ... | [] rewrite left-identM {(foldr
--         (λ a → _⊗M_ (foldr (λ a₁ → _⊗M_ (α u a₁)) unitM (a u)))
--         unitM
--         ts)} = IH
--      ... | x :: xs rewrite
--            sym (foldr-monoid {l₁ = xs}{foldr (λ f → _++_ (f u)) [] ts}{_⊗M_}{α u}{unitM}{left-identM}{assocM})
--          | assocM {(α u x)}{(foldr (λ x₁ → mul (oncMonoid bp-pf) (α u x₁)) (unit (oncMonoid bp-pf)) xs)}{(foldr (λ x₁ → mul (oncMonoid bp-pf) (α u x₁)) (unit (oncMonoid bp-pf)) (foldr (λ f → _++_ (f u)) [] ts))}
--       = compat-sym {p = oncMonoid bp-pf} IH     

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
-- chooseᵣ : {U V X Y : Set ℓ} → (U → X → M) → (V → Y → M) → U ⊎ V → X ⊎ Y → M
-- chooseᵣ α β (inj₁ x) (inj₁ y) = α x y
-- chooseᵣ α β (inj₁ x) (inj₂ y) = ∅
-- chooseᵣ α β (inj₂ x) (inj₁ y) = ∅
-- chooseᵣ α β (inj₂ x) (inj₂ y) = β x y

-- choose : Obj → Obj → Obj
-- choose (U , X , α) (V , Y , β) = (U ⊎ V) , (X ⊎ Y) , chooseᵣ α β

-- choose-assoc : ∀{A B C} → Hom (choose A (choose B C)) (choose (choose A B) C)
-- choose-assoc {U , X , α}{V , Y , β}{W , Z , γ} = ⊎-assoc , ⊎-assoc-inv , (λ {x y} → cond {x}{y})
--  where
--   cond : {u : U ⊎ V ⊎ W} {y : (X ⊎ Y) ⊎ Z} →      
--       (chooseᵣ α (chooseᵣ β γ) u (⊎-assoc-inv y)) ≤M (chooseᵣ (chooseᵣ α β) γ (⊎-assoc u) y)
--   cond {inj₁ x} {inj₁ (inj₁ y)} = reflM
--   cond {inj₁ x} {inj₁ (inj₂ y)} = reflM
--   cond {inj₁ x} {inj₂ y} = reflM
--   cond {inj₂ (inj₁ x)} {inj₁ (inj₁ y)} = reflM
--   cond {inj₂ (inj₁ x)} {inj₁ (inj₂ y)} = reflM
--   cond {inj₂ (inj₁ x)} {inj₂ y} = reflM
--   cond {inj₂ (inj₂ x)} {inj₁ (inj₁ y)} = reflM
--   cond {inj₂ (inj₂ x)} {inj₁ (inj₂ y)} = reflM
--   cond {inj₂ (inj₂ x)} {inj₂ y} = reflM

-- choose-assoc-inv : ∀{A B C} → Hom (choose (choose A B) C) (choose A (choose B C))
-- choose-assoc-inv {U , X , α}{V , Y , β}{W , Z , γ} = ⊎-assoc-inv , ⊎-assoc , (λ {u y} → cond {u}{y})
--  where
--    cond : {u : (U ⊎ V) ⊎ W} {y : X ⊎ Y ⊎ Z} →
--      (chooseᵣ (chooseᵣ α β) γ u (⊎-assoc y)) ≤M (chooseᵣ α (chooseᵣ β γ) (⊎-assoc-inv u) y)
--    cond {inj₁ (inj₁ x)} {inj₁ y} = reflM
--    cond {inj₁ (inj₁ x)} {inj₂ (inj₁ y)} = reflM
--    cond {inj₁ (inj₁ x)} {inj₂ (inj₂ y)} = reflM
--    cond {inj₁ (inj₂ x)} {inj₁ y} = reflM
--    cond {inj₁ (inj₂ x)} {inj₂ (inj₁ y)} = reflM
--    cond {inj₁ (inj₂ x)} {inj₂ (inj₂ y)} = reflM
--    cond {inj₂ x} {inj₁ y} = reflM
--    cond {inj₂ x} {inj₂ (inj₁ y)} = reflM
--    cond {inj₂ x} {inj₂ (inj₂ y)} = reflM

-- choose-assoc-iso₁ : ∀{A B C} → choose-assoc {A}{B}{C} ○ choose-assoc-inv ≡h id
-- choose-assoc-iso₁ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set ⊎-assoc-iso₁ , ext-set ⊎-assoc-iso₁

-- choose-assoc-iso₂ : ∀{A B C} → choose-assoc-inv {A}{B}{C} ○ choose-assoc ≡h id
-- choose-assoc-iso₂ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set ⊎-assoc-iso₂ , ext-set ⊎-assoc-iso₂

-- choose-sym : ∀{A B} → Hom (choose A B) (choose B A)
-- choose-sym {U , X , α}{V , Y , β} = ⊎-sym , ⊎-sym , (λ {u y} → cond {u}{y})
--  where
--    cond : {u : U ⊎ V} {y : Y ⊎ X} → (chooseᵣ α β u (⊎-sym y)) ≤M (chooseᵣ β α (⊎-sym u) y)
--    cond {inj₁ x} {inj₁ y} = reflM
--    cond {inj₁ x} {inj₂ y} = reflM
--    cond {inj₂ x} {inj₁ y} = reflM
--    cond {inj₂ x} {inj₂ y} = reflM

-- choose-left-ident : ∀{A} → Hom (choose J A) A
-- choose-left-ident {U , X , α} = ⊎-left-ident , ⊎-left-ident-inv , (λ {u y} → cond {u}{y})
--  where
--   cond : {u : ⊥ ⊎ U} {y : X} →
--       (chooseᵣ {⊥ {ℓ}}{U}{⊥ {ℓ}} (λ x y₁ → ∅) α u (inj₂ y)) ≤M (α (⊎-left-ident u) y)
--   cond {inj₁ u}{x} = ⊥-elim {ℓ} u
--   cond {inj₂ u}{x} = reflM

-- choose-left-ident-inv : ∀{A} → Hom A (choose J A)
-- choose-left-ident-inv {U , X , α} = ⊎-left-ident-inv , ⊎-left-ident , ((λ {u y} → cond {u}{y}))
--  where
--   cond : {u : U} {y : ⊥ ⊎ X} →
--       (α u (⊎-left-ident y)) ≤M (chooseᵣ {⊥ {ℓ}} (λ x y₁ → ∅) α (inj₂ u) y)
--   cond {y = inj₁ x} = ⊥-elim {ℓ} x
--   cond {y = inj₂ y} = reflM

-- choose-left-ident-iso₁ : ∀{A} → choose-left-ident {A} ○ choose-left-ident-inv ≡h id
-- choose-left-ident-iso₁ {U , X , α} = ext-set ⊎-left-ident-iso₁ , ext-set ⊎-left-ident-iso₁

-- choose-left-ident-iso₂ : ∀{A} → choose-left-ident-inv {A} ○ choose-left-ident ≡h id
-- choose-left-ident-iso₂ {U , X , α} = ext-set ⊎-left-ident-iso₂ , ext-set ⊎-left-ident-iso₂

-- choose-right-ident : ∀{A} → Hom (choose A J) A
-- choose-right-ident {U , X , α} = ⊎-right-ident , ⊎-right-ident-inv , (λ {u y} → cond {u}{y})
--  where
--   cond : {u : U ⊎ ⊥} {y : X} →      
--       (chooseᵣ {U}{⊥ {ℓ}}{X}{⊥ {ℓ}} α (λ x y₁ → ∅) u (inj₁ y)) ≤M (α (⊎-right-ident u) y)
--   cond {inj₁ x} = reflM
--   cond {inj₂ y} = ⊥-elim {ℓ} y

-- choose-right-ident-inv : ∀{A} → Hom A (choose A J)
-- choose-right-ident-inv {U , X , α} = ⊎-right-ident-inv , ⊎-right-ident , (λ {u y} → cond {u}{y})
--  where
--   cond : {u : U} {y : X ⊎ ⊥} →
--       (α u (⊎-right-ident y)) ≤M (chooseᵣ {_}{⊥ {ℓ}} α (λ x y₁ → ∅) (inj₁ u) y)
--   cond {y = inj₁ x} = reflM
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
--       (+-cond (chooseᵣ α γ) (chooseᵣ β γ) u (aux₂ y)) ≤M
--       (+-cond (chooseᵣ α β) γ (aux₁ u) y)
--   cond {inj₁ (inj₁ x)} {inj₁ x₁ , b} = reflM
--   cond {inj₁ (inj₁ x)} {inj₂ y , b} = reflM
--   cond {inj₁ (inj₂ x)} {inj₁ x₁ , b} = a-unit-least abp-pf
--   cond {inj₁ (inj₂ x)} {inj₂ y , b} = reflM
--   cond {inj₂ (inj₁ x)} {inj₁ x₁ , b} = reflM
--   cond {inj₂ (inj₁ x)} {inj₂ y , b} = reflM
--   cond {inj₂ (inj₂ x)} {inj₁ x₁ , b} = reflM
--   cond {inj₂ (inj₂ x)} {inj₂ y , b} = a-unit-least abp-pf

-- choose-contract : ∀{A : Obj} → Hom (choose A A) A
-- choose-contract {U , X , α} = aux₁ , inj₁ , (λ {u y} → cond {u}{y})
--  where
--   aux₁ : U ⊎ U → U
--   aux₁ (inj₁ x) = x
--   aux₁ (inj₂ y) = y

--   cond : {u : U ⊎ U} {y : X} → (chooseᵣ α α u (inj₁ y)) ≤M (α (aux₁ u) y)
--   cond {inj₁ u}{x} = reflM
--   cond {inj₂ u}{x} = a-unit-least abp-pf                
