module attack-tree where

open import eq
open import empty
open import level
open import atl-semantics
open import atl-semantics-thms

data ATree (𝔹 : Set) : Set where
  NODE : (b : 𝔹) → ATree 𝔹
  AND  : ATree 𝔹 → ATree 𝔹 → ATree 𝔹
  OR   : ATree 𝔹 → ATree 𝔹 → ATree 𝔹
  SAND : ATree 𝔹 → ATree 𝔹 → ATree 𝔹

⟦_⟧_ : {𝔹 : Set} → ATree 𝔹 → (𝔹 → Three) → Three
⟦ NODE b ⟧ α = α b
⟦ AND t₁ t₂ ⟧ α = (⟦ t₁ ⟧ α) ⊙₃ (⟦ t₂ ⟧ α)
⟦ OR t₁ t₂ ⟧ α = (⟦ t₁ ⟧ α) ⊔₃ (⟦ t₂ ⟧ α)
⟦ SAND t₁ t₂ ⟧ α = (⟦ t₁ ⟧ α) ▷₃ (⟦ t₂ ⟧ α)

AND-sym : ∀{𝔹}{t₁ t₂ : ATree 𝔹}{α} → (⟦ AND t₁ t₂ ⟧ α) ≡ (⟦ AND t₂ t₁ ⟧ α)
AND-sym {𝔹}{t₁}{t₂}{α} = symm₃ {⟦ t₁ ⟧ α}

AND-assoc : ∀{𝔹}{t₁ t₂ t₃ : ATree 𝔹}{α} → (⟦ AND (AND t₁ t₂) t₃ ⟧ α) ≡ (⟦ AND t₁ (AND t₂ t₃) ⟧ α)
AND-assoc {𝔹}{t₁}{t₂}{t₃}{α} = assoc₃ {⟦ t₁ ⟧ α}

AND-contract : (∀{a} → (a ⊙₃ a) ≡ a) → ⊥ {lzero}
AND-contract p = not-same-half-zero (p {zero})

OR-sym : ∀{𝔹}{t₁ t₂ : ATree 𝔹}{α} → (⟦ OR t₁ t₂ ⟧ α) ≡ (⟦ OR t₂ t₁ ⟧ α)
OR-sym {𝔹}{t₁}{t₂}{α} = lchoice-sym {⟦ t₁ ⟧ α}

OR-assoc : ∀{𝔹}{t₁ t₂ t₃ : ATree 𝔹}{α} → (⟦ OR (OR t₁ t₂) t₃ ⟧ α) ≡ (⟦ OR t₁ (OR t₂ t₃) ⟧ α)
OR-assoc {𝔹}{t₁}{t₂}{t₃}{α} = lchoice-assoc₃ {⟦ t₁ ⟧ α}

OR-contract : ∀{𝔹}{t : ATree 𝔹}{α} → (⟦ OR t t ⟧ α) ≡ (⟦ t ⟧ α)
OR-contract {𝔹}{t} = lchoice-contract

SAND-assoc : ∀{𝔹}{t₁ t₂ t₃ : ATree 𝔹}{α} → (⟦ SAND (SAND t₁ t₂) t₃ ⟧ α) ≡ (⟦ SAND t₁ (SAND t₂ t₃) ⟧ α)
SAND-assoc {𝔹}{t₁}{t₂}{t₃}{α} = sym (land-assoc {⟦ t₁ ⟧ α}{⟦ t₂ ⟧ α}{⟦ t₃ ⟧ α})

SAND-contract : (∀{a} → (a ▷₃ a) ≡ a) → ⊥ {lzero}
SAND-contract p = not-same-half-zero (p {zero})

AND-OR-dist₁ : ∀{𝔹}{t₁ t₂ t₃ : ATree 𝔹}{α} → (⟦ AND t₁ (OR t₂ t₃) ⟧ α) ≡ (⟦ OR (AND t₁ t₂) (AND t₁ t₃) ⟧ α)
AND-OR-dist₁ {𝔹}{t₁}{t₂}{t₃}{α} = sym (para-over-lchoice {⟦ t₁ ⟧ α})

AND-OR-dist₂ : ∀{𝔹}{t₁ t₂ t₃ : ATree 𝔹}{α} → (⟦ AND (OR t₁ t₂) t₃ ⟧ α) ≡ (⟦ OR (AND t₁ t₃) (AND t₂ t₃) ⟧ α)
AND-OR-dist₂ {𝔹}{t₁}{t₂}{t₃}{α} = sym (para-over-lchoice2 {⟦ t₁ ⟧ α})

SAND-OR-dist₁ : ∀{𝔹}{t₁ t₂ t₃ : ATree 𝔹}{α} → (⟦ SAND t₁ (OR t₂ t₃) ⟧ α) ≡ (⟦ OR (SAND t₁ t₂) (SAND t₁ t₃) ⟧ α)
SAND-OR-dist₁ {𝔹}{t₁}{t₂}{t₃}{α} = sym (seq-over-lchoice {⟦ t₁ ⟧ α})

SAND-OR-dist₂ : ∀{𝔹}{t₁ t₂ t₃ : ATree 𝔹}{α} → (⟦ SAND (OR t₁ t₂) t₃ ⟧ α) ≡ (⟦ OR (SAND t₁ t₃) (SAND t₂ t₃) ⟧ α)
SAND-OR-dist₂ {𝔹}{t₁}{t₂}{t₃}{α} = sym (seq-over-lchoice2 {⟦ t₃ ⟧ α}{⟦ t₁ ⟧ α})
