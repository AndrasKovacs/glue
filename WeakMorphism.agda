{-# OPTIONS --rewriting #-}

module WeakMorphism where

{-
The notion of weak morphism already needs:
  - Π←, because otherwise we can't type lam
  - ▶-iso, except ▶p

Glued needs:
  - preservation of ▶, ∙ up to iso
  - Π natural iso except Πq, lam, app

GlobalSection:
  - Π← does not work. Since weak morphisms aren't typable without Π←, global section doesn't seem to be
    a morphism in an obvious way.
  - El is strict
  - Only Bool← for Bool.
-}


open import StrictLib hiding (id; _∘_)
import Syntax as S
open import Data.Bool renaming (Bool to 𝔹; true to 𝕋; false to 𝔽)

postulate
  Con   : ∀ {i} → S.Con i → Set i
  Ty    : ∀ {i Γˢ j} → S.Ty {i} Γˢ j → Con Γˢ → Set j
  Sub   : ∀ {i Γˢ j Δˢ} → S.Sub {i} Γˢ {j} Δˢ → Con Γˢ → Con Δˢ
  Tm    : ∀ {i Γˢ j Aˢ} → S.Tm {i} Γˢ {j} Aˢ → ((Γ : Con Γˢ) → Ty Aˢ Γ)

  -- this would be (Con S.∙ ≡ ⊤), but we can simplify because of terminality of ⊤
  ∙     : Con S.∙
  ∙η    : (Γ : Con S.∙) → Γ ≡ ∙

  ▶→    : ∀ {i}{Γˢ : S.Con i}{j}{Aˢ : S.Ty Γˢ j} → Con (Γˢ S.▶ Aˢ) → (Σ (Con Γˢ) (Ty Aˢ))
  ▶←    : ∀ {i}{Γˢ : S.Con i}{j}{Aˢ : S.Ty Γˢ j} → (Σ (Con Γˢ) (Ty Aˢ)) → Con (Γˢ S.▶ Aˢ)
  ▶p    : ∀ {i}{Γˢ : S.Con i}{j}{Aˢ : S.Ty Γˢ j} x → ▶→ {i}{Γˢ}{j}{Aˢ} (▶← x) ≡ x
  ▶q    : ∀ {i}{Γˢ : S.Con i}{j}{Aˢ : S.Ty Γˢ j} x → ▶← {i}{Γˢ}{j}{Aˢ} (▶→ x) ≡ x

{-# REWRITE ▶p ▶q #-}

postulate

  []T   : ∀ {i}{Γˢ : S.Con i}{j}{Δˢ : S.Con j}{k}{Aˢ : S.Ty Δˢ k}{σˢ : S.Sub Γˢ Δˢ}
          → Ty (Aˢ S.[ σˢ ]T) ≡ (λ Γ → Ty Aˢ (Sub σˢ Γ))
  id    : ∀ {i Γˢ} → Sub (S.id {i}{Γˢ}) ≡ (λ Γ → Γ)
  ∘     : ∀ {i Γˢ j Δˢ k Σˢ σˢ δˢ} → Sub (S._∘_ {i}{Γˢ}{j}{Δˢ} σˢ {k}{Σˢ} δˢ) ≡ (λ Σ → Sub σˢ (Sub δˢ Σ))

{-# REWRITE []T id ∘ #-}

postulate
  ε     : ∀ {i Γˢ} → Sub (S.ε {i}{Γˢ}) ≡ (λ Γ → ∙)
  ,s    : ∀{i}{Γˢ : S.Con i}{j}{Δˢ : S.Con j}{σˢ : S.Sub Γˢ Δˢ}{k}{Aˢ : S.Ty Δˢ k}{tˢ : S.Tm Γˢ (Aˢ S.[ σˢ ]T)}
          → Sub (S._,s_ σˢ {k}{Aˢ} tˢ) ≡ (λ Γ → ▶← ((Sub σˢ Γ) , Tm tˢ Γ))
  π₁    : ∀{i}{Γˢ : S.Con i}{j}{Δˢ : S.Con j}{k}{Aˢ : S.Ty Δˢ k}(σˢ : S.Sub Γˢ (Δˢ S.▶ Aˢ))
          → Sub (S.π₁ σˢ) ≡ (λ Γ → ₁ (▶→ (Sub σˢ Γ)))
{-# REWRITE ,s π₁ #-}

postulate
  π₂    : ∀{i}{Γˢ : S.Con i}{j}{Δˢ : S.Con j}{k}{Aˢ : S.Ty Δˢ k}(σˢ : S.Sub Γˢ (Δˢ S.▶ Aˢ))
          → Tm (S.π₂ σˢ) ≡ (λ Γ → ₂ (▶→ (Sub σˢ Γ)))

--spec--------------------------------------------------------------------------
  Tmπ₂ :
   (i  : Level)
   (Γˢ : S.Con i)
   (Γ  : Con Γˢ → Set i)
   (j  : Level)
   (Δˢ : S.Con j)
   (Δ  : Con Δˢ → Set j)
   (σˢ : S.Sub Γˢ Δˢ)
   (σ  : (Γᶠ₁ : Con Γˢ) → Γ Γᶠ₁ → Δ (Sub σˢ Γᶠ₁))
   (k  : Level)
   (Aˢ : S.Ty Δˢ k)
   (A  : (Γᶠ₁ : Con Δˢ) → Δ Γᶠ₁ → Ty Aˢ Γᶠ₁ → Set k)
   (Γᶠ : Con (Γˢ S.▶ Aˢ S.[ σˢ ]T))
   → Tm (S.π₂ S.id) Γᶠ ≡ ₂ (▶→ Γᶠ)
--------------------------------------------------------------------------------

  []t   : ∀{i}{Δˢ : S.Con i}{j}{A : S.Ty Δˢ j}(tˢ : S.Tm Δˢ A){k}{Γˢ : S.Con k}(σˢ : S.Sub Γˢ Δˢ)
          → Tm (tˢ S.[ σˢ ]t) ≡ (λ Γ → Tm tˢ (Sub σˢ Γ))

  -- strict Π would be:
  -- Π     : ∀{i}{Γˢ : S.Con i}{j}(Aˢ : S.Ty Γˢ j){k}(Bˢ : S.Ty (Γˢ S.▶ Aˢ) k)
  --         → Ty (S.Π Aˢ Bˢ) ≡ (λ Γ → (α : Ty Aˢ Γ) → Ty Bˢ (▶← (Γ , α)))

  Π→    : ∀{i}{Γˢ : S.Con i}{j} Γ (Aˢ : S.Ty Γˢ j){k}(Bˢ : S.Ty (Γˢ S.▶ Aˢ) k)
          → Ty (S.Π Aˢ Bˢ) Γ → ((A : Ty Aˢ Γ) → Ty Bˢ (▶← (Γ , A)))

  Π←    : ∀{i}{Γˢ : S.Con i}{j} Γ (Aˢ : S.Ty Γˢ j){k}(Bˢ : S.Ty (Γˢ S.▶ Aˢ) k)
          → ((A : Ty Aˢ Γ) → Ty Bˢ (▶← (Γ , A))) → Ty (S.Π Aˢ Bˢ) Γ
{-# REWRITE π₂ []t Tmπ₂ #-}


postulate
  -- Π→nat : ∀{i}{Δˢ : S.Con i}{j}{Δ : Con Δˢ }(Aˢ : S.Ty Δˢ j){k}(Bˢ : S.Ty (Δˢ S.▶ Aˢ) k){l}{Γˢ}{σˢ : S.Sub {l} Γˢ {i} Δˢ}
  --          (Γ  : Con Γˢ)
  --          (f  : Ty (S.Π Aˢ Bˢ) (Sub σˢ Γ))
  --          (A  : Ty Aˢ (Sub σˢ Γ))
  --         → Π→ {Γˢ = Γˢ} Γ (Aˢ S.[ σˢ ]T) (Bˢ S.[ σˢ S.^ Aˢ ]T) f A ≡ Π→ {Γˢ = Δˢ}(Sub σˢ Γ) Aˢ Bˢ f {!A!}

  Πp    : ∀{i}{Γˢ : S.Con i}{j}{Γ}{Aˢ : S.Ty Γˢ j}{k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k}(f : ((A : Ty Aˢ Γ) → Ty Bˢ (▶← (Γ , A)))) A
          → Π→ _ Aˢ Bˢ (Π← _ Aˢ Bˢ f) A ≡ f A

  Πq    : ∀{i}{Γˢ : S.Con i}{j}{Γ}{Aˢ : S.Ty Γˢ j}{k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k}(x : Ty (S.Π Aˢ Bˢ) Γ)
          → Π← _ Aˢ Bˢ (Π→ _ Aˢ Bˢ x) ≡ x

--spec--------------------------------------------------------------------------
  TyΠ[] :
     ∀ {i}{Γˢ : S.Con i}{j}{Δˢ : S.Con j}{k}{Aˢ : S.Ty Δˢ k}{σˢ : S.Sub Γˢ Δˢ}{l}{Γˢ}{σˢ : S.Sub {l} Γˢ Δˢ}
       {m}{Bˢ : S.Ty (Δˢ S.▶ Aˢ) m}
       → Ty (S.Π (Aˢ S.[ σˢ ]T) (Bˢ S.[ σˢ S.^ Aˢ ]T)) ≡ λ Γ → Ty (S.Π Aˢ Bˢ) (Sub σˢ Γ)
--------------------------------------------------------------------------------
{-# REWRITE Πp Πq TyΠ[] #-}


postulate
  lam   : ∀{i}{Γˢ : S.Con i}{j}{Aˢ : S.Ty Γˢ j}{k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k}(tˢ : S.Tm (Γˢ S.▶ Aˢ) Bˢ)
          → Tm (S.lam tˢ) ≡ (λ Γ → Π← _ Aˢ Bˢ (λ A → Tm tˢ (▶← (Γ , A))))

  app   : ∀{i}{Γˢ : S.Con i}{j}{Aˢ : S.Ty Γˢ j}{k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k}(tˢ : S.Tm Γˢ (S.Π Aˢ Bˢ))
          → Tm (S.app tˢ) ≡ (λ Γ → Π→ _ Aˢ Bˢ (Tm tˢ (▶→ Γ .₁)) (▶→ Γ .₂))

  U→    : ∀{i}{Γˢ : S.Con i}{j : Level} Γ → Ty (S.U {i}{Γˢ} j) Γ → Set j
{-# REWRITE lam app #-}

--spec--------------------------------------------------------------------------
postulate
  TyU[] :
    (i  : Level)
    (Γˢ : S.Con i)
    (j  : Level)
    (Δˢ : S.Con j)
    (σˢ : S.Sub Γˢ Δˢ)
    (k  : Level)
    (Γᶠ : Con Γˢ)
    → Ty (S.U k) (Sub σˢ Γᶠ) ≡ Ty (S.U k) Γᶠ
{-# REWRITE TyU[] #-}

postulate
  TyEl[] :
     (i  : Level)
     (Γˢ : S.Con i)
     (j  : Level)
     (Δˢ : S.Con j)
     (σˢ : S.Sub Γˢ Δˢ)
     (k  : Level)
     (aˢ : S.Tm Δˢ (S.U k))
     (Γᶠ : Con Γˢ)
     → Ty (S.El (aˢ S.[ σˢ ]t)) Γᶠ ≡ Ty (S.El aˢ) (Sub σˢ Γᶠ)
{-# REWRITE TyEl[] #-}
--------------------------------------------------------------------------------

postulate
  U→nat :
    (i  : Level)
    (Γˢ : S.Con i)
    (j  : Level)
    (Δˢ : S.Con j)
    (σˢ : S.Sub Γˢ Δˢ)
    (k  : Level)
    (Γᶠ : Con Γˢ)
    (Aᶠ : Ty (S.U k) Γᶠ)
    → U→ {j} {Δˢ} {k} (Sub {i} {Γˢ} {j} {Δˢ} σˢ Γᶠ) Aᶠ ≡  U→ {i} {Γˢ} {k} Γᶠ Aᶠ
{-# REWRITE U→nat #-}

postulate
  El→   : ∀{i}{Γˢ : S.Con i}{j}(aˢ : S.Tm Γˢ (S.U j)) Γ → Ty (S.El aˢ) Γ → U→ Γ (Tm aˢ Γ)
  -- TODO: El→-nat

  c→    : ∀{i}{Γˢ : S.Con i}{j}(Aˢ : S.Ty Γˢ j) Γ → U→ Γ (Tm (S.c Aˢ) Γ) → Ty Aˢ Γ

  Elc→ :
     {i  : Level}
     (Γˢ : S.Con i)
     (Γ  : Con Γˢ)
     {j  : Level}
     (aˢ : S.Tm Γˢ (S.U j))
     (Γᶠ : Con Γˢ)
     (Aᶠ : U→ Γᶠ (Tm aˢ Γᶠ))
     → El→ aˢ Γᶠ (c→ (S.El aˢ) Γᶠ Aᶠ) ≡ Aᶠ

  cEl→ :
     {i  : Level}
     (Γˢ : S.Con i)
     {j  : Level}
     (Aˢ : S.Ty Γˢ j)
     (Γᶠ : Con Γˢ)
     (Aᶠ : Ty Aˢ Γᶠ)
     → c→ Aˢ Γᶠ (El→ (S.c Aˢ) Γᶠ Aᶠ) ≡ Aᶠ
{-# REWRITE Elc→ cEl→ #-}

postulate
  Bool←    : ∀ {i}{Γˢ : S.Con i}(Γ : Con Γˢ) → 𝔹 → Ty S.Bool Γ

--spec--------------------------------------------------------------------------
  TyBool[] : ∀ {i}{Γˢ : S.Con i}{j}{Δˢ : S.Con j}{σˢ : S.Sub Γˢ Δˢ}(Γ : Con Γˢ)
             → Ty S.Bool (Sub σˢ Γ) ≡ Ty S.Bool Γ
--------------------------------------------------------------------------------
{-# REWRITE TyBool[] #-}

postulate
  Bool→nat : ∀ {i}{Γˢ : S.Con i}{j}{Δˢ : S.Con j}{σˢ : S.Sub Γˢ Δˢ}(Γ : Con Γˢ) b →
                Bool← (Sub σˢ Γ) b ≡ Bool← Γ b
{-# REWRITE Bool→nat #-}
