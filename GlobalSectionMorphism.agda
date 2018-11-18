{-# OPTIONS --rewriting #-}

module GlobalSectionMorphism where

open import StrictLib hiding (id; _∘_)
open import Data.Bool renaming (Bool to 𝔹; true to 𝕋; false to 𝔽)
import Syntax as S

Con : ∀ {i} → S.Con i → Set i
Con {i} Γˢ = S.Sub S.∙ Γˢ

Ty : ∀ {i Γˢ j} → S.Ty {i} Γˢ j → Con Γˢ → Set j
Ty {i} {Γˢ} {j} Aˢ σ = S.Tm S.∙ (Aˢ S.[ σ ]T)

Sub : ∀ {i Γˢ j Δˢ} → S.Sub {i} Γˢ {j} Δˢ → Con Γˢ → Con Δˢ
Sub {i} {Γˢ} {j} {Δˢ} σˢ δ = σˢ S.∘ δ

Tm    : ∀ {i Γˢ j Aˢ} → S.Tm {i} Γˢ {j} Aˢ → ((Γ : Con Γˢ) → Ty Aˢ Γ)
Tm {i}{Γˢ}{j}{Aˢ} tˢ σ = tˢ S.[ σ ]t

∙ : Con S.∙
∙ = S.ε

∙η : (Γ : Con S.∙) → Γ ≡ ∙
∙η Γ = S.∙η

▶→  : ∀ {i}{Γˢ : S.Con i}{j}{Aˢ : S.Ty Γˢ j} → Con (Γˢ S.▶ Aˢ) → (Σ (Con Γˢ) (Ty Aˢ))
▶→ {i}{Γˢ}{j}{Aˢ} σ = S.π₁ σ , S.π₂ σ

▶←    : ∀ {i}{Γˢ : S.Con i}{j}{Aˢ : S.Ty Γˢ j} → (Σ (Con Γˢ) (Ty Aˢ)) → Con (Γˢ S.▶ Aˢ)
▶← {i} {Γˢ} {j} {Aˢ} (σ , t) = σ S.,s t

▶p : ∀ {i}{Γˢ : S.Con i}{j}{Aˢ : S.Ty Γˢ j} x → ▶→ {i}{Γˢ}{j}{Aˢ} (▶← x) ≡ x
▶p (σ , t) = refl

▶q  : ∀ {i}{Γˢ : S.Con i}{j}{Aˢ : S.Ty Γˢ j} x → ▶← {i}{Γˢ}{j}{Aˢ} (▶→ x) ≡ x
▶q σ = refl

[]T   : ∀ {i}{Γˢ : S.Con i}{j}{Δˢ : S.Con j}{k}{Aˢ : S.Ty Δˢ k}{σˢ : S.Sub Γˢ Δˢ}
          → Ty (Aˢ S.[ σˢ ]T) ≡ (λ Γ → Ty Aˢ (Sub σˢ Γ))
[]T {i} {Γˢ} {j} {Δˢ} {k} {Aˢ} {σˢ} = refl

id  : ∀ {i Γˢ} → Sub (S.id {i}{Γˢ}) ≡ (λ Γ → Γ)
id = refl

∘ : ∀ {i Γˢ j Δˢ k Σˢ σˢ δˢ} → Sub (S._∘_ {i}{Γˢ}{j}{Δˢ} σˢ {k}{Σˢ} δˢ) ≡ (λ Σ → Sub σˢ (Sub δˢ Σ))
∘ = refl

ε  : ∀ {i Γˢ} → Sub (S.ε {i}{Γˢ}) ≡ (λ _ → ∙)
ε = ext (λ σ → S.∙η)

,s    : ∀{i}{Γˢ : S.Con i}{j}{Δˢ : S.Con j}{σˢ : S.Sub Γˢ Δˢ}{k}{Aˢ : S.Ty Δˢ k}{tˢ : S.Tm Γˢ (Aˢ S.[ σˢ ]T)}
          → Sub (S._,s_ σˢ {k}{Aˢ} tˢ) ≡ (λ Γ → ▶← ((Sub σˢ Γ) , Tm tˢ Γ))
,s = refl

π₁    : ∀{i}{Γˢ : S.Con i}{j}{Δˢ : S.Con j}{k}{Aˢ : S.Ty Δˢ k}(σˢ : S.Sub Γˢ (Δˢ S.▶ Aˢ))
        → Sub (S.π₁ σˢ) ≡ (λ Γ → ₁ (▶→ (Sub σˢ Γ)))
π₁ σˢ  = refl

π₂    : ∀{i}{Γˢ : S.Con i}{j}{Δˢ : S.Con j}{k}{Aˢ : S.Ty Δˢ k}(σˢ : S.Sub Γˢ (Δˢ S.▶ Aˢ))
        → Tm (S.π₂ σˢ) ≡ (λ Γ → ₂ (▶→ (Sub σˢ Γ)))
π₂ σˢ = refl

[]t   : ∀{i}{Δˢ : S.Con i}{j}{A : S.Ty Δˢ j}(tˢ : S.Tm Δˢ A){k}{Γˢ : S.Con k}(σˢ : S.Sub Γˢ Δˢ)
        → Tm (tˢ S.[ σˢ ]t) ≡ (λ Γ → Tm tˢ (Sub σˢ Γ))
[]t tˢ σˢ = refl

Π→    : ∀{i}{Γˢ : S.Con i}{j}{Γ}(Aˢ : S.Ty Γˢ j){k}(Bˢ : S.Ty (Γˢ S.▶ Aˢ) k)
        → Ty (S.Π Aˢ Bˢ) Γ → ((A : Ty Aˢ Γ) → Ty Bˢ (▶← (Γ , A)))
Π→ {i} {Γˢ} {j} {Γ} Aˢ Bˢ tˢ u = S.app tˢ S.[ S.id S.,s u ]t

Π←    : ∀{i}{Γˢ : S.Con i}{j}{Γ}(Aˢ : S.Ty Γˢ j){k}(Bˢ : S.Ty (Γˢ S.▶ Aˢ) k)
        → ((A : Ty Aˢ Γ) → Ty Bˢ (▶← (Γ , A))) → Ty (S.Π Aˢ Bˢ) Γ
Π← {i} {Γˢ} {j} {Γ} Aˢ {k} Bˢ f = {!!} -- S.lam {!!}  -- doesn't seem possible

--   Πp    : ∀{i}{Γˢ : S.Con i}{j}{Γ}{Aˢ : S.Ty Γˢ j}{k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k}(f : ((A : Ty Aˢ Γ) → Ty Bˢ (▶← (Γ , A)))) A
--           → Π→ Aˢ Bˢ (Π← Aˢ Bˢ f) A ≡ f A

--   Πq    : ∀{i}{Γˢ : S.Con i}{j}{Γ}{Aˢ : S.Ty Γˢ j}{k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k}(x : Ty (S.Π Aˢ Bˢ) Γ)
--           → Π← Aˢ Bˢ (Π→ Aˢ Bˢ x) ≡ x

-- {-# REWRITE π₂ []t Πp Πq #-}


lam   : ∀{i}{Γˢ : S.Con i}{j}{Aˢ : S.Ty Γˢ j}{k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k}(tˢ : S.Tm (Γˢ S.▶ Aˢ) Bˢ)
        → Tm (S.lam tˢ) ≡ {!Tm  (S.lam tˢ)!} -- λ Γ → S.lam tˢ S.[ Γ ]t -- (λ Γ → Π← Aˢ Bˢ (λ A → Tm tˢ (▶← (Γ , A))))
lam = {!!}

app   : ∀{i}{Γˢ : S.Con i}{j}{Aˢ : S.Ty Γˢ j}{k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k}(tˢ : S.Tm Γˢ (S.Π Aˢ Bˢ))
        → Tm (S.app tˢ) ≡ (λ Γ → Π→ Aˢ Bˢ (Tm tˢ (▶→ Γ .₁)) (▶→ Γ .₂))
app {i} {Γˢ} {j} {Aˢ} {k} {Bˢ} tˢ = ext λ Γ → {!!} -- OK


-- Only works if other model is Set (in other cases)
U→    : ∀{i}{Γˢ : S.Con i}{j : Level} Γ → Ty (S.U {i}{Γˢ} j) Γ → Set j
U→ {i} {Γˢ} {j} Γ a = S.Tm S.∙ (S.El a)

-- U← : ∀{i}{Γˢ : S.Con i}{j : Level} Γ → Set j → Ty (S.U {i}{Γˢ} j) Γ
-- U← {i} {Γˢ} {j} Γ a = {!!}

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
U→nat i Γˢ j Δˢ σˢ k Γᶠ Aᶠ = refl

-- El, c are strict though...
El→  : ∀{i}{Γˢ : S.Con i}{j}(aˢ : S.Tm Γˢ (S.U j)) Γ → Ty (S.El aˢ) Γ ≡ U→ Γ (Tm aˢ Γ)
El→ aˢ Γ = refl

c : ∀{i}{Γˢ : S.Con i}{j}(Aˢ : S.Ty Γˢ j) Γ → U→ Γ (Tm (S.c Aˢ) Γ) ≡ Ty Aˢ Γ
c Aˢ Γ = refl

-- Only the backwards direction for Bool
Bool←  : ∀ {i}{Γˢ : S.Con i}(Γ : Con Γˢ) → 𝔹 → Ty S.Bool Γ
Bool← Γ 𝔽 = S.false
Bool← Γ 𝕋 = S.true
