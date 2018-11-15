{-# OPTIONS --rewriting #-}

module Canonicity.Pi where

open import StrictLib hiding (id; _∘_)
open import Canonicity.CwF
open import Canonicity.ElU
import Syntax as S

Π :
  ∀{i}{Γˢ : S.Con i}            {Γ : Con _ Γˢ}
   {j}{Aˢ : S.Ty Γˢ j}          (A : Ty Γ _ Aˢ)
   {k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k} (B : Ty (Γ ▶ A) _ Bˢ)
   → Ty Γ (j ⊔ k) (S.Π Aˢ Bˢ)
Π {i} {Γˢ} {Γ} {j} {Aˢ} A {k} {Bˢ} B ν νᴾ tˢ =
  Σ (S.Tm (S.∙ S.▶ Aˢ S.[ ν ]T) (Bˢ S.[ ν S.^ Aˢ ]T)) λ tˢ*
  → (tˢ ≡ S.lam tˢ*)
  × ((u : S.Tm S.∙ (Aˢ S.[ ν ]T))(uᴾ : A ν νᴾ u) → B (ν S.,s u) (νᴾ , uᴾ) (tˢ* S.[ S.id S.,s u ]t))

lam :
     {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Aˢ : S.Ty {i}
     Γˢ j} {A : Ty {i} {Γˢ} Γ j Aˢ} {k : Level} {Bˢ : S.Ty {i ⊔ j} (S._▶_
     {i} Γˢ {j} Aˢ) k} {B : Ty {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} (_▶_ {i} {Γˢ}
     Γ {j} {Aˢ} A) k Bˢ} {tˢ : S.Tm {i ⊔ j} (S._▶_ {i} Γˢ {j} Aˢ) {k} Bˢ} →
     Tm {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} (_▶_ {i} {Γˢ} Γ {j} {Aˢ} A) {k} {Bˢ}
     B tˢ → Tm {i} {Γˢ} Γ {j ⊔ k} {S.Π {i} {Γˢ} {j} Aˢ {k} Bˢ} (Π {i} {Γˢ}
     {Γ} {j} {Aˢ} A {k} {Bˢ} B) (S.lam {i} {Γˢ} {j} {Aˢ} {k} {Bˢ} tˢ)
lam {i} {Γˢ} {Γ} {j} {Aˢ} {A} {k} {Bˢ} {B} {tˢ} t ν νᴾ =
    (tˢ S.[ ν S.^ Aˢ ]t)
  , refl
  , (λ u uᴾ → t (ν S.,s u) (νᴾ , uᴾ))

app :
     {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Aˢ : S.Ty {i}
     Γˢ j} {A : Ty {i} {Γˢ} Γ j Aˢ} {k : Level} {Bˢ : S.Ty {i ⊔ j} (S._▶_
     {i} Γˢ {j} Aˢ) k} {B : Ty {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} (_▶_ {i} {Γˢ}
     Γ {j} {Aˢ} A) k Bˢ} {tˢ : S.Tm {i} Γˢ {j ⊔ k} (S.Π {i} {Γˢ} {j} Aˢ {k}
     Bˢ)} → Tm {i} {Γˢ} Γ {j ⊔ k} {S.Π {i} {Γˢ} {j} Aˢ {k} Bˢ} (Π {i} {Γˢ}
     {Γ} {j} {Aˢ} A {k} {Bˢ} B) tˢ → Tm {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} (_▶_
     {i} {Γˢ} Γ {j} {Aˢ} A) {k} {Bˢ} B (S.app {i} {Γˢ} {j} {Aˢ} {k} {Bˢ}
     tˢ)
app {i} {Γˢ} {Γ} {j} {Aˢ} {A} {k} {Bˢ} {B} {tˢ} t ν νᴾ =
  let t* , q , r = t (S.π₁ ν) (₁ νᴾ)
  in tr (B ν νᴾ)
        {!((λ x → S.app x S.[ S.id S.,s S.π₂ ν ]t) & q ⁻¹)!} -- OK, REWRITE issue
        (r (S.π₂ ν) (₂ νᴾ))
