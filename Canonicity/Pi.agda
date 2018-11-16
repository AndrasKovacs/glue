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

Π[] :
   {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Aˢ : S.Ty {i} Γˢ j} {A :
   Ty {i} {Γˢ} Γ j Aˢ} {k : Level} {Bˢ : S.Ty {i ⊔ j} (S._▶_ {i} Γˢ {j} Aˢ) k} {B :
   Ty {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} (_▶_ {i} {Γˢ} Γ {j} {Aˢ} A) k Bˢ} {l : Level}
   {θˢ : S.Con l} {θ : Con l θˢ} {σˢ : S.Sub {l} θˢ {i} Γˢ} {σ : Sub {l} {θˢ} θ {i}
   {Γˢ} Γ σˢ} → _≡_ {suc j ⊔ (suc k ⊔ l)} {Ty {l} {θˢ} θ (j ⊔ k) (S.Π {l} {θˢ} {j}
   (S._[_]T {i} {Γˢ} {j} Aˢ {l} {θˢ} σˢ) {k} (S._[_]T {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ}
   {k} Bˢ {j ⊔ l} {S._▶_ {l} θˢ {j} (S._[_]T {i} {Γˢ} {j} Aˢ {l} {θˢ} σˢ)} (S._^_
   {l} {θˢ} {i} {Γˢ} σˢ {j} Aˢ)))} (_[_]T {i} {Γˢ} {Γ} {j ⊔ k} {S.Π {i} {Γˢ} {j} Aˢ
   {k} Bˢ} (Π {i} {Γˢ} {Γ} {j} {Aˢ} A {k} {Bˢ} B) {l} {θˢ} {θ} {σˢ} σ) (Π {l} {θˢ}
   {θ} {j} {S._[_]T {i} {Γˢ} {j} Aˢ {l} {θˢ} σˢ} (_[_]T {i} {Γˢ} {Γ} {j} {Aˢ} A {l}
   {θˢ} {θ} {σˢ} σ) {k} {S._[_]T {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} {k} Bˢ {j ⊔ l}
   {S._▶_ {l} θˢ {j} (S._[_]T {i} {Γˢ} {j} Aˢ {l} {θˢ} σˢ)} (S._^_ {l} {θˢ} {i}
   {Γˢ} σˢ {j} Aˢ)} (_[_]T {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} {_▶_ {i} {Γˢ} Γ {j} {Aˢ}
   A} {k} {Bˢ} B {j ⊔ l} {S._▶_ {l} θˢ {j} (S._[_]T {i} {Γˢ} {j} Aˢ {l} {θˢ} σˢ)}
   {_▶_ {l} {θˢ} θ {j} {S._[_]T {i} {Γˢ} {j} Aˢ {l} {θˢ} σˢ} (_[_]T {i} {Γˢ} {Γ}
   {j} {Aˢ} A {l} {θˢ} {θ} {σˢ} σ)} {S._^_ {l} {θˢ} {i} {Γˢ} σˢ {j} Aˢ} (_^_ {l}
   {θˢ} {θ} {i} {Γˢ} {Γ} {σˢ} σ {j} {Aˢ} A)))
Π[] {i} {Γˢ} {Γ} {j} {Aˢ} {A} {k} {Bˢ} {B} {l} {θˢ} {θ} {σˢ} {σ} =
  ext λ ν → ext λ νᴾ → ext λ tˢ →
  ap2̃ Σ {!!} -- trivial if REWRITE works
        {!!} -- also true


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
