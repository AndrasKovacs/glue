{-# OPTIONS --rewriting #-}

module GluedU where

open import StrictLib hiding (id; _∘_)
open import GluedCwF
import Syntax as S
import WeakMorphism as F

-- in the case of canonicity
-- U : ∀{i}{Γˢ : S.Con i}{Γ : Con _ Γˢ} j → Ty Γ (suc j) (S.U j)
-- U {i} {Γˢ} {Γ} j ν νᴾ aˢ = (S.Tm S.∙ (S.El aˢ) → Set j)

U :
  {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} (j : Level) →
  Ty {i} {Γˢ} Γ (suc j) (S.U {i} {Γˢ} j)
U {i} {Γˢ} {Γ} j Γᶠ Γᴾ Aᶠ = F.U→ Aᶠ → Set j

U[] :
   {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Δˢ : S.Con j}
   {Δ : Con j Δˢ} {σˢ : S.Sub {i} Γˢ {j} Δˢ} {σ : Sub {i} {Γˢ} Γ {j} {Δˢ}
   Δ σˢ} {k : Level} → _≡_ {i ⊔ suc (suc k)} {Ty {i} {Γˢ} Γ (suc k) (S.U
   {i} {Γˢ} k)} (_[_]T {j} {Δˢ} {Δ} {suc k} {S.U {j} {Δˢ} k} (U {j} {Δˢ}
   {Δ} k) {i} {Γˢ} {Γ} {σˢ} σ) (U {i} {Γˢ} {Γ} k)
U[] {i} {Γˢ} {Γ} {j} {Δˢ} {Δ} {σˢ} {σ} {k} =
  ext λ Γᶠ → ext λ Γᴾ → ext λ Aᶠ → {!Π≡!} -- needed: naturality for U

      -- (F.U→ {j} {Δˢ} {k} {F.Sub {i} {Γˢ} {j} {Δˢ} σˢ Γᶠ} Aᶠ ≡  F.U→ {i} {Γˢ} {k} {Γᶠ} Aᶠ

El :
  {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {aˢ : S.Tm {i} Γˢ {suc
  j} (S.U {i} {Γˢ} j)} → Tm {i} {Γˢ} Γ {suc j} {S.U {i} {Γˢ} j} (U {i} {Γˢ} {Γ} j)
  aˢ → Ty {i} {Γˢ} Γ j (S.El {i} {Γˢ} {j} aˢ)
El {i} {Γˢ} {Γ} {j} {aˢ} a Γᶠ Γᴾ Aᶠ = a Γᶠ Γᴾ (F.El→ aˢ Γᶠ Aᶠ)

El[] :
  {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Δˢ : S.Con j}
  {Δ : Con j Δˢ} {σˢ : S.Sub {i} Γˢ {j} Δˢ} {σ : Sub {i} {Γˢ} Γ {j} {Δˢ}
  Δ σˢ} {k : Level} {aˢ : S.Tm {j} Δˢ {suc k} (S.U {j} {Δˢ} k)} {a : Tm
  {j} {Δˢ} Δ {suc k} {S.U {j} {Δˢ} k} (U {j} {Δˢ} {Δ} k) aˢ} → _≡_ {i ⊔
  suc k} {Ty {i} {Γˢ} Γ k (S.El {i} {Γˢ} {k} (S._[_]t {j} {Δˢ} {suc k}
  {S.U {j} {Δˢ} k} aˢ {i} {Γˢ} σˢ))} (_[_]T {j} {Δˢ} {Δ} {k} {S.El {j}
  {Δˢ} {k} aˢ} (El {j} {Δˢ} {Δ} {k} {aˢ} a) {i} {Γˢ} {Γ} {σˢ} σ) (El {i}
  {Γˢ} {Γ} {k} {S._[_]t {j} {Δˢ} {suc k} {S.U {j} {Δˢ} k} aˢ {i} {Γˢ}
  σˢ} (tr {i ⊔ suc (suc k)} {i ⊔ suc k} {Ty {i} {Γˢ} Γ (suc k) (S.U {i}
  {Γˢ} k)} (λ x → Tm {i} {Γˢ} Γ {suc k} {S.U {i} {Γˢ} k} x (S._[_]t {j}
  {Δˢ} {suc k} {S.U {j} {Δˢ} k} aˢ {i} {Γˢ} σˢ)) {_[_]T {j} {Δˢ} {Δ}
  {suc k} {S.U {j} {Δˢ} k} (U {j} {Δˢ} {Δ} k) {i} {Γˢ} {Γ} {σˢ} σ} {U
  {i} {Γˢ} {Γ} k} (U[] {i} {Γˢ} {Γ} {j} {Δˢ} {Δ} {σˢ} {σ} {k}) (_[_]t
  {j} {Δˢ} {Δ} {suc k} {S.U {j} {Δˢ} k} {U {j} {Δˢ} {Δ} k} {aˢ} a {i}
  {Γˢ} {Γ} {σˢ} σ)))
El[] {i} {Γˢ} {Γ} {j} {Δˢ} {Δ} {σˢ} {σ} {k} {aˢ} {a} = {!!} -- El naturality needed

--          a (F.Sub σˢ Γᶠ) (σ Γᶠ Γᴾ) (F.El→ aˢ (F.Sub σˢ Γᶠ) Aᶠ))
--       ≡
--          a (F.Sub σˢ Γᶠ) (σ Γᶠ Γᴾ) (F.El→ (aˢ S.[ σˢ ]t) Γᶠ Aᶠ)

c :
 {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level}
 {Aˢ : S.Ty {i} Γˢ j} →
 Ty {i} {Γˢ} Γ j Aˢ →
 Tm {i} {Γˢ} Γ {suc j} {S.U {i} {Γˢ} j} (U {i} {Γˢ} {Γ} j)
 (S.c {i} {Γˢ} {j} Aˢ)
c {i} {Γˢ} {Γ} {j} {Aˢ} A Γᶠ Γᴾ Aᶠ = A Γᶠ Γᴾ (F.c→ Aˢ Γᶠ Aᶠ)

Elc :
  {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Aˢ : S.Ty {i}
  Γˢ j} {A : Ty {i} {Γˢ} Γ j Aˢ} → _≡_ {i ⊔ suc j} {Ty {i} {Γˢ} Γ j Aˢ}
  (El {i} {Γˢ} {Γ} {j} {S.c {i} {Γˢ} {j} Aˢ} (c {i} {Γˢ} {Γ} {j} {Aˢ}
  A)) A
Elc {i} {Γˢ} {Γ} {j} {Aˢ} {A} = ext λ Γᶠ → ext λ Γᴾ → ext λ Aᶠ → A Γᶠ Γᴾ & {!!}

cEl :
  {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {aˢ : S.Tm {i}
  Γˢ {suc j} (S.U {i} {Γˢ} j)} {a : Tm {i} {Γˢ} Γ {suc j} {S.U {i} {Γˢ}
  j} (U {i} {Γˢ} {Γ} j) aˢ} → _≡_ {i ⊔ suc j} {Tm {i} {Γˢ} Γ {suc j}
  {S.U {i} {Γˢ} j} (U {i} {Γˢ} {Γ} j) aˢ} (c {i} {Γˢ} {Γ} {j} {S.El {i}
  {Γˢ} {j} aˢ} (El {i} {Γˢ} {Γ} {j} {aˢ} a)) a
cEl {i} {Γˢ} {Γ} {j} {aˢ} {a} = ext λ Γᶠ → ext λ Γᴾ → ext λ Aᶠ → a Γᶠ Γᴾ & {!!}
