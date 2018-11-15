{-# OPTIONS --rewriting #-}

module Syntax where

open import StrictLib hiding (id; _∘_)

infixl 5 _▶_
infixl 7 _[_]T
infixl 5 _,s_
infix  6 _∘_
infixl 8 _[_]t
infixl 5 _^_

postulate
  Con   : ∀ i → Set (suc i)
  Ty    : ∀ {j}(Γ : Con j) i → Set (suc i ⊔ j)
  ∙     : Con zero
  _▶_   : ∀ {i}(Γ : Con i){j}(A : Ty Γ j) → Con (i ⊔ j)
  Sub   : ∀ {i}(Γ : Con i){j}(Δ : Con j) → Set (i ⊔ j)
  Tm    : ∀ {i}(Γ : Con i){j}(A : Ty Γ j) → Set (i ⊔ j)
  _[_]T : ∀ {i}{Δ : Con i}{j}(A : Ty Δ j){k}{Γ : Con k}(σ : Sub Γ Δ) → Ty Γ j


  id : ∀{i}{Γ : Con i} → Sub Γ Γ

  _∘_ :
    ∀{i}{Θ : Con i}{j}{Δ : Con j}(σ : Sub Θ Δ){k}{Γ : Con k}(δ : Sub Γ Θ)
    → Sub Γ Δ

  ε : ∀{i}{Γ : Con i} → Sub Γ ∙

  ∙η : ∀{i}{Γ : Con i}{σ : Sub Γ ∙} → σ ≡ ε

  _,s_ : ∀{i}{Γ : Con i}{j}{Δ : Con j}(σ : Sub Γ Δ){k}{A : Ty Δ k}(t : Tm Γ (A [ σ ]T)) → Sub Γ (Δ ▶ A)


  π₁ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{A : Ty Δ k}(σ : Sub Γ (Δ ▶ A)) → Sub Γ Δ


  π₂ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{A : Ty Δ k}(σ : Sub Γ (Δ ▶ A)) → Tm Γ (A [ π₁ σ ]T)


  _[_]t : ∀{i}{Δ : Con i}{j}{A : Ty Δ j}(t : Tm Δ A){k}{Γ : Con k}(σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)


  [id]T : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → A [ id ]T ≡ A


  [∘]T : ∀{i}{Θ : Con i}{j}{Δ : Con j}{σ : Sub Θ Δ}{k}{Γ : Con k}{δ : Sub Γ Θ}
          {l}{A : Ty Δ l} → A [ σ ]T [ δ ]T ≡ A [ σ ∘ δ ]T


  idl : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} → id ∘ σ ≡ σ


  idr : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} → σ ∘ id ≡ σ


  ass : ∀{i}{Θ : Con i}{j}{Δ : Con j}{σ : Sub Θ Δ}{k}{Ξ : Con k}{δ : Sub Ξ Θ}{l}{Γ : Con l}{ν : Sub Γ Ξ} → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)


  ▶β₁ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ}{k}{A : Ty Δ k}{t : Tm Γ (A [ σ ]T)} → π₁ {A = A}(σ ,s t) ≡ σ

  ▶β₂ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ}{k}{A : Ty Δ k}{t : Tm Γ (A [ σ ]T)} → coe ((λ x → Tm Γ (A [ x ]T)) & ▶β₁) (π₂ (σ ,s t)) ≡ t

  ▶η : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{A : Ty Δ k}{σ : Sub Γ (Δ ▶ A)} → (π₁ σ ,s π₂ σ) ≡ σ

  ,∘ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ}{k}{A : Ty Δ k}{t : Tm Γ (A [ σ ]T)}{l}{θ : Con l}{δ : Sub θ Γ} → (_,s_ σ {A = A} t) ∘ δ ≡ ((σ ∘ δ) ,s coe (Tm θ & [∘]T) (t [ δ ]t))


-- abbreviations

wk : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → Sub (Γ ▶ A) Γ
wk = π₁ id

vz : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → Tm (Γ ▶ A) (A [ wk ]T)
vz = π₂ id

_^_ : ∀{i}{Γ : Con i}{j}{Δ : Con j}(σ : Sub Γ Δ){k}(A : Ty Δ k) →
  Sub (Γ ▶ A [ σ ]T) (Δ ▶ A)
_^_ {i}{Γ}{j}{Δ} σ {k} A = σ ∘ wk ,s tr (Tm (Γ ▶ A [ σ ]T)) [∘]T
                                        (vz {i}{Γ}{_}{A [ σ ]T})

postulate

  Π : ∀{i}{Γ : Con i}{j}(A : Ty Γ j){k}(B : Ty (Γ ▶ A) k) → Ty Γ (j ⊔ k)

  Π[] : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▶ A) k}{l}{Θ : Con l}{σ : Sub Θ Γ} → Π A B [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ^ A ]T)

  lam : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▶ A) k}(t : Tm (Γ ▶ A) B) → Tm Γ (Π A B)

  app : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▶ A) k}(t : Tm Γ (Π A B)) → Tm (Γ ▶ A) B

  app[] :
    ∀{i}{Γ : Con i}{l}{Δ : Con l}{σ : Sub Γ Δ}{j}{A : Ty Δ j}{k}{B : Ty (Δ ▶ A) k}{t : Tm Δ (Π A B)}
    → app t [ σ ^ A ]t ≡ app (tr (Tm Γ) Π[] (t [ σ ]t))

  Πβ : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▶ A) k}{t : Tm (Γ ▶ A) B} → app (lam t) ≡ t

  Πη : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▶ A) k}{t : Tm Γ (Π A B)} → lam (app t) ≡ t

  U : ∀{i}{Γ : Con i} j → Ty Γ (suc j)
  U[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} {k} → U k [ σ ]T ≡ U k

  El : ∀{i}{Γ : Con i}{j}(a : Tm Γ (U j)) → Ty Γ j

  El[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ}{k}(a : Tm Δ (U k))
         → El a [ σ ]T ≡ El (tr (Tm Γ) U[] (a [ σ ]t))

  c : ∀{i}{Γ : Con i}{j}(A : Ty Γ j) → Tm Γ (U j)

  Elc : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → El (c A) ≡ A

  cEl : ∀{i}{Γ : Con i}{j}{a : Tm Γ (U j)} → c (El a) ≡ a


-- Rewriting
--------------------------------------------------------------------------------

{-# REWRITE [id]T [∘]T idl idr ass ▶β₁ ▶η ,∘ Π[] Πβ Πη U[] El[] Elc cEl #-}

postulate
  [∘]Tr :
    {i : Level} {Θ : Con i} {j : Level} {Δ : Con j} {σ : Sub Θ Δ}
    {k : Level} {Γ : Con k} {δ : Sub Γ Θ} {l : Level} {A : Ty Δ l} →
    [∘]T {σ = σ}{δ = δ}{A = A} ≡ refl

  U[]r : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} {k} → U[] {i}{Γ}{j}{Δ}{σ}{k} ≡ refl

  El[]r : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ}{k}(a : Tm Δ (U k))
         → El[] {i}{Γ}{j}{Δ}{σ}{k} a ≡ refl

  Π[]r :
    ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▶ A) k}{l}{θ : Con l}{σ : Sub θ Γ}
    → Π[]{i}{Γ}{j}{A}{k}{B}{l}{θ}{σ} ≡ refl

{-# REWRITE [∘]Tr U[]r El[]r Π[]r #-}

postulate
  app[]' :
    {i : Level} {Γ : Con i} {l : Level} {Δ : Con l} {σ : Sub Γ Δ}
    {j : Level} {A : Ty Δ j} {k : Level} {B : Ty (Δ ▶ A) k}
    {t : Tm Δ (Π A B)} →
    app t [ σ ∘ π₁ (id {_}{Γ ▶ A [ σ ]T}) ,s π₂ id ]t ≡ app (t [ σ ]t)

  ▶β₂' : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ}{k}{A : Ty Δ k}{t : Tm Γ (A [ σ ]T)} →
         (π₂ {i}{Γ}{j}{Δ}{k}{A}(σ ,s t)) ≡ t
{-# REWRITE app[]' ▶β₂' #-}

postulate
  π₁∘   : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{Σ : Con k}{l}
           {A : Ty Σ l}{σ : Sub Δ (Σ ▶ A)}{δ : Sub Γ Δ} → π₁ σ ∘ δ ≡ π₁ (σ ∘ δ)
{-# REWRITE π₁∘ #-}

postulate
  π₂∘   : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{Σ : Con k}{l}
           {A : Ty Σ l}{σ : Sub Δ (Σ ▶ A)}{δ : Sub Γ Δ} → π₂ σ [ δ ]t ≡ π₂ (σ ∘ δ)
{-# REWRITE π₂∘ #-}

postulate
  π₂∘vz : ∀ {i}{Γˢ : Con i}
           {j}{Δˢ : Con j}
           {k}{Aˢ : Ty Δˢ k}
              {σˢ : Sub Γˢ Δˢ}
              {ν  : Sub ∙ (Γˢ ▶ Aˢ [ σˢ ]T)}
         → π₂ id [ ν ]t ≡ π₂ ν
{-# REWRITE π₂∘vz #-}

postulate
  [id]t : ∀ {i Γ}{j A}{t : Tm {i} Γ {j} A} → t [ id ]t ≡ t
{-# REWRITE [id]t #-}

postulate
  [∘]t  : ∀ {i Γ j Δ k Σ l A}{σ : Sub {i} Γ {j} Δ} {δ : Sub Δ {k} Σ}(t : Tm Σ {l} A)
          → t [ δ ]t [ σ ]t ≡ t [ δ ∘ σ ]t
{-# REWRITE [∘]t #-}

postulate
  c[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ}{k}{A : Ty Δ k}
        → c A [ σ ]t ≡ c (A [ σ ]T)
{-# REWRITE c[] #-}

postulate
  app[]r :
    ∀{i}{Γ : Con i}{l}{Δ : Con l}{σ : Sub Γ Δ}{j}{A : Ty Δ j}{k}{B : Ty (Δ ▶ A) k}(t : Tm Δ (Π A B))
    → app[] {i}{Γ}{l}{Δ}{σ}{j}{A}{k}{B} {t} ≡ refl
{-# REWRITE app[]r #-}

postulate
  lam[] :
    ∀{i}{Γ : Con i}{l}{Δ : Con l}{σ : Sub Γ Δ}{j}{A : Ty Δ j}{k}{B : Ty (Δ ▶ A) k}
        {t : Tm (Δ ▶ A) B}
    → lam t [ σ ]t ≡ lam (t [ σ ^ A ]t)
{-# REWRITE lam[] #-}
