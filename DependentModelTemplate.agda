{-# OPTIONS --rewriting #-}

module DependentModelTemplate where

open import StrictLib hiding (id; _∘_)
import Syntax as S

infixl 5 _▶_
infixl 7 _[_]T
infixl 5 _,s_
infix  6 _∘_
infixl 8 _[_]t
infixl 5 _^_

postulate
  Con : ∀ i → S.Con i → Set (suc i)
  Ty  : ∀ {j}{Γˢ : S.Con j}(Γ : Con j Γˢ) i → S.Ty Γˢ i → Set (suc i ⊔ j)
  ∙   : Con zero S.∙
  _▶_   : ∀ {i}{Γˢ : S.Con i}(Γ : Con i Γˢ)
            {j}{Aˢ : S.Ty Γˢ j}(A : Ty Γ j Aˢ)
            → Con (i ⊔ j) (Γˢ S.▶ Aˢ)

  Sub   : ∀ {i}{Γˢ : S.Con i}(Γ : Con i Γˢ)
            {j}{Δˢ : S.Con j}(Δ : Con j Δˢ)
            → S.Sub Γˢ Δˢ → Set (i ⊔ j)

  Tm  : ∀ {i}{Γˢ : S.Con i}(Γ : Con i Γˢ)
            {j}{Aˢ : S.Ty Γˢ j}(A : Ty Γ j Aˢ) → S.Tm Γˢ Aˢ → Set (i ⊔ j)

  _[_]T :
    ∀ {i}{Δˢ : S.Con i}   {Δ : Con i Δˢ}
      {j}{Aˢ : S.Ty Δˢ j} (A : Ty Δ j Aˢ)
      {k}{Γˢ : S.Con k}   {Γ : Con k Γˢ}
      {σˢ : S.Sub Γˢ Δˢ}  (σ : Sub Γ Δ σˢ)
      → Ty Γ j (Aˢ S.[ σˢ ]T)

  id : ∀{i}{Γˢ : S.Con i}{Γ : Con i Γˢ} → Sub Γ Γ S.id

  _∘_ :
    ∀{i}{θˢ : S.Con i}     {θ : Con _ θˢ}
     {j}{Δˢ : S.Con j}     {Δ : Con _ Δˢ}
        {σˢ : S.Sub θˢ Δˢ} (σ : Sub θ Δ σˢ)
     {k}{Γˢ : S.Con k}     {Γ : Con _ Γˢ}
        {δˢ : S.Sub Γˢ θˢ} (δ : Sub Γ θ δˢ)
    → Sub Γ Δ (σˢ S.∘ δˢ)

  ε : ∀{i}{Γˢ : S.Con i}{Γ : Con i Γˢ}
      → Sub Γ ∙ S.ε

  _,s_ :
    ∀{i}{Γˢ : S.Con i}                {Γ : Con _ Γˢ}
     {j}{Δˢ : S.Con j}                {Δ : Con _ Δˢ}
        {σˢ : S.Sub Γˢ Δˢ}            (σ : Sub Γ Δ σˢ)
     {k}{Aˢ : S.Ty Δˢ k}              {A : Ty Δ _ Aˢ}
        {tˢ : S.Tm Γˢ (Aˢ S.[ σˢ ]T)} (t : Tm Γ (A [ σ ]T) tˢ)
     → Sub Γ (Δ ▶ A) (σˢ S.,s tˢ)

  π₁ :
    ∀{i}{Γˢ : S.Con i}                {Γ : Con _ Γˢ}
     {j}{Δˢ : S.Con j}                {Δ : Con _ Δˢ}
     {k}{Aˢ : S.Ty Δˢ k}              {A : Ty Δ _ Aˢ}
        {σˢ : S.Sub Γˢ (Δˢ S.▶ Aˢ)}   (σ : Sub Γ (Δ ▶ A) σˢ)
    → Sub Γ Δ (S.π₁ σˢ)

  π₂ :
    ∀{i}{Γˢ : S.Con i}                {Γ : Con _ Γˢ}
     {j}{Δˢ : S.Con j}                {Δ : Con _ Δˢ}
     {k}{Aˢ : S.Ty Δˢ k}              {A : Ty Δ _ Aˢ}
        {σˢ : S.Sub Γˢ (Δˢ S.▶ Aˢ)}   (σ : Sub Γ (Δ ▶ A) σˢ)
    → Tm Γ (A [ π₁ σ ]T) (S.π₂ σˢ)

  _[_]t :
    ∀{i}{Δˢ : S.Con i}     {Δ : Con _ Δˢ}
     {j}{Aˢ : S.Ty Δˢ j}   {A : Ty Δ _ Aˢ}
        {tˢ : S.Tm Δˢ Aˢ}  (t : Tm Δ A tˢ)
     {k}{Γˢ : S.Con k}     {Γ : Con _ Γˢ}
        {σˢ : S.Sub Γˢ Δˢ} (σ : Sub Γ Δ σˢ)
    → Tm Γ (A [ σ ]T) (tˢ S.[ σˢ ]t)

  •η :
     ∀  {i}{Γˢ : S.Con i}      {Γ : Con _ Γˢ}
           {σˢ : S.Sub Γˢ S.∙} {σ : Sub Γ ∙ σˢ}
     → tr (Sub Γ ∙) S.∙η σ ≡ ε

  [id]T :
    ∀{i}{Γˢ : S.Con i}   {Γ : Con _ Γˢ}
     {j}{Aˢ : S.Ty Γˢ j} {A : Ty Γ _ Aˢ}
    → A [ id ]T ≡ A

  [∘]T :
    ∀{i}{θˢ : S.Con i}     {θ : Con _ θˢ}
     {j}{Δˢ : S.Con j}     {Δ : Con _ Δˢ}
        {σˢ : S.Sub θˢ Δˢ} {σ : Sub θ Δ σˢ}
     {k}{Γˢ : S.Con k}     {Γ : Con _ Γˢ}
        {δˢ : S.Sub Γˢ θˢ} {δ : Sub Γ θ δˢ}
     {l}{Aˢ : S.Ty Δˢ l}   {A : Ty Δ _ Aˢ}
     → A [ σ ∘ δ ]T ≡ A [ σ ]T [ δ ]T

  idl :
    ∀{i}{Γˢ : S.Con i}     {Γ : Con _ Γˢ}
     {j}{Δˢ : S.Con j}     {Δ : Con _ Δˢ}
        {σˢ : S.Sub Γˢ Δˢ} {σ : Sub Γ Δ σˢ}
    → id ∘ σ ≡ σ

  idr :
    ∀{i}{Γˢ : S.Con i}     {Γ : Con _ Γˢ}
     {j}{Δˢ : S.Con j}     {Δ : Con _ Δˢ}
        {σˢ : S.Sub Γˢ Δˢ} {σ : Sub Γ Δ σˢ}
    → σ ∘ id ≡ σ

  ass :
    ∀{i}{θˢ : S.Con i}     {θ : Con _ θˢ}
     {j}{Δˢ : S.Con j}     {Δ : Con _ Δˢ}
        {σˢ : S.Sub θˢ Δˢ} {σ : Sub θ Δ σˢ}
     {k}{Ξˢ : S.Con k}     {Ξ : Con _ Ξˢ}
        {δˢ : S.Sub Ξˢ θˢ} {δ : Sub Ξ θ δˢ}
     {l}{Γˢ : S.Con l}     {Γ : Con _ Γˢ}
        {νˢ : S.Sub Γˢ Ξˢ} {ν : Sub Γ Ξ νˢ}
     → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)

  ▶β₁ :
    ∀{i}{Γˢ : S.Con i}                {Γ : Con _ Γˢ}
     {j}{Δˢ : S.Con j}                {Δ : Con _ Δˢ}
        {σˢ : S.Sub Γˢ Δˢ}            {σ : Sub Γ Δ σˢ}
     {k}{Aˢ : S.Ty Δˢ k}              {A : Ty Δ _ Aˢ}
        {tˢ : S.Tm Γˢ (Aˢ S.[ σˢ ]T)} {t : Tm Γ (A [ σ ]T) tˢ}
    → π₁ (σ ,s t) ≡ σ

  ▶β₂ :
    ∀{i}{Γˢ : S.Con i}                {Γ : Con _ Γˢ}
     {j}{Δˢ : S.Con j}                {Δ : Con _ Δˢ}
        {σˢ : S.Sub Γˢ Δˢ}            {σ : Sub Γ Δ σˢ}
     {k}{Aˢ : S.Ty Δˢ k}              {A : Ty Δ _ Aˢ}
        {tˢ : S.Tm Γˢ (Aˢ S.[ σˢ ]T)} {t : Tm Γ (A [ σ ]T) tˢ}
    → tr (λ x → Tm Γ (A [ x ]T) tˢ) ▶β₁ (π₂ (σ ,s t)) ≡ t

  ▶η :
    ∀{i}{Γˢ : S.Con i}                {Γ : Con _ Γˢ}
     {j}{Δˢ : S.Con j}                {Δ : Con _ Δˢ}
     {k}{Aˢ : S.Ty Δˢ k}              {A : Ty Δ _ Aˢ}
        {σˢ : S.Sub Γˢ (Δˢ S.▶ Aˢ)}   (σ : Sub Γ (Δ ▶ A) σˢ)
    → (π₁ σ ,s π₂ σ) ≡ σ

  ,∘ :
    ∀{i}{Γˢ : S.Con i}                {Γ : Con _ Γˢ}
     {j}{Δˢ : S.Con j}                {Δ : Con _ Δˢ}
        {σˢ : S.Sub Γˢ Δˢ}            {σ : Sub Γ Δ σˢ}
     {k}{Aˢ : S.Ty Δˢ k}              {A : Ty Δ _ Aˢ}
        {tˢ : S.Tm Γˢ (Aˢ S.[ σˢ ]T)} {t : Tm Γ (A [ σ ]T) tˢ}
     {l}{θˢ : S.Con l}                {θ : Con _ θˢ}
        {δˢ : S.Sub θˢ Γˢ}            {δ : Sub θ Γ δˢ}
    → (σ ,s t) ∘ δ ≡ (σ ∘ δ) ,s tr (λ x → Tm θ x (tˢ S.[ δˢ ]t)) ([∘]T ⁻¹) (t [ δ ]t)

wk :
  ∀{i}{Γˢ : S.Con i}                {Γ : Con _ Γˢ}
   {k}{Aˢ : S.Ty Γˢ k}              {A : Ty Γ _ Aˢ}
  → Sub (Γ ▶ A) Γ (S.wk {Γ = Γˢ})
wk = π₁ id

vz :
  ∀{i}{Γˢ : S.Con i}                {Γ : Con _ Γˢ}
   {k}{Aˢ : S.Ty Γˢ k}              {A : Ty Γ _ Aˢ}
  → Tm (Γ ▶ A) (A [ wk ]T) S.vz
vz = π₂ id

_^_ :
  ∀{i}{Γˢ : S.Con i}                {Γ : Con _ Γˢ}
   {j}{Δˢ : S.Con j}                {Δ : Con _ Δˢ}
      {σˢ : S.Sub Γˢ Δˢ}            (σ : Sub Γ Δ σˢ)
   {k}{Aˢ : S.Ty Δˢ k}              (A : Ty Δ k Aˢ)
  → Sub (Γ ▶ A [ σ ]T) (Δ ▶ A) (σˢ S.^ Aˢ)
_^_ {i} {Γˢ} {Γ} {j} {Δˢ} {Δ} {σˢ} σ {k} {Aˢ} A =
  σ ∘ wk ,s tr (λ x → Tm (Γ ▶ A [ σ ]T) x _) ([∘]T ⁻¹) (vz {A = A [ σ ]T})

postulate
  Π :
    ∀{i}{Γˢ : S.Con i}            {Γ : Con _ Γˢ}
     {j}{Aˢ : S.Ty Γˢ j}          (A : Ty Γ _ Aˢ)
     {k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k} (B : Ty (Γ ▶ A) _ Bˢ)
     → Ty Γ (j ⊔ k) (S.Π Aˢ Bˢ)

  Π[] :
    ∀{i}{Γˢ : S.Con i}           {Γ : Con _ Γˢ}
     {j}{Aˢ : S.Ty Γˢ j}         {A : Ty Γ _ Aˢ}
     {k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k}{B : Ty (Γ ▶ A) _ Bˢ}
     {l}{θˢ : S.Con l}           {θ : Con _ θˢ}
        {σˢ : S.Sub θˢ Γˢ}       {σ : Sub θ Γ σˢ}
    → Π A B [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ^ A ]T)

  lam :
    ∀{i}{Γˢ : S.Con i}            {Γ : Con _ Γˢ}
     {j}{Aˢ : S.Ty Γˢ j}          {A : Ty Γ _ Aˢ}
     {k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k} {B : Ty (Γ ▶ A) _ Bˢ}
        {tˢ : S.Tm (Γˢ S.▶ Aˢ) Bˢ}(t : Tm (Γ ▶ A) B tˢ)
    → Tm Γ (Π A B) (S.lam tˢ)

  app :
    ∀{i}{Γˢ : S.Con i}            {Γ : Con _ Γˢ}
     {j}{Aˢ : S.Ty Γˢ j}          {A : Ty Γ _ Aˢ}
     {k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k} {B : Ty (Γ ▶ A) _ Bˢ}
        {tˢ : S.Tm Γˢ (S.Π Aˢ Bˢ)}(t : Tm Γ (Π A B) tˢ)
    → Tm (Γ ▶ A) B (S.app tˢ)

  app[] :
    ∀{i}{Γˢ : S.Con i}            {Γ : Con _ Γˢ}
     {l}{Δˢ : S.Con l}            {Δ : Con _ Δˢ}
        {σˢ : S.Sub Γˢ Δˢ}        {σ : Sub Γ Δ σˢ}
     {j}{Aˢ : S.Ty Δˢ j}          {A : Ty Δ _ Aˢ}
     {k}{Bˢ : S.Ty (Δˢ S.▶ Aˢ) k} {B : Ty (Δ ▶ A) _ Bˢ}
        {tˢ : S.Tm Δˢ (S.Π Aˢ Bˢ)}(t : Tm Δ (Π A B) tˢ)
    → (app t) [ σ ^ A ]t ≡ app (tr (λ x → Tm Γ x (tˢ S.[ σˢ ]t)) Π[] (t [ σ ]t))

  Πβ :
    ∀{i}{Γˢ : S.Con i}            {Γ : Con _ Γˢ}
     {j}{Aˢ : S.Ty Γˢ j}          {A : Ty Γ _ Aˢ}
     {k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k} {B : Ty (Γ ▶ A) _ Bˢ}
        {tˢ : S.Tm (Γˢ S.▶ Aˢ) Bˢ}{t : Tm (Γ ▶ A) B tˢ}
    → app (lam t) ≡ t

  Πη :
    ∀{i}{Γˢ : S.Con i}            {Γ : Con _ Γˢ}
     {j}{Aˢ : S.Ty Γˢ j}          {A : Ty Γ _ Aˢ}
     {k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k} {B : Ty (Γ ▶ A) _ Bˢ}
        {tˢ : S.Tm Γˢ (S.Π Aˢ Bˢ)}{t : Tm Γ (Π A B) tˢ}
    → lam (app t) ≡ t

  U :
    ∀{i}{Γˢ : S.Con i}{Γ : Con _ Γˢ} j → Ty Γ (suc j) (S.U j)

  U[] :
    ∀{i}{Γˢ : S.Con i}     {Γ : Con _ Γˢ}
     {j}{Δˢ : S.Con j}     {Δ : Con _ Δˢ}
        {σˢ : S.Sub Γˢ Δˢ} {σ : Sub Γ Δ σˢ}
     {k} → U k [ σ ]T ≡ U k

  El :
    ∀{i}{Γˢ : S.Con i}         {Γ : Con _ Γˢ}
     {j}{aˢ : S.Tm Γˢ (S.U j)} (a : Tm Γ (U j) aˢ)
     → Ty Γ j (S.El aˢ)

  El[] :
    ∀{i}{Γˢ : S.Con i}        {Γ : Con _ Γˢ}
     {j}{Δˢ : S.Con j}        {Δ : Con _ Δˢ}
        {σˢ : S.Sub Γˢ Δˢ}    {σ : Sub Γ Δ σˢ}
     {k}{aˢ : S.Tm Δˢ (S.U k)}{a : Tm Δ (U k) aˢ}
    → El a [ σ ]T ≡ El (tr (λ x → Tm Γ x (aˢ S.[ σˢ ]t)) U[] (a [ σ ]t))

  c :
    ∀{i}{Γˢ : S.Con i}  {Γ : Con _ Γˢ}
     {j}{Aˢ : S.Ty Γˢ j}(A : Ty Γ _ Aˢ)
    → Tm Γ (U j) (S.c Aˢ)

  Elc :
    ∀{i}{Γˢ : S.Con i}   {Γ : Con _ Γˢ}
     {j}{Aˢ : S.Ty Γˢ j} {A : Ty Γ _ Aˢ}
     → El (c A) ≡ A

  cEl :
    ∀{i}{Γˢ : S.Con i} {Γ : Con _ Γˢ}
     {j}{aˢ : S.Tm Γˢ (S.U j)}{a : Tm Γ (U j) aˢ}
     → c (El a) ≡ a
