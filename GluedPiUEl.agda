{-# OPTIONS --rewriting #-}

module GluedPiUEl where

open import StrictLib hiding (id; _∘_)
open import GluedCwF
import Syntax as S

Π :
  ∀{i}{Γˢ : S.Con i}            {Γ : Con _ Γˢ}
   {j}{Aˢ : S.Ty Γˢ j}          (A : Ty Γ _ Aˢ)
   {k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k} (B : Ty (Γ ▶ A) _ Bˢ)
   → Ty Γ (j ⊔ k) (S.Π Aˢ Bˢ)
Π = {!!}

--   Π[] :
--     ∀{i}{Γˢ : S.Con i}           {Γ : Con _ Γˢ}
--      {j}{Aˢ : S.Ty Γˢ j}         {A : Ty Γ _ Aˢ}
--      {k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k}{B : Ty (Γ ▶ A) _ Bˢ}
--      {l}{θˢ : S.Con l}           {θ : Con _ θˢ}
--         {σˢ : S.Sub θˢ Γˢ}       {σ : Sub θ Γ σˢ}
--     → Π A B [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ^ A ]T)

--   lam :
--      {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Aˢ : S.Ty {i}
--      Γˢ j} {A : Ty {i} {Γˢ} Γ j Aˢ} {k : Level} {Bˢ : S.Ty {i ⊔ j} (S._▶_
--      {i} Γˢ {j} Aˢ) k} {B : Ty {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} (_▶_ {i} {Γˢ}
--      Γ {j} {Aˢ} A) k Bˢ} {tˢ : S.Tm {i ⊔ j} (S._▶_ {i} Γˢ {j} Aˢ) {k} Bˢ} →
--      Tm {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} (_▶_ {i} {Γˢ} Γ {j} {Aˢ} A) {k} {Bˢ}
--      B tˢ → Tm {i} {Γˢ} Γ {j ⊔ k} {S.Π {i} {Γˢ} {j} Aˢ {k} Bˢ} (Π {i} {Γˢ}
--      {Γ} {j} {Aˢ} A {k} {Bˢ} B) (S.lam {i} {Γˢ} {j} {Aˢ} {k} {Bˢ} tˢ)

--   app :
--      {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Aˢ : S.Ty {i}
--      Γˢ j} {A : Ty {i} {Γˢ} Γ j Aˢ} {k : Level} {Bˢ : S.Ty {i ⊔ j} (S._▶_
--      {i} Γˢ {j} Aˢ) k} {B : Ty {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} (_▶_ {i} {Γˢ}
--      Γ {j} {Aˢ} A) k Bˢ} {tˢ : S.Tm {i} Γˢ {j ⊔ k} (S.Π {i} {Γˢ} {j} Aˢ {k}
--      Bˢ)} → Tm {i} {Γˢ} Γ {j ⊔ k} {S.Π {i} {Γˢ} {j} Aˢ {k} Bˢ} (Π {i} {Γˢ}
--      {Γ} {j} {Aˢ} A {k} {Bˢ} B) tˢ → Tm {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} (_▶_
--      {i} {Γˢ} Γ {j} {Aˢ} A) {k} {Bˢ} B (S.app {i} {Γˢ} {j} {Aˢ} {k} {Bˢ}
--      tˢ)

--   app[] :
--     ∀{i}{Γˢ : S.Con i}            {Γ : Con _ Γˢ}
--      {l}{Δˢ : S.Con l}            {Δ : Con _ Δˢ}
--         {σˢ : S.Sub Γˢ Δˢ}        {σ : Sub Γ Δ σˢ}
--      {j}{Aˢ : S.Ty Δˢ j}          {A : Ty Δ _ Aˢ}
--      {k}{Bˢ : S.Ty (Δˢ S.▶ Aˢ) k} {B : Ty (Δ ▶ A) _ Bˢ}
--         {tˢ : S.Tm Δˢ (S.Π Aˢ Bˢ)}(t : Tm Δ (Π A B) tˢ)
--     → (app t) [ σ ^ A ]t ≡ app (tr (λ x → Tm Γ x (tˢ S.[ σˢ ]t)) Π[] (t [ σ ]t))

--   Πβ :
--     ∀{i}{Γˢ : S.Con i}            {Γ : Con _ Γˢ}
--      {j}{Aˢ : S.Ty Γˢ j}          {A : Ty Γ _ Aˢ}
--      {k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k} {B : Ty (Γ ▶ A) _ Bˢ}
--         {tˢ : S.Tm (Γˢ S.▶ Aˢ) Bˢ}{t : Tm (Γ ▶ A) B tˢ}
--     → app (lam t) ≡ t

--   Πη :
--     ∀{i}{Γˢ : S.Con i}            {Γ : Con _ Γˢ}
--      {j}{Aˢ : S.Ty Γˢ j}          {A : Ty Γ _ Aˢ}
--      {k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k} {B : Ty (Γ ▶ A) _ Bˢ}
--         {tˢ : S.Tm Γˢ (S.Π Aˢ Bˢ)}{t : Tm Γ (Π A B) tˢ}
--     → lam (app t) ≡ t

-- --------------------------------------------------------------------------------

--   U :
--     ∀{i}{Γˢ : S.Con i}{Γ : Con _ Γˢ} j → Ty Γ (suc j) (S.U j)

--   U[] :
--      {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Δˢ : S.Con j}
--      {Δ : Con j Δˢ} {σˢ : S.Sub {i} Γˢ {j} Δˢ} {σ : Sub {i} {Γˢ} Γ {j} {Δˢ}
--      Δ σˢ} {k : Level} → _≡_ {i ⊔ suc (suc k)} {Ty {i} {Γˢ} Γ (suc k) (S.U
--      {i} {Γˢ} k)} (_[_]T {j} {Δˢ} {Δ} {suc k} {S.U {j} {Δˢ} k} (U {j} {Δˢ}
--      {Δ} k) {i} {Γˢ} {Γ} {σˢ} σ) (U {i} {Γˢ} {Γ} k)

--   El :
--     ∀{i}{Γˢ : S.Con i}         {Γ : Con _ Γˢ}
--      {j}{aˢ : S.Tm Γˢ (S.U j)} (a : Tm Γ (U j) aˢ)
--      → Ty Γ j (S.El aˢ)

--   El[] :
--     {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Δˢ : S.Con j}
--     {Δ : Con j Δˢ} {σˢ : S.Sub {i} Γˢ {j} Δˢ} {σ : Sub {i} {Γˢ} Γ {j} {Δˢ}
--     Δ σˢ} {k : Level} {aˢ : S.Tm {j} Δˢ {suc k} (S.U {j} {Δˢ} k)} {a : Tm
--     {j} {Δˢ} Δ {suc k} {S.U {j} {Δˢ} k} (U {j} {Δˢ} {Δ} k) aˢ} → _≡_ {i ⊔
--     suc k} {Ty {i} {Γˢ} Γ k (S.El {i} {Γˢ} {k} (S._[_]t {j} {Δˢ} {suc k}
--     {S.U {j} {Δˢ} k} aˢ {i} {Γˢ} σˢ))} (_[_]T {j} {Δˢ} {Δ} {k} {S.El {j}
--     {Δˢ} {k} aˢ} (El {j} {Δˢ} {Δ} {k} {aˢ} a) {i} {Γˢ} {Γ} {σˢ} σ) (El {i}
--     {Γˢ} {Γ} {k} {S._[_]t {j} {Δˢ} {suc k} {S.U {j} {Δˢ} k} aˢ {i} {Γˢ}
--     σˢ} (tr {i ⊔ suc (suc k)} {i ⊔ suc k} {Ty {i} {Γˢ} Γ (suc k) (S.U {i}
--     {Γˢ} k)} (λ x → Tm {i} {Γˢ} Γ {suc k} {S.U {i} {Γˢ} k} x (S._[_]t {j}
--     {Δˢ} {suc k} {S.U {j} {Δˢ} k} aˢ {i} {Γˢ} σˢ)) {_[_]T {j} {Δˢ} {Δ}
--     {suc k} {S.U {j} {Δˢ} k} (U {j} {Δˢ} {Δ} k) {i} {Γˢ} {Γ} {σˢ} σ} {U
--     {i} {Γˢ} {Γ} k} (U[] {i} {Γˢ} {Γ} {j} {Δˢ} {Δ} {σˢ} {σ} {k}) (_[_]t
--     {j} {Δˢ} {Δ} {suc k} {S.U {j} {Δˢ} k} {U {j} {Δˢ} {Δ} k} {aˢ} a {i}
--     {Γˢ} {Γ} {σˢ} σ)))

--   c :
--     ∀{i}{Γˢ : S.Con i}  {Γ : Con _ Γˢ}
--      {j}{Aˢ : S.Ty Γˢ j}(A : Ty Γ _ Aˢ)
--     → Tm Γ (U j) (S.c Aˢ)

--   Elc :
--     {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Aˢ : S.Ty {i}
--     Γˢ j} {A : Ty {i} {Γˢ} Γ j Aˢ} → _≡_ {i ⊔ suc j} {Ty {i} {Γˢ} Γ j Aˢ}
--     (El {i} {Γˢ} {Γ} {j} {S.c {i} {Γˢ} {j} Aˢ} (c {i} {Γˢ} {Γ} {j} {Aˢ}
--     A)) A

--   cEl :
--     {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {aˢ : S.Tm {i}
--     Γˢ {suc j} (S.U {i} {Γˢ} j)} {a : Tm {i} {Γˢ} Γ {suc j} {S.U {i} {Γˢ}
--     j} (U {i} {Γˢ} {Γ} j) aˢ} → _≡_ {i ⊔ suc j} {Tm {i} {Γˢ} Γ {suc j}
--     {S.U {i} {Γˢ} j} (U {i} {Γˢ} {Γ} j) aˢ} (c {i} {Γˢ} {Γ} {j} {S.El {i}
--     {Γˢ} {j} aˢ} (El {i} {Γˢ} {Γ} {j} {aˢ} a)) a
