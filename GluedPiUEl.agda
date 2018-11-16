{-# OPTIONS --rewriting #-}

module GluedPiUEl where

open import StrictLib hiding (id; _∘_)
open import GluedCwF
import Syntax as S
import WeakMorphism as F

Π :
  ∀{i}{Γˢ : S.Con i}            {Γ : Con _ Γˢ}
   {j}{Aˢ : S.Ty Γˢ j}          (A : Ty Γ _ Aˢ)
   {k}{Bˢ : S.Ty (Γˢ S.▶ Aˢ) k} (B : Ty (Γ ▶ A) _ Bˢ)
   → Ty Γ (j ⊔ k) (S.Π Aˢ Bˢ)
Π {i} {Γˢ} {Γ} {j} {Aˢ} A {k} {Bˢ} B Γᶠ Γᴾ fᶠ =
    (Aᶠ : F.Ty Aˢ Γᶠ)(Aᴾ : A Γᶠ Γᴾ Aᶠ)
  → B (F.▶← (Γᶠ , Aᶠ)) (Γᴾ , Aᴾ) (F.Π→ _ Aˢ Bˢ fᶠ Aᶠ)

postulate
  posting : ∀ {i j}{B : Set j}(A : Set i) → (A → B) → B

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
  ext λ Γᶠ → ext λ Γᴾ → ext λ fᶠ → posting (F.Ty Aˢ (F.Sub σˢ Γᶠ)) λ Aᶠ → cheat -- OK by Π→ naturality


lam :
   {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Aˢ : S.Ty {i}
   Γˢ j} {A : Ty {i} {Γˢ} Γ j Aˢ} {k : Level} {Bˢ : S.Ty {i ⊔ j} (S._▶_
   {i} Γˢ {j} Aˢ) k} {B : Ty {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} (_▶_ {i} {Γˢ}
   Γ {j} {Aˢ} A) k Bˢ} {tˢ : S.Tm {i ⊔ j} (S._▶_ {i} Γˢ {j} Aˢ) {k} Bˢ} →
   Tm {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} (_▶_ {i} {Γˢ} Γ {j} {Aˢ} A) {k} {Bˢ}
   B tˢ → Tm {i} {Γˢ} Γ {j ⊔ k} {S.Π {i} {Γˢ} {j} Aˢ {k} Bˢ} (Π {i} {Γˢ}
   {Γ} {j} {Aˢ} A {k} {Bˢ} B) (S.lam {i} {Γˢ} {j} {Aˢ} {k} {Bˢ} tˢ)
lam {i} {Γˢ} {Γ} {j} {Aˢ} {A} {k} {Bˢ} {B} {tˢ} t =
  {!!}


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
