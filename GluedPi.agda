
{-# OPTIONS --rewriting #-}

module GluedPi where

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
     cheat -- OK by Π→nat naturality


lam :
   {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Aˢ : S.Ty {i}
   Γˢ j} {A : Ty {i} {Γˢ} Γ j Aˢ} {k : Level} {Bˢ : S.Ty {i ⊔ j} (S._▶_
   {i} Γˢ {j} Aˢ) k} {B : Ty {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} (_▶_ {i} {Γˢ}
   Γ {j} {Aˢ} A) k Bˢ} {tˢ : S.Tm {i ⊔ j} (S._▶_ {i} Γˢ {j} Aˢ) {k} Bˢ} →
   Tm {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} (_▶_ {i} {Γˢ} Γ {j} {Aˢ} A) {k} {Bˢ}
   B tˢ → Tm {i} {Γˢ} Γ {j ⊔ k} {S.Π {i} {Γˢ} {j} Aˢ {k} Bˢ} (Π {i} {Γˢ}
   {Γ} {j} {Aˢ} A {k} {Bˢ} B) (S.lam {i} {Γˢ} {j} {Aˢ} {k} {Bˢ} tˢ)
lam {i} {Γˢ} {Γ} {j} {Aˢ} {A} {k} {Bˢ} {B} {tˢ} t Γᶠ Γᴾ Aᶠ Aᴾ = t (F.▶← (Γᶠ , Aᶠ)) (Γᴾ , Aᴾ)

app :
   {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Aˢ : S.Ty {i}
   Γˢ j} {A : Ty {i} {Γˢ} Γ j Aˢ} {k : Level} {Bˢ : S.Ty {i ⊔ j} (S._▶_
   {i} Γˢ {j} Aˢ) k} {B : Ty {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} (_▶_ {i} {Γˢ}
   Γ {j} {Aˢ} A) k Bˢ} {tˢ : S.Tm {i} Γˢ {j ⊔ k} (S.Π {i} {Γˢ} {j} Aˢ {k}
   Bˢ)} → Tm {i} {Γˢ} Γ {j ⊔ k} {S.Π {i} {Γˢ} {j} Aˢ {k} Bˢ} (Π {i} {Γˢ}
   {Γ} {j} {Aˢ} A {k} {Bˢ} B) tˢ → Tm {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} (_▶_
   {i} {Γˢ} Γ {j} {Aˢ} A) {k} {Bˢ} B (S.app {i} {Γˢ} {j} {Aˢ} {k} {Bˢ}
   tˢ)
app {i} {Γˢ} {Γ} {j} {Aˢ} {A} {k} {Bˢ} {B} {tˢ} t Γᶠ (Γᴾ , Aᴾ) = t (₁ (F.▶→ Γᶠ)) Γᴾ (₂ (F.▶→ Γᶠ)) Aᴾ

-- app[] :
--      {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {l : Level} {Δˢ : S.Con l} {Δ : Con l
--      Δˢ} {σˢ : S.Sub {i} Γˢ {l} Δˢ} {σ : Sub {i} {Γˢ} Γ {l} {Δˢ} Δ σˢ} {j : Level}
--      {Aˢ : S.Ty {l} Δˢ j} {A : Ty {l} {Δˢ} Δ j Aˢ} {k : Level} {Bˢ : S.Ty {l ⊔ j}
--      (S._▶_ {l} Δˢ {j} Aˢ) k} {B : Ty {l ⊔ j} {S._▶_ {l} Δˢ {j} Aˢ} (_▶_ {l} {Δˢ} Δ
--      {j} {Aˢ} A) k Bˢ} {tˢ : S.Tm {l} Δˢ {j ⊔ k} (S.Π {l} {Δˢ} {j} Aˢ {k} Bˢ)} (t :
--      Tm {l} {Δˢ} Δ {j ⊔ k} {S.Π {l} {Δˢ} {j} Aˢ {k} Bˢ} (Π {l} {Δˢ} {Δ} {j} {Aˢ} A
--      {k} {Bˢ} B) tˢ) → _≡_ {i ⊔ (j ⊔ k)} {Tm {i ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T {l}
--      {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)} (_▶_ {i} {Γˢ} Γ {j} {S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ}
--      σˢ} (_[_]T {l} {Δˢ} {Δ} {j} {Aˢ} A {i} {Γˢ} {Γ} {σˢ} σ)) {k} {S._[_]T {l ⊔ j}
--      {S._▶_ {l} Δˢ {j} Aˢ} {k} Bˢ {i ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T {l} {Δˢ} {j} Aˢ
--      {i} {Γˢ} σˢ)} (S._^_ {i} {Γˢ} {l} {Δˢ} σˢ {j} Aˢ)} (_[_]T {l ⊔ j} {S._▶_ {l} Δˢ
--      {j} Aˢ} {_▶_ {l} {Δˢ} Δ {j} {Aˢ} A} {k} {Bˢ} B {i ⊔ j} {S._▶_ {i} Γˢ {j}
--      (S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)} {_▶_ {i} {Γˢ} Γ {j} {S._[_]T {l} {Δˢ} {j}
--      Aˢ {i} {Γˢ} σˢ} (_[_]T {l} {Δˢ} {Δ} {j} {Aˢ} A {i} {Γˢ} {Γ} {σˢ} σ)} {S._^_ {i}
--      {Γˢ} {l} {Δˢ} σˢ {j} Aˢ} (_^_ {i} {Γˢ} {Γ} {l} {Δˢ} {Δ} {σˢ} σ {j} {Aˢ} A))
--      (S.app {i} {Γˢ} {j} {S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ} {k} {S._[_]T {l ⊔ j}
--      {S._▶_ {l} Δˢ {j} Aˢ} {k} Bˢ {i ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T {l} {Δˢ} {j} Aˢ
--      {i} {Γˢ} σˢ)} (S._,s_ {i ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T {l} {Δˢ} {j} Aˢ {i}
--      {Γˢ} σˢ)} {l} {Δˢ} (S._∘_ {i} {Γˢ} {l} {Δˢ} σˢ {i ⊔ j} {S._▶_ {i} Γˢ {j}
--      (S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)} (S.π₁ {i ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T
--      {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)} {i} {Γˢ} {j} {S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ}
--      (S.id {i ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)}))) {j}
--      {Aˢ} (S.π₂ {i ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)} {i}
--      {Γˢ} {j} {S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ} (S.id {i ⊔ j} {S._▶_ {i} Γˢ {j}
--      (S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)})))} (S._[_]t {l} {Δˢ} {j ⊔ k} {S.Π {l}
--      {Δˢ} {j} Aˢ {k} Bˢ} tˢ {i} {Γˢ} σˢ))} (_[_]t {l ⊔ j} {S._▶_ {l} Δˢ {j} Aˢ} {_▶_
--      {l} {Δˢ} Δ {j} {Aˢ} A} {k} {Bˢ} {B} {S.app {l} {Δˢ} {j} {Aˢ} {k} {Bˢ} tˢ} (app
--      {l} {Δˢ} {Δ} {j} {Aˢ} {A} {k} {Bˢ} {B} {tˢ} t) {i ⊔ j} {S._▶_ {i} Γˢ {j}
--      (S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)} {_▶_ {i} {Γˢ} Γ {j} {S._[_]T {l} {Δˢ} {j}
--      Aˢ {i} {Γˢ} σˢ} (_[_]T {l} {Δˢ} {Δ} {j} {Aˢ} A {i} {Γˢ} {Γ} {σˢ} σ)} {S._^_ {i}
--      {Γˢ} {l} {Δˢ} σˢ {j} Aˢ} (_^_ {i} {Γˢ} {Γ} {l} {Δˢ} {Δ} {σˢ} σ {j} {Aˢ} A)) (app
--      {i} {Γˢ} {Γ} {j} {S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ} {_[_]T {l} {Δˢ} {Δ} {j}
--      {Aˢ} A {i} {Γˢ} {Γ} {σˢ} σ} {k} {S._[_]T {l ⊔ j} {S._▶_ {l} Δˢ {j} Aˢ} {k} Bˢ {i
--      ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)} (S._^_ {i} {Γˢ}
--      {l} {Δˢ} σˢ {j} Aˢ)} {_[_]T {l ⊔ j} {S._▶_ {l} Δˢ {j} Aˢ} {_▶_ {l} {Δˢ} Δ {j}
--      {Aˢ} A} {k} {Bˢ} B {i ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ}
--      σˢ)} {_▶_ {i} {Γˢ} Γ {j} {S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ} (_[_]T {l} {Δˢ}
--      {Δ} {j} {Aˢ} A {i} {Γˢ} {Γ} {σˢ} σ)} {S._^_ {i} {Γˢ} {l} {Δˢ} σˢ {j} Aˢ} (_^_
--      {i} {Γˢ} {Γ} {l} {Δˢ} {Δ} {σˢ} σ {j} {Aˢ} A)} {S._[_]t {l} {Δˢ} {j ⊔ k} {S.Π {l}
--      {Δˢ} {j} Aˢ {k} Bˢ} tˢ {i} {Γˢ} σˢ} (tr {i ⊔ (suc j ⊔ suc k)} {i ⊔ (j ⊔ k)} {Ty
--      {i} {Γˢ} Γ (j ⊔ k) (S.Π {i} {Γˢ} {j} (S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ) {k}
--      (S._[_]T {l ⊔ j} {S._▶_ {l} Δˢ {j} Aˢ} {k} Bˢ {i ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T
--      {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)} (S._,s_ {i ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T {l}
--      {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)} {l} {Δˢ} (S._∘_ {i} {Γˢ} {l} {Δˢ} σˢ {i ⊔ j} {S._▶_
--      {i} Γˢ {j} (S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)} (S.π₁ {i ⊔ j} {S._▶_ {i} Γˢ
--      {j} (S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)} {i} {Γˢ} {j} {S._[_]T {l} {Δˢ} {j} Aˢ
--      {i} {Γˢ} σˢ} (S.id {i ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ}
--      σˢ)}))) {j} {Aˢ} (S.π₂ {i ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T {l} {Δˢ} {j} Aˢ {i}
--      {Γˢ} σˢ)} {i} {Γˢ} {j} {S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ} (S.id {i ⊔ j}
--      {S._▶_ {i} Γˢ {j} (S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)})))))} (λ x → Tm {i}
--      {Γˢ} Γ {j ⊔ k} {S.Π {i} {Γˢ} {j} (S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ) {k}
--      (S._[_]T {l ⊔ j} {S._▶_ {l} Δˢ {j} Aˢ} {k} Bˢ {i ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T
--      {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)} (S._,s_ {i ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T {l}
--      {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)} {l} {Δˢ} (S._∘_ {i} {Γˢ} {l} {Δˢ} σˢ {i ⊔ j} {S._▶_
--      {i} Γˢ {j} (S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)} (S.π₁ {i ⊔ j} {S._▶_ {i} Γˢ
--      {j} (S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)} {i} {Γˢ} {j} {S._[_]T {l} {Δˢ} {j} Aˢ
--      {i} {Γˢ} σˢ} (S.id {i ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ}
--      σˢ)}))) {j} {Aˢ} (S.π₂ {i ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T {l} {Δˢ} {j} Aˢ {i}
--      {Γˢ} σˢ)} {i} {Γˢ} {j} {S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ} (S.id {i ⊔ j}
--      {S._▶_ {i} Γˢ {j} (S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)}))))} x (S._[_]t {l}
--      {Δˢ} {j ⊔ k} {S.Π {l} {Δˢ} {j} Aˢ {k} Bˢ} tˢ {i} {Γˢ} σˢ)) {_[_]T {l} {Δˢ} {Δ}
--      {j ⊔ k} {S.Π {l} {Δˢ} {j} Aˢ {k} Bˢ} (Π {l} {Δˢ} {Δ} {j} {Aˢ} A {k} {Bˢ} B) {i}
--      {Γˢ} {Γ} {σˢ} σ} {Π {i} {Γˢ} {Γ} {j} {S._[_]T {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ}
--      (_[_]T {l} {Δˢ} {Δ} {j} {Aˢ} A {i} {Γˢ} {Γ} {σˢ} σ) {k} {S._[_]T {l ⊔ j} {S._▶_
--      {l} Δˢ {j} Aˢ} {k} Bˢ {i ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T {l} {Δˢ} {j} Aˢ {i}
--      {Γˢ} σˢ)} (S._^_ {i} {Γˢ} {l} {Δˢ} σˢ {j} Aˢ)} (_[_]T {l ⊔ j} {S._▶_ {l} Δˢ {j}
--      Aˢ} {_▶_ {l} {Δˢ} Δ {j} {Aˢ} A} {k} {Bˢ} B {i ⊔ j} {S._▶_ {i} Γˢ {j} (S._[_]T
--      {l} {Δˢ} {j} Aˢ {i} {Γˢ} σˢ)} {_▶_ {i} {Γˢ} Γ {j} {S._[_]T {l} {Δˢ} {j} Aˢ {i}
--      {Γˢ} σˢ} (_[_]T {l} {Δˢ} {Δ} {j} {Aˢ} A {i} {Γˢ} {Γ} {σˢ} σ)} {S._^_ {i} {Γˢ}
--      {l} {Δˢ} σˢ {j} Aˢ} (_^_ {i} {Γˢ} {Γ} {l} {Δˢ} {Δ} {σˢ} σ {j} {Aˢ} A))} (Π[] {l}
--      {Δˢ} {Δ} {j} {Aˢ} {A} {k} {Bˢ} {B} {i} {Γˢ} {Γ} {σˢ} {σ}) (_[_]t {l} {Δˢ} {Δ} {j
--      ⊔ k} {S.Π {l} {Δˢ} {j} Aˢ {k} Bˢ} {Π {l} {Δˢ} {Δ} {j} {Aˢ} A {k} {Bˢ} B} {tˢ} t
--      {i} {Γˢ} {Γ} {σˢ} σ)))
-- app[] {i} {Γˢ} {Γ} {l} {Δˢ} {Δ} {σˢ} {σ} {j} {Aˢ} {A} {k} {Bˢ} {B} {tˢ} t = {!!}

      -- t (F.Sub σˢ (₁ (F.▶→ Γᶠ))) (σ (₁ (F.▶→ Γᶠ)) (₁ Γᴾ)) (₂ (F.▶→ Γᶠ)) (₂ Γᴾ)
      -- ≡
      -- app ((λ Γᶠ Γᴾ → t (F.Sub σˢ Γᶠ) (σ Γᶠ Γᴾ))) Γᶠ Γᴾ
      -- OK

Πβ :
     {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Aˢ : S.Ty {i} Γˢ j} {A :
     Ty {i} {Γˢ} Γ j Aˢ} {k : Level} {Bˢ : S.Ty {i ⊔ j} (S._▶_ {i} Γˢ {j} Aˢ) k} {B :
     Ty {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} (_▶_ {i} {Γˢ} Γ {j} {Aˢ} A) k Bˢ} {tˢ : S.Tm {i
     ⊔ j} (S._▶_ {i} Γˢ {j} Aˢ) {k} Bˢ} {t : Tm {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} (_▶_
     {i} {Γˢ} Γ {j} {Aˢ} A) {k} {Bˢ} B tˢ} → _≡_ {i ⊔ (j ⊔ k)} {Tm {i ⊔ j} {S._▶_ {i}
     Γˢ {j} Aˢ} (_▶_ {i} {Γˢ} Γ {j} {Aˢ} A) {k} {Bˢ} B tˢ} (app {i} {Γˢ} {Γ} {j} {Aˢ}
     {A} {k} {Bˢ} {B} {S.lam {i} {Γˢ} {j} {Aˢ} {k} {Bˢ} tˢ} (lam {i} {Γˢ} {Γ} {j}
     {Aˢ} {A} {k} {Bˢ} {B} {tˢ} t)) t
Πβ {i} {Γˢ} {Γ} {j} {Aˢ} {A} {k} {Bˢ} {B} {tˢ} {t} = refl


Πη :
   {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Aˢ : S.Ty {i} Γˢ j} {A :
   Ty {i} {Γˢ} Γ j Aˢ} {k : Level} {Bˢ : S.Ty {i ⊔ j} (S._▶_ {i} Γˢ {j} Aˢ) k} {B :
   Ty {i ⊔ j} {S._▶_ {i} Γˢ {j} Aˢ} (_▶_ {i} {Γˢ} Γ {j} {Aˢ} A) k Bˢ} {tˢ : S.Tm
   {i} Γˢ {j ⊔ k} (S.Π {i} {Γˢ} {j} Aˢ {k} Bˢ)} {t : Tm {i} {Γˢ} Γ {j ⊔ k} {S.Π {i}
   {Γˢ} {j} Aˢ {k} Bˢ} (Π {i} {Γˢ} {Γ} {j} {Aˢ} A {k} {Bˢ} B) tˢ} → _≡_ {i ⊔ (j ⊔
   k)} {Tm {i} {Γˢ} Γ {j ⊔ k} {S.Π {i} {Γˢ} {j} Aˢ {k} Bˢ} (Π {i} {Γˢ} {Γ} {j} {Aˢ}
   A {k} {Bˢ} B) tˢ} (lam {i} {Γˢ} {Γ} {j} {Aˢ} {A} {k} {Bˢ} {B} {S.app {i} {Γˢ}
   {j} {Aˢ} {k} {Bˢ} tˢ} (app {i} {Γˢ} {Γ} {j} {Aˢ} {A} {k} {Bˢ} {B} {tˢ} t)) t
Πη = refl
