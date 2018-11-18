{-# OPTIONS --rewriting #-}

module Glued.Bool where

open import StrictLib hiding (id; _∘_)
open import Glued.CwF
import Syntax as S
import WeakMorphism as F
open import Data.Bool renaming (Bool to 𝔹; true to 𝕋; false to 𝔽)

Bool :
  {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} → Ty {i} {Γˢ} Γ zero (S.Bool {i} {Γˢ})
Bool {i} {Γˢ} {Γ} Γᶠ Γᴾ boolᶠ = (F.Bool← Γᶠ 𝕋 ≡ boolᶠ) ⊎ (F.Bool← Γᶠ 𝔽 ≡ boolᶠ)

Bool[] :
  {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Δˢ : S.Con j} {Δ : Con j
  Δˢ} {σˢ : S.Sub {i} Γˢ {j} Δˢ} {σ : Sub {i} {Γˢ} Γ {j} {Δˢ} Δ σˢ} → _≡_ {suc
  zero ⊔ i} {Ty {i} {Γˢ} Γ zero (S.Bool {i} {Γˢ})} (_[_]T {j} {Δˢ} {Δ} {zero}
  {S.Bool {j} {Δˢ}} (Bool {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ) (Bool {i} {Γˢ} {Γ})
Bool[] {i} {Γˢ} {Γ} {j} {Δˢ} {Δ} {σˢ} {σ} = refl  -- by Bool←nat

true :
  {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} → Tm {i} {Γˢ} Γ {zero} {S.Bool {i}
  {Γˢ}} (Bool {i} {Γˢ} {Γ}) (S.true {i} {Γˢ})
true {i} {Γˢ} {Γ} Γᶠ Γᴾ = {!F.Bool→ Γᶠ!}

-- true[] :
--   {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Δˢ : S.Con j} {Δ : Con j
--   Δˢ} {σˢ : S.Sub {i} Γˢ {j} Δˢ} {σ : Sub {i} {Γˢ} Γ {j} {Δˢ} Δ σˢ} → _≡_ {i} {Tm
--   {i} {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} (_[_]T {j} {Δˢ} {Δ} {zero} {S.Bool {j} {Δˢ}}
--   (Bool {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ) (tr {suc zero ⊔ i} {i} {S.Ty {i} Γˢ
--   zero} (S.Tm {i} Γˢ {zero}) {S.Bool {i} {Γˢ}} {S.Bool {i} {Γˢ}} refl (S.true {i}
--   {Γˢ}))} (_[_]t {j} {Δˢ} {Δ} {zero} {S.Bool {j} {Δˢ}} {Bool {j} {Δˢ} {Δ}} {S.true
--   {j} {Δˢ}} (true {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ) (coe {i} {Tm {i} {Γˢ} Γ
--   {zero} {S.Bool {i} {Γˢ}} (Bool {i} {Γˢ} {Γ}) (S.true {i} {Γˢ})} {Tm {i} {Γˢ} Γ
--   {zero} {S.Bool {i} {Γˢ}} (_[_]T {j} {Δˢ} {Δ} {zero} {S.Bool {j} {Δˢ}} (Bool {j}
--   {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ) (S.true {i} {Γˢ})} (_&_ {suc zero ⊔ i} {suc i}
--   {Ty {i} {Γˢ} Γ zero (S.Bool {i} {Γˢ})} {Set i} (λ x → Tm {i} {Γˢ} Γ {zero}
--   {S.Bool {i} {Γˢ}} x (S.true {i} {Γˢ})) {Bool {i} {Γˢ} {Γ}} {_[_]T {j} {Δˢ} {Δ}
--   {zero} {S.Bool {j} {Δˢ}} (Bool {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ} (_⁻¹ {suc zero
--   ⊔ i} {Ty {i} {Γˢ} Γ zero (S.Bool {i} {Γˢ})} {_[_]T {j} {Δˢ} {Δ} {zero} {S.Bool
--   {j} {Δˢ}} (Bool {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ} {Bool {i} {Γˢ} {Γ}} (Bool[]
--   {i} {Γˢ} {Γ} {j} {Δˢ} {Δ} {σˢ} {σ}))) (true {i} {Γˢ} {Γ}))
-- true[] = {!!}

-- false :
--   {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} → Tm {i} {Γˢ} Γ {zero} {S.Bool {i}
--   {Γˢ}} (Bool {i} {Γˢ} {Γ}) (S.false {i} {Γˢ})
-- false = {!!}

-- false[] :
--     {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Δˢ : S.Con j} {Δ : Con j
--     Δˢ} {σˢ : S.Sub {i} Γˢ {j} Δˢ} {σ : Sub {i} {Γˢ} Γ {j} {Δˢ} Δ σˢ} → _≡_ {i} {Tm
--     {i} {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} (_[_]T {j} {Δˢ} {Δ} {zero} {S.Bool {j} {Δˢ}}
--     (Bool {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ) (tr {suc zero ⊔ i} {i} {S.Ty {i} Γˢ
--     zero} (S.Tm {i} Γˢ {zero}) {S.Bool {i} {Γˢ}} {S.Bool {i} {Γˢ}} refl (S.false {i}
--     {Γˢ}))} (_[_]t {j} {Δˢ} {Δ} {zero} {S.Bool {j} {Δˢ}} {Bool {j} {Δˢ} {Δ}}
--     {S.false {j} {Δˢ}} (false {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ) (coe {i} {Tm {i}
--     {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} (Bool {i} {Γˢ} {Γ}) (S.false {i} {Γˢ})} {Tm {i}
--     {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} (_[_]T {j} {Δˢ} {Δ} {zero} {S.Bool {j} {Δˢ}}
--     (Bool {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ) (S.false {i} {Γˢ})} (_&_ {suc zero ⊔ i}
--     {suc i} {Ty {i} {Γˢ} Γ zero (S.Bool {i} {Γˢ})} {Set i} (λ x → Tm {i} {Γˢ} Γ
--     {zero} {S.Bool {i} {Γˢ}} x (S.false {i} {Γˢ})) {Bool {i} {Γˢ} {Γ}} {_[_]T {j}
--     {Δˢ} {Δ} {zero} {S.Bool {j} {Δˢ}} (Bool {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ} (_⁻¹
--     {suc zero ⊔ i} {Ty {i} {Γˢ} Γ zero (S.Bool {i} {Γˢ})} {_[_]T {j} {Δˢ} {Δ} {zero}
--     {S.Bool {j} {Δˢ}} (Bool {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ} {Bool {i} {Γˢ} {Γ}}
--     (Bool[] {i} {Γˢ} {Γ} {j} {Δˢ} {Δ} {σˢ} {σ}))) (false {i} {Γˢ} {Γ}))
-- false[] = {!!}
