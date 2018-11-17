{-# OPTIONS --rewriting #-}

module Canonicity.Bool where

open import StrictLib hiding (id; _∘_)
open import Canonicity.CwF
import Syntax as S

Bool :
  {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} → Ty {i} {Γˢ} Γ zero (S.Bool {i} {Γˢ})
Bool {i} {Γˢ} {Γ} σ σᴾ t = S.true ≡ t ⊎ S.false ≡ t

Bool[] :
  {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Δˢ : S.Con j} {Δ : Con j
  Δˢ} {σˢ : S.Sub {i} Γˢ {j} Δˢ} {σ : Sub {i} {Γˢ} Γ {j} {Δˢ} Δ σˢ} → _≡_ {suc
  zero ⊔ i} {Ty {i} {Γˢ} Γ zero (S.Bool {i} {Γˢ})} (_[_]T {j} {Δˢ} {Δ} {zero}
  {S.Bool {j} {Δˢ}} (Bool {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ) (Bool {i} {Γˢ} {Γ})
Bool[] = refl

true :
  {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} → Tm {i} {Γˢ} Γ {zero} {S.Bool {i}
  {Γˢ}} (Bool {i} {Γˢ} {Γ}) (S.true {i} {Γˢ})
true σ σᴾ = inl refl

true[] :
    {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Δˢ : S.Con j} {Δ : Con j
    Δˢ} {σˢ : S.Sub {i} Γˢ {j} Δˢ} {σ : Sub {i} {Γˢ} Γ {j} {Δˢ} Δ σˢ} → _≡_ {i} {Tm
    {i} {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} (_[_]T {j} {Δˢ} {Δ} {zero} {S.Bool {j} {Δˢ}}
    (Bool {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ) (tr {suc zero ⊔ i} {i} {S.Ty {i} Γˢ
    zero} (S.Tm {i} Γˢ {zero}) {S.Bool {i} {Γˢ}} {S.Bool {i} {Γˢ}} refl (S.true {i}
    {Γˢ}))} (_[_]t {j} {Δˢ} {Δ} {zero} {S.Bool {j} {Δˢ}} {Bool {j} {Δˢ} {Δ}} {S.true
    {j} {Δˢ}} (true {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ) (coe {i} {Tm {i} {Γˢ} Γ
    {zero} {S.Bool {i} {Γˢ}} (Bool {i} {Γˢ} {Γ}) (S.true {i} {Γˢ})} {Tm {i} {Γˢ} Γ
    {zero} {S.Bool {i} {Γˢ}} (_[_]T {j} {Δˢ} {Δ} {zero} {S.Bool {j} {Δˢ}} (Bool {j}
    {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ) (S.true {i} {Γˢ})} (_&_ {suc zero ⊔ i} {suc i}
    {Ty {i} {Γˢ} Γ zero (S.Bool {i} {Γˢ})} {Set i} (λ x → Tm {i} {Γˢ} Γ {zero}
    {S.Bool {i} {Γˢ}} x (S.true {i} {Γˢ})) {Bool {i} {Γˢ} {Γ}} {_[_]T {j} {Δˢ} {Δ}
    {zero} {S.Bool {j} {Δˢ}} (Bool {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ} (_⁻¹ {suc zero
    ⊔ i} {Ty {i} {Γˢ} Γ zero (S.Bool {i} {Γˢ})} {_[_]T {j} {Δˢ} {Δ} {zero} {S.Bool
    {j} {Δˢ}} (Bool {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ} {Bool {i} {Γˢ} {Γ}} (Bool[]
    {i} {Γˢ} {Γ} {j} {Δˢ} {Δ} {σˢ} {σ}))) (true {i} {Γˢ} {Γ}))
true[] = refl

false :
  {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} → Tm {i} {Γˢ} Γ {zero} {S.Bool {i}
  {Γˢ}} (Bool {i} {Γˢ} {Γ}) (S.false {i} {Γˢ})
false σ σᴾ = inr refl

false[] :
    {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Δˢ : S.Con j} {Δ : Con j
    Δˢ} {σˢ : S.Sub {i} Γˢ {j} Δˢ} {σ : Sub {i} {Γˢ} Γ {j} {Δˢ} Δ σˢ} → _≡_ {i} {Tm
    {i} {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} (_[_]T {j} {Δˢ} {Δ} {zero} {S.Bool {j} {Δˢ}}
    (Bool {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ) (tr {suc zero ⊔ i} {i} {S.Ty {i} Γˢ
    zero} (S.Tm {i} Γˢ {zero}) {S.Bool {i} {Γˢ}} {S.Bool {i} {Γˢ}} refl (S.false {i}
    {Γˢ}))} (_[_]t {j} {Δˢ} {Δ} {zero} {S.Bool {j} {Δˢ}} {Bool {j} {Δˢ} {Δ}}
    {S.false {j} {Δˢ}} (false {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ) (coe {i} {Tm {i}
    {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} (Bool {i} {Γˢ} {Γ}) (S.false {i} {Γˢ})} {Tm {i}
    {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} (_[_]T {j} {Δˢ} {Δ} {zero} {S.Bool {j} {Δˢ}}
    (Bool {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ) (S.false {i} {Γˢ})} (_&_ {suc zero ⊔ i}
    {suc i} {Ty {i} {Γˢ} Γ zero (S.Bool {i} {Γˢ})} {Set i} (λ x → Tm {i} {Γˢ} Γ
    {zero} {S.Bool {i} {Γˢ}} x (S.false {i} {Γˢ})) {Bool {i} {Γˢ} {Γ}} {_[_]T {j}
    {Δˢ} {Δ} {zero} {S.Bool {j} {Δˢ}} (Bool {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ} (_⁻¹
    {suc zero ⊔ i} {Ty {i} {Γˢ} Γ zero (S.Bool {i} {Γˢ})} {_[_]T {j} {Δˢ} {Δ} {zero}
    {S.Bool {j} {Δˢ}} (Bool {j} {Δˢ} {Δ}) {i} {Γˢ} {Γ} {σˢ} σ} {Bool {i} {Γˢ} {Γ}}
    (Bool[] {i} {Γˢ} {Γ} {j} {Δˢ} {Δ} {σˢ} {σ}))) (false {i} {Γˢ} {Γ}))
false[] = refl

ite :
    {i : Level} {Γˢ : S.Con i} {Γ : Con i Γˢ} {j : Level} {Pˢ : S.Ty {i} (S._▶_ {i}
    Γˢ {zero} (S.Bool {i} {Γˢ})) j} (P : Ty {i} {S._▶_ {i} Γˢ {zero} (S.Bool {i}
    {Γˢ})} (_▶_ {i} {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} (Bool {i} {Γˢ} {Γ})) j Pˢ) {tˢ :
    S.Tm {i} Γˢ {j} (S._[_]T {i} {S._▶_ {i} Γˢ {zero} (S.Bool {i} {Γˢ})} {j} Pˢ {i}
    {Γˢ} (S._,s_ {i} {Γˢ} {i} {Γˢ} (S.id {i} {Γˢ}) {zero} {S.Bool {i} {Γˢ}} (S.true
    {i} {Γˢ})))} → Tm {i} {Γˢ} Γ {j} {S._[_]T {i} {S._▶_ {i} Γˢ {zero} (S.Bool {i}
    {Γˢ})} {j} Pˢ {i} {Γˢ} (S._,s_ {i} {Γˢ} {i} {Γˢ} (S.id {i} {Γˢ}) {zero} {S.Bool
    {i} {Γˢ}} (S.true {i} {Γˢ}))} (_[_]T {i} {S._▶_ {i} Γˢ {zero} (S.Bool {i} {Γˢ})}
    {_▶_ {i} {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} (Bool {i} {Γˢ} {Γ})} {j} {Pˢ} P {i}
    {Γˢ} {Γ} {S._,s_ {i} {Γˢ} {i} {Γˢ} (S.id {i} {Γˢ}) {zero} {S.Bool {i} {Γˢ}}
    (S.true {i} {Γˢ})} (_,s_ {i} {Γˢ} {Γ} {i} {Γˢ} {Γ} {S.id {i} {Γˢ}} (id {i} {Γˢ}
    {Γ}) {zero} {S.Bool {i} {Γˢ}} {Bool {i} {Γˢ} {Γ}} {S.true {i} {Γˢ}} (coe {i} {Tm
    {i} {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} (Bool {i} {Γˢ} {Γ}) (S.true {i} {Γˢ})} {Tm
    {i} {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} (_[_]T {i} {Γˢ} {Γ} {zero} {S.Bool {i} {Γˢ}}
    (Bool {i} {Γˢ} {Γ}) {i} {Γˢ} {Γ} {S.id {i} {Γˢ}} (id {i} {Γˢ} {Γ})) (S.true {i}
    {Γˢ})} (_&_ {suc zero ⊔ i} {suc i} {Ty {i} {Γˢ} Γ zero (S.Bool {i} {Γˢ})} {Set
    i} (λ x → Tm {i} {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} x (S.true {i} {Γˢ})) {Bool {i}
    {Γˢ} {Γ}} {_[_]T {i} {Γˢ} {Γ} {zero} {S.Bool {i} {Γˢ}} (Bool {i} {Γˢ} {Γ}) {i}
    {Γˢ} {Γ} {S.id {i} {Γˢ}} (id {i} {Γˢ} {Γ})} (_⁻¹ {suc zero ⊔ i} {Ty {i} {Γˢ} Γ
    zero (S.Bool {i} {Γˢ})} {_[_]T {i} {Γˢ} {Γ} {zero} {S.Bool {i} {Γˢ}} (Bool {i}
    {Γˢ} {Γ}) {i} {Γˢ} {Γ} {S.id {i} {Γˢ}} (id {i} {Γˢ} {Γ})} {Bool {i} {Γˢ} {Γ}}
    (Bool[] {i} {Γˢ} {Γ} {i} {Γˢ} {Γ} {S.id {i} {Γˢ}} {id {i} {Γˢ} {Γ}}))) (true {i}
    {Γˢ} {Γ})))) tˢ → {fˢ : S.Tm {i} Γˢ {j} (S._[_]T {i} {S._▶_ {i} Γˢ {zero}
    (S.Bool {i} {Γˢ})} {j} Pˢ {i} {Γˢ} (S._,s_ {i} {Γˢ} {i} {Γˢ} (S.id {i} {Γˢ})
    {zero} {S.Bool {i} {Γˢ}} (S.false {i} {Γˢ})))} → Tm {i} {Γˢ} Γ {j} {S._[_]T {i}
    {S._▶_ {i} Γˢ {zero} (S.Bool {i} {Γˢ})} {j} Pˢ {i} {Γˢ} (S._,s_ {i} {Γˢ} {i}
    {Γˢ} (S.id {i} {Γˢ}) {zero} {S.Bool {i} {Γˢ}} (S.false {i} {Γˢ}))} (_[_]T {i}
    {S._▶_ {i} Γˢ {zero} (S.Bool {i} {Γˢ})} {_▶_ {i} {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}}
    (Bool {i} {Γˢ} {Γ})} {j} {Pˢ} P {i} {Γˢ} {Γ} {S._,s_ {i} {Γˢ} {i} {Γˢ} (S.id {i}
    {Γˢ}) {zero} {S.Bool {i} {Γˢ}} (S.false {i} {Γˢ})} (_,s_ {i} {Γˢ} {Γ} {i} {Γˢ}
    {Γ} {S.id {i} {Γˢ}} (id {i} {Γˢ} {Γ}) {zero} {S.Bool {i} {Γˢ}} {Bool {i} {Γˢ}
    {Γ}} {S.false {i} {Γˢ}} (coe {i} {Tm {i} {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} (Bool
    {i} {Γˢ} {Γ}) (S.false {i} {Γˢ})} {Tm {i} {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} (_[_]T
    {i} {Γˢ} {Γ} {zero} {S.Bool {i} {Γˢ}} (Bool {i} {Γˢ} {Γ}) {i} {Γˢ} {Γ} {S.id {i}
    {Γˢ}} (id {i} {Γˢ} {Γ})) (S.false {i} {Γˢ})} (_&_ {suc zero ⊔ i} {suc i} {Ty {i}
    {Γˢ} Γ zero (S.Bool {i} {Γˢ})} {Set i} (λ x → Tm {i} {Γˢ} Γ {zero} {S.Bool {i}
    {Γˢ}} x (S.false {i} {Γˢ})) {Bool {i} {Γˢ} {Γ}} {_[_]T {i} {Γˢ} {Γ} {zero}
    {S.Bool {i} {Γˢ}} (Bool {i} {Γˢ} {Γ}) {i} {Γˢ} {Γ} {S.id {i} {Γˢ}} (id {i} {Γˢ}
    {Γ})} (_⁻¹ {suc zero ⊔ i} {Ty {i} {Γˢ} Γ zero (S.Bool {i} {Γˢ})} {_[_]T {i} {Γˢ}
    {Γ} {zero} {S.Bool {i} {Γˢ}} (Bool {i} {Γˢ} {Γ}) {i} {Γˢ} {Γ} {S.id {i} {Γˢ}}
    (id {i} {Γˢ} {Γ})} {Bool {i} {Γˢ} {Γ}} (Bool[] {i} {Γˢ} {Γ} {i} {Γˢ} {Γ} {S.id
    {i} {Γˢ}} {id {i} {Γˢ} {Γ}}))) (false {i} {Γˢ} {Γ})))) fˢ → {bˢ : S.Tm {i} Γˢ
    {zero} (S.Bool {i} {Γˢ})} (b : Tm {i} {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} (Bool {i}
    {Γˢ} {Γ}) bˢ) → Tm {i} {Γˢ} Γ {j} {S._[_]T {i} {S._▶_ {i} Γˢ {zero} (S.Bool {i}
    {Γˢ})} {j} Pˢ {i} {Γˢ} (S._,s_ {i} {Γˢ} {i} {Γˢ} (S.id {i} {Γˢ}) {zero} {S.Bool
    {i} {Γˢ}} bˢ)} (_[_]T {i} {S._▶_ {i} Γˢ {zero} (S.Bool {i} {Γˢ})} {_▶_ {i} {Γˢ}
    Γ {zero} {S.Bool {i} {Γˢ}} (Bool {i} {Γˢ} {Γ})} {j} {Pˢ} P {i} {Γˢ} {Γ} {S._,s_
    {i} {Γˢ} {i} {Γˢ} (S.id {i} {Γˢ}) {zero} {S.Bool {i} {Γˢ}} bˢ} (_,s_ {i} {Γˢ}
    {Γ} {i} {Γˢ} {Γ} {S.id {i} {Γˢ}} (id {i} {Γˢ} {Γ}) {zero} {S.Bool {i} {Γˢ}}
    {Bool {i} {Γˢ} {Γ}} {bˢ} (coe {i} {Tm {i} {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} (Bool
    {i} {Γˢ} {Γ}) bˢ} {Tm {i} {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} (_[_]T {i} {Γˢ} {Γ}
    {zero} {S.Bool {i} {Γˢ}} (Bool {i} {Γˢ} {Γ}) {i} {Γˢ} {Γ} {S.id {i} {Γˢ}} (id
    {i} {Γˢ} {Γ})) bˢ} (_&_ {suc zero ⊔ i} {suc i} {Ty {i} {Γˢ} Γ zero (S.Bool {i}
    {Γˢ})} {Set i} (λ x → Tm {i} {Γˢ} Γ {zero} {S.Bool {i} {Γˢ}} x bˢ) {Bool {i}
    {Γˢ} {Γ}} {_[_]T {i} {Γˢ} {Γ} {zero} {S.Bool {i} {Γˢ}} (Bool {i} {Γˢ} {Γ}) {i}
    {Γˢ} {Γ} {S.id {i} {Γˢ}} (id {i} {Γˢ} {Γ})} (_⁻¹ {suc zero ⊔ i} {Ty {i} {Γˢ} Γ
    zero (S.Bool {i} {Γˢ})} {_[_]T {i} {Γˢ} {Γ} {zero} {S.Bool {i} {Γˢ}} (Bool {i}
    {Γˢ} {Γ}) {i} {Γˢ} {Γ} {S.id {i} {Γˢ}} (id {i} {Γˢ} {Γ})} {Bool {i} {Γˢ} {Γ}}
    (Bool[] {i} {Γˢ} {Γ} {i} {Γˢ} {Γ} {S.id {i} {Γˢ}} {id {i} {Γˢ} {Γ}}))) b)))
    (S.ite {i} {Γˢ} {j} Pˢ tˢ fˢ bˢ)
ite {i} {Γˢ} {Γ} {j} {Pˢ} P {tˢ} t {fˢ} f {bˢ} b σ σᴾ with b σ σᴾ
... | inl eq = cheat -- {!t σ σᴾ!}   -- OK by ite[], ite-true and ite-false
... | inr eq = cheat -- {!b σ σᴾ!}

-- ite-true, ite-false, ite[] OK
