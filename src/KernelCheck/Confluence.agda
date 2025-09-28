module KernelCheck.Confluence where

open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Nullary.Decidable using (Dec; yes; no)

open import Relation.Binary.PropositionalEquality
open import KernelCheck.Prog
open import KernelCheck.Util

StepThd-unique : ∀ {ℂ i E X T E1 X1 T1 E2 X2 T2}
  → StepThd ℂ i E X T E1 X1 T1
  → StepThd ℂ i E X T E2 X2 T2
  → E1 ≡ E2 × X1 ≡ X2 × T1 ≡ T2
StepThd-unique (const _ _ _ _ _) (const _ _ _ _ _) = refl , refl , refl
StepThd-unique (binOp _ _ _ _ _ _) (binOp _ _ _ _ _ _) = refl , refl , refl
StepThd-unique (rdReg _ _ _ _ _) (rdReg _ _ _ _ _) = refl , refl , refl
StepThd-unique (rdGbl _ _ _ _ _ _) (rdGbl _ _ _ _ _ _) = refl , refl , refl
StepThd-unique (wrGbl _ _ _ _ _ _ _) (wrGbl _ _ _ _ _ _ _) = refl , refl , refl

diamond : ∀ ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2
  → StepProgRefl ℂ ℰ X P ℰ1 X1 P1
  → StepProgRefl ℂ ℰ X P ℰ2 X2 P2
  → ∃[ ℰ' ] ∃[ X' ] ∃[ P' ] StepProgRefl ℂ ℰ1 X1 P1 ℰ' X' P' × StepProgRefl ℂ ℰ2 X2 P2 ℰ' X' P'
diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (refl _ _ _) (refl _ _ _) = ℰ , X , P , refl _ _ _ , refl _ _ _
diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (refl _ _ _) (schd i .ℰ .X .P E' X' T' x) = _ , _ , _ , schd i ℰ X P E' X' T' x , refl _ _ _
diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (refl _ _ _) (sync I .ℰ .X .P p) = _ , _ , _ , sync I ℰ X P p , refl _ _ _
diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (schd i .ℰ .X .P E' X' T' x) (refl _ _ _) = _ , _ , _ , refl _ _ _ , schd i ℰ X P E' X' T' x
diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (sync I .ℰ .X .P p) (refl _ _ _) = _ , _ , _ , refl _ _ _ , sync I ℰ X P p
diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (schd i .ℰ .X .P E1' X1' T1' x1) (schd j .ℰ .X .P E2' X2' T2' x2) with Tid.val i ≟ Tid.val j
... | yes refl = ℰ1 , X1 , P1 , refl _ _ _ , rhs
  where
  eqs : E1' ≡ E2' × X1 ≡ X2 × T1' ≡ T2'
  eqs = StepThd-unique x1 x2

  ℰ1≡ℰ2 : E1' ≡ E2' → ℰ1 ≡ ℰ2
  ℰ1≡ℰ2 refl = refl

  P1≡P2 : T1' ≡ T2' → P1 ≡ P2
  P1≡P2 refl = refl

  rhs : StepProgRefl ℂ ℰ2 X2 P2 ℰ1 X1 P1
  rhs = transport (cong₃ (λ a b c → StepProgRefl ℂ a b c ℰ1 X1 P1) (ℰ1≡ℰ2 (proj₁ eqs)) (proj₁ (proj₂ eqs)) (P1≡P2 (proj₂ (proj₂ eqs)))) (refl ℰ1 X1 P1)
... | no i≠j = {!!}
  where
  E' = updFun tidEq (updFun tidEq ℰ i E1') j E2'
  T' = updFun tidEq (updFun tidEq P i T1') j T2'
  -- l = (updFun tidEq ℰ i E1') X1' (updFun tidEq P i T1')
diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (schd i ℰ₁ X₁ P₁ E' X' T' x) (sync I ℰ₂ X₂ P₂ p) = {!!}
diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (sync I ℰ₁ X₁ P₁ p) (schd i ℰ₂ X₂ P₂ E' X' T' x) = {!!}
diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (sync I ℰ₁ X₁ P₁ p) (sync I₁ ℰ₂ X₂ P₂ p₁) = {!!}
