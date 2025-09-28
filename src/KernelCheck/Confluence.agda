module KernelCheck.Confluence where

open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false; not)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Nullary.Decidable using (Dec; yes; no)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import KernelCheck.Prog
open import KernelCheck.Util
open import KernelCheck.DecSet

StepThd-i≡j : ∀ {ℂ i E X T E1 X1 T1 E2 X2 T2}
  → StepThd ℂ i E X T E1 X1 T1
  → StepThd ℂ i E X T E2 X2 T2
  → E1 ≡ E2 × X1 ≡ X2 × T1 ≡ T2
StepThd-i≡j (const _ _ _ _ _) (const _ _ _ _ _) = refl , refl , refl
StepThd-i≡j (binOp _ _ _ _ _ _) (binOp _ _ _ _ _ _) = refl , refl , refl
StepThd-i≡j (rdReg _ _ _ _ _) (rdReg _ _ _ _ _) = refl , refl , refl
StepThd-i≡j (rdGbl _ _ _ _ _ _) (rdGbl _ _ _ _ _ _) = refl , refl , refl
StepThd-i≡j (wrGbl _ _ _ _ _ _ _) (wrGbl _ _ _ _ _ _ _) = refl , refl , refl

StepThd-i≢j : ∀ {ℂ i j Ei Ti Ei1 Ti1 Ei2 Ti2 Ej Tj Ej1 Tj1 Ej2 Tj2 X X'1 X''1 X'2 X''2}
  → i ≢ j
  → StepThd ℂ i Ei X Ti Ei1 X'1 Ti1
  → StepThd ℂ j Ej X'1 Tj Ej1 X''1 Tj1
  → StepThd ℂ j Ej X Tj Ej2 X'2 Tj2
  → StepThd ℂ i Ei X'2 Ti Ei2 X''2 Ti2
  → Ei1 ≡ Ei2 × Ti1 ≡ Ti2 × Ej1 ≡ Ej2 × Tj1 ≡ Tj2 × X''1 ≡ X''2
StepThd-i≢j _ (const _ _ _ _ _) (const _ _ _ _ _) (const _ _ _ _ _) (const _ _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (const _ _ _ _ _) (binOp _ _ _ _ _ _) (binOp _ _ _ _ _ _) (const _ _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (const _ _ _ _ _) (rdReg _ _ _ _ _) (rdReg _ _ _ _ _) (const _ _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (const _ _ _ _ _) (rdGbl _ _ _ _ _ _) (rdGbl _ _ _ _ _ _) (const _ _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (const _ _ _ _ _) (wrGbl _ _ _ _ _ _ _) (wrGbl _ _ _ _ _ _ _) (const _ _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (binOp _ _ _ _ _ _) (const _ _ _ _ _) (const _ _ _ _ _) (binOp _ _ _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (binOp _ _ _ _ _ _) (binOp _ _ _ _ _ _) (binOp _ _ _ _ _ _) (binOp _ _ _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (binOp _ _ _ _ _ _) (rdReg _ _ _ _ _) (rdReg _ _ _ _ _) (binOp _ _ _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (binOp _ _ _ _ _ _) (rdGbl _ _ _ _ _ _) (rdGbl _ _ _ _ _ _) (binOp _ _ _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (binOp _ _ _ _ _ _) (wrGbl _ _ _ _ _ _ _) (wrGbl _ _ _ _ _ _ _) (binOp _ _ _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (rdReg _ _ _ _ _) (const _ _ _ _ _) (const _ _ _ _ _) (rdReg _ _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (rdReg _ _ _ _ _) (binOp _ _ _ _ _ _) (binOp _ _ _ _ _ _) (rdReg _ _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (rdReg _ _ _ _ _) (rdReg _ _ _ _ _) (rdReg _ _ _ _ _) (rdReg _ _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (rdReg _ _ _ _ _) (rdGbl _ _ _ _ _ _) (rdGbl _ _ _ _ _ _) (rdReg _ _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (rdReg _ _ _ _ _) (wrGbl _ _ _ _ _ _ _) (wrGbl _ _ _ _ _ _ _) (rdReg _ _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (rdGbl _ _ _ _ _ _) (const _ _ _ _ _) (const _ _ _ _ _) (rdGbl _ _ _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (rdGbl _ _ _ _ _ _) (binOp _ _ _ _ _ _) (binOp _ _ _ _ _ _) (rdGbl _ _ _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (rdGbl _ _ _ _ _ _) (rdReg _ _ _ _ _) (rdReg _ _ _ _ _) (rdGbl _ _ _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j {i = i} {j = j} {X = X} i≢j (rdGbl _ _ _ g1 _ _) (rdGbl _ _ _ g2 _ _) (rdGbl _ _ _ .g2 _ _) (rdGbl _ _ _ .g1 _ _) = refl , refl , refl , refl , funext (λ g → lem g (gidEq g g1) (gidEq g g2))
  where
  lem-yy-rd : ∀ g → MemEvs.rd (doRd (doRd (X g) i) j) ≡ MemEvs.rd (doRd (doRd (X g) j) i)
  lem-yy-rd g = updFun-comm tidEq (MemEvs.rd (X g)) i≢j _ _

  lem : ∀ g
    → Dec (g ≡ g1)
    → Dec (g ≡ g2)
    → updFun gidEq (updFun gidEq X g1 (doRd (X g1) i)) g2 (doRd (updFun gidEq X g1 (doRd (X g1) i) g2) j) g ≡
      updFun gidEq (updFun gidEq X g2 (doRd (X g2) j)) g1 (doRd (updFun gidEq X g2 (doRd (X g2) j) g1) i) g
  lem g (yes refl) (yes refl) = begin
      updFun gidEq (updFun gidEq X g (doRd (X g) i)) g (doRd (updFun gidEq X g (doRd (X g) i) g) j) g
    ≡⟨ updFun-simp-≡ gidEq (updFun gidEq X g (doRd (X g) i)) g _ ⟩
      doRd (updFun gidEq X g (doRd (X g) i) g) j
    ≡⟨ cong (λ a → doRd a j) (updFun-simp-≡ gidEq X g _) ⟩
      doRd (doRd (X g) i) j
    ≡⟨ MemEvs-≡ (lem-yy-rd g) refl ⟩
      doRd (doRd (X g) j) i
    ≡⟨ sym (cong (λ a → doRd a i) (updFun-simp-≡ gidEq X g _)) ⟩
      doRd (updFun gidEq X g (doRd (X g) j) g) i
    ≡⟨ sym (updFun-simp-≡ gidEq (updFun gidEq X g (doRd (X g) j)) g _) ⟩
      updFun gidEq (updFun gidEq X g (doRd (X g) j)) g (doRd (updFun gidEq X g (doRd (X g) j) g) i) g
    ∎
  lem g (yes refl) (no g≢g2) = begin
      updFun gidEq (updFun gidEq X g (doRd (X g) i)) g2 (doRd (updFun gidEq X g (doRd (X g) i) g2) j) g
    ≡⟨ updFun-simp-≢ gidEq (updFun gidEq X g (doRd (X g) i)) g2 g _ (≢-sym g≢g2) ⟩
      (updFun gidEq X g (doRd (X g) i)) g
    ≡⟨ updFun-simp-≡ gidEq X g _ ⟩
      doRd (X g) i
    ≡⟨ cong (λ a → doRd a i) (sym (updFun-simp-≢ gidEq X g2 g _ (≢-sym g≢g2))) ⟩
      doRd (updFun gidEq X g2 (doRd (X g2) j) g) i
    ≡⟨ sym (updFun-simp-≡ gidEq (updFun gidEq X g2 (doRd (X g2) j)) g _) ⟩
      updFun gidEq (updFun gidEq X g2 (doRd (X g2) j)) g (doRd (updFun gidEq X g2 (doRd (X g2) j) g) i) g
    ∎
  lem g (no g≢g1) (yes refl) = begin
      updFun gidEq (updFun gidEq X g1 (doRd (X g1) i)) g (doRd (updFun gidEq X g1 (doRd (X g1) i) g) j) g
    ≡⟨ updFun-simp-≡ gidEq (updFun gidEq X g1 (doRd (X g1) i)) g _ ⟩
      doRd (updFun gidEq X g1 (doRd (X g1) i) g) j
    ≡⟨ cong (λ a → doRd a j) (updFun-simp-≢ gidEq X g1 g _ (≢-sym g≢g1)) ⟩
      doRd (X g) j
    ≡⟨ sym (updFun-simp-≡ gidEq X g _) ⟩
      (updFun gidEq X g (doRd (X g) j)) g
    ≡⟨ sym (updFun-simp-≢ gidEq (updFun gidEq X g (doRd (X g) j)) g1 g _ (≢-sym g≢g1)) ⟩
      updFun gidEq (updFun gidEq X g (doRd (X g) j)) g1 (doRd (updFun gidEq X g (doRd (X g) j) g1) i) g
    ∎
  lem g (no g≢g1) (no g≢g2) = begin
      updFun gidEq (updFun gidEq X g1 (doRd (X g1) i)) g2 (doRd (updFun gidEq X g1 (doRd (X g1) i) g2) j) g
    ≡⟨ updFun-simp-≢ gidEq (updFun gidEq X g1 (doRd (X g1) i)) g2 g _ (≢-sym g≢g2) ⟩
      updFun gidEq X g1 (doRd (X g1) i) g
    ≡⟨ updFun-simp-≢ gidEq X g1 g _ (≢-sym g≢g1) ⟩
      X g
    ≡⟨ sym (updFun-simp-≢ gidEq X g2 g _ (≢-sym g≢g2)) ⟩
      updFun gidEq X g2 (doRd (X g2) j) g
    ≡⟨ sym (updFun-simp-≢ gidEq (updFun gidEq X g2 (doRd (X g2) j)) g1 g _ (≢-sym g≢g1)) ⟩
      updFun gidEq (updFun gidEq X g2 (doRd (X g2) j)) g1 (doRd (updFun gidEq X g2 (doRd (X g2) j) g1) i) g
    ∎
StepThd-i≢j {i = i} {j = j} {X = X} i≢j (rdGbl _ _ _ g1 _ _) (wrGbl _ _ g2 _ _ _ _) (wrGbl _ _ .g2 _ _ _ _) (rdGbl _ _ _ .g1 _ _) = refl , refl , refl , refl , funext (λ g → lem g (gidEq g g1) (gidEq g g2))
  where
  lem : ∀ g
    → Dec (g ≡ g1)
    → Dec (g ≡ g2)
    → updFun gidEq (updFun gidEq X g1 (doRd (X g1) i)) g2 (doWr (updFun gidEq X g1 (doRd (X g1) i) g2) j) g ≡
      updFun gidEq (updFun gidEq X g2 (doWr (X g2) j)) g1 (doRd (updFun gidEq X g2 (doWr (X g2) j) g1) i) g
  lem g (yes refl) (yes refl) = begin
      updFun gidEq (updFun gidEq X g (doRd (X g) i)) g (doWr (updFun gidEq X g (doRd (X g) i) g) j) g
    ≡⟨ updFun-simp-≡ gidEq (updFun gidEq X g (doRd (X g) i)) g _ ⟩
      doWr (updFun gidEq X g (doRd (X g) i) g) j
    ≡⟨ cong (λ a → doWr a j) (updFun-simp-≡ gidEq X g _) ⟩
      doWr (doRd (X g) i) j
    ≡⟨ MemEvs-≡ refl refl ⟩
      doRd (doWr (X g) j) i
    ≡⟨ sym (cong (λ a → doRd a i) (updFun-simp-≡ gidEq X g _)) ⟩
      doRd (updFun gidEq X g (doWr (X g) j) g) i
    ≡⟨ sym (updFun-simp-≡ gidEq (updFun gidEq X g (doWr (X g) j)) g _) ⟩
      updFun gidEq (updFun gidEq X g (doWr (X g) j)) g (doRd (updFun gidEq X g (doWr (X g) j) g) i) g
    ∎
  lem g (no g≢g1) (yes refl) = begin
      updFun gidEq (updFun gidEq X g1 (doRd (X g1) i)) g (doWr (updFun gidEq X g1 (doRd (X g1) i) g) j) g
    ≡⟨ updFun-simp-≡ gidEq (updFun gidEq X g1 (doRd (X g1) i)) g _ ⟩
      doWr (updFun gidEq X g1 (doRd (X g1) i) g) j
    ≡⟨ cong (λ a → doWr a j) (updFun-simp-≢ gidEq X g1 g _ (≢-sym g≢g1)) ⟩
      doWr (X g) j
    ≡⟨ sym (updFun-simp-≡ gidEq X g _) ⟩
      (updFun gidEq X g (doWr (X g) j)) g
    ≡⟨ sym (updFun-simp-≢ gidEq (updFun gidEq X g (doWr (X g) j)) g1 g _ (≢-sym g≢g1)) ⟩
      updFun gidEq (updFun gidEq X g (doWr (X g) j)) g1 (doRd (updFun gidEq X g (doWr (X g) j) g1) i) g
    ∎
  lem g (yes refl) (no g≢g2) = begin
      updFun gidEq (updFun gidEq X g (doRd (X g) i)) g2 (doWr (updFun gidEq X g (doRd (X g) i) g2) j) g
    ≡⟨ updFun-simp-≢ gidEq (updFun gidEq X g (doRd (X g) i)) g2 g _ (≢-sym g≢g2) ⟩
      (updFun gidEq X g (doRd (X g) i)) g
    ≡⟨ updFun-simp-≡ gidEq X g _ ⟩
      doRd (X g) i
    ≡⟨ cong (λ a → doRd a i) (sym (updFun-simp-≢ gidEq X g2 g _ (≢-sym g≢g2))) ⟩
      doRd (updFun gidEq X g2 (doWr (X g2) j) g) i
    ≡⟨ sym (updFun-simp-≡ gidEq (updFun gidEq X g2 (doWr (X g2) j)) g _) ⟩
      updFun gidEq (updFun gidEq X g2 (doWr (X g2) j)) g (doRd (updFun gidEq X g2 (doWr (X g2) j) g) i) g
    ∎
  lem g (no g≢g1) (no g≢g2) = begin
      updFun gidEq (updFun gidEq X g1 (doRd (X g1) i)) g2 (doWr (updFun gidEq X g1 (doRd (X g1) i) g2) j) g
    ≡⟨ updFun-simp-≢ gidEq (updFun gidEq X g1 (doRd (X g1) i)) g2 g _ (≢-sym g≢g2) ⟩
      updFun gidEq X g1 (doRd (X g1) i) g
    ≡⟨ updFun-simp-≢ gidEq X g1 g _ (≢-sym g≢g1) ⟩
      X g
    ≡⟨ sym (updFun-simp-≢ gidEq X g2 g _ (≢-sym g≢g2)) ⟩
      updFun gidEq X g2 (doWr (X g2) j) g
    ≡⟨ sym (updFun-simp-≢ gidEq (updFun gidEq X g2 (doWr (X g2) j)) g1 g _ (≢-sym g≢g1)) ⟩
      updFun gidEq (updFun gidEq X g2 (doWr (X g2) j)) g1 (doRd (updFun gidEq X g2 (doWr (X g2) j) g1) i) g
    ∎
StepThd-i≢j _ (wrGbl _ _ g1 _ _ _ _) (const _ _ _ _ _) (const _ _ _ _ _) (wrGbl _ _ .g1 _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (wrGbl _ _ g1 _ _ _ _) (binOp _ _ _ _ _ _) (binOp _ _ _ _ _ _) (wrGbl _ _ .g1 _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j _ (wrGbl _ _ g1 _ _ _ _) (rdReg _ _ _ _ _) (rdReg _ _ _ _ _) (wrGbl _ _ .g1 _ _ _ _) = refl , refl , refl , refl , refl
StepThd-i≢j {i = i} {j = j} {X = X} i≢j (wrGbl _ _ g1 _ _ _ _) (rdGbl _ _ _ g2 _ _) (rdGbl _ _ _ .g2 _ _) (wrGbl _ _ .g1 _ _ _ _) = refl , refl , refl , refl , funext (λ g → lem g (gidEq g g1) (gidEq g g2))
  where
  lem : ∀ g
    → Dec (g ≡ g1)
    → Dec (g ≡ g2)
    → updFun gidEq (updFun gidEq X g1 (doWr (X g1) i)) g2 (doRd (updFun gidEq X g1 (doWr (X g1) i) g2) j) g ≡
      updFun gidEq (updFun gidEq X g2 (doRd (X g2) j)) g1 (doWr (updFun gidEq X g2 (doRd (X g2) j) g1) i) g
  lem g (yes refl) (yes refl) = begin
      updFun gidEq (updFun gidEq X g (doWr (X g) i)) g (doRd (updFun gidEq X g (doWr (X g) i) g) j) g
    ≡⟨ updFun-simp-≡ gidEq (updFun gidEq X g (doWr (X g) i)) g _ ⟩
      doRd (updFun gidEq X g (doWr (X g) i) g) j
    ≡⟨ cong (λ a → doRd a j) (updFun-simp-≡ gidEq X g _) ⟩
      doRd (doWr (X g) i) j
    ≡⟨ MemEvs-≡ refl refl ⟩
      doWr (doRd (X g) j) i
    ≡⟨ sym (cong (λ a → doWr a i) (updFun-simp-≡ gidEq X g _)) ⟩
      doWr (updFun gidEq X g (doRd (X g) j) g) i
    ≡⟨ sym (updFun-simp-≡ gidEq (updFun gidEq X g (doRd (X g) j)) g _) ⟩
      updFun gidEq (updFun gidEq X g (doRd (X g) j)) g (doWr (updFun gidEq X g (doRd (X g) j) g) i) g
    ∎
  lem g (no g≢g1) (yes refl) = begin
      updFun gidEq (updFun gidEq X g1 (doWr (X g1) i)) g (doRd (updFun gidEq X g1 (doWr (X g1) i) g) j) g
    ≡⟨ updFun-simp-≡ gidEq (updFun gidEq X g1 (doWr (X g1) i)) g _ ⟩
      doRd (updFun gidEq X g1 (doWr (X g1) i) g) j
    ≡⟨ cong (λ a → doRd a j) (updFun-simp-≢ gidEq X g1 g _ (≢-sym g≢g1)) ⟩
      doRd (X g) j
    ≡⟨ sym (updFun-simp-≡ gidEq X g _) ⟩
      (updFun gidEq X g (doRd (X g) j)) g
    ≡⟨ sym (updFun-simp-≢ gidEq (updFun gidEq X g (doRd (X g) j)) g1 g _ (≢-sym g≢g1)) ⟩
      updFun gidEq (updFun gidEq X g (doRd (X g) j)) g1 (doWr (updFun gidEq X g (doRd (X g) j) g1) i) g
    ∎
  lem g (yes refl) (no g≢g2) = begin
      updFun gidEq (updFun gidEq X g (doWr (X g) i)) g2 (doRd (updFun gidEq X g (doWr (X g) i) g2) j) g
    ≡⟨ updFun-simp-≢ gidEq (updFun gidEq X g (doWr (X g) i)) g2 g _ (≢-sym g≢g2) ⟩
      (updFun gidEq X g (doWr (X g) i)) g
    ≡⟨ updFun-simp-≡ gidEq X g _ ⟩
      doWr (X g) i
    ≡⟨ cong (λ a → doWr a i) (sym (updFun-simp-≢ gidEq X g2 g _ (≢-sym g≢g2))) ⟩
      doWr (updFun gidEq X g2 (doRd (X g2) j) g) i
    ≡⟨ sym (updFun-simp-≡ gidEq (updFun gidEq X g2 (doRd (X g2) j)) g _) ⟩
      updFun gidEq (updFun gidEq X g2 (doRd (X g2) j)) g (doWr (updFun gidEq X g2 (doRd (X g2) j) g) i) g
    ∎
  lem g (no g≢g1) (no g≢g2) = begin
      updFun gidEq (updFun gidEq X g1 (doWr (X g1) i)) g2 (doRd (updFun gidEq X g1 (doWr (X g1) i) g2) j) g
    ≡⟨ updFun-simp-≢ gidEq (updFun gidEq X g1 (doWr (X g1) i)) g2 g _ (≢-sym g≢g2) ⟩
      updFun gidEq X g1 (doWr (X g1) i) g
    ≡⟨ updFun-simp-≢ gidEq X g1 g _ (≢-sym g≢g1) ⟩
      X g
    ≡⟨ sym (updFun-simp-≢ gidEq X g2 g _ (≢-sym g≢g2)) ⟩
      updFun gidEq X g2 (doRd (X g2) j) g
    ≡⟨ sym (updFun-simp-≢ gidEq (updFun gidEq X g2 (doRd (X g2) j)) g1 g _ (≢-sym g≢g1)) ⟩
      updFun gidEq (updFun gidEq X g2 (doRd (X g2) j)) g1 (doWr (updFun gidEq X g2 (doRd (X g2) j) g1) i) g
    ∎
StepThd-i≢j {i = i} {j = j} {X = X} i≢j (wrGbl _ _ g1 _ _ _ _) (wrGbl _ _ g2 _ _ _ no-race-ij) (wrGbl _ _ .g2 _ _ _ _) (wrGbl _ _ .g1 _ _ _ _) = refl , refl , refl , refl , funext (λ g → lem g (gidEq g g1) (gidEq g g2))
  where
  simp-wr : ∀ g → MemEvs.wr (updFun gidEq X g (doWr (X g) i) g) ≡ (i , ! i)
  simp-wr g = begin
      MemEvs.wr (updFun gidEq X g (doWr (X g) i) g)
    ≡⟨ cong MemEvs.wr (updFun-simp-≡ gidEq X g _) ⟩
      i , ! i
    ∎

  i≡j : ∀ g → noRacingWr j (MemEvs.wr (updFun gidEq X g (doWr (X g) i) g)) → i ≡ j
  i≡j g p = cong mkTid step2
    where
    step1 : not (Dec.does (Tid.val i ≟ Tid.val j)) ≡ false
    step1 = subst (λ a → noRacingWr j a) (simp-wr g) p

    step2 : Tid.val i ≡ Tid.val j
    step2 = from-does-true (Tid.val i ≡ Tid.val j) (Tid.val i ≟ Tid.val j) (not-false step1)

  lem : ∀ g
    → Dec (g ≡ g1)
    → Dec (g ≡ g2)
    → updFun gidEq (updFun gidEq X g1 (doWr (X g1) i)) g2 (doWr (updFun gidEq X g1 (doWr (X g1) i) g2) j) g ≡
      updFun gidEq (updFun gidEq X g2 (doWr (X g2) j)) g1 (doWr (updFun gidEq X g2 (doWr (X g2) j) g1) i) g
  lem g (yes refl) (yes refl) = begin
      updFun gidEq (updFun gidEq X g (doWr (X g) i)) g (doWr (updFun gidEq X g (doWr (X g) i) g) j) g
    ≡⟨ updFun-simp-≡ gidEq (updFun gidEq X g (doWr (X g) i)) g _ ⟩
      doWr (updFun gidEq X g (doWr (X g) i) g) j
    ≡⟨ cong (λ a → doWr a j) (updFun-simp-≡ gidEq X g _) ⟩
      doWr (doWr (X g) i) j
    ≡⟨ MemEvs-≡ refl (cong (λ k → k , ! k) (sym (i≡j g no-race-ij))) ⟩
      doWr (doWr (X g) j) i
    ≡⟨ sym (cong (λ a → doWr a i) (updFun-simp-≡ gidEq X g _)) ⟩
      doWr (updFun gidEq X g (doWr (X g) j) g) i
    ≡⟨ sym (updFun-simp-≡ gidEq (updFun gidEq X g (doWr (X g) j)) g _) ⟩
      updFun gidEq (updFun gidEq X g (doWr (X g) j)) g (doWr (updFun gidEq X g (doWr (X g) j) g) i) g
    ∎
  lem g (no g≢g1) (yes refl) = begin
      updFun gidEq (updFun gidEq X g1 (doWr (X g1) i)) g (doWr (updFun gidEq X g1 (doWr (X g1) i) g) j) g
    ≡⟨ updFun-simp-≡ gidEq (updFun gidEq X g1 (doWr (X g1) i)) g _ ⟩
      doWr (updFun gidEq X g1 (doWr (X g1) i) g) j
    ≡⟨ cong (λ a → doWr a j) (updFun-simp-≢ gidEq X g1 g _ (≢-sym g≢g1)) ⟩
      doWr (X g) j
    ≡⟨ sym (updFun-simp-≡ gidEq X g _) ⟩
      (updFun gidEq X g (doWr (X g) j)) g
    ≡⟨ sym (updFun-simp-≢ gidEq (updFun gidEq X g (doWr (X g) j)) g1 g _ (≢-sym g≢g1)) ⟩
      updFun gidEq (updFun gidEq X g (doWr (X g) j)) g1 (doWr (updFun gidEq X g (doWr (X g) j) g1) i) g
    ∎
  lem g (yes refl) (no g≢g2) = begin
      updFun gidEq (updFun gidEq X g (doWr (X g) i)) g2 (doWr (updFun gidEq X g (doWr (X g) i) g2) j) g
    ≡⟨ updFun-simp-≢ gidEq (updFun gidEq X g (doWr (X g) i)) g2 g _ (≢-sym g≢g2) ⟩
      (updFun gidEq X g (doWr (X g) i)) g
    ≡⟨ updFun-simp-≡ gidEq X g _ ⟩
      doWr (X g) i
    ≡⟨ cong (λ a → doWr a i) (sym (updFun-simp-≢ gidEq X g2 g _ (≢-sym g≢g2))) ⟩
      doWr (updFun gidEq X g2 (doWr (X g2) j) g) i
    ≡⟨ sym (updFun-simp-≡ gidEq (updFun gidEq X g2 (doWr (X g2) j)) g _) ⟩
      updFun gidEq (updFun gidEq X g2 (doWr (X g2) j)) g (doWr (updFun gidEq X g2 (doWr (X g2) j) g) i) g
    ∎
  lem g (no g≢g1) (no g≢g2) = begin
      updFun gidEq (updFun gidEq X g1 (doWr (X g1) i)) g2 (doWr (updFun gidEq X g1 (doWr (X g1) i) g2) j) g
    ≡⟨ updFun-simp-≢ gidEq (updFun gidEq X g1 (doWr (X g1) i)) g2 g _ (≢-sym g≢g2) ⟩
      updFun gidEq X g1 (doWr (X g1) i) g
    ≡⟨ updFun-simp-≢ gidEq X g1 g _ (≢-sym g≢g1) ⟩
      X g
    ≡⟨ sym (updFun-simp-≢ gidEq X g2 g _ (≢-sym g≢g2)) ⟩
      updFun gidEq X g2 (doWr (X g2) j) g
    ≡⟨ sym (updFun-simp-≢ gidEq (updFun gidEq X g2 (doWr (X g2) j)) g1 g _ (≢-sym g≢g1)) ⟩
      updFun gidEq (updFun gidEq X g2 (doWr (X g2) j)) g1 (doWr (updFun gidEq X g2 (doWr (X g2) j) g1) i) g
    ∎

diamond : ∀ ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2
  → StepProgRefl ℂ ℰ X P ℰ1 X1 P1
  → StepProgRefl ℂ ℰ X P ℰ2 X2 P2
  → ∃[ ℰ' ] ∃[ X' ] ∃[ P' ] StepProgRefl ℂ ℰ1 X1 P1 ℰ' X' P' × StepProgRefl ℂ ℰ2 X2 P2 ℰ' X' P'
diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (refl _ _ _) (refl _ _ _) = ℰ , X , P , refl _ _ _ , refl _ _ _
diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (refl _ _ _) (schd i .ℰ .X .P E T E' X' T' ℰi≡E Pi≡T x) = _ , _ , _ , schd i ℰ X P E T E' X' T' ℰi≡E Pi≡T x , refl _ _ _
diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (refl _ _ _) (sync I .ℰ .X .P p) = _ , _ , _ , sync I ℰ X P p , refl _ _ _
diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (schd i .ℰ .X .P E T E' X' T' ℰi≡E Pi≡T x) (refl _ _ _) = _ , _ , _ , refl _ _ _ , schd i ℰ X P E T E' X' T' ℰi≡E Pi≡T x
diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (sync I .ℰ .X .P p) (refl _ _ _) = _ , _ , _ , refl _ _ _ , sync I ℰ X P p
diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (schd i .ℰ .X .P E1 T1 E1' .X1 T1' ℰi≡E1 Pi≡T1 x1)
                                  (schd j .ℰ .X .P E2 T2 E2' .X2 T2' ℰj≡E2 Pj≡T2 x2) with Tid.val i ≟ Tid.val j
... | yes refl = ℰ1 , X1 , P1 , refl _ _ _ , rhs
  where
  E1≡E2 : E1 ≡ E2
  E1≡E2 = trans (sym ℰi≡E1) ℰj≡E2

  T1≡T2 : T1 ≡ T2
  T1≡T2 = trans (sym Pi≡T1) Pj≡T2

  eqs : E1' ≡ E2' × X1 ≡ X2 × T1' ≡ T2'
  eqs with E1≡E2 | T1≡T2
  ... | refl | refl = StepThd-i≡j x1 x2

  ℰ1≡ℰ2 : E1' ≡ E2' → ℰ1 ≡ ℰ2
  ℰ1≡ℰ2 refl = refl

  P1≡P2 : T1' ≡ T2' → P1 ≡ P2
  P1≡P2 refl = refl

  rhs : StepProgRefl ℂ ℰ2 X2 P2 ℰ1 X1 P1
  rhs = transport (cong₃ (λ a b c → StepProgRefl ℂ a b c ℰ1 X1 P1) (ℰ1≡ℰ2 (proj₁ eqs)) (proj₁ (proj₂ eqs)) (P1≡P2 (proj₂ (proj₂ eqs)))) (refl ℰ1 X1 P1)
... | no i≢j = {!!}
diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (schd i ℰ₁ X₁ P₁ E T E' X' T' p q x) (sync I ℰ₂ X₂ P₂ r) = {!!}
diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (sync I ℰ₁ X₁ P₁ r) (schd i ℰ₂ X₂ P₂ E T E' X' T' p q x) = {!!}
diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (sync I ℰ₁ X₁ P₁ r) (sync I₁ ℰ₂ X₂ P₂ r₁) = {!!}
