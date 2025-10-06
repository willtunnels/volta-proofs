module KernelCheck.Confluence where

open import Function.Base using (_∘_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; _≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties
open import Data.Bool using (Bool; true; false; not)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
import Data.Product.Properties
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import KernelCheck.Prog
open import KernelCheck.Util
open import KernelCheck.DecSet

<-Rd : Tid → Rd → Rd → Set
<-Rd i r1 r2 = noRacingRd i r2 → noRacingRd i r1

<-Wr : Tid → Wr → Wr → Set
<-Wr i w1 w2 = noRacingWr i w2 → noRacingWr i w1

<-MemEvs : Tid → MemEvs → MemEvs → Set
<-MemEvs i X1 X2 = <-Rd i (X1 .MemEvs.rd) (X2 .MemEvs.rd) × <-Wr i (X1 .MemEvs.wr) (X2 .MemEvs.wr)

-- X1 < X2 iff a race for i under X1 implies a race for i under X2
<-Mem : Tid → Mem → Mem → Set
<-Mem i X1 X2 = ∀ g → <-MemEvs i (X1 g) (X2 g)

postulate
  StepThd-<-Mem : ∀ {ℂ i R1 G1 X1 T1 R2 G2 X2 T2}
    → StepThd ℂ i (just (R1 , G1 , X1 , T1)) (just (R2 , G2 , X2 , T2))
    → ∀ j → <-Mem j X1 X2

  StepThd-mono : ∀ {ℂ i R G X1 X2 T}
    → <-Mem i X1 X2
    → StepThd ℂ i (just (R , G , X1 , T)) nothing
    → StepThd ℂ i (just (R , G , X2 , T)) nothing

StepThd-≢-comm : ∀ {ℂ i j R1 G1 T1 R1' G1' T1' R2 G2 T2 R2' G2' T2' X X'1 X'2}
  → i ≢ j
  → StepThd ℂ i (just (R1 , G1 , X , T1)) (just (R1' , G1' , X'1 , T1'))
  → StepThd ℂ j (just (R2 , G2 , X , T2)) (just (R2' , G2' , X'2 , T2'))
  → (∃[ X'' ] StepThd ℂ j (just (R2 , G2 , X'1 , T2)) (just (R2' , G2' , X'' , T2')) ×
              StepThd ℂ i (just (R1 , G1 , X'2 , T1)) (just (R1' , G1' , X'' , T1')))
  ⊎ (StepThd ℂ j (just (R2 , G2 , X'1 , T2)) nothing ×
     StepThd ℂ i (just (R1 , G1 , X'2 , T1)) nothing)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (const _ _ _ r c _) (const _ _ _ r₁ c₁ _) =
  inj₁ (X , const R2 G2 X r₁ c₁ T2' , const R1 G1 X r c T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (const _ _ _ r c _) (binOp _ _ _ r₁ r1 r2 _) =
  inj₁ (X , binOp R2 G2 X r₁ r1 r2 T2' , const R1 G1 X r c T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (const _ _ _ r c _) (rdReg _ _ _ r1 r2 _) =
  inj₁ (X , rdReg R2 G2 X r1 r2 T2' , const R1 G1 X r c T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (const _ _ _ r c _) (rdGbl _ _ _ r₁ g _ x) =
  inj₁ ((X [ g ↦ doRd (X g) j ]) ,
       rdGbl R2 G2 X r₁ g T2' x ,
       const R1 G1 (X [ g ↦ doRd (X g) j ]) r c T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (const _ _ _ r c _) (wrGbl _ _ _ g r₁ _ x x₁) =
  inj₁ ((X [ g ↦ doWr (X g) j ]) ,
       wrGbl R2 G2 X g r₁ T2' x x₁ ,
       const R1 G1 (X [ g ↦ doWr (X g) j ]) r c T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (binOp _ _ _ r r1 r2 _) (const _ _ _ r₁ c _) =
  inj₁ (X , const R2 G2 X r₁ c T2' , binOp R1 G1 X r r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (binOp _ _ _ r r1 r2 _) (binOp _ _ _ r₁ r3 r4 _) =
  inj₁ (X , binOp R2 G2 X r₁ r3 r4 T2' , binOp R1 G1 X r r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (binOp _ _ _ r r1 r2 _) (rdReg _ _ _ r3 r4 _) =
  inj₁ (X , rdReg R2 G2 X r3 r4 T2' , binOp R1 G1 X r r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (binOp _ _ _ r r1 r2 _) (rdGbl _ _ _ r₁ g _ x) =
  inj₁ ((X [ g ↦ doRd (X g) j ]) ,
       rdGbl R2 G2 X r₁ g T2' x ,
       binOp R1 G1 (X [ g ↦ doRd (X g) j ]) r r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (binOp _ _ _ r r1 r2 _) (wrGbl _ _ _ g r₁ _ x x₁) =
  inj₁ ((X [ g ↦ doWr (X g) j ]) ,
       wrGbl R2 G2 X g r₁ T2' x x₁ ,
       binOp R1 G1 (X [ g ↦ doWr (X g) j ]) r r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdReg _ _ _ r1 r2 _) (const _ _ _ r c _) =
  inj₁ (X , const R2 G2 X r c T2' , rdReg R1 G1 X r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdReg _ _ _ r1 r2 _) (binOp _ _ _ r r3 r4 _) =
  inj₁ (X , binOp R2 G2 X r r3 r4 T2' , rdReg R1 G1 X r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdReg _ _ _ r1 r2 _) (rdReg _ _ _ r3 r4 _) =
  inj₁ (X , rdReg R2 G2 X r3 r4 T2' , rdReg R1 G1 X r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdReg _ _ _ r1 r2 _) (rdGbl _ _ _ r g _ x) =
  inj₁ ((X [ g ↦ doRd (X g) j ]) ,
       rdGbl R2 G2 X r g T2' x ,
       rdReg R1 G1 (X [ g ↦ doRd (X g) j ]) r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdReg _ _ _ r1 r2 _) (wrGbl _ _ _ g r _ x x₁) =
  inj₁ ((X [ g ↦ doWr (X g) j ]) ,
       wrGbl R2 G2 X g r T2' x x₁ ,
       rdReg R1 G1 (X [ g ↦ doWr (X g) j ]) r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdGbl _ _ _ r g _ x) (const _ _ _ r₁ c _) =
  inj₁ ((X [ g ↦ doRd (X g) i ]) ,
    const R2 G2 (X [ g ↦ doRd (X g) i ]) r₁ c T2' ,
    rdGbl R1 G1 X r g T1' x)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdGbl _ _ _ r g _ x) (binOp _ _ _ r₁ r1 r2 _) =
  inj₁ ((X [ g ↦ doRd (X g) i ]) ,
       binOp R2 G2 (X [ g ↦ doRd (X g) i ]) r₁ r1 r2 T2' ,
       rdGbl R1 G1 X r g T1' x)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdGbl _ _ _ r g _ x) (rdReg _ _ _ r1 r2 _) =
  inj₁ ((X [ g ↦ doRd (X g) i ]) ,
       rdReg R2 G2 (X [ g ↦ doRd (X g) i ]) r1 r2 T2' ,
       rdGbl R1 G1 X r g T1' x)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdGbl _ _ _ r g _ x) (rdGbl _ _ _ r₁ g₁ _ x₁) =
  inj₁ ((X [ g ↦ doRd (X g) i ] [ g₁ ↦ doRd ((X [ g ↦ doRd (X g) i ]) g₁) j ]) ,
       rdGbl R2 G2 (X [ g ↦ doRd (X g) i ]) r₁ g₁ T2' lhs-noRace ,
       cast rhs-step≡ (rdGbl R1 G1 (X [ g₁ ↦ doRd (X g₁) j ]) r g T1' rhs-noRace))
  where
  lhs-noRace : noRacingWr j (MemEvs.wr ((X [ g ↦ doRd (X g) i ]) g₁))
  lhs-noRace = cast (cong (λ a → noRacingWr j a) eq) x₁
    where
    eq : MemEvs.wr (X g₁) ≡ MemEvs.wr ((X [ g ↦ doRd (X g) i ]) g₁)
    eq with gidEq g g₁
    ... | yes refl = begin
        MemEvs.wr (X g)
      ≡⟨ refl ⟩
        MemEvs.wr (doRd (X g) i)
      ≡⟨ cong MemEvs.wr (sym ([↦]-simp-≡ _ _ _)) ⟩
        MemEvs.wr ((X [ g ↦ doRd (X g) i ]) g)
      ∎
    ... | no g≢g₁ = begin
        MemEvs.wr (X g₁)
      ≡⟨ cong MemEvs.wr (sym ([↦]-simp-≢ _ _ _ _ g≢g₁)) ⟩
        MemEvs.wr ((X [ g ↦ doRd (X g) i ]) g₁)
      ∎

  rhs-noRace : noRacingWr i (MemEvs.wr ((X [ g₁ ↦ doRd (X g₁) j ]) g))
  rhs-noRace = cast (cong (λ a → noRacingWr i a) eq) x
    where
    eq : MemEvs.wr (X g) ≡ MemEvs.wr ((X [ g₁ ↦ doRd (X g₁) j ]) g)
    eq with gidEq g₁ g
    ... | yes refl = begin
        MemEvs.wr (X g₁)
      ≡⟨ refl ⟩
        MemEvs.wr (doRd (X g₁) j)
      ≡⟨ cong MemEvs.wr (sym ([↦]-simp-≡ _ _ _)) ⟩
        MemEvs.wr ((X [ g₁ ↦ doRd (X g₁) j ]) g₁)
      ∎
    ... | no g≢g = begin
        MemEvs.wr (X g)
      ≡⟨ cong MemEvs.wr (sym ([↦]-simp-≢ _ _ _ _ g≢g)) ⟩
        MemEvs.wr ((X [ g₁ ↦ doRd (X g₁) j ]) g)
      ∎

  mem≡-1 : ∀ g
    → (X [ g ↦ doRd (X g) j ] [ g ↦ doRd ((X [ g ↦ doRd (X g) j ]) g) i ]) g ≡
      (X [ g ↦ doRd (X g) i ] [ g ↦ doRd ((X [ g ↦ doRd (X g) i ]) g) j ]) g
  mem≡-1 g = begin
      (X [ g ↦ doRd (X g) j ] [ g ↦ doRd ((X [ g ↦ doRd (X g) j ]) g) i ]) g
    ≡⟨ [↦]-simp-≡ _ _ _ ⟩
      doRd ((X [ g ↦ doRd (X g) j ]) g) i
    ≡⟨ cong (λ a → doRd a i) ([↦]-simp-≡ _ _ _) ⟩
      doRd (doRd (X g) j) i
    ≡⟨ doRd-comm (evs (λ z → MemEvs.rd (X g) z) (X g .MemEvs.wr)) (≢-sym i≢j) ⟩
      doRd (doRd (X g) i) j
    ≡⟨ cong (λ a → doRd a j) (sym ([↦]-simp-≡ _ _ _)) ⟩
      doRd ((X [ g ↦ doRd (X g) i ]) g) j
    ≡⟨ sym ([↦]-simp-≡ _ _ _) ⟩
      (X [ g ↦ doRd (X g) i ] [ g ↦ doRd ((X [ g ↦ doRd (X g) i ]) g) j ]) g
    ∎

  mem≡-2 : ∀ g g₁
    → g ≢ g₁
    → (X [ g ↦ doRd (X g) j ] [ g ↦ doRd ((X [ g ↦ doRd (X g) j ]) g) i ]) g₁ ≡
      (X [ g ↦ doRd (X g) i ] [ g ↦ doRd ((X [ g ↦ doRd (X g) i ]) g) j ]) g₁
  mem≡-2 g g₁ g≢g₁ = begin
      (X [ g ↦ doRd (X g) j ] [ g ↦ doRd ((X [ g ↦ doRd (X g) j ]) g) i ]) g₁
    ≡⟨ [↦]-simp-≢ _ _ _ _ g≢g₁ ⟩
      (X [ g ↦ doRd (X g) j ]) g₁
    ≡⟨ [↦]-simp-≢ _ _ _ _ g≢g₁ ⟩
      X g₁
    ≡⟨ sym ([↦]-simp-≢ _ _ _ _ g≢g₁) ⟩
      (X [ g ↦ doRd (X g) i ]) g₁
    ≡⟨ sym ([↦]-simp-≢ _ _ _ _ g≢g₁) ⟩
      (X [ g ↦ doRd (X g) i ] [ g ↦ doRd ((X [ g ↦ doRd (X g) i ]) g) j ]) g₁
    ∎

  mem≡-1,2 : ∀ g g₁
    → (X [ g ↦ doRd (X g) j ] [ g ↦ doRd ((X [ g ↦ doRd (X g) j ]) g) i ]) g₁ ≡
      (X [ g ↦ doRd (X g) i ] [ g ↦ doRd ((X [ g ↦ doRd (X g) i ]) g) j ]) g₁
  mem≡-1,2 g g₁ with gidEq g g₁
  ... | yes refl = mem≡-1 g
  ... | no g≢g₁ = mem≡-2 g g₁ g≢g₁

  mem≡-3 : ∀ g g₁
    → g ≢ g₁
    → ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doRd ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g ≡
      ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doRd (X g) i ]) g₁) j ]) g
  mem≡-3 g g₁ g≢g₁ = begin
      ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doRd ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g
    ≡⟨ [↦]-simp-≡ _ _ _ ⟩
      doRd ((X [ g₁ ↦ doRd (X g₁) j ]) g) i
    ≡⟨ cong (λ a → doRd a i) ([↦]-simp-≢ _ _ _ _ (≢-sym g≢g₁)) ⟩
      doRd (X g) i
    ≡⟨ sym ([↦]-simp-≡ _ _ _) ⟩
      (X [ g ↦ doRd (X g) i ]) g
    ≡⟨ sym ([↦]-simp-≢ (X [ g ↦ doRd (X g) i ]) g₁ g _ (≢-sym g≢g₁)) ⟩ --
      ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doRd (X g) i ]) g₁) j ]) g
    ∎

  mem≡-4 : ∀ g g₁
    → g ≢ g₁
    → ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doRd ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g₁ ≡
      ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doRd (X g) i ]) g₁) j ]) g₁
  mem≡-4 g g₁ g≢g₁ = begin
      ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doRd ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g₁
    ≡⟨ [↦]-simp-≢ _ _ _ _ g≢g₁ ⟩
      (X [ g₁ ↦ doRd (X g₁) j ]) g₁
    ≡⟨ [↦]-simp-≡ _ _ _ ⟩
      doRd (X g₁) j
    ≡⟨ sym (cong (λ a → doRd a j) ([↦]-simp-≢ _ _ _ _ g≢g₁)) ⟩
      doRd ((X [ g ↦ doRd (X g) i ]) g₁) j
    ≡⟨ sym ([↦]-simp-≡ _ _ _) ⟩
      ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doRd (X g) i ]) g₁) j ]) g₁
    ∎

  mem≡-5 : ∀ g g₁ g₂
    → g ≢ g₁
    → g ≢ g₂
    → g₁ ≢ g₂
    → ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doRd ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g₂ ≡
      ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doRd (X g) i ]) g₁) j ]) g₂
  mem≡-5 g g₁ g₂ g≢g₁ g≢g₂ g₁≢g₂ = begin
      ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doRd ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g₂
    ≡⟨ [↦]-simp-≢ _ _ _ _ g≢g₂ ⟩
      (X [ g₁ ↦ doRd (X g₁) j ]) g₂
    ≡⟨ [↦]-simp-≢ _ _ _ _ g₁≢g₂ ⟩
      X g₂
    ≡⟨ sym ([↦]-simp-≢ _ _ _ _ g≢g₂) ⟩
      (X [ g ↦ doRd (X g) i ]) g₂
    ≡⟨ sym ([↦]-simp-≢ _ _ _ _ g₁≢g₂) ⟩
      ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doRd (X g) i ]) g₁) j ]) g₂
    ∎

  mem≡-3,4,5 : ∀ g g₁ g₂
    → g ≢ g₁
    → ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doRd ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g₂ ≡
      ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doRd (X g) i ]) g₁) j ]) g₂
  mem≡-3,4,5 g g₁ g₂ g≢g₁ with gidEq g g₂ | gidEq g₁ g₂
  ... | yes refl | yes refl = ⊥-elim (g≢g₁ refl)
  ... | yes refl | no g₁≢g₂ = mem≡-3 g₂ g₁ g≢g₁
  ... | no g≢g₂ | yes refl = mem≡-4 g g₂ g≢g₂
  ... | no g≢g₂ | no g₁≢g₂ = mem≡-5 g g₁ g₂ g≢g₁ g≢g₂ g₁≢g₂

  mem≡ : ∀ g g₁ g₂
    → ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doRd ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g₂ ≡
      ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doRd (X g) i ]) g₁) j ]) g₂
  mem≡ g g₁ g₂ with gidEq g g₁
  ... | yes refl = mem≡-1,2 g g₂
  ... | no g≢g₁ = mem≡-3,4,5 g g₁ g₂ g≢g₁

  rhs-step≡ :
    StepThd ℂ i
      (just (R1 , G1 , (X [ g₁ ↦ doRd (X g₁) j ]) , (rdGbl r g ⨟ T1')))
      (just ((R1 [ r ↦ G1 g ]) , G1 , (X [ g₁ ↦ doRd (X g₁) j ] [ g ↦ doRd ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) , T1'))
    ≡
    StepThd ℂ i
      (just (R1 , G1 , (X [ g₁ ↦ doRd (X g₁) j ]) , (rdGbl r g ⨟ T1')))
      (just ((R1 [ r ↦ G1 g ]) , G1 , (X [ g ↦ doRd (X g) i ] [ g₁ ↦ doRd ((X [ g ↦ doRd (X g) i ]) g₁) j ]) , T1'))
  rhs-step≡ = cong (λ a →
    StepThd ℂ i
      (just (R1 , G1 , (X [ g₁ ↦ doRd (X g₁) j ]) , (rdGbl r g ⨟ T1')))
      (just ((R1 [ r ↦ G1 g ]) , G1 , a , T1')))
    (funext (mem≡ g g₁))
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdGbl _ _ _ r g _ x) (wrGbl _ _ _ g₁ r₁ _ x₁ x₂) with gidEq g g₁
... | yes refl = inj₂ (wrGblBad R2 G2 (X [ g ↦ doRd (X g) i ]) g r₁ T2' (inj₁ race1) , rdGblBad R1 G1 (X [ g ↦ doWr (X g) j ]) r g T1' race2)
  where
  race1 : ¬ noRacingRd j (MemEvs.rd ((X [ g ↦ doRd (X g) i ]) g))
  race1 = yesRacingRd→¬noRacingRd j (MemEvs.rd ((X [ g ↦ doRd (X g) i ]) g)) (i , cast (cong (j ∈_) (sym lem)) (∈! j i (≢-sym i≢j)))
    where
    lem : MemEvs.rd ((X [ g ↦ doRd (X g) i ]) g) i ≡ ! i
    lem = begin
        MemEvs.rd ((X [ g ↦ doRd (X g) i ]) g) i
      ≡⟨ cong (λ a → MemEvs.rd a i) ([↦]-simp-≡ _ _ _) ⟩
        MemEvs.rd (doRd (X g) i) i
      ≡⟨ [↦]-simp-≡ _ _ _ ⟩
        ! i
      ∎

  race2 : ¬ noRacingWr i (MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g))
  race2 = yesRacingWr→¬noRacingWr i (MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g)) (fst , snd)
    where
    lem : MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g) ≡ (j , ! j)
    lem = cong MemEvs.wr ([↦]-simp-≡ _ _ _)

    fst : i ≢ MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g) .proj₁
    fst = cast (cong (i ≢_) (sym (Data.Product.Properties.×-≡,≡←≡ lem .proj₁))) i≢j

    snd : i ∈ MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g) .proj₂
    snd = cast (cong (i ∈_) (sym (Data.Product.Properties.×-≡,≡←≡ lem .proj₂))) (∈! i j i≢j)
... | no g≢g₁ = inj₁ ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doRd (X g) i ]) g₁) j ] ,
                      wrGbl R2 G2 (X [ g ↦ doRd (X g) i ]) g₁ r₁ T2' noRace1 noRace2 ,
                      cast rhs-step≡ (rdGbl R1 G1 (X [ g₁ ↦ doWr (X g₁) j ]) r g T1' noRace3))
    where
    noRace1 : noRacingRd j (MemEvs.rd ((X [ g ↦ doRd (X g) i ]) g₁))
    noRace1 = cast (cong (λ a → noRacingRd j (MemEvs.rd a)) (sym ([↦]-simp-≢ _ _ _ _ g≢g₁))) x₁

    noRace2 : noRacingWr j (MemEvs.wr ((X [ g ↦ doRd (X g) i ]) g₁))
    noRace2 = cast (cong (λ a → noRacingWr j (MemEvs.wr a)) (sym ([↦]-simp-≢ _ _ _ _ g≢g₁))) x₂

    noRace3 : noRacingWr i (MemEvs.wr ((X [ g₁ ↦ doWr (X g₁) j ]) g))
    noRace3 = cast (cong (λ a → noRacingWr i (MemEvs.wr a)) (sym ([↦]-simp-≢ _ _ _ _ (≢-sym g≢g₁)))) x

    mem≡-1 : ∀ g g₁
      → g ≢ g₁
      → ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doRd ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) g ≡
        ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doRd (X g) i ]) g₁) j ]) g
    mem≡-1 g g₁ g≢g₁ = begin
        ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doRd ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) g
      ≡⟨ [↦]-simp-≡ _ _ _ ⟩
        doRd ((X [ g₁ ↦ doWr (X g₁) j ]) g) i
      ≡⟨ cong (λ a → doRd a i) ([↦]-simp-≢ _ _ _ _ (≢-sym g≢g₁)) ⟩
        doRd (X g) i
      ≡⟨ sym ([↦]-simp-≡ _ _ _) ⟩
        (X [ g ↦ doRd (X g) i ]) g
      ≡⟨ sym ([↦]-simp-≢ (X [ g ↦ doRd (X g) i ]) g₁ g _ (≢-sym g≢g₁)) ⟩
        ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doRd (X g) i ]) g₁) j ]) g
      ∎

    mem≡-2 : ∀ g g₁
      → g ≢ g₁
      → ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doRd ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) g₁ ≡
        ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doRd (X g) i ]) g₁) j ]) g₁
    mem≡-2 g g₁ g≢g₁ = begin
        ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doRd ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) g₁
      ≡⟨ [↦]-simp-≢ _ _ _ _ g≢g₁ ⟩
        (X [ g₁ ↦ doWr (X g₁) j ]) g₁
      ≡⟨ [↦]-simp-≡ _ _ _ ⟩
        doWr (X g₁) j
      ≡⟨ sym (cong (λ a → doWr a j) ([↦]-simp-≢ _ _ _ _ g≢g₁)) ⟩
        doWr ((X [ g ↦ doRd (X g) i ]) g₁) j
      ≡⟨ sym ([↦]-simp-≡ _ _ _) ⟩
        ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doRd (X g) i ]) g₁) j ]) g₁
      ∎

    mem≡-3 : ∀ g g₁ g₂
      → g ≢ g₁
      → g ≢ g₂
      → g₁ ≢ g₂
      → ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doRd ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) g₂ ≡
        ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doRd (X g) i ]) g₁) j ]) g₂
    mem≡-3 g g₁ g₂ g≢g₁ g≢g₂ g₁≢g₂ = begin
        ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doRd ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) g₂
      ≡⟨ [↦]-simp-≢ _ _ _ _ g≢g₂ ⟩
        (X [ g₁ ↦ doWr (X g₁) j ]) g₂
      ≡⟨ [↦]-simp-≢ _ _ _ _ g₁≢g₂ ⟩
        X g₂
      ≡⟨ sym ([↦]-simp-≢ _ _ _ _ g≢g₂) ⟩
        (X [ g ↦ doRd (X g) i ]) g₂
      ≡⟨ sym ([↦]-simp-≢ _ _ _ _ g₁≢g₂) ⟩
        ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doRd (X g) i ]) g₁) j ]) g₂
      ∎

    mem≡-1,2,3 : ∀ g g₁ g₂
      → g ≢ g₁
      → ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doRd ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) g₂ ≡
        ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doRd (X g) i ]) g₁) j ]) g₂
    mem≡-1,2,3 g g₁ g₂ g≢g₁ with gidEq g g₂ | gidEq g₁ g₂
    ... | yes refl | yes refl = ⊥-elim (g≢g₁ refl)
    ... | yes refl | no g₁≢g₂ = mem≡-1 g₂ g₁ g≢g₁
    ... | no g≢g₂ | yes refl = mem≡-2 g g₂ g≢g₂
    ... | no g≢g₂ | no g₁≢g₂ = mem≡-3 g g₁ g₂ g≢g₁ g≢g₂ g₁≢g₂

    mem≡ : ∀ g₂
      → ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doRd ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) g₂ ≡
        ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doRd (X g) i ]) g₁) j ]) g₂
    mem≡ g₂ = mem≡-1,2,3 g g₁ g₂ g≢g₁

    rhs-step≡ :
      StepThd ℂ i
        (just (R1 , G1 , (X [ g₁ ↦ doWr (X g₁) j ]) , (rdGbl r g ⨟ T1')))
        (just ((R1 [ r ↦ G1 g ]) , G1 , ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doRd ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) , T1'))
      ≡
      StepThd ℂ i
        (just (R1 , G1 , (X [ g₁ ↦ doWr (X g₁) j ]) , (rdGbl r g ⨟ T1')))
        (just ((R1 [ r ↦ G1 g ]) , G1 , ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doRd (X g) i ]) g₁) j ]) , T1'))
    rhs-step≡ = cong (λ a →
      StepThd ℂ i
        (just (R1 , G1 , (X [ g₁ ↦ doWr (X g₁) j ]) , (rdGbl r g ⨟ T1')))
        (just ((R1 [ r ↦ G1 g ]) , G1 , a , T1')))
      (funext mem≡)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (wrGbl _ _ _ g r _ x x₁) (const _ _ _ r₁ c _) =
  inj₁ ((X [ g ↦ doWr (X g) i ]) ,
       const R2 G2 (X [ g ↦ doWr (X g) i ]) r₁ c T2' ,
       wrGbl R1 G1 X g r T1' x x₁)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (wrGbl _ _ _ g r _ x x₁) (binOp _ _ _ r₁ r1 r2 _) =
  inj₁ ((X [ g ↦ doWr (X g) i ]) ,
       binOp R2 G2 (X [ g ↦ doWr (X g) i ]) r₁ r1 r2 T2' ,
       wrGbl R1 G1 X g r T1' x x₁)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (wrGbl _ _ _ g r _ x x₁) (rdReg _ _ _ r1 r2 _) =
  inj₁ ((X [ g ↦ doWr (X g) i ]) ,
       rdReg R2 G2 (X [ g ↦ doWr (X g) i ]) r1 r2 T2' ,
       wrGbl R1 G1 X g r T1' x x₁)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (wrGbl _ _ _ g r _ x x₁) (rdGbl _ _ _ r₁ g₁ _ x₂) with gidEq g g₁
... | yes refl = inj₂ (rdGblBad R2 G2 (X [ g ↦ doWr (X g) i ]) r₁ g T2' race1 , wrGblBad R1 G1 (X [ g ↦ doRd (X g) j ]) g r T1' (inj₁ race2))
  where
  race1 : ¬ noRacingWr j (MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g))
  race1 = yesRacingWr→¬noRacingWr j (MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g)) (fst , snd)
    where
    lem : MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g) ≡ (i , ! i)
    lem = cong MemEvs.wr ([↦]-simp-≡ _ _ _)

    fst : j ≢ MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g) .proj₁
    fst = cast (cong (j ≢_) (sym (Data.Product.Properties.×-≡,≡←≡ lem .proj₁))) (≢-sym i≢j)

    snd : j ∈ MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g) .proj₂
    snd = cast (cong (j ∈_) (sym (Data.Product.Properties.×-≡,≡←≡ lem .proj₂))) (∈! j i (≢-sym i≢j))

  race2 : ¬ noRacingRd i (MemEvs.rd ((X [ g ↦ doRd (X g) j ]) g))
  race2 = yesRacingRd→¬noRacingRd i (MemEvs.rd ((X [ g ↦ doRd (X g) j ]) g)) (j , cast (cong (i ∈_) (sym lem)) (∈! i j i≢j))
    where
    lem : MemEvs.rd ((X [ g ↦ doRd (X g) j ]) g) j ≡ ! j
    lem = begin
        MemEvs.rd ((X [ g ↦ doRd (X g) j ]) g) j
      ≡⟨ cong (λ a → MemEvs.rd a j) ([↦]-simp-≡ _ _ _) ⟩
        MemEvs.rd (doRd (X g) j) j
      ≡⟨ [↦]-simp-≡ _ _ _ ⟩
        ! j
      ∎
... | no g≢g₁ = inj₁ ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ] ,
                      rdGbl R2 G2 (X [ g ↦ doWr (X g) i ]) r₁ g₁ T2' noRace1 ,
                      cast rhs-step≡ (wrGbl R1 G1 (X [ g₁ ↦ doRd (X g₁) j ]) g r T1' noRace2 noRace3))
    where
    noRace1 : noRacingWr j (MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g₁))
    noRace1 = cast (cong (λ a → noRacingWr j (MemEvs.wr a)) (sym ([↦]-simp-≢ _ _ _ _ g≢g₁))) x₂

    noRace2 : noRacingRd i (MemEvs.rd ((X [ g₁ ↦ doRd (X g₁) j ]) g))
    noRace2 = cast (cong (λ a → noRacingRd i (MemEvs.rd a)) (sym ([↦]-simp-≢ _ _ _ _ (≢-sym g≢g₁)))) x

    noRace3 : noRacingWr i (MemEvs.wr ((X [ g₁ ↦ doRd (X g₁) j ]) g))
    noRace3 = cast (cong (λ a → noRacingWr i (MemEvs.wr a)) (sym ([↦]-simp-≢ _ _ _ _ (≢-sym g≢g₁)))) x₁

    mem≡-1 : ∀ g g₁
      → g ≢ g₁
      → ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g ≡
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g
    mem≡-1 g g₁ g≢g₁ = begin
        ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g
      ≡⟨ [↦]-simp-≡ _ _ _ ⟩
        doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i
      ≡⟨ cong (λ a → doWr a i) ([↦]-simp-≢ _ _ _ _ (≢-sym g≢g₁)) ⟩
        doWr (X g) i
      ≡⟨ sym ([↦]-simp-≡ _ _ _) ⟩
        (X [ g ↦ doWr (X g) i ]) g
      ≡⟨ sym ([↦]-simp-≢ (X [ g ↦ doWr (X g) i ]) g₁ g _ (≢-sym g≢g₁)) ⟩
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g
      ∎

    mem≡-2 : ∀ g g₁
      → g ≢ g₁
      → ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g₁ ≡
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g₁
    mem≡-2 g g₁ g≢g₁ = begin
        ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g₁
      ≡⟨ [↦]-simp-≢ _ _ _ _ g≢g₁ ⟩
        (X [ g₁ ↦ doRd (X g₁) j ]) g₁
      ≡⟨ [↦]-simp-≡ _ _ _ ⟩
        doRd (X g₁) j
      ≡⟨ sym (cong (λ a → doRd a j) ([↦]-simp-≢ _ _ _ _ g≢g₁)) ⟩
        doRd ((X [ g ↦ doWr (X g) i ]) g₁) j
      ≡⟨ sym ([↦]-simp-≡ _ _ _) ⟩
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g₁
      ∎

    mem≡-3 : ∀ g g₁ g₂
      → g ≢ g₁
      → g ≢ g₂
      → g₁ ≢ g₂
      → ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g₂ ≡
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g₂
    mem≡-3 g g₁ g₂ g≢g₁ g≢g₂ g₁≢g₂ = begin
        ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g₂
      ≡⟨ [↦]-simp-≢ _ _ _ _ g≢g₂ ⟩
        (X [ g₁ ↦ doRd (X g₁) j ]) g₂
      ≡⟨ [↦]-simp-≢ _ _ _ _ g₁≢g₂ ⟩
        X g₂
      ≡⟨ sym ([↦]-simp-≢ _ _ _ _ g≢g₂) ⟩
        (X [ g ↦ doWr (X g) i ]) g₂
      ≡⟨ sym ([↦]-simp-≢ _ _ _ _ g₁≢g₂) ⟩
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g₂
      ∎

    mem≡-1,2,3 : ∀ g g₁ g₂
      → g ≢ g₁
      → ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g₂ ≡
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g₂
    mem≡-1,2,3 g g₁ g₂ g≢g₁ with gidEq g g₂ | gidEq g₁ g₂
    ... | yes refl | yes refl = ⊥-elim (g≢g₁ refl)
    ... | yes refl | no g₁≢g₂ = mem≡-1 g₂ g₁ g≢g₁
    ... | no g≢g₂ | yes refl = mem≡-2 g g₂ g≢g₂
    ... | no g≢g₂ | no g₁≢g₂ = mem≡-3 g g₁ g₂ g≢g₁ g≢g₂ g₁≢g₂

    mem≡ : ∀ g₂
      → ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g₂ ≡
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g₂
    mem≡ g₂ = mem≡-1,2,3 g g₁ g₂ g≢g₁

    rhs-step≡ :
      StepThd ℂ i
        (just (R1 , G1 , (X [ g₁ ↦ doRd (X g₁) j ]) , (wrGbl g r ⨟ T1')))
        (just (R1 , (G1 [ g ↦ R1 r ]) , ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) , T1'))
      ≡
      StepThd ℂ i
        (just (R1 , G1 , (X [ g₁ ↦ doRd (X g₁) j ]) , (wrGbl g r ⨟ T1')))
        (just (R1 , (G1 [ g ↦ R1 r ]) , ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) , T1'))
    rhs-step≡ = cong (λ a →
      StepThd ℂ i
        (just (R1 , G1 , (X [ g₁ ↦ doRd (X g₁) j ]) , (wrGbl g r ⨟ T1')))
        (just (R1 , (G1 [ g ↦ R1 r ]) , a , T1')))
      (funext mem≡)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (wrGbl _ _ _ g r _ x x₁) (wrGbl _ _ _ g₁ r₁ _ x₂ x₃) with gidEq g g₁
... | yes refl = inj₂ (wrGblBad R2 G2 (X [ g ↦ doWr (X g) i ]) g r₁ T2' (inj₂ race1) , wrGblBad R1 G1 (X [ g ↦ doWr (X g) j ]) g r T1' (inj₂ race2))
  where
  race1 : ¬ noRacingWr j (MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g))
  race1 = yesRacingWr→¬noRacingWr j (MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g)) (fst , snd)
    where
    lem : MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g) ≡ (i , ! i)
    lem = cong MemEvs.wr ([↦]-simp-≡ _ _ _)

    fst : j ≢ MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g) .proj₁
    fst = cast (cong (j ≢_) (sym (Data.Product.Properties.×-≡,≡←≡ lem .proj₁))) (≢-sym i≢j)

    snd : j ∈ MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g) .proj₂
    snd = cast (cong (j ∈_) (sym (Data.Product.Properties.×-≡,≡←≡ lem .proj₂))) (∈! j i (≢-sym i≢j))

  race2 : ¬ noRacingWr i (MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g))
  race2 = yesRacingWr→¬noRacingWr i (MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g)) (fst , snd)
    where
    lem : MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g) ≡ (j , ! j)
    lem = cong MemEvs.wr ([↦]-simp-≡ _ _ _)

    fst : i ≢ MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g) .proj₁
    fst = cast (cong (i ≢_) (sym (Data.Product.Properties.×-≡,≡←≡ lem .proj₁))) i≢j

    snd : i ∈ MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g) .proj₂
    snd = cast (cong (i ∈_) (sym (Data.Product.Properties.×-≡,≡←≡ lem .proj₂))) (∈! i j i≢j)
... | no g≢g₁ = inj₁ ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doWr (X g) i ]) g₁) j ] ,
                      wrGbl R2 G2 (X [ g ↦ doWr (X g) i ]) g₁ r₁ T2' noRace1 noRace2 ,
                      cast rhs-step≡ (wrGbl R1 G1 (X [ g₁ ↦ doWr (X g₁) j ]) g r T1' noRace3 noRace4))
    where
    noRace1 : noRacingRd j (MemEvs.rd ((X [ g ↦ doWr (X g) i ]) g₁))
    noRace1 = cast (cong (λ a → noRacingRd j (MemEvs.rd a)) (sym ([↦]-simp-≢ _ _ _ _ g≢g₁))) x₂

    noRace2 : noRacingWr j (MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g₁))
    noRace2 = cast (cong (λ a → noRacingWr j (MemEvs.wr a)) (sym ([↦]-simp-≢ _ _ _ _ g≢g₁))) x₃

    noRace3 : noRacingRd i (MemEvs.rd ((X [ g₁ ↦ doWr (X g₁) j ]) g))
    noRace3 = cast (cong (λ a → noRacingRd i (MemEvs.rd a)) (sym ([↦]-simp-≢ _ _ _ _ (≢-sym g≢g₁)))) x

    noRace4 : noRacingWr i (MemEvs.wr ((X [ g₁ ↦ doWr (X g₁) j ]) g))
    noRace4 = cast (cong (λ a → noRacingWr i (MemEvs.wr a)) (sym ([↦]-simp-≢ _ _ _ _ (≢-sym g≢g₁)))) x₁

    mem≡-1 : ∀ g g₁
      → g ≢ g₁
      → ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) g ≡
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g
    mem≡-1 g g₁ g≢g₁ = begin
        ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) g
      ≡⟨ [↦]-simp-≡ _ _ _ ⟩
        doWr ((X [ g₁ ↦ doWr (X g₁) j ]) g) i
      ≡⟨ cong (λ a → doWr a i) ([↦]-simp-≢ _ _ _ _ (≢-sym g≢g₁)) ⟩
        doWr (X g) i
      ≡⟨ sym ([↦]-simp-≡ _ _ _) ⟩
        (X [ g ↦ doWr (X g) i ]) g
      ≡⟨ sym ([↦]-simp-≢ (X [ g ↦ doWr (X g) i ]) g₁ g _ (≢-sym g≢g₁)) ⟩
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g
      ∎

    mem≡-2 : ∀ g g₁
      → g ≢ g₁
      → ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) g₁ ≡
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g₁
    mem≡-2 g g₁ g≢g₁ = begin
        ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) g₁
      ≡⟨ [↦]-simp-≢ _ _ _ _ g≢g₁ ⟩
        (X [ g₁ ↦ doWr (X g₁) j ]) g₁
      ≡⟨ [↦]-simp-≡ _ _ _ ⟩
        doWr (X g₁) j
      ≡⟨ sym (cong (λ a → doWr a j) ([↦]-simp-≢ _ _ _ _ g≢g₁)) ⟩
        doWr ((X [ g ↦ doWr (X g) i ]) g₁) j
      ≡⟨ sym ([↦]-simp-≡ _ _ _) ⟩
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g₁
      ∎

    mem≡-3 : ∀ g g₁ g₂
      → g ≢ g₁
      → g ≢ g₂
      → g₁ ≢ g₂
      → ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) g₂ ≡
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g₂
    mem≡-3 g g₁ g₂ g≢g₁ g≢g₂ g₁≢g₂ = begin
        ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) g₂
      ≡⟨ [↦]-simp-≢ _ _ _ _ g≢g₂ ⟩
        (X [ g₁ ↦ doWr (X g₁) j ]) g₂
      ≡⟨ [↦]-simp-≢ _ _ _ _ g₁≢g₂ ⟩
        X g₂
      ≡⟨ sym ([↦]-simp-≢ _ _ _ _ g≢g₂) ⟩
        (X [ g ↦ doWr (X g) i ]) g₂
      ≡⟨ sym ([↦]-simp-≢ _ _ _ _ g₁≢g₂) ⟩
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g₂
      ∎

    mem≡-1,2,3 : ∀ g g₁ g₂
      → g ≢ g₁
      → ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) g₂ ≡
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g₂
    mem≡-1,2,3 g g₁ g₂ g≢g₁ with gidEq g g₂ | gidEq g₁ g₂
    ... | yes refl | yes refl = ⊥-elim (g≢g₁ refl)
    ... | yes refl | no g₁≢g₂ = mem≡-1 g₂ g₁ g≢g₁
    ... | no g≢g₂ | yes refl = mem≡-2 g g₂ g≢g₂
    ... | no g≢g₂ | no g₁≢g₂ = mem≡-3 g g₁ g₂ g≢g₁ g≢g₂ g₁≢g₂

    mem≡ : ∀ g₂
      → ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) g₂ ≡
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g₂
    mem≡ g₂ = mem≡-1,2,3 g g₁ g₂ g≢g₁

    rhs-step≡ :
      StepThd ℂ i
        (just (R1 , G1 , (X [ g₁ ↦ doWr (X g₁) j ]) , (wrGbl g r ⨟ T1')))
        (just (R1 , (G1 [ g ↦ R1 r ]) , ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) , T1'))
      ≡
      StepThd ℂ i
        (just (R1 , G1 , (X [ g₁ ↦ doWr (X g₁) j ]) , (wrGbl g r ⨟ T1')))
        (just (R1 , (G1 [ g ↦ R1 r ]) , ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doWr (X g) i ]) g₁) j ]) , T1'))
    rhs-step≡ = cong (λ a →
      StepThd ℂ i
        (just (R1 , G1 , (X [ g₁ ↦ doWr (X g₁) j ]) , (wrGbl g r ⨟ T1')))
        (just (R1 , (G1 [ g ↦ R1 r ]) , a , T1')))
      (funext mem≡)

StepThd-≡ : ∀ {ℂ i C C1 C2}
  → StepThd ℂ i C C1
  → StepThd ℂ i C C2
  → C1 ≡ C2
StepThd-≡ (const R G X r c T) (const .R .G .X .r .c .T) = refl
StepThd-≡ (binOp R G X r r1 r2 T) (binOp .R .G .X .r .r1 .r2 .T) = refl
StepThd-≡ (rdReg R G X r1 r2 T) (rdReg .R .G .X .r1 .r2 .T) = refl
StepThd-≡ (rdGbl R G X r g T x) (rdGbl .R .G .X .r .g .T x₁) = refl
StepThd-≡ (rdGbl R G X r g T x) (rdGblBad .R .G .X .r .g .T x₁) = ⊥-elim (x₁ x)
StepThd-≡ (rdGblBad R G X r g T x) (rdGbl .R .G .X .r .g .T x₁) = ⊥-elim (x x₁)
StepThd-≡ (rdGblBad R G X r g T x) (rdGblBad .R .G .X .r .g .T x₁) = refl
StepThd-≡ (wrGbl R G X g r T x x₁) (wrGbl .R .G .X .g .r .T x₂ x₃) = refl
StepThd-≡ (wrGbl R G X g r T x x₁) (wrGblBad .R .G .X .g .r .T x₂) = ⊥-elim (case x₂ (λ y → y x) (λ y → y x₁))
StepThd-≡ (wrGblBad R G X g r T x) (wrGbl .R .G .X .g .r .T x₁ x₂) = ⊥-elim (case x (λ y → y x₁) (λ y → y x₂))
StepThd-≡ (wrGblBad R G X g r T x) (wrGblBad .R .G .X .g .r .T x₁) = refl

diamond : ∀ {ℂ C C1 C2}
  → StepProgRefl ℂ C C1
  → StepProgRefl ℂ C C2
  → ∃[ C' ] StepProgRefl ℂ C1 C' × StepProgRefl ℂ C2 C'
diamond (refl C) (refl .C) = C , refl C , refl C
diamond (refl .(just (Rs , Gs , X , Ts))) (schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃) = just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , (Ts [ i ↦ T' ])) ,
                                                                                             schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃ ,
                                                                                             refl (just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , (Ts [ i ↦ T' ])))
diamond (refl .(just (Rs , Gs , X , Ts))) (schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃) = nothing , schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃ , refl nothing
diamond (refl .(just (Rs , Gs , X , Ts))) (sync I Rs Gs X Ts p) = just (Rs , syncEnvs I X Gs , syncMem I X , syncStep I Ts p) ,
                                                                  sync I Rs Gs X Ts p ,
                                                                  refl (just (Rs , syncEnvs I X Gs , syncMem I X , syncStep I Ts p))
diamond (schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃) (refl .(just (Rs , Gs , X , Ts))) = just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , (Ts [ i ↦ T' ])) ,
                                                                                             refl (just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , (Ts [ i ↦ T' ]))) ,
                                                                                             schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃
diamond {ℂ = ℂ} (schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃) (schd i₁ .Rs .Gs .X .Ts R₁ G₁ T₁ R'' G'' X'' T'' x₄ x₅ x₆ x₇) with tidEq i i₁
... | yes refl = just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , (Ts [ i ↦ T' ])) ,
                 refl (just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , (Ts [ i ↦ T' ]))) ,
                 cast eq' (refl (just ((Rs [ i ↦ R'' ]) , (Gs [ i ↦ G'' ]) , X'' , (Ts [ i ↦ T'' ]))))
  where
  R≡ : R ≡ R₁
  R≡ = trans (sym x) x₄

  G≡ : G ≡ G₁
  G≡ = trans (sym x₁) x₅

  T≡ : T ≡ T₁
  T≡ = trans (sym x₂) x₆

  eq : just (R' , G' , X' , T') ≡ just (R'' , G'' , X'' , T'')
  eq with R≡ | G≡ | T≡
  ... | refl | refl | refl = StepThd-≡ x₃ x₇

  eq' :
    StepProgRefl ℂ
      (just ((Rs [ i ↦ R'' ]) , (Gs [ i ↦ G'' ]) , X'' , (Ts [ i ↦ T'' ])))
      (just ((Rs [ i ↦ R'' ]) , (Gs [ i ↦ G'' ]) , X'' , (Ts [ i ↦ T'' ])))
    ≡
    StepProgRefl ℂ
      (just ((Rs [ i ↦ R'' ]) , (Gs [ i ↦ G'' ]) , X'' , (Ts [ i ↦ T'' ])))
      (just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , (Ts [ i ↦ T' ])))
  eq' with eq
  ... | refl = refl
... | no i≢i₁ = case
                  nextStep
                  (λ (X''' , lhs , rhs) → just ((Rs [ i ↦ R' ] [ i₁ ↦ R'' ]) , (Gs [ i ↦ G' ] [ i₁ ↦ G'' ]) , X''' , (Ts [ i ↦ T' ] [ i₁ ↦ T'' ])) ,
                                   schd i₁ (Rs [ i ↦ R' ]) (Gs [ i ↦ G' ]) X' (Ts [ i ↦ T' ]) R₁ G₁ T₁ R'' G'' X''' T'' ≡R₁ ≡G₁ ≡T₁ lhs ,
                                   cast (rhs≡ X''') (schd  i (Rs [ i₁ ↦ R'' ]) (Gs [ i₁ ↦ G'' ]) X'' (Ts [ i₁ ↦ T'' ]) R G T R' G' X''' T' ≡R ≡G ≡T rhs))
                  (λ (lhs , rhs) → nothing ,
                                   schdBad i₁ (Rs [ i ↦ R' ]) (Gs [ i ↦ G' ]) X' (Ts [ i ↦ T' ]) R₁ G₁ T₁ ≡R₁ ≡G₁ ≡T₁ lhs ,
                                   schdBad i (Rs [ i₁ ↦ R'' ]) (Gs [ i₁ ↦ G'' ]) X'' (Ts [ i₁ ↦ T'' ]) R G T ≡R ≡G ≡T rhs)
  where
  nextStep : (∃[ X''' ] StepThd ℂ i₁ (just (R₁ , G₁ , X' , T₁)) (just (R'' , G'' , X''' , T'')) × StepThd _ i (just (R , G , X'' , T)) (just (R' , G' , X''' , T')))
           ⊎ (StepThd ℂ i₁ (just (R₁ , G₁ , X' , T₁)) nothing × StepThd _ i (just (R , G , X'' , T)) nothing)
  nextStep = StepThd-≢-comm i≢i₁ x₃ x₇

  ≡R₁ : (Rs [ i ↦ R' ]) i₁ ≡ R₁
  ≡R₁ = trans ([↦]-simp-≢ Rs i i₁ R' i≢i₁) x₄
  ≡G₁ : (Gs [ i ↦ G' ]) i₁ ≡ G₁
  ≡G₁ = trans ([↦]-simp-≢ Gs i i₁ G' i≢i₁) x₅
  ≡T₁ : (Ts [ i ↦ T' ]) i₁ ≡ T₁
  ≡T₁ = trans ([↦]-simp-≢ Ts i i₁ T' i≢i₁) x₆

  ≡R : (Rs [ i₁ ↦ R'' ]) i ≡ R
  ≡R = trans ([↦]-simp-≢ Rs i₁ i R'' (≢-sym i≢i₁)) x
  ≡G : (Gs [ i₁ ↦ G'' ]) i ≡ G
  ≡G = trans ([↦]-simp-≢ Gs i₁ i G'' (≢-sym i≢i₁)) x₁
  ≡T : (Ts [ i₁ ↦ T'' ]) i ≡ T
  ≡T = trans ([↦]-simp-≢ Ts i₁ i T'' (≢-sym i≢i₁)) x₂

  Rs≡ : Rs [ i₁ ↦ R'' ] [ i ↦ R' ] ≡ Rs [ i ↦ R' ] [ i₁ ↦ R'' ]
  Rs≡ = [↦]-comm Rs (≢-sym i≢i₁) R'' R'
  Gs≡ : Gs [ i₁ ↦ G'' ] [ i ↦ G' ] ≡ Gs [ i ↦ G' ] [ i₁ ↦ G'' ]
  Gs≡ = [↦]-comm Gs (≢-sym i≢i₁) G'' G'
  Ts≡ : Ts [ i₁ ↦ T'' ] [ i ↦ T' ] ≡ Ts [ i ↦ T' ] [ i₁ ↦ T'' ]
  Ts≡ = [↦]-comm Ts (≢-sym i≢i₁) T'' T'

  rhs≡ : ∀ X''' →
    StepProgRefl ℂ
      (just ((Rs [ i₁ ↦ R'' ]) , (Gs [ i₁ ↦ G'' ]) , X'' , (Ts [ i₁ ↦ T'' ])))
      (just ((Rs [ i₁ ↦ R'' ] [ i ↦ R' ]) , (Gs [ i₁ ↦ G'' ] [ i ↦ G' ]) , X''' , (Ts [ i₁ ↦ T'' ] [ i ↦ T' ])))
    ≡
    StepProgRefl ℂ
      (just ((Rs [ i₁ ↦ R'' ]) , (Gs [ i₁ ↦ G'' ]) , X'' , (Ts [ i₁ ↦ T'' ])))
      (just ((Rs [ i ↦ R' ] [ i₁ ↦ R'' ]) , (Gs [ i ↦ G' ] [ i₁ ↦ G'' ]) , X''' , (Ts [ i ↦ T' ] [ i₁ ↦ T'' ])))
  rhs≡ X''' = cong₃ (λ a b c →
    StepProgRefl ℂ
      (just ((Rs [ i₁ ↦ R'' ]) , (Gs [ i₁ ↦ G'' ]) , X'' , (Ts [ i₁ ↦ T'' ])))
      (just (a , b , X''' , c)))
    Rs≡ Gs≡ Ts≡
diamond (schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃) (schdBad i₁ .Rs .Gs .X .Ts R₁ G₁ T₁ x₄ x₅ x₆ x₇) = {!!}
diamond (schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃) (sync I .Rs .Gs .X .Ts p) = {!!}
diamond (schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃) (refl .(just (Rs , Gs , X , Ts))) = nothing , refl nothing , schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃
diamond (schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃) (schd i₁ .Rs .Gs .X .Ts R₁ G₁ T₁ R' G' X' T' x₄ x₅ x₆ x₇) = {!!}
diamond (schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃) (schdBad i₁ .Rs .Gs .X .Ts R₁ G₁ T₁ x₄ x₅ x₆ x₇) = nothing , refl nothing , refl nothing
diamond (schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃) (sync I .Rs .Gs .X .Ts p) = {!!}
diamond (sync I Rs Gs X Ts p) (refl .(just (Rs , Gs , X , Ts))) = just (Rs , syncEnvs I X Gs , syncMem I X , syncStep I Ts p) ,
                                                                  refl (just (Rs , syncEnvs I X Gs , syncMem I X , syncStep I Ts p)) ,
                                                                  sync I Rs Gs X Ts p
diamond (sync I Rs Gs X Ts p) (schd i .Rs .Gs .X .Ts R G T R' G' X' T' x x₁ x₂ x₃) = {!!}
diamond (sync I Rs Gs X Ts p) (schdBad i .Rs .Gs .X .Ts R G T x x₁ x₂ x₃) = {!!}
diamond (sync I Rs Gs X Ts p) (sync I₁ .Rs .Gs .X .Ts p₁) = {!!}
