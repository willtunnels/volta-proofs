module KernelCheck.Confluence where

open import Function.Base using (_∘_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; _≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂; map; map₁; map₂)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties
open import Data.Bool using (Bool; true; false; not)
import Data.Bool.Properties
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
import Data.Product.Properties
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import KernelCheck.Prog
open import KernelCheck.Util
open import KernelCheck.DecSet

≤-Rd : Tid → Rd → Rd → Set
≤-Rd i r1 r2 = noRacingRd i r2 → noRacingRd i r1

≤-Wr : Tid → Wr → Wr → Set
≤-Wr i w1 w2 = noRacingWr i w2 → noRacingWr i w1

≤-MemEvs : Tid → MemEvs → MemEvs → Set
≤-MemEvs i X1 X2 = ≤-Rd i (X1 .MemEvs.rd) (X2 .MemEvs.rd) × ≤-Wr i (X1 .MemEvs.wr) (X2 .MemEvs.wr)

-- X1 ≤ X2 iff a race for i under X1 implies a race for i under X2
≤-Mem : Tid → Mem → Mem → Set
≤-Mem i X1 X2 = ∀ g → ≤-MemEvs i (X1 g) (X2 g)

≥-Mem : Tid → Mem → Mem → Set
≥-Mem i X1 X2 = ≤-Mem i X2 X1

≤-Mem-refl : ∀ j X → ≤-Mem j X X
≤-Mem-refl j X g = (λ z → z) , (λ z → z)

≤-Mem-doRd : ∀ i j X g → ≤-Mem i X (X [ g ↦ doRd (X g) j ])
≤-Mem-doRd i j X g g' with gidEq g g'
... | yes refl = (λ p k → map₂ (lem-rd k) (p k)) , rhs
  where
  lem-rd : ∀ k → (X [ g ↦ doRd (X g) j ]) g .MemEvs.rd k i ≡ false → X g .MemEvs.rd k i ≡ false
  lem-rd k p with tidEq k j
  ... | yes refl = ⊥-elim (false≢true (sym (cast (cong (λ a → a i ≡ false) simp-rd) p)))
    where
    simp-rd : (X [ g ↦ doRd (X g) k ]) g .MemEvs.rd k ≡ all
    simp-rd = (cong (λ a → a .MemEvs.rd k) ([↦]-simp-≡ X g (doRd (X g) k)))
      ∙ [↦]-simp-≡ ((X g) .MemEvs.rd) k all
  ... | no k≢j = cong (λ a → a i) (sym simp-rd) ∙ p
    where
    simp-rd : (X [ g ↦ doRd (X g) j ]) g .MemEvs.rd k ≡ X g .MemEvs.rd k
    simp-rd = (cong (λ a → a .MemEvs.rd k) ([↦]-simp-≡ X g (doRd (X g) j)))
      ∙ [↦]-simp-≢ ((X g) .MemEvs.rd) j k all (≢-sym k≢j)

  lem-wr : (X [ g ↦ doRd (X g) j ]) g .MemEvs.wr ≡ X g .MemEvs.wr
  lem-wr = cong MemEvs.wr ([↦]-simp-≡ X g (doRd (X g) j))

  rhs = map
    (λ y → cast (cong (λ a → i ≡ a .proj₁) lem-wr) y)
    (λ y → cast (cong (λ a → a .proj₂ i ≡ false) lem-wr) y)
... | no g≢g' = (λ p k → map₂ (lem-rd k) (p k)) , map f1 f2
  where
  simp-Xg' : (X [ g ↦ doRd (X g) j ]) g' ≡ X g'
  simp-Xg' = [↦]-simp-≢ X g g' (doRd (X g) j) g≢g'

  lem-rd : ∀ k → (X [ g ↦ doRd (X g) j ]) g' .MemEvs.rd k i ≡ false → X g' .MemEvs.rd k i ≡ false
  lem-rd k p = cast (cong (λ a → a .MemEvs.rd k i ≡ false) simp-Xg') p

  f1 = cast (cong (λ a → i ≡ a .MemEvs.wr .proj₁) simp-Xg')
  f2 = cast (cong (λ a → a .MemEvs.wr .proj₂ i ≡ false) simp-Xg')

≤-Mem-doWr : ∀ i j X g → i ≢ j → ≤-Mem i X (X [ g ↦ doWr (X g) j ])
≤-Mem-doWr i j X g i≢j g' with gidEq g g'
... | yes refl = (λ p k → map₂ (lem-rd k) (p k)) , map lem-wr1 lem-wr2
  where
  lem-rd : ∀ k → (X [ g ↦ doWr (X g) j ]) g .MemEvs.rd k i ≡ false → X g .MemEvs.rd k i ≡ false
  lem-rd k p = (sym (cong (λ a → a .MemEvs.rd k i) ([↦]-simp-≡ X g (doWr (X g) j)))) ∙ p

  X' = X [ g ↦ doWr (X g) j ]

  simp-wr : X' g .MemEvs.wr ≡ (j , all)
  simp-wr = cong MemEvs.wr ([↦]-simp-≡ X g (doWr (X g) j))

  lem-wr1 : i ≡ X' g .MemEvs.wr .proj₁ → i ≡ X g .MemEvs.wr .proj₁
  lem-wr1 p = ⊥-elim (i≢j (cast (cong (λ a → i ≡ a .proj₁) simp-wr) p))

  lem-wr2 : X' g .MemEvs.wr .proj₂ i ≡ false → X g .MemEvs.wr .proj₂ i ≡ false
  lem-wr2 p = ⊥-elim (false≢true ((sym p) ∙ cong (λ a → a .proj₂ i) simp-wr))
... | no g≢g' = (λ p k → map₂ (lem-rd k) (p k)) , map f1 f2
  where
  simp-Xg' : (X [ g ↦ doWr (X g) j ]) g' ≡ X g'
  simp-Xg' = [↦]-simp-≢ X g g' (doWr (X g) j) g≢g'

  lem-rd : ∀ k → (X [ g ↦ doWr (X g) j ]) g' .MemEvs.rd k i ≡ false → X g' .MemEvs.rd k i ≡ false
  lem-rd k p = cast (cong (λ a → a .MemEvs.rd k i ≡ false) simp-Xg') p

  f1 = cast (cong (λ a → i ≡ a .MemEvs.wr .proj₁) simp-Xg')
  f2 = cast (cong (λ a → a .MemEvs.wr .proj₂ i ≡ false) simp-Xg')

StepThd-≤-Mem : ∀ {ℂ i R1 G1 X1 T1 R2 G2 X2 T2}
  → StepThd ℂ i (just (R1 , G1 , X1 , T1)) (just (R2 , G2 , X2 , T2))
  → ∀ j → j ≢ i → ≤-Mem j X1 X2
StepThd-≤-Mem {X1 = X1} (const _ _ _ r c _) j i≢j = ≤-Mem-refl j X1
StepThd-≤-Mem {X1 = X1} (binOp _ _ _ r r1 r2 _) j i≢j = ≤-Mem-refl j X1
StepThd-≤-Mem {X1 = X1} (rdReg _ _ _ r1 r2 _) j i≢j = ≤-Mem-refl j X1
StepThd-≤-Mem {i = i} {X1 = X1} (rdGbl _ _ _ r g _ x) j i≢j = ≤-Mem-doRd j i X1 g
StepThd-≤-Mem {i = i} {X1 = X1} (wrGbl _ _ _ g r _ x x₁) j i≢j = ≤-Mem-doWr j i X1 g i≢j

yesRacingRd-mono : ∀ i X X' g → ≤-Mem i X X' → yesRacingRd i (MemEvs.rd (X g)) → yesRacingRd i (MemEvs.rd (X' g))
yesRacingRd-mono i X X' g p q = ¬noRacingRd→yesRacingRd i (MemEvs.rd (X' g)) (λ noRaceX' → yesRacingRd→¬noRacingRd i (MemEvs.rd (X g)) q (p g .proj₁ noRaceX'))

yesRacingWr-mono : ∀ i X X' g → ≤-Mem i X X' → yesRacingWr i (MemEvs.wr (X g)) → yesRacingWr i (MemEvs.wr (X' g))
yesRacingWr-mono i X X' g p q = ¬noRacingWr→yesRacingWr i (MemEvs.wr (X' g)) (λ noRaceX' → yesRacingWr→¬noRacingWr i (MemEvs.wr (X g)) q (p g .proj₂ noRaceX'))

StepThd-mono-nothing : ∀ {ℂ i R G X1 X2 T}
  → ≤-Mem i X1 X2
  → StepThd ℂ i (just (R , G , X1 , T)) nothing
  → StepThd ℂ i (just (R , G , X2 , T)) nothing
StepThd-mono-nothing {i = i} {X1 = X1} {X2 = X2} p (rdGblBad _ _ _ r g T x) = rdGblBad _ _ _ r g T
  (yesRacingWr→¬noRacingWr i (MemEvs.wr (X2 g)) (yesRacingWr-mono i X1 X2 g p (¬noRacingWr→yesRacingWr i (MemEvs.wr (X1 g)) x)))
StepThd-mono-nothing {i = i} {X1 = X1} {X2 = X2} p (wrGblBad _ _ _ g r T x) = wrGblBad _ _ _ g r T (map f1 f2 x)
  where
  f1 = (λ q → yesRacingRd→¬noRacingRd i (MemEvs.rd (X2 g)) (yesRacingRd-mono i X1 X2 g p (¬noRacingRd→yesRacingRd i (MemEvs.rd (X1 g)) q)))
  f2 = (λ q → yesRacingWr→¬noRacingWr i (MemEvs.wr (X2 g)) (yesRacingWr-mono i X1 X2 g p (¬noRacingWr→yesRacingWr i (MemEvs.wr (X1 g)) q)))

StepThd-just-sync : ∀ {ℂ i I R G X T R' G' X' T'}
  → i ∉ I
  → StepThd ℂ i (just (R , G , X , T)) (just (R' , G' , X' , T'))
  → StepThd ℂ i (just (R , G , syncMem I X , T)) (just (R' , G' , syncMem I X' , T'))
StepThd-just-sync = {!!}

StepThd-return-stuck : ∀ {ℂ i R G X T C} → StepThd ℂ i (just (R , G , X , T)) C → T ≢ return
StepThd-return-stuck (const _ _ _ r c T) = λ ()
StepThd-return-stuck (binOp _ _ _ r r1 r2 T) = λ ()
StepThd-return-stuck (rdReg _ _ _ r1 r2 T) = λ ()
StepThd-return-stuck (rdGbl _ _ _ r g T x) = λ ()
StepThd-return-stuck (rdGblBad _ _ _ r g T x) = λ ()
StepThd-return-stuck (wrGbl _ _ _ g r T x x₁) = λ ()
StepThd-return-stuck (wrGblBad _ _ _ g r T x) = λ ()

StepThd-sync-stuck : ∀ {ℂ i R G X T C} I T' → StepThd ℂ i (just (R , G , X , T)) C → T ≢ sync I ⨟ T'
StepThd-sync-stuck _ _ (const _ _ _ r c T) = λ ()
StepThd-sync-stuck _ _ (binOp _ _ _ r r1 r2 T) = λ ()
StepThd-sync-stuck _ _ (rdReg _ _ _ r1 r2 T) = λ ()
StepThd-sync-stuck _ _ (rdGbl _ _ _ r g T x) = λ ()
StepThd-sync-stuck _ _ (rdGblBad _ _ _ r g T x) = λ ()
StepThd-sync-stuck _ _ (wrGbl _ _ _ g r T x x₁) = λ ()
StepThd-sync-stuck _ _ (wrGblBad _ _ _ g r T x) = λ ()

StepThd-sync-step : ∀ {ℂ i I Ts R G X T C} → Ts i ≡ T → canSync I Ts → StepThd ℂ i (just (R , G , X , T)) C → i ∉ I
StepThd-sync-step {i = i} {I = I} Ts≡ p x with ∉-dec i I
... | yes i∉I = i∉I
... | no i∈I = ⊥-elim (case (p i (Data.Bool.Properties.¬-not i∈I))
  (λ q → StepThd-return-stuck x (sym Ts≡ ∙ q))
  (λ q → StepThd-sync-stuck I (q .proj₁) x (sym Ts≡ ∙ q .proj₂)))

StepThd-≢-comm : ∀ {ℂ i j R1 G1 T1 R1' G1' T1' R2 G2 T2 R2' G2' T2' X X'1 X'2}
  → i ≢ j
  → StepThd ℂ i (just (R1 , G1 , X , T1)) (just (R1' , G1' , X'1 , T1'))
  → StepThd ℂ j (just (R2 , G2 , X , T2)) (just (R2' , G2' , X'2 , T2'))
  → (∃[ X'' ] StepThd ℂ j (just (R2 , G2 , X'1 , T2)) (just (R2' , G2' , X'' , T2')) ×
              StepThd ℂ i (just (R1 , G1 , X'2 , T1)) (just (R1' , G1' , X'' , T1')) ×
              (∀ Gs → WellSynced ℂ Gs X'1 → WellSynced ℂ Gs X'2 → WellSynced ℂ Gs X''))
  ⊎ (StepThd ℂ j (just (R2 , G2 , X'1 , T2)) nothing ×
     StepThd ℂ i (just (R1 , G1 , X'2 , T1)) nothing)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (const _ _ _ r c _) (const _ _ _ r₁ c₁ _) =
  inj₁ (X , const R2 G2 X r₁ c₁ T2' , const R1 G1 X r c T1' , λ _ ws _ → ws)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (const _ _ _ r c _) (binOp _ _ _ r₁ r1 r2 _) =
  inj₁ (X , binOp R2 G2 X r₁ r1 r2 T2' , const R1 G1 X r c T1' , λ _ ws _ → ws)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (const _ _ _ r c _) (rdReg _ _ _ r1 r2 _) =
  inj₁ (X , rdReg R2 G2 X r1 r2 T2' , const R1 G1 X r c T1' , λ _ ws _ → ws)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (const _ _ _ r c _) (rdGbl _ _ _ r₁ g _ x) =
  inj₁ ((X [ g ↦ doRd (X g) j ]) ,
       rdGbl R2 G2 X r₁ g T2' x ,
       const R1 G1 (X [ g ↦ doRd (X g) j ]) r c T1' ,
       λ Gs z z₁ → z₁)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (const _ _ _ r c _) (wrGbl _ _ _ g r₁ _ x x₁) =
  inj₁ ((X [ g ↦ doWr (X g) j ]) ,
       wrGbl R2 G2 X g r₁ T2' x x₁ ,
       const R1 G1 (X [ g ↦ doWr (X g) j ]) r c T1' ,
       λ Gs z z₁ → z₁)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (binOp _ _ _ r r1 r2 _) (const _ _ _ r₁ c _) =
  inj₁ (X , const R2 G2 X r₁ c T2' , binOp R1 G1 X r r1 r2 T1' , λ _ ws _ → ws )
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (binOp _ _ _ r r1 r2 _) (binOp _ _ _ r₁ r3 r4 _) =
  inj₁ (X , binOp R2 G2 X r₁ r3 r4 T2' , binOp R1 G1 X r r1 r2 T1' , λ _ ws _ → ws )
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (binOp _ _ _ r r1 r2 _) (rdReg _ _ _ r3 r4 _) =
  inj₁ (X , rdReg R2 G2 X r3 r4 T2' , binOp R1 G1 X r r1 r2 T1' , λ _ ws _ → ws )
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (binOp _ _ _ r r1 r2 _) (rdGbl _ _ _ r₁ g _ x) =
  inj₁ ((X [ g ↦ doRd (X g) j ]) ,
       rdGbl R2 G2 X r₁ g T2' x ,
       binOp R1 G1 (X [ g ↦ doRd (X g) j ]) r r1 r2 T1' ,
       λ Gs z z₁ → z₁)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (binOp _ _ _ r r1 r2 _) (wrGbl _ _ _ g r₁ _ x x₁) =
  inj₁ ((X [ g ↦ doWr (X g) j ]) ,
       wrGbl R2 G2 X g r₁ T2' x x₁ ,
       binOp R1 G1 (X [ g ↦ doWr (X g) j ]) r r1 r2 T1' ,
       λ Gs z z₁ → z₁)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdReg _ _ _ r1 r2 _) (const _ _ _ r c _) =
  inj₁ (X , const R2 G2 X r c T2' , rdReg R1 G1 X r1 r2 T1' , λ Gs z z₁ → z)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdReg _ _ _ r1 r2 _) (binOp _ _ _ r r3 r4 _) =
  inj₁ (X , binOp R2 G2 X r r3 r4 T2' , rdReg R1 G1 X r1 r2 T1' , λ Gs z z₁ → z)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdReg _ _ _ r1 r2 _) (rdReg _ _ _ r3 r4 _) =
  inj₁ (X , rdReg R2 G2 X r3 r4 T2' , rdReg R1 G1 X r1 r2 T1' , λ Gs z z₁ → z)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdReg _ _ _ r1 r2 _) (rdGbl _ _ _ r g _ x) =
  inj₁ ((X [ g ↦ doRd (X g) j ]) ,
       rdGbl R2 G2 X r g T2' x ,
       rdReg R1 G1 (X [ g ↦ doRd (X g) j ]) r1 r2 T1' ,
       λ Gs z z₁ → z₁)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdReg _ _ _ r1 r2 _) (wrGbl _ _ _ g r _ x x₁) =
  inj₁ ((X [ g ↦ doWr (X g) j ]) ,
       wrGbl R2 G2 X g r T2' x x₁ ,
       rdReg R1 G1 (X [ g ↦ doWr (X g) j ]) r1 r2 T1' ,
       λ Gs z z₁ → z₁)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdGbl _ _ _ r g _ x) (const _ _ _ r₁ c _) =
  inj₁ ((X [ g ↦ doRd (X g) i ]) ,
    const R2 G2 (X [ g ↦ doRd (X g) i ]) r₁ c T2' ,
    rdGbl R1 G1 X r g T1' x ,
    λ Gs z z₁ → z)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdGbl _ _ _ r g _ x) (binOp _ _ _ r₁ r1 r2 _) =
  inj₁ ((X [ g ↦ doRd (X g) i ]) ,
       binOp R2 G2 (X [ g ↦ doRd (X g) i ]) r₁ r1 r2 T2' ,
       rdGbl R1 G1 X r g T1' x ,
       λ Gs z z₁ → z)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdGbl _ _ _ r g _ x) (rdReg _ _ _ r1 r2 _) =
  inj₁ ((X [ g ↦ doRd (X g) i ]) ,
       rdReg R2 G2 (X [ g ↦ doRd (X g) i ]) r1 r2 T2' ,
       rdGbl R1 G1 X r g T1' x ,
       λ Gs z z₁ → z)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (rdGbl _ _ _ r g _ x) (rdGbl _ _ _ r₁ g₁ _ x₁) =
  inj₁ ((X [ g ↦ doRd (X g) i ] [ g₁ ↦ doRd ((X [ g ↦ doRd (X g) i ]) g₁) j ]) ,
       rdGbl R2 G2 (X [ g ↦ doRd (X g) i ]) r₁ g₁ T2' lhs-noRace ,
       cast rhs-step≡ (rdGbl R1 G1 (X [ g₁ ↦ doRd (X g₁) j ]) r g T1' rhs-noRace) ,
       λ Gs ws1 _ → doRd-WS ℂ Gs (X [ g ↦ doRd (X g) i ]) g₁ j ws1)
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
  race1 = yesRacingRd→¬noRacingRd j (MemEvs.rd ((X [ g ↦ doRd (X g) i ]) g)) (i , ≢-sym i≢j , cast (cong (j ∈_) (sym lem)) refl)
    where
    lem : MemEvs.rd ((X [ g ↦ doRd (X g) i ]) g) i ≡ all
    lem = begin
        MemEvs.rd ((X [ g ↦ doRd (X g) i ]) g) i
      ≡⟨ cong (λ a → MemEvs.rd a i) ([↦]-simp-≡ _ _ _) ⟩
        MemEvs.rd (doRd (X g) i) i
      ≡⟨ [↦]-simp-≡ _ _ _ ⟩
        all
      ∎

  race2 : ¬ noRacingWr i (MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g))
  race2 = yesRacingWr→¬noRacingWr i (MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g)) (fst , snd)
    where
    lem : MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g) ≡ (j , all)
    lem = cong MemEvs.wr ([↦]-simp-≡ _ _ _)

    fst : i ≢ MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g) .proj₁
    fst = cast (cong (i ≢_) (sym (Data.Product.Properties.×-≡,≡←≡ lem .proj₁))) i≢j

    snd : i ∈ MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g) .proj₂
    snd = cast (cong (i ∈_) (sym (Data.Product.Properties.×-≡,≡←≡ lem .proj₂))) refl
... | no g≢g₁ = inj₁ ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doRd (X g) i ]) g₁) j ] ,
                      wrGbl R2 G2 (X [ g ↦ doRd (X g) i ]) g₁ r₁ T2' noRace1 noRace2 ,
                      cast rhs-step≡ (rdGbl R1 G1 (X [ g₁ ↦ doWr (X g₁) j ]) r g T1' noRace3) ,
                      λ Gs _ ws2 → cast (cong (λ a → WellSynced ℂ Gs a) (funext mem≡)) (doRd-WS _ _ _ _ _ ws2))
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
       wrGbl R1 G1 X g r T1' x x₁ ,
       λ Gs z z₁ → z)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (wrGbl _ _ _ g r _ x x₁) (binOp _ _ _ r₁ r1 r2 _) =
  inj₁ ((X [ g ↦ doWr (X g) i ]) ,
       binOp R2 G2 (X [ g ↦ doWr (X g) i ]) r₁ r1 r2 T2' ,
       wrGbl R1 G1 X g r T1' x x₁ ,
       λ Gs z z₁ → z)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (wrGbl _ _ _ g r _ x x₁) (rdReg _ _ _ r1 r2 _) =
  inj₁ ((X [ g ↦ doWr (X g) i ]) ,
       rdReg R2 G2 (X [ g ↦ doWr (X g) i ]) r1 r2 T2' ,
       wrGbl R1 G1 X g r T1' x x₁ ,
       λ Gs z z₁ → z)
StepThd-≢-comm {ℂ} {i} {j} {R1} {G1} {T1} {R1'} {G1'} {T1'} {R2} {G2} {T2} {R2'} {G2'} {T2'} {X} {X'1} {X'2} i≢j (wrGbl _ _ _ g r _ x x₁) (rdGbl _ _ _ r₁ g₁ _ x₂) with gidEq g g₁
... | yes refl = inj₂ (rdGblBad R2 G2 (X [ g ↦ doWr (X g) i ]) r₁ g T2' race1 , wrGblBad R1 G1 (X [ g ↦ doRd (X g) j ]) g r T1' (inj₁ race2))
  where
  race1 : ¬ noRacingWr j (MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g))
  race1 = yesRacingWr→¬noRacingWr j (MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g)) (fst , snd)
    where
    lem : MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g) ≡ (i , all)
    lem = cong MemEvs.wr ([↦]-simp-≡ _ _ _)

    fst : j ≢ MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g) .proj₁
    fst = cast (cong (j ≢_) (sym (Data.Product.Properties.×-≡,≡←≡ lem .proj₁))) (≢-sym i≢j)

    snd : j ∈ MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g) .proj₂
    snd = cast (cong (j ∈_) (sym (Data.Product.Properties.×-≡,≡←≡ lem .proj₂))) refl

  race2 : ¬ noRacingRd i (MemEvs.rd ((X [ g ↦ doRd (X g) j ]) g))
  race2 = yesRacingRd→¬noRacingRd i (MemEvs.rd ((X [ g ↦ doRd (X g) j ]) g)) (j , i≢j , cast (cong (i ∈_) (sym lem)) refl)
    where
    lem : MemEvs.rd ((X [ g ↦ doRd (X g) j ]) g) j ≡ all
    lem = begin
        MemEvs.rd ((X [ g ↦ doRd (X g) j ]) g) j
      ≡⟨ cong (λ a → MemEvs.rd a j) ([↦]-simp-≡ _ _ _) ⟩
        MemEvs.rd (doRd (X g) j) j
      ≡⟨ [↦]-simp-≡ _ _ _ ⟩
        all
      ∎
... | no g≢g₁ = inj₁ ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ] ,
                      rdGbl R2 G2 (X [ g ↦ doWr (X g) i ]) r₁ g₁ T2' noRace1 ,
                      cast rhs-step≡ (wrGbl R1 G1 (X [ g₁ ↦ doRd (X g₁) j ]) g r T1' noRace2 noRace3) ,
                      λ Gs ws1 _ → doRd-WS _ _ _ _ _ ws1)
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
    lem : MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g) ≡ (i , all)
    lem = cong MemEvs.wr ([↦]-simp-≡ _ _ _)

    fst : j ≢ MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g) .proj₁
    fst = cast (cong (j ≢_) (sym (Data.Product.Properties.×-≡,≡←≡ lem .proj₁))) (≢-sym i≢j)

    snd : j ∈ MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g) .proj₂
    snd = cast (cong (j ∈_) (sym (Data.Product.Properties.×-≡,≡←≡ lem .proj₂))) refl

  race2 : ¬ noRacingWr i (MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g))
  race2 = yesRacingWr→¬noRacingWr i (MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g)) (fst , snd)
    where
    lem : MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g) ≡ (j , all)
    lem = cong MemEvs.wr ([↦]-simp-≡ _ _ _)

    fst : i ≢ MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g) .proj₁
    fst = cast (cong (i ≢_) (sym (Data.Product.Properties.×-≡,≡←≡ lem .proj₁))) i≢j

    snd : i ∈ MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g) .proj₂
    snd = cast (cong (i ∈_) (sym (Data.Product.Properties.×-≡,≡←≡ lem .proj₂))) refl
... | no g≢g₁ = inj₁ ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doWr (X g) i ]) g₁) j ] ,
                      wrGbl R2 G2 (X [ g ↦ doWr (X g) i ]) g₁ r₁ T2' noRace1 noRace2 ,
                      cast rhs-step≡ (wrGbl R1 G1 (X [ g₁ ↦ doWr (X g₁) j ]) g r T1' noRace3 noRace4) ,
                      λ Gs ws1 ws2 → doWr-WS ℂ Gs X g g₁ i j ws1 ws2)
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

syncEnvs-∉ : ∀ {A} i I X (Gs : GEnvs A) → i ∉ I → (syncEnvs I X Gs) i ≡ Gs i
syncEnvs-∉ i I X Gs i∉I = funext lem
  where
  lem : (g : Gid) → syncEnvs I X Gs i g ≡ Gs i g
  lem g with ∈-dec i I | ∈-dec (proj₁ (MemEvs.wr (X g))) I
  ... | yes i∈I | yes _ = ⊥-elim ((∉→¬∈ i I i∉I) i∈I)
  ... | yes i∈I | no _ = ⊥-elim ((∉→¬∈ i I i∉I) i∈I)
  ... | no _ | yes _ = refl
  ... | no _ | no _ = refl

syncStep-∉ : ∀ {ℂ} i I (Ts : Prog ℂ) p → i ∉ I → (syncStep I Ts p) i ≡ Ts i
syncStep-∉ i I Ts p i∉I with ∈-dec i I
... | yes i∈I = ⊥-elim ((∉→¬∈ i I i∉I) i∈I)
... | no _ = refl

∈∧∉→≢ : ∀ (i1 i2 : Tid) (I : TidSet) → i1 ∈ I → i2 ∉ I → i1 ≢ i2
∈∧∉→≢ i1 i2 I i1∈I i2∉I with tidEq i1 i2
... | yes refl = ⊥-elim (false≢true (sym i2∉I ∙ i1∈I))
... | no i1≢i2 = i1≢i2

canSync-∉ : ∀ {ℂ} i I Ts T → i ∉ I → canSync {ℂ} I Ts → canSync {ℂ} I (Ts [ i ↦ T ])
canSync-∉ i I Ts T i∉I p j j∈I = map (λ q → Ts≡ ∙ q) (λ q → (q .proj₁) , (Ts≡ ∙ q .proj₂)) (p j j∈I)
  where
  Ts≡ : (Ts [ i ↦ T ]) j ≡ Ts j
  Ts≡ = [↦]-simp-≢ Ts i j T (≢-sym (∈∧∉→≢ j i I j∈I i∉I))

syncEnvs-XX' : ∀ {ℂ} I X X' (Gs : GEnvs ℂ) i (G : GEnv ℂ) j g
  → i ∉ I
  → syncEnvs I X (Gs [ i ↦ G ]) j g ≡ syncEnvs I X' (Gs [ i ↦ G ]) j g
syncEnvs-XX' I X X' Gs i G j g i∉I with ∈-dec j I | ∈-dec (proj₁ (MemEvs.wr (X g))) I | ∈-dec (proj₁ (MemEvs.wr (X' g))) I
... | yes _ | yes _ | yes _ = {!!}
... | yes j∈I | yes _ | no _ = {!!}
... | yes j∈I | no _ | yes _ = {!!}
... | yes _ | no _ | no _ = refl
... | no _ | yes _ | yes _ = refl
... | no _ | yes _ | no _ = refl
... | no _ | no _ | yes _ = refl
... | no _ | no _ | no _ = refl


syncMem-≤-Mem : ∀ i I X → i ∉ I → ≤-Mem i X (syncMem I X)
syncMem-≤-Mem i I X i∉I g = lem-rd , lem-wr
  where
  lem-rd : ≤-Rd i (X g .MemEvs.rd) (syncMem I X g .MemEvs.rd)
  lem-rd p j = map₂ (∈→∈-flip i (X g .MemEvs.rd j) (syncMem I X g .MemEvs.rd j) (syncMemRd-∉ I (X g .MemEvs.rd) j i i∉I)) (p j)

  lem-wr : ≤-Wr i (X g .MemEvs.wr) (syncMem I X g .MemEvs.wr)
  lem-wr = map
    (λ p → p ∙ syncMemWr-simp1 I (X g .MemEvs.wr))
    (∈→∈-flip i (X g .MemEvs.wr .proj₂) (syncMemWr I (X g .MemEvs.wr) .proj₂) (syncMemWr-∉ I (X g .MemEvs.wr) i i∉I))

syncMem-≥-Mem : ∀ i I X → i ∉ I → ≥-Mem i X (syncMem I X)
syncMem-≥-Mem i I X i∉I g = lem-rd , lem-wr
  where
  lem-rd : ≤-Rd i (syncMem I X g .MemEvs.rd) (X g .MemEvs.rd)
  lem-rd p j = map₂ (∈→∈-flip i (syncMem I X g .MemEvs.rd j) (X g .MemEvs.rd j) (syncMemRd-⊆ I (MemEvs.rd (X g)) j i)) (p j)

  lem-wr : ≤-Wr i (syncMem I X g .MemEvs.wr) (X g .MemEvs.wr)
  lem-wr = map
    (λ p → p ∙ sym (syncMemWr-simp1 I (X g .MemEvs.wr)))
    (∈→∈-flip i (syncMem I X g .MemEvs.wr .proj₂) (X g .MemEvs.wr .proj₂) (syncMemWr-⊆ I (MemEvs.wr (X g)) i))

diamond : ∀ {ℂ C C1 C2}
  → StepProgRefl ℂ C C1
  → StepProgRefl ℂ C C2
  → ∃[ C' ] StepProgRefl ℂ C1 C' × StepProgRefl ℂ C2 C'
diamond (refl C) (refl .C) =
  C ,
  refl C ,
  refl C
diamond (refl .(just (Rs , Gs , X , p , Ts))) (schd i Rs Gs X p Ts R G T R' G' X' T' x x₁ x₂ x₃) =
  just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , StepThd-WS x₁ x₃ p , (Ts [ i ↦ T' ])) ,
  schd i Rs Gs X p Ts R G T R' G' X' T' x x₁ x₂ x₃ ,
  refl (just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , StepThd-WS x₁ x₃ p , (Ts [ i ↦ T' ])))
diamond (refl .(just (Rs , Gs , X , p , Ts))) (schdBad i Rs Gs X p Ts R G T x x₁ x₂ x₃) =
  nothing ,
  schdBad i Rs Gs X p Ts R G T x x₁ x₂ x₃ ,
  refl nothing
diamond (refl .(just (Rs , Gs , X , p , Ts))) (sync I Rs Gs X p Ts q) =
  just (Rs , syncEnvs I X Gs , syncMem I X , sync-WS _ I X Gs p , syncStep I Ts q) ,
  sync I Rs Gs X p Ts q ,
  refl (just (Rs , syncEnvs I X Gs , syncMem I X , sync-WS _ I X Gs p , syncStep I Ts q))
diamond (schd i Rs Gs X p Ts R G T R' G' X' T' x x₁ x₂ x₃) (refl .(just (Rs , Gs , X , p , Ts))) =
  just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , StepThd-WS x₁ x₃ p , (Ts [ i ↦ T' ])) ,
  refl (just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , StepThd-WS x₁ x₃ p , (Ts [ i ↦ T' ]))) ,
  schd i Rs Gs X p Ts R G T R' G' X' T' x x₁ x₂ x₃
diamond {ℂ = ℂ} (schd i Rs Gs X p Ts R G T R' G' X' T' x x₁ x₂ x₃) (schd i₁ .Rs .Gs .X .p .Ts R₁ G₁ T₁ R'' G'' X'' T'' x₄ x₅ x₆ x₇) with tidEq i i₁
... | yes refl =
  just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , StepThd-WS x₁ x₃ p , (Ts [ i ↦ T' ])) ,
  refl (just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , StepThd-WS x₁ x₃ p , (Ts [ i ↦ T' ]))) ,
  cast eq' (refl (just ((Rs [ i ↦ R'' ]) , (Gs [ i ↦ G'' ]) , X'' , StepThd-WS x₅ x₇ p , (Ts [ i ↦ T'' ]))))
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
      (just ((Rs [ i ↦ R'' ]) , (Gs [ i ↦ G'' ]) , X'' , StepThd-WS x₅ x₇ p , (Ts [ i ↦ T'' ])))
      (just ((Rs [ i ↦ R'' ]) , (Gs [ i ↦ G'' ]) , X'' , StepThd-WS x₅ x₇ p , (Ts [ i ↦ T'' ])))
    ≡
    StepProgRefl ℂ
      (just ((Rs [ i ↦ R'' ]) , (Gs [ i ↦ G'' ]) , X'' , StepThd-WS x₅ x₇ p , (Ts [ i ↦ T'' ])))
      (just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , StepThd-WS x₁ x₃ p , (Ts [ i ↦ T' ])))
  eq' with eq
  ... | refl = cong (λ a → StepProgRefl ℂ (just ((Rs [ i ↦ R'' ]) , (Gs [ i ↦ G'' ]) , X'' , StepThd-WS x₅ x₇ p , (Ts [ i ↦ T'' ]))) a)
                    (CfgProg-≡-intro (StepThd-WS x₅ x₇ p) (StepThd-WS x₁ x₃ p) refl refl refl refl)
... | no i≢i₁ =
  case nextStep
    (λ (X''' , lhs , rhs , →ws) →
      just ((Rs [ i ↦ R' ] [ i₁ ↦ R'' ]) , (Gs [ i ↦ G' ] [ i₁ ↦ G'' ]) , X''' , →ws (Gs [ i ↦ G' ] [ i₁ ↦ G'' ]) {!!} {!!} , (Ts [ i ↦ T' ] [ i₁ ↦ T'' ])) ,
      {! schd i₁ (Rs [ i ↦ R' ]) (Gs [ i ↦ G' ]) X' (StepThd-WS x₁ x₃ p) (Ts [ i ↦ T' ]) R₁ G₁ T₁ R'' G'' X''' T'' ≡R₁ ≡G₁ ≡T₁ lhs !} ,
      {!!}) -- cast {!!} (schd i (Rs [ i₁ ↦ R'' ]) (Gs [ i₁ ↦ G'' ]) X'' {!!} (Ts [ i₁ ↦ T'' ]) R G T R' G' X''' T' ≡R ≡G ≡T rhs))
    (λ (lhs , rhs) →
      nothing ,
      schdBad i₁ (Rs [ i ↦ R' ]) (Gs [ i ↦ G' ]) X' (StepThd-WS x₁ x₃ p) (Ts [ i ↦ T' ]) R₁ G₁ T₁ ≡R₁ ≡G₁ ≡T₁ lhs ,
      schdBad i (Rs [ i₁ ↦ R'' ]) (Gs [ i₁ ↦ G'' ]) X'' (StepThd-WS x₅ x₇ p) (Ts [ i₁ ↦ T'' ]) R G T ≡R ≡G ≡T rhs)
  where
  nextStep : (
    ∃[ X''' ]
      StepThd ℂ i₁ (just (R₁ , G₁ , X' , T₁)) (just (R'' , G'' , X''' , T'')) ×
      StepThd ℂ i (just (R , G , X'' , T)) (just (R' , G' , X''' , T')) ×
      (∀ Gs → WellSynced ℂ Gs X' → WellSynced ℂ Gs X'' → WellSynced ℂ Gs X''')
    ) ⊎ (
      StepThd ℂ i₁ (just (R₁ , G₁ , X' , T₁)) nothing × StepThd _ i (just (R , G , X'' , T)) nothing
    )
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

  lhs' : (X''' : Mem)
    → (lhs : StepThd ℂ i₁ (just (R₁ , G₁ , X' , T₁)) (just (R'' , G'' , X''' , T'')))
    → StepProg ℂ
        (just (Rs [ i ↦ R' ] , Gs [ i ↦ G' ] , X' , StepThd-WS x₁ x₃ p , Ts [ i ↦ T' ]))
        (just ((Rs [ i ↦ R' ]) [ i₁ ↦ R'' ] , (Gs [ i ↦ G' ]) [ i₁ ↦ G'' ] , X''' , StepThd-WS ≡G₁ lhs (StepThd-WS x₁ x₃ p) , (Ts [ i ↦ T' ]) [ i₁ ↦ T'' ]))
  lhs' X''' lhs = schd i₁ (Rs [ i ↦ R' ]) (Gs [ i ↦ G' ]) X' (StepThd-WS x₁ x₃ p) (Ts [ i ↦ T' ]) R₁ G₁ T₁ R'' G'' X''' T'' ≡R₁ ≡G₁ ≡T₁ lhs

  -- rhs≡ : ∀ X''' ws''' →
  --   StepProgRefl ℂ
  --     (just ((Rs [ i₁ ↦ R'' ]) , (Gs [ i₁ ↦ G'' ]) , X'' , StepThd-WS x₅ x₇ p , (Ts [ i₁ ↦ T'' ])))
  --     (just ((Rs [ i₁ ↦ R'' ] [ i ↦ R' ]) , (Gs [ i₁ ↦ G'' ] [ i ↦ G' ]) , X''' , {!!} , (Ts [ i₁ ↦ T'' ] [ i ↦ T' ])))
  --   ≡
  --   StepProgRefl ℂ
  --     (just ((Rs [ i₁ ↦ R'' ]) , (Gs [ i₁ ↦ G'' ]) , X'' , StepThd-WS x₅ x₇ p , (Ts [ i₁ ↦ T'' ])))
  --     (just ((Rs [ i ↦ R' ] [ i₁ ↦ R'' ]) , (Gs [ i ↦ G' ] [ i₁ ↦ G'' ]) , X''' , {!!} , (Ts [ i ↦ T' ] [ i₁ ↦ T'' ])))
  -- rhs≡ X''' ws''' = {!!}
  -- rhs≡ X''' ws''' = cong₃ (λ a b c →
  --   StepProgRefl ℂ
  --     (just ((Rs [ i₁ ↦ R'' ]) , (Gs [ i₁ ↦ G'' ]) , X'' , StepThd-WS x₅ x₇ p , (Ts [ i₁ ↦ T'' ])))
  --     (just (a , b , X''' , ws''' , c)))
  --   Rs≡ Gs≡ Ts≡
diamond {ℂ = ℂ} (schd i Rs Gs X p Ts R G T R' G' X' T' x x₁ x₂ x₃) (schdBad i₁ .Rs .Gs .X .p .Ts R₁ G₁ T₁ x₄ x₅ x₆ x₇) with tidEq i i₁
... | yes refl =
  ⊥-elim (nothing≢just (sym eq))
  where
  R≡ : R ≡ R₁
  R≡ = trans (sym x) x₄

  G≡ : G ≡ G₁
  G≡ = trans (sym x₁) x₅

  T≡ : T ≡ T₁
  T≡ = trans (sym x₂) x₆

  eq : just (R' , G' , X' , T') ≡ nothing
  eq with R≡ | G≡ | T≡
  ... | refl | refl | refl = StepThd-≡ x₃ x₇
... | no i≢i₁ =
  nothing ,
  lhs ,
  refl nothing
  where
  lhsThd : StepThd ℂ i₁ (just (R₁ , G₁ , X' , T₁)) nothing
  lhsThd = StepThd-mono-nothing (StepThd-≤-Mem x₃ i₁ (≢-sym i≢i₁)) x₇

  lhs : StepProgRefl ℂ (just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , StepThd-WS x₁ x₃ p , (Ts [ i ↦ T' ]))) nothing
  lhs = schdBad i₁ (Rs [ i ↦ R' ]) (Gs [ i ↦ G' ]) X' (StepThd-WS x₁ x₃ p) (Ts [ i ↦ T' ]) R₁ G₁ T₁
    (trans ([↦]-simp-≢ Rs i i₁ R' i≢i₁) x₄)
    (trans ([↦]-simp-≢ Gs i i₁ G' i≢i₁) x₅)
    (trans ([↦]-simp-≢ Ts i i₁ T' i≢i₁) x₆)
    lhsThd
diamond {ℂ = ℂ} (schdBad i Rs Gs X p Ts R G T x x₁ x₂ x₃) (schd i₁ .Rs .Gs .X .p .Ts R₁ G₁ T₁ R' G' X' T' x₄ x₅ x₆ x₇) with tidEq i i₁
... | yes refl =
  ⊥-elim (nothing≢just (sym eq))
  where
  R≡ : R ≡ R₁
  R≡ = trans (sym x) x₄

  G≡ : G ≡ G₁
  G≡ = trans (sym x₁) x₅

  T≡ : T ≡ T₁
  T≡ = trans (sym x₂) x₆

  eq : just (R' , G' , X' , T') ≡ nothing
  eq with R≡ | G≡ | T≡
  ... | refl | refl | refl = StepThd-≡ x₇ x₃
... | no i≢i₁ =
  nothing ,
  refl nothing ,
  rhs
  where
  rhsThd : StepThd ℂ i (just (R , G , X' , T)) nothing
  rhsThd = StepThd-mono-nothing (StepThd-≤-Mem x₇ i i≢i₁) x₃

  rhs : StepProgRefl ℂ (just ((Rs [ i₁ ↦ R' ]) , (Gs [ i₁ ↦ G' ]) , X' , StepThd-WS x₅ x₇ p , (Ts [ i₁ ↦ T' ]))) nothing
  rhs = schdBad i (Rs [ i₁ ↦ R' ]) (Gs [ i₁ ↦ G' ]) X' (StepThd-WS x₅ x₇ p) (Ts [ i₁ ↦ T' ]) R G T
    (trans ([↦]-simp-≢ Rs i₁ i R' (≢-sym i≢i₁)) x)
    (trans ([↦]-simp-≢ Gs i₁ i G' (≢-sym i≢i₁)) x₁)
    (trans ([↦]-simp-≢ Ts i₁ i T' (≢-sym i≢i₁)) x₂)
    rhsThd
diamond {ℂ = ℂ} (schd i Rs Gs X ws Ts R G T R' G' X' T' x x₁ x₂ x₃) (sync I .Rs .Gs .X .ws .Ts q) =
  just (Rs [ i ↦ R' ] , syncEnvs I X (Gs [ i ↦ G' ]) , syncMem I X' , {!!} , syncStep I (Ts [ i ↦ T' ]) p') ,
  stepLeft' ,
  stepRight'
  where
  i∉I : i ∉ I
  i∉I = StepThd-sync-step x₂ q x₃

  p' : canSync I (Ts [ i ↦ T' ])
  p' = canSync-∉ i I Ts T' i∉I q

  Gs≡ : syncEnvs I X Gs i ≡ G
  Gs≡ = syncEnvs-∉ i I X Gs i∉I ∙ x₁

  Ts≡ : syncStep I Ts q i ≡ T
  Ts≡ = syncStep-∉ i I Ts q i∉I ∙ x₂

  syncEnvs-comm : (syncEnvs I X Gs) [ i ↦ G' ] ≡ syncEnvs I X (Gs [ i ↦ G' ])
  syncEnvs-comm = {!!}

  syncStep-comm : (syncStep I Ts q) [ i ↦ T' ] ≡ syncStep I (Ts [ i ↦ T' ]) p'
  syncStep-comm = {!!}

  stepLeft : StepProgRefl ℂ
      (just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , StepThd-WS x₁ x₃ ws , (Ts [ i ↦ T' ])))
      (just ((Rs [ i ↦ R' ]) , syncEnvs I X' (Gs [ i ↦ G' ]) , syncMem I X' , sync-WS _ I X' (Gs [ i ↦ G' ]) (StepThd-WS x₁ x₃ ws) , syncStep I (Ts [ i ↦ T' ]) p'))
  stepLeft = sync I (Rs [ i ↦ R' ]) (Gs [ i ↦ G' ]) X' (StepThd-WS x₁ x₃ ws) (Ts [ i ↦ T' ]) p'

  stepLeft' = cast (cong (λ a → StepProgRefl ℂ
      (just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , StepThd-WS x₁ x₃ ws , (Ts [ i ↦ T' ])))
      (just ((Rs [ i ↦ R' ]) , a , syncMem I X' , {!!} , syncStep I (Ts [ i ↦ T' ]) p')))
    (funext λ j → funext λ g → syncEnvs-XX' I X' X Gs i G' j g i∉I)) stepLeft

  stepRight : StepProgRefl ℂ
      (just (Rs , syncEnvs I X Gs , syncMem I X , sync-WS _ I X Gs ws , syncStep I Ts q))
      {!!}
  stepRight = schd i Rs (syncEnvs I X Gs) (syncMem I X) (sync-WS _ I X Gs ws) (syncStep I Ts q) R G T R' G' (syncMem I X') T' x Gs≡ Ts≡  (StepThd-just-sync i∉I x₃)

  stepRight' = cast (cong₂ (λ a b → StepProgRefl ℂ
      (just (Rs , syncEnvs I X Gs , syncMem I X , sync-WS _ I X Gs ws , syncStep I Ts q))
      (just ((Rs [ i ↦ R' ]) , a , syncMem I X' , {!!} , b)))
    syncEnvs-comm syncStep-comm) stepRight
diamond (sync I Rs Gs X ws Ts q) (schd i .Rs .Gs .X .ws .Ts R G T R' G' X' T' x x₁ x₂ x₃) = {!!}
  where
  i∉I : i ∉ I
  i∉I = StepThd-sync-step x₂ q x₃
diamond (schdBad i Rs Gs X ws Ts R G T x x₁ x₂ x₃) (refl .(just (Rs , Gs , X , ws , Ts))) =
  nothing ,
  refl nothing ,
  schdBad i Rs Gs X ws Ts R G T x x₁ x₂ x₃
diamond (schdBad i Rs Gs X ws Ts R G T x x₁ x₂ x₃) (schdBad i₁ .Rs .Gs .X .ws .Ts R₁ G₁ T₁ x₄ x₅ x₆ x₇) =
  nothing ,
  refl nothing ,
  refl nothing
diamond {ℂ = ℂ} (schdBad i Rs Gs X ws Ts R G T x x₁ x₂ x₃) (sync I .Rs .Gs .X .ws .Ts q) =
  nothing ,
  refl nothing ,
  rhs
  where
  i∉I : i ∉ I
  i∉I = StepThd-sync-step x₂ q x₃

  rhs : StepProgRefl ℂ (just (Rs , syncEnvs I X Gs , syncMem I X , sync-WS _ I X Gs ws , syncStep I Ts q)) nothing
  rhs = schdBad i Rs (syncEnvs I X Gs) (syncMem I X) (sync-WS _ I X Gs ws) (syncStep I Ts q) R G T x
    (syncEnvs-∉ i I X Gs i∉I ∙ x₁)
    (syncStep-∉ i I Ts q i∉I ∙ x₂)
    (StepThd-mono-nothing (syncMem-≤-Mem i I X i∉I) x₃)
diamond {ℂ = ℂ} (sync I Rs Gs X ws Ts q) (schdBad i .Rs .Gs .X .ws .Ts R G T x x₁ x₂ x₃) =
  nothing ,
  lhs ,
  refl nothing
  where
  i∉I : i ∉ I
  i∉I = StepThd-sync-step x₂ q x₃

  lhs : StepProgRefl ℂ (just (Rs , syncEnvs I X Gs , syncMem I X , sync-WS _ I X Gs ws , syncStep I Ts q)) nothing
  lhs = schdBad i Rs (syncEnvs I X Gs) (syncMem I X) (sync-WS _ I X Gs ws) (syncStep I Ts q) R G T x
    (syncEnvs-∉ i I X Gs i∉I ∙ x₁)
    (syncStep-∉ i I Ts q i∉I ∙ x₂)
    (StepThd-mono-nothing (syncMem-≤-Mem i I X i∉I) x₃)
diamond (sync I Rs Gs X ws Ts q) (refl .(just (Rs , Gs , X , ws , Ts))) =
  just (Rs , syncEnvs I X Gs , syncMem I X , sync-WS _ I X Gs ws , syncStep I Ts q) ,
  refl (just (Rs , syncEnvs I X Gs , syncMem I X , sync-WS _ I X Gs ws , syncStep I Ts q)) ,
  sync I Rs Gs X ws Ts q
diamond (sync I Rs Gs X ws Ts q) (sync I₁ .Rs .Gs .X .ws .Ts p₁) = {!!}
