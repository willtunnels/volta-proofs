module Volta.Confluence where

open import Function.Base using (_∘_; _$_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; _≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂; map; map₁; map₂)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties
open import Data.Bool using (Bool; true; false; not)
import Data.Bool.Properties
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Product.Properties using (×-≡,≡←≡; Σ-≡,≡→≡)
open import Relation.Nullary.Decidable using (Dec; yes; no; toSum)
open import Relation.Nullary.Negation using (¬_)

import Relation.Binary.HeterogeneousEquality as H
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Volta.Prog
open import Volta.Util
open import Volta.DecSet

StepThd-≤-Mem : ∀ {ℂ i R1 G1 X1 T1 R2 G2 X2 T2}
  → StepThd ℂ i (just (R1 , G1 , X1 , T1)) (just (R2 , G2 , X2 , T2))
  → ∀ j → j ≢ i → ≤-Mem j X1 X2
StepThd-≤-Mem {X1 = X1} (const _ _ _ r c _) j i≢j = ≤-Mem-refl j X1
StepThd-≤-Mem {X1 = X1} (binOp _ _ _ r r1 r2 _) j i≢j = ≤-Mem-refl j X1
StepThd-≤-Mem {X1 = X1} (rdReg _ _ _ r1 r2 _) j i≢j = ≤-Mem-refl j X1
StepThd-≤-Mem {i = i} {X1 = X1} (rdGbl _ _ _ r g _ x) j i≢j = ≤-Mem-doRd j i X1 g
StepThd-≤-Mem {i = i} {X1 = X1} (wrGbl _ _ _ g r _ x x₁) j i≢j = ≤-Mem-doWr-other j i X1 g i≢j

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

StepThd-change-G-nothing : ∀ {ℂ i R G G' X T}
  → StepThd ℂ i (just (R , G , X , T)) nothing
  → StepThd ℂ i (just (R , G' , X , T)) nothing
StepThd-change-G-nothing (rdGblBad _ _ _ r g T x) = rdGblBad _ _ _ r g T x
StepThd-change-G-nothing (wrGblBad _ _ _ g r T x) = wrGblBad _ _ _ g r T x

StepThd-just-sync : ∀ {ℂ i I R G X T R' G' X' T'}
  → i ∉ I
  → StepThd ℂ i (just (R , G , X , T)) (just (R' , G' , X' , T'))
  → StepThd ℂ i (just (R , G , syncMem I X , T)) (just (R' , G' , syncMem I X' , T'))
StepThd-just-sync {ℂ} {i} {I} {R} {G} {X} {T} {R'} {G'} {X'} {T'} i∉I (const .R .G .X r c .T') = const R G (syncMem I X) r c T'
StepThd-just-sync {ℂ} {i} {I} {R} {G} {X} {T} {R'} {G'} {X'} {T'} i∉I (binOp .R .G .X r r1 r2 .T') = binOp R G (syncMem I X) r r1 r2 T'
StepThd-just-sync {ℂ} {i} {I} {R} {G} {X} {T} {R'} {G'} {X'} {T'} i∉I (rdReg .R .G .X r1 r2 .T') = rdReg R G (syncMem I X) r1 r2 T'
StepThd-just-sync {ℂ} {i} {I} {R} {G} {X} {T} {R'} {G'} {X'} {T'} i∉I (rdGbl .R .G .X r g .T' x) = subst (StepThd ℂ i (just (R , G , syncMem I X , rdGbl r g ⨟ T'))) mem≡ (rdGbl R G (syncMem I X) r g T' noRace)
  where
  noRace : noRacingWr i (MemEvs.wr (syncMem I X g))
  noRace = map (λ p → cast (cong (i ≡_) (sym (syncMemWr-simp1 I (X g .MemEvs.wr)))) p) (λ p → lem (∈-dec (X g .MemEvs.wr .proj₁) I) p) x
    where
    lem : ∀ {j J} → Dec (j ∈ I) → i ∉ J → i ∉ syncMemWr I (j , J) .proj₂
    lem {j} {J} dec i∉J with syncMemWr I (j , J) .proj₂ i | inspect (syncMemWr I (j , J) .proj₂) i
    ... | true | [ eq ] = ⊥-elim (false≢true (sym i∉J ∙ syncMemWr-⊆ I (j , J) i (subst (_≡ true) (sym eq) refl)))
    ... | false | _ = refl
  
  mem≡ : just ((R [ r ↦ G g ]) , G , (syncMem I X [ g ↦ doRd (syncMem I X g) i ]) , T') ≡ just ((R [ r ↦ G g ]) , G , syncMem I (X [ g ↦ doRd (X g) i ]) , T')
  mem≡ = cong (λ X' → just ((R [ r ↦ G g ]) , G , X' , T')) (funext λ g' → lem-g' g' (gidEq g g'))
    where
    lem-g' : ∀ g' → Dec (g ≡ g') → (syncMem I X [ g ↦ doRd (syncMem I X g) i ]) g' ≡ syncMem I (X [ g ↦ doRd (X g) i ]) g'
    lem-g' .g (yes refl) = begin
        (syncMem I X [ g ↦ doRd (syncMem I X g) i ]) g
      ≡⟨ [↦]-simp-≡ (syncMem I X) g (doRd (syncMem I X g) i) ⟩
        doRd (syncMem I X g) i
      ≡⟨ lem-rdEq ⟩
        syncMem I (X [ g ↦ doRd (X g) i ]) g
      ∎
      where
      lem-rdEq : doRd (syncMem I X g) i ≡ syncMem I (X [ g ↦ doRd (X g) i ]) g
      lem-rdEq = MemEvs-≡ rdEq wrEq
        where
        helper : ∀ j → Dec (i ≡ j) → MemEvs.rd (doRd (syncMem I X g) i) j ≡ MemEvs.rd (syncMem I (X [ g ↦ doRd (X g) i ]) g) j
        helper .i (yes refl) = begin
            (syncMemRd I (MemEvs.rd (X g)) [ i ↦ all ]) i
          ≡⟨ [↦]-simp-≡ (syncMemRd I (MemEvs.rd (X g))) i all ⟩
            all
          ≡⟨ sym ([↦]-simp-≡ (MemEvs.rd (X g)) i all) ⟩
            (MemEvs.rd (X g) [ i ↦ all ]) i
          ≡⟨ refl ⟩
            MemEvs.rd (doRd (X g) i) i
          ≡⟨ cong (λ m → MemEvs.rd m i) (sym ([↦]-simp-≡ X g (doRd (X g) i))) ⟩
            MemEvs.rd ((X [ g ↦ doRd (X g) i ]) g) i
          ≡⟨ sym (syncMemRd-simp-∉ I (MemEvs.rd ((X [ g ↦ doRd (X g) i ]) g)) i i∉I) ⟩
            (syncMemRd I (MemEvs.rd ((X [ g ↦ doRd (X g) i ]) g))) i
          ∎
        helper j (no i≢j) = trans ([↦]-simp-≢ (syncMemRd I (MemEvs.rd (X g))) i j all i≢j)
                                    (trans (funext λ k → sym (syncMemRd-cong I (MemEvs.rd (X g) [ i ↦ all ]) (MemEvs.rd (X g)) j k (cong (_$ k) ([↦]-simp-≢ (MemEvs.rd (X g)) i j all i≢j))))
                                           (cong (λ m → syncMemRd I (MemEvs.rd m) j) (sym ([↦]-simp-≡ X g (doRd (X g) i)))))
        
        rdEq : MemEvs.rd (doRd (syncMem I X g) i) ≡ MemEvs.rd (syncMem I (X [ g ↦ doRd (X g) i ]) g)
        rdEq = funext λ j → helper j (tidEq i j)
        
        wrEq : MemEvs.wr (doRd (syncMem I X g) i) ≡ MemEvs.wr (syncMem I (X [ g ↦ doRd (X g) i ]) g)
        wrEq = cong (syncMemWr I) (cong MemEvs.wr (sym ([↦]-simp-≡ X g (doRd (X g) i))))
    lem-g' g' (no g≢g') = trans ([↦]-simp-≢ (syncMem I X) g g' (doRd (syncMem I X g) i) g≢g')
                                  (sym (cong (λ m → evs (syncMemRd I (MemEvs.rd m)) (syncMemWr I (MemEvs.wr m))) ([↦]-simp-≢ X g g' (doRd (X g) i) g≢g')))
StepThd-just-sync {ℂ} {i} {I} {R} {G} {X} {T} {R'} {G'} {X'} {T'} i∉I (wrGbl .R .G .X g r .T' noRaceRd noRaceWr) = subst (StepThd ℂ i (just (R , G , syncMem I X , wrGbl g r ⨟ T'))) mem≡ (wrGbl R G (syncMem I X) g r T' noRaceRd' noRaceWr')
  where
  noRaceRd' : noRacingRd i (MemEvs.rd (syncMem I X g))
  noRaceRd' j = map (λ p → cast (cong (i ≡_) refl) p) (λ p → lem p) (noRaceRd j)
    where
    lem : i ∉ MemEvs.rd (X g) j → i ∉ syncMemRd I (MemEvs.rd (X g)) j
    lem i∉J with syncMemRd I (MemEvs.rd (X g)) j i | inspect (syncMemRd I (MemEvs.rd (X g)) j) i
    ... | true | [ eq ] = ⊥-elim (false≢true (sym i∉J ∙ syncMemRd-⊆ I (MemEvs.rd (X g)) j i (subst (_≡ true) (sym eq) refl)))
    ... | false | _ = refl
  
  noRaceWr' : noRacingWr i (MemEvs.wr (syncMem I X g))
  noRaceWr' = map (λ p → cast (cong (i ≡_) (sym (syncMemWr-simp1 I (X g .MemEvs.wr)))) p) (λ p → lem (∈-dec (X g .MemEvs.wr .proj₁) I) p) noRaceWr
    where
    lem : ∀ {j J} → Dec (j ∈ I) → i ∉ J → i ∉ syncMemWr I (j , J) .proj₂
    lem {j} {J} dec i∉J with syncMemWr I (j , J) .proj₂ i | inspect (syncMemWr I (j , J) .proj₂) i
    ... | true | [ eq ] = ⊥-elim (false≢true (sym i∉J ∙ syncMemWr-⊆ I (j , J) i (subst (_≡ true) (sym eq) refl)))
    ... | false | _ = refl
  
  mem≡ : just (R , (G [ g ↦ R r ]) , (syncMem I X [ g ↦ doWr (syncMem I X g) i ]) , T') ≡ just (R , (G [ g ↦ R r ]) , syncMem I (X [ g ↦ doWr (X g) i ]) , T')
  mem≡ = cong (λ X' → just (R , (G [ g ↦ R r ]) , X' , T')) (funext λ g' → lem-g' g' (gidEq g g'))
    where
    lem-g' : ∀ g' → Dec (g ≡ g') → (syncMem I X [ g ↦ doWr (syncMem I X g) i ]) g' ≡ syncMem I (X [ g ↦ doWr (X g) i ]) g'
    lem-g' .g (yes refl) = begin
        (syncMem I X [ g ↦ doWr (syncMem I X g) i ]) g
      ≡⟨ [↦]-simp-≡ (syncMem I X) g (doWr (syncMem I X g) i) ⟩
        doWr (syncMem I X g) i
      ≡⟨ lem-wrEq ⟩
        syncMem I (X [ g ↦ doWr (X g) i ]) g
      ∎
      where
      lem-wrEq : doWr (syncMem I X g) i ≡ syncMem I (X [ g ↦ doWr (X g) i ]) g
      lem-wrEq = MemEvs-≡ rdEq wrEq
        where
        helper : ∀ j → Dec (i ≡ j) → MemEvs.rd (doWr (syncMem I X g) i) j ≡ MemEvs.rd (syncMem I (X [ g ↦ doWr (X g) i ]) g) j
        helper j dec = begin
            MemEvs.rd (doWr (syncMem I X g) i) j
          ≡⟨ refl ⟩
            syncMemRd I (MemEvs.rd (X g)) j
          ≡⟨ cong (λ m → syncMemRd I (MemEvs.rd m) j) (sym ([↦]-simp-≡ X g (doWr (X g) i))) ⟩
            syncMemRd I (MemEvs.rd ((X [ g ↦ doWr (X g) i ]) g)) j
          ∎
        
        rdEq : MemEvs.rd (doWr (syncMem I X g) i) ≡ MemEvs.rd (syncMem I (X [ g ↦ doWr (X g) i ]) g)
        rdEq = funext λ j → helper j (tidEq i j)
        
        wrEq : MemEvs.wr (doWr (syncMem I X g) i) ≡ MemEvs.wr (syncMem I (X [ g ↦ doWr (X g) i ]) g)
        wrEq = begin
            MemEvs.wr (doWr (syncMem I X g) i)
          ≡⟨ refl ⟩
            (i , all)
          ≡⟨ cong (i ,_) (sym (syncMemWr-simp-∉ I (i , all) i∉I)) ⟩
            (i , syncMemWr I (i , all) .proj₂)
          ≡⟨ cong (λ j → (j , syncMemWr I (i , all) .proj₂)) (sym (syncMemWr-simp1 I (i , all))) ⟩
            (syncMemWr I (i , all) .proj₁ , syncMemWr I (i , all) .proj₂)
          ≡⟨ refl ⟩
            syncMemWr I (i , all)
          ≡⟨ cong (syncMemWr I) (sym (cong MemEvs.wr ([↦]-simp-≡ X g (doWr (X g) i)))) ⟩
            syncMemWr I (MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g))
          ∎
    lem-g' g' (no g≢g') = trans ([↦]-simp-≢ (syncMem I X) g g' (doWr (syncMem I X g) i) g≢g')
                                  (sym (cong (λ m → evs (syncMemRd I (MemEvs.rd m)) (syncMemWr I (MemEvs.wr m))) ([↦]-simp-≢ X g g' (doWr (X g) i) g≢g')))

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

StepThd-≢-comm : ∀ {ℂ i j R1 R1' R2 R2' T1 T1' T2' T2 G G'1 G'2 X X'1 X'2}
  → i ≢ j
  → StepThd ℂ i (just (R1 , G , X , T1)) (just (R1' , G'1 , X'1 , T1'))
  → StepThd ℂ j (just (R2 , G , X , T2)) (just (R2' , G'2 , X'2 , T2'))
  → (∃[ G'' ] ∃[ X'' ]
              StepThd ℂ j (just (R2 , G'1 , X'1 , T2)) (just (R2' , G'' , X'' , T2')) ×
              StepThd ℂ i (just (R1 , G'2 , X'2 , T1)) (just (R1' , G'' , X'' , T1')))
  ⊎ (StepThd ℂ j (just (R2 , G , X'1 , T2)) nothing ×
     StepThd ℂ i (just (R1 , G , X'2 , T1)) nothing)
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (const _ _ _ r c _) (const _ _ _ r₁ c₁ _) =
  inj₁ (G , X , const R2 G X r₁ c₁ T2' , const R1 G X r c T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (const _ _ _ r c _) (binOp _ _ _ r₁ r1 r2 _) =
  inj₁ (G , X , binOp R2 G X r₁ r1 r2 T2' , const R1 G X r c T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (const _ _ _ r c _) (rdReg _ _ _ r1 r2 _) =
  inj₁ (G , X , rdReg R2 G X r1 r2 T2' , const R1 G X r c T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (const _ _ _ r c _) (rdGbl _ _ _ r₁ g _ x) =
  inj₁ (G , (X [ g ↦ doRd (X g) j ]) , rdGbl R2 G X r₁ g T2' x , const R1 G (X [ g ↦ doRd (X g) j ]) r c T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (const _ _ _ r c _) (wrGbl _ _ _ g r₁ _ x x₁) =
  inj₁ ((G [ g ↦ R2 r₁ ]) , (X [ g ↦ doWr (X g) j ]) , wrGbl R2 G X g r₁ T2' x x₁ , const R1 (G [ g ↦ R2 r₁ ]) (X [ g ↦ doWr (X g) j ]) r c T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (binOp .R1 .G .X r r1 r2 .T1') (const .R2 .G .X r₁ c .T2') =
  inj₁ (G , X , const R2 G X r₁ c T2' , binOp R1 G X r r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (binOp _ _ _ r r1 r2 _) (binOp _ _ _ r₁ r3 r4 _) =
  inj₁ (G , X , binOp R2 G X r₁ r3 r4 T2' , binOp R1 G X r r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (binOp _ _ _ r r1 r2 _) (rdReg _ _ _ r3 r4 _) =
  inj₁ (G , X , rdReg R2 G X r3 r4 T2' , binOp R1 G X r r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (binOp _ _ _ r r1 r2 _) (rdGbl _ _ _ r₁ g _ x) =
  inj₁ (G , (X [ g ↦ doRd (X g) j ]) , rdGbl R2 G X r₁ g T2' x , binOp R1 G (X [ g ↦ doRd (X g) j ]) r r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (binOp _ _ _ r r1 r2 _) (wrGbl _ _ _ g r₁ _ x x₁) =
  inj₁ ((G [ g ↦ R2 r₁ ]) , (X [ g ↦ doWr (X g) j ]) , wrGbl R2 G X g r₁ T2' x x₁ , binOp R1 (G [ g ↦ R2 r₁ ]) (X [ g ↦ doWr (X g) j ]) r r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (rdReg _ _ _ r1 r2 _) (const _ _ _ r c _) =
  inj₁ (G , X , const R2 G X r c T2' , rdReg R1 G X r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (rdReg _ _ _ r1 r2 _) (binOp _ _ _ r r3 r4 _) =
  inj₁ (G , X , binOp R2 G X r r3 r4 T2' , rdReg R1 G X r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (rdReg _ _ _ r1 r2 _) (rdReg _ _ _ r3 r4 _) =
  inj₁ (G , X , rdReg R2 G X r3 r4 T2' , rdReg R1 G X r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (rdReg _ _ _ r1 r2 _) (rdGbl _ _ _ r g _ x) =
  inj₁ (G , (X [ g ↦ doRd (X g) j ]) , rdGbl R2 G X r g T2' x , rdReg R1 G (X [ g ↦ doRd (X g) j ]) r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (rdReg _ _ _ r1 r2 _) (wrGbl _ _ _ g r _ x x₁) =
  inj₁ ((G [ g ↦ R2 r ]) , (X [ g ↦ doWr (X g) j ]) , wrGbl R2 G X g r T2' x x₁ , rdReg R1 (G [ g ↦ R2 r ]) (X [ g ↦ doWr (X g) j ]) r1 r2 T1')
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (rdGbl _ _ _ r g _ x) (const _ _ _ r₁ c _) =
  inj₁ (G , (X [ g ↦ doRd (X g) i ]) , const R2 G (X [ g ↦ doRd (X g) i ]) r₁ c T2' , rdGbl R1 G X r g T1' x)
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (rdGbl _ _ _ r g _ x) (binOp _ _ _ r₁ r1 r2 _) =
  inj₁ (G , (X [ g ↦ doRd (X g) i ]) , binOp R2 G (X [ g ↦ doRd (X g) i ]) r₁ r1 r2 T2' , rdGbl R1 G X r g T1' x)
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (rdGbl _ _ _ r g _ x) (rdReg _ _ _ r1 r2 _) =
  inj₁ (G , (X [ g ↦ doRd (X g) i ]) , rdReg R2 G (X [ g ↦ doRd (X g) i ]) r1 r2 T2' , rdGbl R1 G X r g T1' x)
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (rdGbl _ _ _ r g _ x) (rdGbl _ _ _ r₁ g₁ _ x₁) =
  inj₁ (G , (X [ g ↦ doRd (X g) i ] [ g₁ ↦ doRd ((X [ g ↦ doRd (X g) i ]) g₁) j ]) , rdGbl R2 G (X [ g ↦ doRd (X g) i ]) r₁ g₁ T2' lhs-noRace , cast rhs-step≡ (rdGbl R1 G (X [ g₁ ↦ doRd (X g₁) j ]) r g T1' rhs-noRace))
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
      (just (R1 , G , (X [ g₁ ↦ doRd (X g₁) j ]) , (rdGbl r g ⨟ T1')))
      (just ((R1 [ r ↦ G g ]) , G , (X [ g₁ ↦ doRd (X g₁) j ] [ g ↦ doRd ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) , T1'))
    ≡
    StepThd ℂ i
      (just (R1 , G , (X [ g₁ ↦ doRd (X g₁) j ]) , (rdGbl r g ⨟ T1')))
      (just ((R1 [ r ↦ G g ]) , G , (X [ g ↦ doRd (X g) i ] [ g₁ ↦ doRd ((X [ g ↦ doRd (X g) i ]) g₁) j ]) , T1'))
  rhs-step≡ = cong (λ a →
    StepThd ℂ i
      (just (R1 , G , (X [ g₁ ↦ doRd (X g₁) j ]) , (rdGbl r g ⨟ T1')))
      (just ((R1 [ r ↦ G g ]) , G , a , T1')))
    (funext (mem≡ g g₁))
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (rdGbl _ _ _ r g _ x) (wrGbl _ _ _ g₁ r₁ _ x₁ x₂) with gidEq g g₁
... | yes refl = inj₂ (wrGblBad R2 G (X [ g ↦ doRd (X g) i ]) g r₁ T2' (inj₁ race1) , rdGblBad R1 G (X [ g ↦ doWr (X g) j ]) r g T1' race2)
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
    fst = cast (cong (i ≢_) (sym (×-≡,≡←≡ lem .proj₁))) i≢j

    snd : i ∈ MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g) .proj₂
    snd = cast (cong (i ∈_) (sym (×-≡,≡←≡ lem .proj₂))) refl
... | no g≢g₁ = inj₁ (G [ g₁ ↦ R2 r₁ ] , ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doRd (X g) i ]) g₁) j ]) , wrGbl {ℂ = ℂ} R2 G (X [ g ↦ doRd (X g) i ]) g₁ r₁ T2' noRace1 noRace2 , cast rhs-step≡ (rdGbl R1 (G [ g₁ ↦ R2 r₁ ]) (X [ g₁ ↦ doWr (X g₁) j ]) r g T1' noRace3))
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
        (just (R1 , G'2 , (X [ g₁ ↦ doWr (X g₁) j ]) , (rdGbl r g ⨟ T1')))
        (just ((R1 [ r ↦ (G [ g₁ ↦ R2 r₁ ]) g ]) , G'2 , ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doRd ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) , T1'))
      ≡
      StepThd ℂ i
        (just (R1 , G'2 , (X [ g₁ ↦ doWr (X g₁) j ]) , (rdGbl r g ⨟ T1')))
        (just ((R1 [ r ↦ G g ]) , G'2 , ((X [ g ↦ doRd (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doRd (X g) i ]) g₁) j ]) , T1'))
    rhs-step≡ = cong₂ (λ a b →
      StepThd ℂ i
        (just (R1 , G'2 , (X [ g₁ ↦ doWr (X g₁) j ]) , (rdGbl r g ⨟ T1')))
        (just (a , G'2 , b , T1')))
      (cong (λ a → R1 [ r ↦ a ]) ([↦]-simp-≢ G g₁ g (R2 r₁) (≢-sym g≢g₁))) (funext mem≡)
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (wrGbl _ _ _ g r _ x x₁) (const _ _ _ r₁ c _) =
  inj₁ ((G [ g ↦ R1 r ]) , (X [ g ↦ doWr (X g) i ]) , const R2 (G [ g ↦ R1 r ]) (X [ g ↦ doWr (X g) i ]) r₁ c T2' , wrGbl R1 G X g r T1' x x₁)
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (wrGbl _ _ _ g r _ x x₁) (binOp _ _ _ r₁ r1 r2 _) =
  inj₁ ((G [ g ↦ R1 r ]) , (X [ g ↦ doWr (X g) i ]) , binOp R2 (G [ g ↦ R1 r ]) (X [ g ↦ doWr (X g) i ]) r₁ r1 r2 T2' , wrGbl R1 G X g r T1' x x₁)
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (wrGbl _ _ _ g r _ x x₁) (rdReg _ _ _ r1 r2 _) =
  inj₁ ((G [ g ↦ R1 r ]) , (X [ g ↦ doWr (X g) i ]) , rdReg R2 (G [ g ↦ R1 r ]) (X [ g ↦ doWr (X g) i ]) r1 r2 T2' , wrGbl R1 G X g r T1' x x₁)
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (wrGbl _ _ _ g r _ x x₁) (rdGbl _ _ _ r₁ g₁ _ x₂) with gidEq g g₁
... | yes refl = inj₂ (rdGblBad R2 G (X [ g ↦ doWr (X g) i ]) r₁ g T2' race1 , wrGblBad R1 G (X [ g ↦ doRd (X g) j ]) g r T1' (inj₁ race2))
  where
  race1 : ¬ noRacingWr j (MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g))
  race1 = yesRacingWr→¬noRacingWr j (MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g)) (fst , snd)
    where
    lem : MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g) ≡ (i , all)
    lem = cong MemEvs.wr ([↦]-simp-≡ _ _ _)

    fst : j ≢ MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g) .proj₁
    fst = cast (cong (j ≢_) (sym (×-≡,≡←≡ lem .proj₁))) (≢-sym i≢j)

    snd : j ∈ MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g) .proj₂
    snd = cast (cong (j ∈_) (sym (×-≡,≡←≡ lem .proj₂))) refl

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
... | no g≢g₁ = inj₁ (G [ g ↦ R1 r ] , ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) , cast lhs-step≡ (rdGbl {ℂ = ℂ} R2 G'1 (X [ g ↦ doWr (X g) i ]) r₁ g₁ T2' noRace1) , cast rhs-step≡ (wrGbl R1 G (X [ g₁ ↦ doRd (X g₁) j ]) g r T1' noRace2 noRace3))
    where
    noRace1 : noRacingWr j (MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g₁))
    noRace1 = cast (cong (λ a → noRacingWr j (MemEvs.wr a)) (sym ([↦]-simp-≢ _ _ _ _ g≢g₁))) x₂

    noRace2 : noRacingRd i (MemEvs.rd ((X [ g₁ ↦ doRd (X g₁) j ]) g))
    noRace2 = cast (cong (λ a → noRacingRd i (MemEvs.rd a)) (sym ([↦]-simp-≢ _ _ _ _ (≢-sym g≢g₁)))) x

    noRace3 : noRacingWr i (MemEvs.wr ((X [ g₁ ↦ doRd (X g₁) j ]) g))
    noRace3 = cast (cong (λ a → noRacingWr i (MemEvs.wr a)) (sym ([↦]-simp-≢ _ _ _ _ (≢-sym g≢g₁)))) x₁

    lhs-step≡ :
      StepThd ℂ j
        (just (R2 , G'1 , (X [ g ↦ doWr (X g) i ]) , (rdGbl r₁ g₁ ⨟ T2')))
        (just ((R2 [ r₁ ↦ G'1 g₁ ]) , G'1 , ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) , T2'))
      ≡
      StepThd ℂ j
        (just (R2 , G'1 , (X [ g ↦ doWr (X g) i ]) , (rdGbl r₁ g₁ ⨟ T2')))
        (just ((R2 [ r₁ ↦ G g₁ ]) , G'1 , ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) , T2'))
    lhs-step≡ = cong (λ a →
      StepThd ℂ j
        (just (R2 , G'1 , (X [ g ↦ doWr (X g) i ]) , (rdGbl r₁ g₁ ⨟ T2')))
        (just (a , G'1 , ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) , T2')))
      (cong (λ a → R2 [ r₁ ↦ a ]) ([↦]-simp-≢ G g g₁ (R1 r) g≢g₁))

    mem≡-1 : ∀ g g₁
      → g ≢ g₁
      → ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g ≡
        ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g
    mem≡-1 g g₁ g≢g₁ = begin
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g
      ≡⟨ [↦]-simp-≢ _ _ _ _ (≢-sym g≢g₁) ⟩
        (X [ g ↦ doWr (X g) i ]) g
      ≡⟨ [↦]-simp-≡ _ _ _ ⟩
        doWr (X g) i
      ≡⟨ sym (cong (λ a → doWr a i) ([↦]-simp-≢ _ _ _ _ (≢-sym g≢g₁))) ⟩
        doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i
      ≡⟨ sym ([↦]-simp-≡ _ _ _) ⟩
        ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g
      ∎

    mem≡-2 : ∀ g g₁
      → g ≢ g₁
      → ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g₁ ≡
        ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g₁
    mem≡-2 g g₁ g≢g₁ = begin
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g₁
      ≡⟨ [↦]-simp-≡ _ _ _ ⟩
        doRd ((X [ g ↦ doWr (X g) i ]) g₁) j
      ≡⟨ cong (λ a → doRd a j) ([↦]-simp-≢ _ _ _ _ g≢g₁) ⟩
        doRd (X g₁) j
      ≡⟨ sym ([↦]-simp-≡ _ _ _) ⟩
        (X [ g₁ ↦ doRd (X g₁) j ]) g₁
      ≡⟨ sym ([↦]-simp-≢ (X [ g₁ ↦ doRd (X g₁) j ]) g g₁ _ g≢g₁) ⟩
        ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g₁
      ∎

    mem≡-3 : ∀ g g₁ g₂
      → g ≢ g₁
      → g ≢ g₂
      → g₁ ≢ g₂
      → ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g₂ ≡
        ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g₂
    mem≡-3 g g₁ g₂ g≢g₁ g≢g₂ g₁≢g₂ = begin
        ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g₂
      ≡⟨ [↦]-simp-≢ _ _ _ _ g₁≢g₂ ⟩
        (X [ g ↦ doWr (X g) i ]) g₂
      ≡⟨ [↦]-simp-≢ _ _ _ _ g≢g₂ ⟩
        X g₂
      ≡⟨ sym ([↦]-simp-≢ _ _ _ _ g₁≢g₂) ⟩
        (X [ g₁ ↦ doRd (X g₁) j ]) g₂
      ≡⟨ sym ([↦]-simp-≢ _ _ _ _ g≢g₂) ⟩
        ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g₂
      ∎

    mem≡-1,2,3 : ∀ g g₁ g₂
      → g ≢ g₁
      → ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g₂ ≡
        ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g₂
    mem≡-1,2,3 g g₁ g₂ g≢g₁ with gidEq g g₂ | gidEq g₁ g₂
    ... | yes refl | yes refl = ⊥-elim (g≢g₁ refl)
    ... | yes refl | no g₁≢g₂ = mem≡-1 g₂ g₁ g≢g₁
    ... | no g≢g₂ | yes refl = mem≡-2 g g₂ g≢g₂
    ... | no g≢g₂ | no g₁≢g₂ = mem≡-3 g g₁ g₂ g≢g₁ g≢g₂ g₁≢g₂

    mem≡ : ∀ g₂
      → ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) g₂ ≡
        ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) g₂
    mem≡ g₂ = mem≡-1,2,3 g g₁ g₂ g≢g₁

    rhs-step≡ :
      StepThd ℂ i
        (just (R1 , G , (X [ g₁ ↦ doRd (X g₁) j ]) , (wrGbl g r ⨟ T1')))
        (just (R1 , (G [ g ↦ R1 r ]) , ((X [ g₁ ↦ doRd (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doRd (X g₁) j ]) g) i ]) , T1'))
      ≡
      StepThd ℂ i
        (just (R1 , G , (X [ g₁ ↦ doRd (X g₁) j ]) , (wrGbl g r ⨟ T1')))
        (just (R1 , (G [ g ↦ R1 r ]) , ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doRd ((X [ g ↦ doWr (X g) i ]) g₁) j ]) , T1'))
    rhs-step≡ = cong (λ b →
      StepThd ℂ i
        (just (R1 , G , (X [ g₁ ↦ doRd (X g₁) j ]) , (wrGbl g r ⨟ T1')))
        (just (R1 , (G [ g ↦ R1 r ]) , b , T1')))
      (funext (λ g₂ → sym (mem≡ g₂)))
StepThd-≢-comm {ℂ} {i} {j} {R1} {R1'} {R2} {R2'} {T1} {T1'} {T2'} {T2} {G} {G'1} {G'2} {X} {X'1} {X'2} i≢j (wrGbl _ _ _ g r _ x x₁) (wrGbl _ _ _ g₁ r₁ _ x₂ x₃) with gidEq g g₁
... | yes refl = inj₂ (wrGblBad R2 G (X [ g ↦ doWr (X g) i ]) g r₁ T2' (inj₂ race1) , wrGblBad R1 G (X [ g ↦ doWr (X g) j ]) g r T1' (inj₂ race2))
  where
  race1 : ¬ noRacingWr j (MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g))
  race1 = yesRacingWr→¬noRacingWr j (MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g)) (fst , snd)
    where
    lem : MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g) ≡ (i , all)
    lem = cong MemEvs.wr ([↦]-simp-≡ _ _ _)

    fst : j ≢ MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g) .proj₁
    fst = cast (cong (j ≢_) (sym (×-≡,≡←≡ lem .proj₁))) (≢-sym i≢j)

    snd : j ∈ MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g) .proj₂
    snd = cast (cong (j ∈_) (sym (×-≡,≡←≡ lem .proj₂))) refl

  race2 : ¬ noRacingWr i (MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g))
  race2 = yesRacingWr→¬noRacingWr i (MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g)) (fst , snd)
    where
    lem : MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g) ≡ (j , all)
    lem = cong MemEvs.wr ([↦]-simp-≡ _ _ _)

    fst : i ≢ MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g) .proj₁
    fst = cast (cong (i ≢_) (sym (×-≡,≡←≡ lem .proj₁))) i≢j

    snd : i ∈ MemEvs.wr ((X [ g ↦ doWr (X g) j ]) g) .proj₂
    snd = cast (cong (i ∈_) (sym (×-≡,≡←≡ lem .proj₂))) refl
... | no g≢g₁ = inj₁ ((G [ g₁ ↦ R2 r₁ ]) [ g ↦ R1 r ] , (X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doWr (X g) i ]) g₁) j ] , cast lhs-step≡ (wrGbl R2 (G [ g ↦ R1 r ]) (X [ g ↦ doWr (X g) i ]) g₁ r₁ T2' noRace1 noRace2) , cast rhs-step≡ (wrGbl R1 (G [ g₁ ↦ R2 r₁ ]) (X [ g₁ ↦ doWr (X g₁) j ]) g r T1' noRace3 noRace4))
    where
    noRace1 : noRacingRd j (MemEvs.rd ((X [ g ↦ doWr (X g) i ]) g₁))
    noRace1 = cast (cong (λ a → noRacingRd j (MemEvs.rd a)) (sym ([↦]-simp-≢ _ _ _ _ g≢g₁))) x₂

    noRace2 : noRacingWr j (MemEvs.wr ((X [ g ↦ doWr (X g) i ]) g₁))
    noRace2 = cast (cong (λ a → noRacingWr j (MemEvs.wr a)) (sym ([↦]-simp-≢ _ _ _ _ g≢g₁))) x₃

    noRace3 : noRacingRd i (MemEvs.rd ((X [ g₁ ↦ doWr (X g₁) j ]) g))
    noRace3 = cast (cong (λ a → noRacingRd i (MemEvs.rd a)) (sym ([↦]-simp-≢ _ _ _ _ (≢-sym g≢g₁)))) x

    noRace4 : noRacingWr i (MemEvs.wr ((X [ g₁ ↦ doWr (X g₁) j ]) g))
    noRace4 = cast (cong (λ a → noRacingWr i (MemEvs.wr a)) (sym ([↦]-simp-≢ _ _ _ _ (≢-sym g≢g₁)))) x₁

    gbl≡ : ∀ g₂
      → ((G [ g ↦ R1 r ]) [ g₁ ↦ R2 r₁ ]) g₂ ≡ ((G [ g₁ ↦ R2 r₁ ]) [ g ↦ R1 r ]) g₂
    gbl≡ g₂ with gidEq g g₂ | gidEq g₁ g₂
    ... | yes refl | yes refl = ⊥-elim (g≢g₁ refl)
    ... | yes refl | no g₁≢g₂ = begin
        ((G [ g₂ ↦ R1 r ]) [ g₁ ↦ R2 r₁ ]) g₂
      ≡⟨ [↦]-simp-≢ (G [ g₂ ↦ R1 r ]) g₁ g₂ (R2 r₁) g₁≢g₂ ⟩
        (G [ g₂ ↦ R1 r ]) g₂
      ≡⟨ [↦]-simp-≡ G g₂ (R1 r) ⟩
        R1 r
      ≡⟨ sym ([↦]-simp-≡ (G [ g₁ ↦ R2 r₁ ]) g₂ (R1 r)) ⟩
        ((G [ g₁ ↦ R2 r₁ ]) [ g₂ ↦ R1 r ]) g₂
      ∎
    ... | no g≢g₂ | yes refl = begin
        ((G [ g ↦ R1 r ]) [ g₂ ↦ R2 r₁ ]) g₂
      ≡⟨ [↦]-simp-≡ (G [ g ↦ R1 r ]) g₂ (R2 r₁) ⟩
        R2 r₁
      ≡⟨ sym ([↦]-simp-≡ G g₂ (R2 r₁)) ⟩
        (G [ g₂ ↦ R2 r₁ ]) g₂
      ≡⟨ sym ([↦]-simp-≢ (G [ g₂ ↦ R2 r₁ ]) g g₂ (R1 r) g≢g₂) ⟩
        ((G [ g₂ ↦ R2 r₁ ]) [ g ↦ R1 r ]) g₂
      ∎
    ... | no g≢g₂ | no g₁≢g₂ = begin
        ((G [ g ↦ R1 r ]) [ g₁ ↦ R2 r₁ ]) g₂
      ≡⟨ [↦]-simp-≢ (G [ g ↦ R1 r ]) g₁ g₂ (R2 r₁) g₁≢g₂ ⟩
        (G [ g ↦ R1 r ]) g₂
      ≡⟨ [↦]-simp-≢ G g g₂ (R1 r) g≢g₂ ⟩
        G g₂
      ≡⟨ sym ([↦]-simp-≢ G g₁ g₂ (R2 r₁) g₁≢g₂) ⟩
        (G [ g₁ ↦ R2 r₁ ]) g₂
      ≡⟨ sym ([↦]-simp-≢ (G [ g₁ ↦ R2 r₁ ]) g g₂ (R1 r) g≢g₂) ⟩
        ((G [ g₁ ↦ R2 r₁ ]) [ g ↦ R1 r ]) g₂
      ∎

    lhs-step≡ :
      StepThd ℂ j
        (just (R2 , (G [ g ↦ R1 r ]) , (X [ g ↦ doWr (X g) i ]) , (wrGbl g₁ r₁ ⨟ T2')))
        (just (R2 , ((G [ g ↦ R1 r ]) [ g₁ ↦ R2 r₁ ]) , ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doWr (X g) i ]) g₁) j ]) , T2'))
      ≡
      StepThd ℂ j
        (just (R2 , (G [ g ↦ R1 r ]) , (X [ g ↦ doWr (X g) i ]) , (wrGbl g₁ r₁ ⨟ T2')))
        (just (R2 , ((G [ g₁ ↦ R2 r₁ ]) [ g ↦ R1 r ]) , ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doWr (X g) i ]) g₁) j ]) , T2'))
    lhs-step≡ = cong (λ b →
      StepThd ℂ j
        (just (R2 , (G [ g ↦ R1 r ]) , (X [ g ↦ doWr (X g) i ]) , (wrGbl g₁ r₁ ⨟ T2')))
        (just (R2 , b , ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doWr (X g) i ]) g₁) j ]) , T2')))
      (funext gbl≡)

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
        (just (R1 , G'2 , (X [ g₁ ↦ doWr (X g₁) j ]) , (wrGbl g r ⨟ T1')))
        (just (R1 , (G'2 [ g ↦ R1 r ]) , ((X [ g₁ ↦ doWr (X g₁) j ]) [ g ↦ doWr ((X [ g₁ ↦ doWr (X g₁) j ]) g) i ]) , T1'))
      ≡
      StepThd ℂ i
        (just (R1 , G'2 , (X [ g₁ ↦ doWr (X g₁) j ]) , (wrGbl g r ⨟ T1')))
        (just (R1 , (G'2 [ g ↦ R1 r ]) , ((X [ g ↦ doWr (X g) i ]) [ g₁ ↦ doWr ((X [ g ↦ doWr (X g) i ]) g₁) j ]) , T1'))
    rhs-step≡ = cong (λ a →
      StepThd ℂ i
        (just (R1 , G'2 , (X [ g₁ ↦ doWr (X g₁) j ]) , (wrGbl g r ⨟ T1')))
        (just (R1 , (G'2 [ g ↦ R1 r ]) , a , T1')))
      (funext mem≡)
 
