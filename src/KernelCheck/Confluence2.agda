module KernelCheck.Confluence2 where

open import Function.Base using (_∘_; _$_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; _≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂; map; map₁; map₂)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties
open import Data.Bool using (Bool; true; false; not)
import Data.Bool.Properties
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Product.Properties using (×-≡,≡←≡; ×-≡,≡→≡; Σ-≡,≡→≡)
open import Relation.Nullary.Decidable using (Dec; yes; no; toSum; fromSum)
open import Relation.Nullary.Negation using (¬_)

import Relation.Binary.HeterogeneousEquality as H
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import KernelCheck.Prog
open import KernelCheck.Util
open import KernelCheck.DecSet
open import KernelCheck.Confluence

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

syncStep-∉ : ∀ {ℂ} i I (Ts : Prog ℂ) p → i ∉ I → (syncStep I Ts p) i ≡ Ts i
syncStep-∉ i I Ts p i∉I with ∈-dec i I
... | yes i∈I = ⊥-elim ((∉→¬∈ i I i∉I) i∈I)
... | no _ = refl

canSync-∉ : ∀ {ℂ} i I Ts T → i ∉ I → canSync {ℂ} I Ts → canSync {ℂ} I (Ts [ i ↦ T ])
canSync-∉ i I Ts T i∉I p j j∈I = map (λ q → Ts≡ ∙ q) (λ q → (q .proj₁) , (Ts≡ ∙ q .proj₂)) (p j j∈I)
  where
  Ts≡ : (Ts [ i ↦ T ]) j ≡ Ts j
  Ts≡ = [↦]-simp-≢ Ts i j T (∉∧∈→≢ i j I i∉I j∈I)

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

syncStep-[↦]-comm : ∀ ℂ I (Ts : Prog ℂ) (q : canSync I Ts) Ti i j (i∉I : i ∉ I) → ((syncStep I Ts q) [ i ↦ Ti ]) j ≡ syncStep I (Ts [ i ↦ Ti ]) (canSync-∉ i I Ts Ti i∉I q) j
syncStep-[↦]-comm ℂ I Ts q Ti i j i∉I = lem (tidEq i j) (∈-dec j I)
  where
  q' = canSync-∉ i I Ts Ti i∉I q
  lem : Dec (i ≡ j) → Dec (j ∈ I) → ((syncStep I Ts q) [ i ↦ Ti ]) j ≡ syncStep I (Ts [ i ↦ Ti ]) q' j
  lem (yes refl) (yes j∈I) = ∉∧∈→⊥ i I i∉I j∈I
  lem (yes refl) (no j∉I) = [↦]-simp-≡ (syncStep I Ts q) i Ti ∙ sym (syncStep-simp-∉ I (Ts [ i ↦ Ti ]) q' i i∉I ∙ [↦]-simp-≡ Ts i Ti)
  lem (no i≢j) (yes j∈I) = [↦]-simp-≢ (syncStep I Ts q) i j Ti i≢j ∙ syncStep-∈-≡ I Ts q (Ts [ i ↦ Ti ]) q' j j∈I (sym ([↦]-simp-≢ Ts i j Ti i≢j))
  lem (no i≢j) (no j∉I) = [↦]-simp-≢ (syncStep I Ts q) i j Ti i≢j ∙ syncStep-simp-∉ I Ts q j (¬∈→∉ j I j∉I) ∙ sym (syncStep-simp-∉ I (Ts [ i ↦ Ti ]) q' j (¬∈→∉ j I j∉I) ∙ [↦]-simp-≢ Ts i j Ti i≢j)

liveDisjoint : {ℂ : Magma} (I : TidSet) (J : TidSet) (Ts : Prog ℂ) → Set
liveDisjoint {ℂ} I J Ts = ∀ i → i ∈ (I ∩ J) → Ts i ≡ return

≢→liveDisjoint : {ℂ : Magma} {I : TidSet} {J : TidSet} {Ts : Prog ℂ} → I ≢ J → canSync I Ts → canSync J Ts → liveDisjoint I J Ts
≢→liveDisjoint {ℂ} {I} {J} {Ts} I≢J canSyncI canSyncJ i i∈I∩J =
  case' (canSyncI i (∩-elim1 i I J i∈I∩J)) (λ p → p)
    λ (Ti , p) → case' (canSyncJ i (∩-elim2 i I J i∈I∩J)) (λ p → p)
      λ (Tj , q) → ⊥-elim (I≢J (⨟-injective1 ℂ I J Ti Tj ((sym p) ∙ q))) 

liveDisjoint→canSync : {ℂ : Magma} (I : TidSet) (J : TidSet) (Ts : Prog ℂ) (pi : canSync I Ts) (pj : canSync J Ts)
  → liveDisjoint I J Ts
  → canSync I (syncStep J Ts pj)
liveDisjoint→canSync {ℂ} I J Ts pi pj disjoint i i∈I = case' (toSum (∈-dec i J))
  (λ i∈J → inj₁ (syncStep-return J Ts pj i (disjoint i (∩-intro i I J i∈I i∈J))))
  (λ i∉J → case' (pi i i∈I) (λ e → inj₁ (subst (λ a → a ≡ return) (use-simp i∉J) e)) (λ e → inj₂ (e .proj₁ , subst (λ a → a ≡ (sync I ⨟ e .proj₁)) (use-simp i∉J) (e .proj₂))))
  where
  use-simp : ¬ (i ∈ J) → Ts i ≡ syncStep J Ts pj i
  use-simp i∉J = sym (syncStep-simp-∉ J Ts pj i (¬∈→∉ i J i∉J))

syncMem-comm : ∀ I J X → syncMem I (syncMem J X) ≡ syncMem J (syncMem I X)
syncMem-comm I J X = funext λ g → MemEvs-≡
  (funext λ i → lemRd g i (∈-dec i I) (∈-dec i J))
  (×-≡,≡→≡ (lemWr1 g , (lemWr2 g (∈-dec (MemEvs.wr (syncMem J X g) .proj₁) I) (∈-dec (MemEvs.wr (syncMem I X g) .proj₁) J))))
  where
  lemRd : ∀ g i → Dec (i ∈ I) → Dec (i ∈ J) → syncMemRd I (MemEvs.rd (syncMem J X g)) i ≡ syncMemRd J (MemEvs.rd (syncMem I X g)) i
  lemRd g i (yes p) (yes q) = syncMemRd-simp-∈ I (MemEvs.rd (syncMem J X g)) i p
    ∙ cong (_- I) (syncMemRd-simp-∈ J (MemEvs.rd (X g)) i q)
    ∙ setMinus-comm (X g .MemEvs.rd i) J I
    ∙ sym (cong (_- J) (syncMemRd-simp-∈ I (MemEvs.rd (X g)) i p))
    ∙ sym (syncMemRd-simp-∈ J (MemEvs.rd (syncMem I X g)) i q)
  lemRd g i (no p) (yes q) = syncMemRd-simp-∉ I (MemEvs.rd (syncMem J X g)) i (¬∈→∉ i I p)
    ∙ syncMemRd-simp-∈ J (MemEvs.rd (X g)) i q
    ∙ sym (cong (_- J) (syncMemRd-simp-∉ I (MemEvs.rd (X g)) i (¬∈→∉ i I p)))
    ∙ sym (syncMemRd-simp-∈ J (MemEvs.rd (syncMem I X g)) i q)
  lemRd g i (yes p) (no q) = syncMemRd-simp-∈ I (MemEvs.rd (syncMem J X g)) i p
    ∙ cong (_- I) (syncMemRd-simp-∉ J (MemEvs.rd (X g)) i (¬∈→∉ i J q))
    ∙ sym (syncMemRd-simp-∈ I (MemEvs.rd (X g)) i p)
    ∙ sym (syncMemRd-simp-∉ J (MemEvs.rd (syncMem I X g)) i (¬∈→∉ i J q))
  lemRd g i (no p) (no q) = syncMemRd-simp-∉ I (MemEvs.rd (syncMem J X g)) i (¬∈→∉ i I p)
    ∙ syncMemRd-simp-∉ J (MemEvs.rd (X g)) i (¬∈→∉ i J q)
    ∙ sym (syncMemRd-simp-∉ I (MemEvs.rd (X g)) i (¬∈→∉ i I p))
    ∙ sym (syncMemRd-simp-∉ J (MemEvs.rd (syncMem I X g)) i (¬∈→∉ i J q))

  lemWr1 : ∀ g
    → syncMemWr I (MemEvs.wr (syncMem J X g)) .proj₁ ≡
      syncMemWr J (MemEvs.wr (syncMem I X g)) .proj₁
  lemWr1 g = syncMemWr-simp1 I (MemEvs.wr (syncMem J X g))
    ∙ syncMemWr-simp1 J (MemEvs.wr (X g))
    ∙ sym (syncMemWr-simp1 I (MemEvs.wr (X g)))
    ∙ sym (syncMemWr-simp1 J (MemEvs.wr (syncMem I X g)))

  lemWr2 : ∀ g
    → Dec (MemEvs.wr (syncMem J X g) .proj₁ ∈ I)
    → Dec (MemEvs.wr (syncMem I X g) .proj₁ ∈ J)
    → syncMemWr I (MemEvs.wr (syncMem J X g)) .proj₂ ≡ syncMemWr J (MemEvs.wr (syncMem I X g)) .proj₂
  lemWr2 g (yes p) (yes q) =
    syncMemWr-simp-∈ I (MemEvs.wr (syncMem J X g)) p
    ∙ cong (_- I) (syncMemWr-simp-∈ J (MemEvs.wr (X g)) (subst (λ x → x ∈ J) (syncMemWr-simp1 I (MemEvs.wr (X g))) q))
    ∙ setMinus-comm (MemEvs.wr (X g) .proj₂) J I
    ∙ sym (cong (_- J) (syncMemWr-simp-∈ I (MemEvs.wr (X g)) (subst (λ x → x ∈ I) (syncMemWr-simp1 J (MemEvs.wr (X g))) p)))
    ∙ sym (syncMemWr-simp-∈ J (MemEvs.wr (syncMem I X g)) q)
  lemWr2 g (no p) (yes q) =
    syncMemWr-simp-∉ I (MemEvs.wr (syncMem J X g)) (¬∈→∉ (MemEvs.wr (syncMem J X g) .proj₁) I p)
    ∙ syncMemWr-simp-∈ J (MemEvs.wr (X g)) (subst (λ x → x ∈ J) (syncMemWr-simp1 I (MemEvs.wr (X g))) q)
    ∙ sym (cong (_- J) (syncMemWr-simp-∉ I (MemEvs.wr (X g)) (¬∈→∉ (MemEvs.wr (X g) .proj₁) I (subst (λ x → ¬ (x ∈ I)) (syncMemWr-simp1 J (MemEvs.wr (X g))) p))))
    ∙ sym (syncMemWr-simp-∈ J (MemEvs.wr (syncMem I X g)) q)
  lemWr2 g (yes p) (no q) =
    syncMemWr-simp-∈ I (MemEvs.wr (syncMem J X g)) p
    ∙ cong (_- I) (syncMemWr-simp-∉ J (MemEvs.wr (X g)) (¬∈→∉ (MemEvs.wr (X g) .proj₁) J (subst (λ x → ¬ (x ∈ J)) (syncMemWr-simp1 I (MemEvs.wr (X g))) q)))
    ∙ sym (syncMemWr-simp-∈ I (MemEvs.wr (X g)) (subst (λ x → x ∈ I) (syncMemWr-simp1 J (MemEvs.wr (X g))) p))
    ∙ sym (syncMemWr-simp-∉ J (MemEvs.wr (syncMem I X g)) (¬∈→∉ (MemEvs.wr (syncMem I X g) .proj₁) J q))
  lemWr2 g (no p) (no q) =
    syncMemWr-simp-∉ I (MemEvs.wr (syncMem J X g)) (¬∈→∉ (MemEvs.wr (syncMem J X g) .proj₁) I p)
    ∙ syncMemWr-simp-∉ J (MemEvs.wr (X g)) (¬∈→∉ (MemEvs.wr (X g) .proj₁) J (subst (λ x → ¬ (x ∈ J)) (syncMemWr-simp1 I (MemEvs.wr (X g))) q))
    ∙ sym (syncMemWr-simp-∉ I (MemEvs.wr (X g)) (¬∈→∉ (MemEvs.wr (X g) .proj₁) I (subst (λ x → ¬ (x ∈ I)) (syncMemWr-simp1 J (MemEvs.wr (X g))) p)))
    ∙ sym (syncMemWr-simp-∉ J (MemEvs.wr (syncMem I X g)) (¬∈→∉ (MemEvs.wr (syncMem I X g) .proj₁) J q))

syncStep-syncStep-comm : ∀ {ℂ} I J (Ts : Prog ℂ) (p : canSync I Ts) (q : canSync J Ts) (p' : canSync J (syncStep I Ts p)) (q' : canSync I (syncStep J Ts q))
  → I ≢ J
  → syncStep I (syncStep J Ts q) q' ≡
    syncStep J (syncStep I Ts p) p'
syncStep-syncStep-comm I J Ts p q p' q' I≢J = {!!}

diamond : ∀ {ℂ C C1 C2}
  → StepProgRefl ℂ C C1
  → StepProgRefl ℂ C C2
  → ∃[ C' ] StepProgRefl ℂ C1 C' × StepProgRefl ℂ C2 C'
diamond (refl C) (refl .C) =
  C , refl C , refl C
diamond (refl .(just (Rs , G , X , Ts))) (schd i Rs X Ts R G T R' G' X' T' x x₁ x₂) =
  just (Rs [ i ↦ R' ] , G' , X' , Ts [ i ↦ T' ])
  , schd i Rs X Ts R G T R' G' X' T' x x₁ x₂
  , refl (just (Rs [ i ↦ R' ] , G' , X' , Ts [ i ↦ T' ]))
diamond (refl .(just (Rs , G , X , Ts))) (schdBad i Rs X Ts R G T x x₁ x₂) =
  nothing
  , schdBad i Rs X Ts R G T x x₁ x₂
  , refl nothing
diamond (refl .(just (Rs , G , X , Ts))) (sync I Rs G X Ts q) =
  just (Rs , G , syncMem I X , syncStep I Ts q)
  , sync I Rs G X Ts q
  , refl (just (Rs , G , syncMem I X , syncStep I Ts q))
diamond (schd i Rs X Ts R G T R' G' X' T' x x₁ x₂) (refl .(just (Rs , G , X , Ts))) =
  just (Rs [ i ↦ R' ] , G' , X' , Ts [ i ↦ T' ])
  , refl (just (Rs [ i ↦ R' ] , G' , X' , Ts [ i ↦ T' ]))
  , schd i Rs X Ts R G T R' G' X' T' x x₁ x₂
diamond {ℂ = ℂ} (schd i Rs X Ts R G T R' G' X' T' x x₂ x₁) (schd i₁ .Rs .X .Ts R₁ .G T₁ R'' G'' X'' T'' x₃ x₅ x₄) with tidEq i i₁
... | yes refl =
  just ((Rs [ i ↦ R' ]) , G' , X' , Ts [ i ↦ T' ])
  , refl (just ((Rs [ i ↦ R' ]) , G' , X' , Ts [ i ↦ T' ]))
  , cast eq' (refl (just ((Rs [ i ↦ R'' ]) , G'' , X'' , Ts [ i ↦ T'' ])))
  where
  R≡ : R ≡ R₁
  R≡ = trans (sym x) x₃

  T≡ : T ≡ T₁
  T≡ = trans (sym x₂) x₅

  eq : just (R' , G' , X' , T') ≡ just (R'' , G'' , X'' , T'')
  eq with R≡ | T≡
  ... | refl | refl = StepThd-≡ x₁ x₄

  eq' :
    StepProgRefl ℂ
      (just ((Rs [ i ↦ R'' ]) , G'' , X'' , Ts [ i ↦ T'' ]))
      (just ((Rs [ i ↦ R'' ]) , G'' , X'' , Ts [ i ↦ T'' ]))
    ≡
    StepProgRefl ℂ
      (just ((Rs [ i ↦ R'' ]) , G'' , X'' , Ts [ i ↦ T'' ]))
      (just ((Rs [ i ↦ R' ]) , G' , X' , Ts [ i ↦ T' ]))
  eq' with eq
  ... | refl = cong (λ a → StepProgRefl ℂ (just ((Rs [ i ↦ R'' ]) , G'' , X'' , Ts [ i ↦ T'' ])) a)
                    (CfgProg-≡-intro refl refl refl refl)
... | no i≢i₁ = case' nextStep
    (λ (G''' , X''' , lhs , rhs) →
      just ((Rs [ i ↦ R' ] [ i₁ ↦ R'' ]) , G''' , X''' , (Ts [ i ↦ T' ] [ i₁ ↦ T'' ])) ,
      mkLhs G''' X''' lhs  ,
      mkRhs' G''' X''' rhs)
    (λ (lhs , rhs) →
      nothing ,
      schdBad i₁ (Rs [ i ↦ R' ]) X' (Ts [ i ↦ T' ]) R₁ G' T₁ ≡R₁ ≡T₁ (StepThd-change-G-nothing lhs) ,
      schdBad i (Rs [ i₁ ↦ R'' ]) X'' (Ts [ i₁ ↦ T'' ]) R G'' T ≡R ≡T (StepThd-change-G-nothing rhs))
  where
  nextStep : (∃[ G''' ] ∃[ X''' ]
      StepThd ℂ i₁ (just (R₁ , G' , X' , T₁)) (just (R'' , G''' , X''' , T'')) ×
      StepThd ℂ i (just (R , G'' , X'' , T)) (just (R' , G''' , X''' , T')))
    ⊎ (StepThd ℂ i₁ (just (R₁ , G , X' , T₁)) nothing × StepThd _ i (just (R , G , X'' , T)) nothing)
  nextStep = StepThd-≢-comm {ℂ = ℂ} i≢i₁ x₁ x₄

  ≡R₁ : (Rs [ i ↦ R' ]) i₁ ≡ R₁
  ≡R₁ = trans ([↦]-simp-≢ Rs i i₁ R' i≢i₁) x₃

  ≡T₁ : (Ts [ i ↦ T' ]) i₁ ≡ T₁
  ≡T₁ = trans ([↦]-simp-≢ Ts i i₁ T' i≢i₁) x₅

  mkLhs : (G''' : GEnv (ℂ .Magma.Carrier)) (X''' : Mem)
    → (lhs : StepThd ℂ i₁ (just (R₁ , G' , X' , T₁)) (just (R'' , G''' , X''' , T'')))
    → StepProgRefl ℂ
        (just (Rs [ i ↦ R' ] , G' , X' , Ts [ i ↦ T' ]))
        (just ((Rs [ i ↦ R' ] [ i₁ ↦ R'' ]) , G''' , X''' , (Ts [ i ↦ T' ] [ i₁ ↦ T'' ])))
  mkLhs G''' X''' lhs = schd i₁ (Rs [ i ↦ R' ]) X' (Ts [ i ↦ T' ]) R₁ G' T₁ R'' G''' X''' T'' ≡R₁ ≡T₁ lhs

  ≡R : (Rs [ i₁ ↦ R'' ]) i ≡ R
  ≡R = trans ([↦]-simp-≢ Rs i₁ i R'' (≢-sym i≢i₁)) x

  ≡T : (Ts [ i₁ ↦ T'' ]) i ≡ T
  ≡T = trans ([↦]-simp-≢ Ts i₁ i T'' (≢-sym i≢i₁)) x₂

  mkRhs : (G''' : GEnv (ℂ .Magma.Carrier)) (X''' : Mem)
    → (rhs : StepThd ℂ i (just (R , G'' , X'' , T)) (just (R' , G''' , X''' , T')))
    → StepProgRefl ℂ
        (just (Rs [ i₁ ↦ R'' ] , G'' , X'' , Ts [ i₁ ↦ T'' ]))
        (just ((Rs [ i₁ ↦ R'' ] [ i ↦ R' ]) , G''' , X''' , (Ts [ i₁ ↦ T'' ] [ i ↦ T' ])))
  mkRhs G''' X''' rhs = schd i (Rs [ i₁ ↦ R'' ]) X'' (Ts [ i₁ ↦ T'' ]) R G'' T R' G''' X''' T' ≡R ≡T rhs

  Rs≡ : Rs [ i₁ ↦ R'' ] [ i ↦ R' ] ≡ Rs [ i ↦ R' ] [ i₁ ↦ R'' ]
  Rs≡ = [↦]-comm Rs (≢-sym i≢i₁) R'' R'

  Ts≡ : Ts [ i₁ ↦ T'' ] [ i ↦ T' ] ≡ Ts [ i ↦ T' ] [ i₁ ↦ T'' ]
  Ts≡ = [↦]-comm Ts (≢-sym i≢i₁) T'' T'

  mkRhs' : (G''' : GEnv (ℂ .Magma.Carrier)) (X''' : Mem)
    → (rhs : StepThd ℂ i (just (R , G'' , X'' , T)) (just (R' , G''' , X''' , T')))
    → StepProgRefl ℂ
        (just (Rs [ i₁ ↦ R'' ] , G'' , X'' , Ts [ i₁ ↦ T'' ]))
        (just ((Rs [ i ↦ R' ] [ i₁ ↦ R'' ]) , G''' , X''' , (Ts [ i ↦ T' ] [ i₁ ↦ T'' ])))
  mkRhs' G''' X''' rhs = cast (cong₂ (λ a b →
      StepProgRefl ℂ
        (just (Rs [ i₁ ↦ R'' ] , G'' , X'' , Ts [ i₁ ↦ T'' ]))
        (just (a , G''' , X''' , b))) Rs≡ Ts≡)
      (mkRhs G''' X''' rhs)
diamond {ℂ = ℂ} (schd i Rs X Ts R G T R' G' X' T' x x₂ x₁) (schdBad i₁ .Rs .X .Ts R₁ .G T₁ x₃ x₅ x₄) with tidEq i i₁
... | yes refl =
  ⊥-elim (nothing≢just (sym eq))
  where
  R≡ : R ≡ R₁
  R≡ = trans (sym x) x₃

  T≡ : T ≡ T₁
  T≡ = trans (sym x₂) x₅

  eq : just (R' , G' , X' , T') ≡ nothing
  eq with R≡ | T≡
  ... | refl | refl = StepThd-≡ x₁ x₄
... | no i≢i₁ =
  nothing ,
  lhs ,
  refl nothing
  where
  lhsThd' : StepThd ℂ i₁ (just (R₁ , G , X' , T₁)) nothing
  lhsThd' = StepThd-mono-nothing (StepThd-≤-Mem x₁ i₁ (≢-sym i≢i₁)) x₄

  lhsThd : StepThd ℂ i₁ (just (R₁ , G' , X' , T₁)) nothing
  lhsThd = StepThd-change-G-nothing lhsThd'

  lhs : StepProgRefl ℂ (just ((Rs [ i ↦ R' ]) , G' , X' , (Ts [ i ↦ T' ]))) nothing
  lhs = schdBad i₁ (Rs [ i ↦ R' ]) X' (Ts [ i ↦ T' ]) R₁ G' T₁
    (trans ([↦]-simp-≢ Rs i i₁ R' i≢i₁) x₃)
    (trans ([↦]-simp-≢ Ts i i₁ T' i≢i₁) x₅)
    lhsThd
diamond {ℂ = ℂ} (schdBad i Rs X Ts R G T x x₂ x₁) (schd i₁ .Rs .X .Ts R₁ .G T₁ R' G' X' T' x₃ x₅ x₄) with tidEq i i₁
... | yes refl =
  ⊥-elim (nothing≢just eq)
  where
  R≡ : R ≡ R₁
  R≡ = trans (sym x) x₃

  T≡ : T ≡ T₁
  T≡ = trans (sym x₂) x₅

  eq : nothing ≡ just (R' , G' , X' , T')
  eq with R≡ | T≡
  ... | refl | refl = StepThd-≡ x₁ x₄
... | no i≢i₁ =
  nothing ,
  refl nothing ,
  rhs
  where
  rhsThd' : StepThd ℂ i (just (R , G , X' , T)) nothing
  rhsThd' = StepThd-mono-nothing (StepThd-≤-Mem x₄ i i≢i₁) x₁

  rhsThd : StepThd ℂ i (just (R , G' , X' , T)) nothing
  rhsThd = StepThd-change-G-nothing rhsThd'

  rhs : StepProgRefl ℂ (just ((Rs [ i₁ ↦ R' ]) , G' , X' , (Ts [ i₁ ↦ T' ]))) nothing
  rhs = schdBad i (Rs [ i₁ ↦ R' ]) X' (Ts [ i₁ ↦ T' ]) R G' T
    (trans ([↦]-simp-≢ Rs i₁ i R' (≢-sym i≢i₁)) x)
    (trans ([↦]-simp-≢ Ts i₁ i T' (≢-sym i≢i₁)) x₂)
    rhsThd
diamond {ℂ = ℂ} (schd i Rs X Ts R G T R' G' X' T' x x₁ x₃) (sync I .Rs .G .X .Ts q) =
  just (Rs [ i ↦ R' ] , G' , syncMem I X' , syncStep I (Ts [ i ↦ T' ]) q')
  , stepLeft
  , stepRight'
  where
  i∉I : i ∉ I
  i∉I = StepThd-sync-step x₁ q x₃

  q' : canSync I (Ts [ i ↦ T' ])
  q' = canSync-∉ i I Ts T' i∉I q

  Ts≡ : syncStep I Ts q i ≡ T
  Ts≡ = syncStep-∉ i I Ts q i∉I ∙ x₁

  stepLeft :
    StepProgRefl ℂ
      (just ((Rs [ i ↦ R' ]) , G' , X' , (Ts [ i ↦ T' ])))
      (just ((Rs [ i ↦ R' ]) , G' , syncMem I X' , syncStep I (Ts [ i ↦ T' ]) q'))
  stepLeft = sync {ℂ = ℂ} I (Rs [ i ↦ R' ]) G' X' (Ts [ i ↦ T' ]) q'

  stepRight :
    StepProgRefl ℂ
      (just (Rs , G , syncMem I X , syncStep I Ts q))
      (just ((Rs [ i ↦ R' ]) , G' , syncMem I X' , (syncStep I Ts q) [ i ↦ T' ]))
  stepRight = schd {ℂ = ℂ} i Rs (syncMem I X) (syncStep I Ts q) R G T R' G' (syncMem I X') T' x Ts≡ (StepThd-just-sync i∉I x₃) 

  stepRight' = cast
    (cong (λ a → StepProgRefl ℂ
        (just (Rs , G , syncMem I X , syncStep I Ts q))
        (just ((Rs [ i ↦ R' ]) , G' , syncMem I X' , a)))
      (funext λ j → syncStep-[↦]-comm ℂ I Ts q T' i j i∉I))
    stepRight
diamond {ℂ = ℂ} (sync I Rs G X Ts q) (schd i .Rs .X .Ts R G T R' G' X' T' x x₁ x₃) =
  just (Rs [ i ↦ R' ] , G' , syncMem I X' , syncStep I (Ts [ i ↦ T' ]) q')
  , stepLeft'
  , stepRight
  where
  i∉I : i ∉ I
  i∉I = StepThd-sync-step x₁ q x₃

  q' : canSync I (Ts [ i ↦ T' ])
  q' = canSync-∉ i I Ts T' i∉I q

  Ts≡ : syncStep I Ts q i ≡ T
  Ts≡ = syncStep-∉ i I Ts q i∉I ∙ x₁

  stepLeft :
    StepProgRefl ℂ
      (just (Rs , G , syncMem I X , syncStep I Ts q))
      (just ((Rs [ i ↦ R' ]) , G' , syncMem I X' , (syncStep I Ts q) [ i ↦ T' ]))
  stepLeft = schd {ℂ = ℂ} i Rs (syncMem I X) (syncStep I Ts q) R G T R' G' (syncMem I X') T' x Ts≡ (StepThd-just-sync i∉I x₃)

  stepLeft' = cast
    (cong (λ a → StepProgRefl ℂ
        (just (Rs , G , syncMem I X , syncStep I Ts q))
        (just ((Rs [ i ↦ R' ]) , G' , syncMem I X' , a)))
      (funext λ j → syncStep-[↦]-comm ℂ I Ts q T' i j i∉I))
    stepLeft

  stepRight :
    StepProgRefl ℂ
      (just ((Rs [ i ↦ R' ]) , G' , X' , (Ts [ i ↦ T' ])))
      (just ((Rs [ i ↦ R' ]) , G' , syncMem I X' , syncStep I (Ts [ i ↦ T' ]) q'))
  stepRight = sync {ℂ = ℂ} I (Rs [ i ↦ R' ]) G' X' (Ts [ i ↦ T' ]) q'
diamond (schdBad i Rs X Ts R G T x x₂ x₃) (refl .(just (Rs , G , X , Ts))) =
  nothing , refl nothing , schdBad i Rs X Ts R G T x x₂ x₃
diamond (schdBad i Rs X Ts R G T x x₁ x₂) (schdBad i₁ .Rs .X .Ts R₁ G₁ T₁ x₃ x₄ x₅) =
  nothing , refl nothing , refl nothing
diamond {ℂ = ℂ} (schdBad i Rs X Ts R G T x x₁ x₂) (sync I .Rs .G .X .Ts q) =
  nothing , refl nothing , rhs
  where
  i∉I : i ∉ I
  i∉I = StepThd-sync-step x₁ q x₂

  rhs : StepProgRefl ℂ (just (Rs , G , syncMem I X , syncStep I Ts q)) nothing
  rhs = schdBad i Rs (syncMem I X) (syncStep I Ts q) R G T x
    (syncStep-∉ i I Ts q i∉I ∙ x₁)
    (StepThd-mono-nothing (syncMem-≤-Mem i I X i∉I) x₂)
diamond {ℂ = ℂ} (sync I Rs G X Ts q) (schdBad i .Rs .X .Ts R G T x x₁ x₂) =
  nothing , lhs , refl nothing
  where
  i∉I : i ∉ I
  i∉I = StepThd-sync-step x₁ q x₂

  lhs : StepProgRefl ℂ (just (Rs , G , syncMem I X , syncStep I Ts q)) nothing
  lhs = schdBad i Rs (syncMem I X) (syncStep I Ts q) R G T x
    (syncStep-∉ i I Ts q i∉I ∙ x₁)
    (StepThd-mono-nothing (syncMem-≤-Mem i I X i∉I) x₂)
diamond (sync I Rs G X Ts q) (refl .(just (Rs , G , X , Ts))) =
  just (Rs , G , syncMem I X , syncStep I Ts q) , refl (just (Rs , G , syncMem I X , syncStep I Ts q)) , sync I Rs G X Ts q
diamond {ℂ = ℂ} (sync I Rs G X Ts q) (sync I₁ .Rs .G .X .Ts p₁) with (fromSum (LEM (I ≡ I₁)))
... | yes refl = just (Rs , G , syncMem I X , syncStep I Ts q) , refl (just (Rs , G , syncMem I X , syncStep I Ts q)) , stepRight
  where
  stepRight : StepProgRefl ℂ (just (Rs , G , syncMem I X , syncStep I Ts p₁)) (just (Rs , G , syncMem I X , syncStep I Ts q))
  stepRight = subst (λ a → StepProgRefl ℂ (just (Rs , G , syncMem I X , syncStep I Ts a))
    (just (Rs , G , syncMem I X , syncStep I Ts q))) (sym (canSync-isProp I Ts p₁ q))
    (refl (just (Rs , G , syncMem I X , syncStep I Ts q)))
... | no I≢I₁ = just (Rs , G , syncMem I₁ (syncMem I X) , syncStep I₁ (syncStep I Ts q) canSyncLeft) , stepLeft , stepRight'
  where
  canSyncLeft : canSync I₁ (syncStep I Ts q)
  canSyncLeft = liveDisjoint→canSync I₁ I Ts p₁ q (≢→liveDisjoint (≢-sym I≢I₁) p₁ q)

  stepLeft :
    StepProgRefl ℂ
      (just (Rs , G , syncMem I X , syncStep I Ts q))
      (just (Rs , G , syncMem I₁ (syncMem I X) , syncStep I₁ (syncStep I Ts q) canSyncLeft))
  stepLeft = sync I₁ Rs G (syncMem I X) (syncStep I Ts q) canSyncLeft

  canSyncRight : canSync I (syncStep I₁ Ts p₁)
  canSyncRight = liveDisjoint→canSync I I₁ Ts q p₁ (≢→liveDisjoint I≢I₁ q p₁)

  stepRight :
    StepProgRefl ℂ
      (just (Rs , G , syncMem I₁ X , syncStep I₁ Ts p₁))
      (just (Rs , G , syncMem I (syncMem I₁ X) , syncStep I (syncStep I₁ Ts p₁) canSyncRight))
  stepRight = sync I Rs G (syncMem I₁ X) (syncStep I₁ Ts p₁) canSyncRight

  stepRight' :
    StepProgRefl ℂ
      (just (Rs , G , syncMem I₁ X , syncStep I₁ Ts p₁))
      (just (Rs , G , syncMem I₁ (syncMem I X) , syncStep I₁ (syncStep I Ts q) canSyncLeft))
  stepRight' = cast (cong₂ (λ a b →
    StepProgRefl ℂ
      (just (Rs , G , syncMem I₁ X , syncStep I₁ Ts p₁))
      (just (Rs , G , a , b))) (syncMem-comm I I₁ X) (syncStep-syncStep-comm {ℂ} I I₁ Ts q p₁ _ _ I≢I₁))
    stepRight
