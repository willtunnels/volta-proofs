{-# OPTIONS --allow-unsolved-metas #-}
module KernelCheck.Prog where

open import Axiom.UniquenessOfIdentityProofs.WithK
open import Function.Base using (_∘_; _$_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
import Data.Bool.Properties
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Negation using (¬_)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import KernelCheck.DecSet
open import KernelCheck.Util

record Magma : Set₁ where
  field
    Carrier : Set
    ⊕ : Carrier → Carrier → Carrier

open Magma

record Rid : Set where
  constructor mkRid
  field
    val : ℕ

record Gid : Set where
  constructor mkGid
  field
    val : ℕ

record Tid : Set where
  constructor mkTid
  field
    val : ℕ

ridEq : DecidableEquality Rid
ridEq x y with Rid.val x ≟ Rid.val y
... | yes refl = yes refl
... | no ¬p = no (¬p ∘ cong Rid.val)

gidEq : DecidableEquality Gid
gidEq x y with Gid.val x ≟ Gid.val y
... | yes refl = yes refl
... | no ¬p = no (¬p ∘ cong Gid.val)

tidEq : DecidableEquality Tid
tidEq x y with Tid.val x ≟ Tid.val y
... | yes refl = yes refl
... | no ¬p = no (¬p ∘ cong Tid.val)

instance
  RidHasDecEq : HasDecEq Rid
  RidHasDecEq = record { eq = ridEq }

  GidHasDecEq : HasDecEq Gid
  GidHasDecEq = record { eq = gidEq }

  TidHasDecEq : HasDecEq Tid
  TidHasDecEq = record { eq = tidEq }

TidSet = DecSet Tid

REnv : Set → Set
REnv A = Rid → A

REnvs : Set → Set
REnvs A = Tid → REnv A

GEnv : Set → Set
GEnv A = Gid → A

GEnvs : Set → Set
GEnvs A = Tid → GEnv A

data Stmt (ℂ : Magma) : Set where
  -- x ← c
  const : Rid → Carrier ℂ → Stmt ℂ
  -- x ← x1 ⊕ x2
  binOp : Rid → Rid → Rid → Stmt ℂ
  -- x ← y
  rdReg : Rid → Rid → Stmt ℂ
  -- x ← *y
  rdGbl : Rid → Gid → Stmt ℂ
  -- *x ← y
  wrGbl : Gid → Rid → Stmt ℂ
  -- sync I
  sync : TidSet → Stmt ℂ

data Thd (ℂ : Magma) : Set where
  return : Thd ℂ
  _⨟_ : Stmt ℂ → Thd ℂ → Thd ℂ

Prog : Magma → Set
Prog ℂ = Tid → Thd ℂ

Rd : Set
Rd = Tid → TidSet

Wr : Set
Wr = Tid × TidSet

-- Given (rd : Rd) for address g, if j ∈ rd i then i has performed a read of g since j last sync'ed with it
noRacingRd : Tid → Rd → Set
noRacingRd i rd = ∀ j → i ≡ j ⊎ i ∉ rd j

-- Given ((i , I) : Wr) for address g, if j ∈ I then i has performed a write of g since j last sync'ed with it
noRacingWr : Tid → Wr → Set
noRacingWr i (j , I) = i ≡ j ⊎ i ∉ I

yesRacingRd : Tid → Rd → Set
yesRacingRd i rd = ∃[ j ] i ≢ j × i ∈ rd j

yesRacingWr : Tid → Wr → Set
yesRacingWr i (j , I) = i ≢ j × i ∈ I

¬noRacingRd→yesRacingRd : ∀ i rd → ¬ noRacingRd i rd → yesRacingRd i rd
¬noRacingRd→yesRacingRd i rd p = lem .proj₁ , ¬× (lem .proj₂) .proj₁ , ¬∉→∈ i (rd (lem .proj₁)) (¬× (lem .proj₂) .proj₂)
  where
  lem : ∃[ j ] ¬ (i ≡ j ⊎ i ∉ rd j)
  lem = ¬∀→∃¬ p

  ¬× : {A B : Set} → ¬ (A ⊎ B) → ¬ A × ¬ B
  ¬× ¬AB = (λ x → ¬AB (inj₁ x)) , (λ x → ¬AB (inj₂ x))

yesRacingRd→¬noRacingRd : ∀ i rd → yesRacingRd i rd → ¬ noRacingRd i rd
yesRacingRd→¬noRacingRd i rd (j , p) q = case (q j) (p .proj₁) (λ x → ∉→¬∈ i (rd j) x (p .proj₂))

¬noRacingWr→yesRacingWr : ∀ i wr → ¬ noRacingWr i wr → yesRacingWr i wr
¬noRacingWr→yesRacingWr i (j , I) ¬p with tidEq i j | ∈-dec i I
... | yes i≡j | yes i∈I = ⊥-elim (¬p (inj₁ i≡j))
... | yes i≡j | no ¬i∈I = ⊥-elim (¬p (inj₁ i≡j))
... | no i≢j | yes i∈I = i≢j , i∈I
... | no i≢j | no ¬i∈I with I i
... | true = ⊥-elim (¬i∈I refl)
... | false = ⊥-elim (¬p (inj₂ refl))

yesRacingWr→¬noRacingWr : ∀ i wr → yesRacingWr i wr → ¬ noRacingWr i wr
yesRacingWr→¬noRacingWr i (j , I) (i≢j , i∈I) (inj₁ i≡j) = i≢j i≡j
yesRacingWr→¬noRacingWr i (j , I) (i≢j , i∈I) (inj₂ i∉I) with i∈I | i∉I
... | p | q = ⊥-elim (false≢true (trans (sym q) p))

record MemEvs : Set where
  constructor evs
  field
    rd : Rd
    wr : Wr

Mem : Set
Mem = Gid → MemEvs

MemEvs-≡ : ∀ {x x' y y'} → x ≡ x' → y ≡ y' → evs x y ≡ evs x' y'
MemEvs-≡ refl refl = refl

module _ {A B : Set} {{eq : HasDecEq A}} where
  opaque
    _[_↦_] : (A → B) → A → B → A → B
    _[_↦_] f x y x' = if Dec.does (HasDecEq.eq eq x x') then y else f x'

    [↦]-simp-≡ : (f : A → B) (x : A) (y : B) → (f [ x ↦ y ]) x ≡ y
    [↦]-simp-≡ f x y with HasDecEq.eq eq x x
    ... | yes _ = refl
    ... | no ¬p = ⊥-elim (¬p refl)

    [↦]-simp-≢ : (f : A → B) (x x' : A) (y : B) → x ≢ x' → (f [ x ↦ y ]) x' ≡ f x'
    [↦]-simp-≢ f x x' y neq with HasDecEq.eq eq x x'
    ... | yes p = ⊥-elim (neq p)
    ... | no ¬p = refl

    [↦]-id : (f : A → B) (x : A) (x' : A) → (f [ x ↦ f x ]) x' ≡ f x'
    [↦]-id f x x' with HasDecEq.eq eq x x'
    ... | yes refl = refl
    ... | no _ = refl

    [↦]-comm : (f : A → B) {x1 x2 : A} → x1 ≢ x2 → (y1 y2 : B) → (f [ x1 ↦ y1 ]) [ x2 ↦ y2 ] ≡ (f [ x2 ↦ y2 ]) [ x1 ↦ y1 ]
    [↦]-comm f {x1} {x2} neq y1 y2 = funext lem
      where
      lem : (z : A) → ((f [ x1 ↦ y1 ]) [ x2 ↦ y2 ]) z ≡ ((f [ x2 ↦ y2 ]) [ x1 ↦ y1 ]) z
      lem z with HasDecEq.eq eq x1 z | HasDecEq.eq eq x2 z
      ... | yes p | yes q = ⊥-elim (neq (trans p (sym q)))
      ... | no ¬p | yes q = refl
      ... | yes p | no ¬q = refl
      ... | no ¬p | no ¬q = refl

doRd : MemEvs → Tid → MemEvs
doRd x i = record x { rd = (MemEvs.rd x) [ i ↦ all ] }

doWr : MemEvs → Tid → MemEvs
doWr x i = record x { wr = i , all }

doRd-comm : ∀ x {i j} → i ≢ j → doRd (doRd x i) j ≡ doRd (doRd x j) i
doRd-comm x {i} {j} i≢j = MemEvs-≡ ([↦]-comm (MemEvs.rd x) i≢j all all) refl

doRd-noRace : ∀ i j g g' (X : Mem) → noRacingWr i ((X [ g ↦ doRd (X g) j ]) g' .MemEvs.wr) → noRacingWr i (X g' .MemEvs.wr)
doRd-noRace i j g g' X p = {!!}

canSync : {ℂ : Magma} → TidSet → Prog ℂ → Set
canSync I Ts = ∀ i → i ∈ I → Ts i ≡ return ⊎ ∃[ T ] Ts i ≡ sync I ⨟ T

syncStep : {ℂ : Magma} (I : TidSet) (Ts : Prog ℂ) → canSync I Ts → Prog ℂ
syncStep I Ts p i with ∈-dec i I
syncStep I Ts p i | yes q with p i q
syncStep I Ts p i | yes q | inj₁ T = return
syncStep I Ts p i | yes q | inj₂ T = T .proj₁
syncStep I Ts p i | no  _ = Ts i

syncEnvs : {A : Set} → TidSet → Mem → GEnvs A → GEnvs A
syncEnvs I X Gs i g with ∈-dec i I | ∈-dec (proj₁ (MemEvs.wr (X g))) I
... | yes _ | yes _ = Gs (proj₁ (MemEvs.wr (X g))) g
... | yes _ | no  _ = Gs i g
... | no  _ | yes _ = Gs i g
... | no  _ | no  _ = Gs i g

syncMemRd : TidSet → Rd → Rd
syncMemRd I rd i with ∈-dec i I
... | yes _ = rd i - I
... | no _ = rd i

syncMemWr : TidSet → Wr → Wr
syncMemWr I (i , J) with ∈-dec i I
... | yes _ = i , J - I
... | no _ = i , J

syncMemRd-⊆ : ∀ I x i → syncMemRd I x i ⊆ x i
syncMemRd-⊆ I x i j p with ∈-dec i I
... | yes _ = ∧-elim1 (x i j) (not (I j)) p
... | no _ = p

syncMemRd-∉ : ∀ I x i j → j ∉ I → j ∈ x i → j ∈ syncMemRd I x i
syncMemRd-∉ I x i j j∉I p with ∈-dec i I
... | yes _ = ∧-intro (x i j) (not (I j)) (p , subst (λ a → not a ≡ true) (sym j∉I) refl)
... | no _ = p

syncMemWr-simp1 : ∀ I x → syncMemWr I x .proj₁ ≡ x .proj₁
syncMemWr-simp1 I (i , J) with ∈-dec i I
... | yes _ = refl
... | no _ = refl

syncMemWr-⊆ : ∀ I x → syncMemWr I x .proj₂ ⊆ x .proj₂
syncMemWr-⊆ I (i , J) j p with ∈-dec i I
... | yes _ = ∧-elim1 (J j) (not (I j)) p
... | no _ = p

syncMemWr-∉ : ∀ I x j → j ∉ I → j ∈ x .proj₂ → j ∈ syncMemWr I x .proj₂
syncMemWr-∉ I (i , J) j j∉I p with ∈-dec i I
... | yes _ = ∧-intro (J j) (not (I j)) (p , subst (λ a → not a ≡ true) (sym j∉I) refl)
... | no _ = p

syncMem : TidSet → Mem → Mem
syncMem I X g = evs (syncMemRd I (MemEvs.rd (X g))) (syncMemWr I (MemEvs.wr (X g)))

opaque
  WellSynced : (ℂ : Magma) → GEnvs (Carrier ℂ) → Mem → Set
  WellSynced ℂ Gs X = ∀ i g → noRacingWr i (X g .MemEvs.wr) → Gs i g ≡ Gs (X g .MemEvs.wr .proj₁) g

  WellSynced-isProp : ∀ ℂ (Gs : GEnvs (Carrier ℂ)) (X : Mem) → (p1 p2 : WellSynced ℂ Gs X) → p1 ≡ p2
  WellSynced-isProp ℂ Gs X p1 p2 = funext' λ i → funext' λ g → funext λ x → uip (p1 i g x) (p2 i g x)

CfgThd : Magma → Set
CfgThd ℂ = Maybe (REnv (Carrier ℂ) × GEnv (Carrier ℂ) × Mem × Thd ℂ)

CfgThd-≡-elim : ∀ {ℂ}
  {R  : REnv (Carrier ℂ)} {G  : GEnv (Carrier ℂ)} {X  : Mem} {T  : Thd ℂ}
  {R' : REnv (Carrier ℂ)} {G' : GEnv (Carrier ℂ)} {X' : Mem} {T' : Thd ℂ}
  → just (R , G , X , T) ≡ just (R' , G' , X' , T')
  → R ≡ R' × G ≡ G' × X ≡ X' × T ≡ T'
CfgThd-≡-elim refl = refl , refl , refl , refl

CfgProg : Magma → Set
CfgProg ℂ = Maybe (REnvs (Carrier ℂ) × Σ (GEnvs (Carrier ℂ)) λ Gs → Σ Mem λ X → WellSynced ℂ Gs X × Prog ℂ)

CfgProg-≡-intro : ∀ {ℂ}
  {Rs  : REnvs (Carrier ℂ)} {Gs  : GEnvs (Carrier ℂ)} {X  : Mem} (p  : WellSynced ℂ Gs  X ) {Ts  : Prog ℂ}
  {Rs' : REnvs (Carrier ℂ)} {Gs' : GEnvs (Carrier ℂ)} {X' : Mem} (p' : WellSynced ℂ Gs' X') {Ts' : Prog ℂ}
  → Rs ≡ Rs' → Gs ≡ Gs' → X ≡ X' → Ts ≡ Ts'
  → just (Rs , Gs , X , p , Ts) ≡ just (Rs' , Gs' , X' , p' , Ts')
CfgProg-≡-intro {ℂ} {Rs} {Gs} {X} p {Ts} p' refl refl refl refl = cong (λ a → just (Rs , Gs , X , a , Ts)) (WellSynced-isProp ℂ Gs X p p')

data StepThd (ℂ : Magma) (i : Tid) : CfgThd ℂ → CfgThd ℂ → Set where
  const : ∀ R G X r c T
    → StepThd ℂ i (just (R , G , X , const r c ⨟ T)) (just (R [ r ↦ c ] , G , X , T))
  binOp : ∀ R G X r r1 r2 T
    → StepThd ℂ i (just (R , G , X , binOp r r1 r2 ⨟ T)) (just (R [ r ↦ ⊕ ℂ (R r1) (R r2) ] , G , X , T))
  rdReg : ∀ R G X r1 r2 T
    → StepThd ℂ i (just (R , G , X , rdReg r1 r2 ⨟ T)) (just (R [ r1 ↦ R r2 ] , G , X , T))
  rdGbl : ∀ R G X r g T
    → noRacingWr i (MemEvs.wr (X g))
    → StepThd ℂ i (just (R , G , X , rdGbl r g ⨟ T)) (just (R [ r ↦ G g ] , G , X [ g ↦ doRd (X g) i ] , T))
  rdGblBad : ∀ R G X r g T
    → ¬ noRacingWr i (MemEvs.wr (X g))
    → StepThd ℂ i (just (R , G , X , rdGbl r g ⨟ T)) nothing
  wrGbl : ∀ R G X g r T
    → noRacingRd i (MemEvs.rd (X g))
    → noRacingWr i (MemEvs.wr (X g))
    → StepThd ℂ i (just (R , G , X , wrGbl g r ⨟ T)) (just (R , G [ g ↦ R r ] , X [ g ↦ doWr (X g) i ] , T))
  wrGblBad : ∀ R G X g r T
    → ¬ noRacingRd i (MemEvs.rd (X g)) ⊎ ¬ noRacingWr i (MemEvs.wr (X g))
    → StepThd ℂ i (just (R , G , X , wrGbl g r ⨟ T)) nothing

opaque
  unfolding WellSynced

  doRd-WS : ∀ ℂ (Gs : GEnvs (Carrier ℂ)) X g i → WellSynced ℂ Gs X → WellSynced ℂ Gs (X [ g ↦ doRd (X g) i ])
  doRd-WS ℂ Gs X g i = {!!}

  doWr-WS : ∀ ℂ (Gs : GEnvs (Carrier ℂ)) X g1 g2 i j →
      WellSynced ℂ Gs (X [ g1 ↦ doWr (X g1) i ]) →
      WellSynced ℂ Gs (X [ g2 ↦ doWr (X g2) j ]) →
      WellSynced ℂ Gs
        ((X [ g1 ↦ doWr (X g1) i ]) [ g2 ↦ doWr ((X [ g1 ↦ doWr (X g1) i ]) g2) j ])
  doWr-WS ℂ Gs X g1 g2 i j ws1 ws2 k g = ?

  StepThd-WS-lem : ∀ ℂ i Gs X G
    → Gs i ≡ G
    → WellSynced ℂ Gs X
    → WellSynced ℂ (Gs [ i ↦ G ]) X
  StepThd-WS-lem ℂ i Gs X G Gs≡ ws j g noRace =
      cong (λ a → (Gs [ i ↦ a ]) j g) (sym Gs≡)
    ∙ cong (_$ g) ([↦]-id Gs i j)
    ∙ ws j g noRace
    ∙ sym (cong (_$ g) ([↦]-id Gs i (X g .MemEvs.wr .proj₁)))
    ∙ cong (λ a → (Gs [ i ↦ a ]) (X g .MemEvs.wr .proj₁) g) Gs≡

  StepThd-WS : ∀ {ℂ i Gs R G X T R' G' X' T'}
    → Gs i ≡ G
    → StepThd ℂ i (just (R , G , X , T)) (just (R' , G' , X' , T'))
    → WellSynced ℂ Gs X
    → WellSynced ℂ (Gs [ i ↦ G' ]) X'
  StepThd-WS {ℂ = ℂ} {i = i} {Gs = Gs} {G = G} {X = X} Gs≡ (const _ _ _ r c _) ws j g noRace = StepThd-WS-lem ℂ i Gs X G Gs≡ ws j g noRace
  StepThd-WS {ℂ = ℂ} {i = i} {Gs = Gs} {G = G} {X = X} Gs≡ (binOp _ _ _ r r1 r2 _) ws j g noRace = StepThd-WS-lem ℂ i Gs X G Gs≡ ws j g noRace
  StepThd-WS {ℂ = ℂ} {i = i} {Gs = Gs} {G = G} {X = X} Gs≡ (rdReg _ _ _ r1 r2 _) ws j g noRace = StepThd-WS-lem ℂ i Gs X G Gs≡ ws j g noRace
  StepThd-WS {ℂ = ℂ} {i = i} {Gs = Gs} {G = G} {X = X} Gs≡ (rdGbl _ _ _ r g₁ _ x) ws j g noRace =
      cong (λ a → (Gs [ i ↦ a ]) j g) (sym Gs≡)
    ∙ cong (_$ g) ([↦]-id Gs i j)
    ∙ ws j g (doRd-noRace j i g₁ g X noRace)
    ∙ cong (λ a → Gs (a .proj₁) g) lem
    ∙ sym (cong (_$ g) ([↦]-id Gs i _))
    ∙ cong (λ a → (Gs [ i ↦ a ]) _ g) Gs≡
    where
    lem : X g .MemEvs.wr ≡ (X [ g₁ ↦ doRd (X g₁) i ]) g .MemEvs.wr
    lem with gidEq g₁ g
    ... | yes refl = cong MemEvs.wr (sym ([↦]-simp-≡ X g₁ (doRd (X g₁) i)))
    ... | no g₁≢g = cong MemEvs.wr (sym ([↦]-simp-≢ X g₁ g (doRd (X g₁) i) g₁≢g))
  StepThd-WS {ℂ = ℂ} {i = i} {Gs = Gs} {R = R} {G = G} {X = X} {G' = G'} Gs≡ (wrGbl _ _ _ g₁ r _ x x₁) ws j g noRace =
    case noRace (λ x₂ → cong (λ a → (Gs [ i ↦ G [ g₁ ↦ R r ] ]) a g) x₂) (lem (tidEq i j) (gidEq g₁ g))
    where
    lem : Dec (i ≡ j) → Dec (g₁ ≡ g)
      → j ∉ (X [ g₁ ↦ doWr (X g₁) i ]) g .MemEvs.wr .proj₂
      → (Gs [ i ↦ G [ g₁ ↦ R r ] ]) j g ≡
        (Gs [ i ↦ G [ g₁ ↦ R r ] ]) ((X [ g₁ ↦ doWr (X g₁) i ]) g .MemEvs.wr .proj₁) g
    lem (yes refl) (yes refl) j∉ = {!!}
    lem (no i≢j) (yes refl) j∉ = {!!}
    lem (yes refl) (no g₁≢g) j∉ = {!!}
    lem (no i≢j) (no g₁≢g) j∉ = {!!} ∙ ws j g (cast (cong (λ a → noRacingWr j (a .MemEvs.wr)) simp-Xg₁) noRace) ∙ {!!}
      where
      simp-Xg₁ : (X [ g₁ ↦ doWr (X g₁) i ]) g ≡ X g
      simp-Xg₁ = [↦]-simp-≢ X g₁ g (doWr (X g₁) i) g₁≢g

  sync-WS : ∀ ℂ I X Gs → WellSynced ℂ Gs X → WellSynced ℂ (syncEnvs I X Gs) (syncMem I X)
  sync-WS ℂ I X Gs p i g noRace with ∈-dec i I | ∈-dec (proj₁ (MemEvs.wr (X g))) I | ∈-dec (proj₁ (MemEvs.wr (syncMem I X g))) I
  ... | yes q | yes r | yes s = refl
  ... | no q | yes r | yes s = p i g (case noRace (λ x → inj₁ x) (λ x → inj₂ (∉-split i I (MemEvs.wr (X g) .proj₂) (¬∈→∉ i I q) x)))
  ... | yes q | no r | yes s = p i g noRace
  ... | no q | no r | yes s = p i g noRace
  ... | yes q | yes r | no s = refl
  ... | no q | yes r | no s = ⊥-elim (false≢true (sym (Data.Bool.Properties.¬-not s) ∙ r))
  ... | yes q | no r | no s = p i g noRace
  ... | no q | no r | no s = p i g noRace

data StepProg (ℂ : Magma) : CfgProg ℂ → CfgProg ℂ → Set where
  schd : ∀ i Rs Gs X p Ts R G T R' G' X' T'
    → Rs i ≡ R
    → (Gs≡ : Gs i ≡ G)
    → Ts i ≡ T
    → (x : StepThd ℂ i (just (R , G , X , T)) (just (R' , G' , X' , T')))
    → StepProg ℂ (just (Rs , Gs , X , p , Ts)) (just (Rs [ i ↦ R' ] , Gs [ i ↦ G' ] , X' , StepThd-WS Gs≡ x p , Ts [ i ↦ T' ]))
  schdBad : ∀ i Rs Gs X p Ts R G T
    → Rs i ≡ R
    → Gs i ≡ G
    → Ts i ≡ T
    → StepThd ℂ i (just (R , G , X , T)) nothing
    → StepProg ℂ (just (Rs , Gs , X , p , Ts)) nothing
  sync : ∀ I Rs Gs X (p : WellSynced ℂ Gs X) Ts
    → (q : canSync I Ts)
    → StepProg ℂ (just (Rs , Gs , X , p , Ts)) (just (Rs , syncEnvs I X Gs , syncMem I X , sync-WS ℂ I X Gs p , syncStep I Ts q))

data StepProg* (ℂ : Magma) : CfgProg ℂ → CfgProg ℂ → Set where
  done : ∀ C
    → StepProg* ℂ C C
  step : ∀ C1 C2 C3
    → StepProg  ℂ C1 C2
    → StepProg* ℂ C2 C3
    → StepProg* ℂ C1 C3

data StepProgRefl (ℂ : Magma) : CfgProg ℂ → CfgProg ℂ → Set where
  refl : ∀ C
    → StepProgRefl ℂ C C
  schd : ∀ i Rs Gs X p Ts R G T R' G' X' T'
    → Rs i ≡ R
    → (Gs≡ : Gs i ≡ G)
    → Ts i ≡ T
    → (x : StepThd ℂ i (just (R , G , X , T)) (just (R' , G' , X' , T')))
    → StepProgRefl ℂ (just (Rs , Gs , X , p , Ts)) (just (Rs [ i ↦ R' ] , Gs [ i ↦ G' ] , X' , StepThd-WS Gs≡ x p , Ts [ i ↦ T' ]))
  schdBad : ∀ i Rs Gs X p Ts R G T
    → Rs i ≡ R
    → Gs i ≡ G
    → Ts i ≡ T
    → StepThd ℂ i (just (R , G , X , T)) nothing
    → StepProgRefl ℂ (just (Rs , Gs , X , p , Ts)) nothing
  sync : ∀ I Rs Gs X p Ts
    → (q : canSync I Ts)
    → StepProgRefl ℂ (just (Rs , Gs , X , p , Ts)) (just (Rs , syncEnvs I X Gs , syncMem I X , sync-WS ℂ I X Gs p , syncStep I Ts q))

data StepProgRefl* (ℂ : Magma) : CfgProg ℂ → CfgProg ℂ → Set where
  done : ∀ C
    → StepProgRefl* ℂ C C
  step : ∀ C1 C2 C3
    → StepProgRefl  ℂ C1 C2
    → StepProgRefl* ℂ C2 C3
    → StepProgRefl* ℂ C1 C3
