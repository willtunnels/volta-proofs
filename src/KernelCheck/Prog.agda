module KernelCheck.Prog where

open import Function.Base using (_∘_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Negation using (¬_)

open import Relation.Binary.PropositionalEquality
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

!_ : Tid → TidSet
(! i) j = not (Dec.does (Tid.val i ≟ Tid.val j))

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
noRacingRd j rd = ∀ i → j ∉ rd i

-- Given ((i , I) : Wr) for address g, if j ∈ I then i has performed a write of g since j last sync'ed with it
noRacingWr : Tid → Wr → Set
noRacingWr j (i , I) = j ∉ I

record MemEvs : Set where
  constructor evs
  field
    rd : Rd
    wr : Wr

Mem : Set
Mem = Gid → MemEvs

MemEvs-≡ : ∀ {x x' y y'} → x ≡ x' → y ≡ y' → evs x y ≡ evs x' y'
MemEvs-≡ refl refl = refl

abstract
  _[_↦_] : {A B : Set} → {{HasDecEq A}} → (A → B) → A → B → A → B
  _[_↦_] {{eq}} f x y x' = if Dec.does (HasDecEq.eq eq x x') then y else f x'

  [↦]-simp-≡ : {A B : Set} {{eq : HasDecEq A}} (f : A → B) (x : A) (y : B) → (f [ x ↦ y ]) x ≡ y
  [↦]-simp-≡ {{eq}} f x y with HasDecEq.eq eq x x
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p refl)

  [↦]-simp-≢ : {A B : Set} {{eq : HasDecEq A}} (f : A → B) (x x' : A) (y : B) → x ≢ x' → (f [ x ↦ y ]) x' ≡ f x'
  [↦]-simp-≢ {{eq}} f x x' y neq with HasDecEq.eq eq x x'
  ... | yes p = ⊥-elim (neq p)
  ... | no ¬p = refl

  [↦]-comm : {A B : Set} {{eq : HasDecEq A}} (f : A → B) {x1 x2 : A} → x1 ≢ x2 → (y1 y2 : B) → (f [ x1 ↦ y1 ]) [ x2 ↦ y2 ] ≡ (f [ x2 ↦ y2 ]) [ x1 ↦ y1 ]
  [↦]-comm {A} {B} {{eq}} f {x1} {x2} neq y1 y2 = funext lem
    where
    lem : (z : A) → ((f [ x1 ↦ y1 ]) [ x2 ↦ y2 ]) z ≡ ((f [ x2 ↦ y2 ]) [ x1 ↦ y1 ]) z
    lem z with HasDecEq.eq eq x1 z | HasDecEq.eq eq x2 z
    ... | yes p | yes q = ⊥-elim (neq (trans p (sym q)))
    ... | no ¬p | yes q = refl
    ... | yes p | no ¬q = refl
    ... | no ¬p | no ¬q = refl

doRd : MemEvs → Tid → MemEvs
doRd x i = record x { rd = (MemEvs.rd x) [ i ↦ ! i ] }

doWr : MemEvs → Tid → MemEvs
doWr x i = record x { wr = i , ! i }

canSync : {ℂ : Magma} → TidSet → Prog ℂ → Set
canSync I Ts = ∀ i → i ∈ I → Ts i ≡ return ⊎ ∃[ T ] Ts i ≡ sync I ⨟ T

syncStep : {ℂ : Magma} (I : TidSet) (Ts : Prog ℂ) → canSync I Ts → Prog ℂ
syncStep I Ts p i with ∈-dec i I
syncStep I Ts p i | yes q with p i q
syncStep I Ts p i | yes q | inj₁ T = return
syncStep I Ts p i | yes q | inj₂ T = proj₁ T
syncStep I Ts p i | no  _ = Ts i

syncEnvs : {A : Set} → TidSet → Mem → GEnvs A → GEnvs A
syncEnvs I X Gs i g with ∈-dec i I | ∈-dec (proj₁ (MemEvs.wr (X g))) I
... | yes _ | yes _ = Gs (proj₁ (MemEvs.wr (X g))) g
... | yes _ | no  _ = Gs i g
... | no  _ | yes _ = Gs i g
... | no  _ | no  _ = Gs i g

syncMem : TidSet → Mem → Mem
syncMem I X g = evs (newRd (MemEvs.rd (X g))) (newWr (MemEvs.wr (X g)))
  where
  newRd : Rd → Rd
  newRd rd i with ∈-dec i I
  newRd rd i | yes _ = rd i - I
  newRd rd i | no  _ = rd i

  newWr : Wr → Wr
  newWr (i , J) with ∈-dec i I
  newWr (i , J) | yes _ = i , J - I
  newWr (i , J) | no  _ = i , J

CfgThd : Magma → Set
CfgThd ℂ = Maybe (REnv (Carrier ℂ) × GEnv (Carrier ℂ) × Mem × Thd ℂ)

cfgThdGetMem : ∀ {ℂ} → CfgThd ℂ → Maybe Mem
cfgThdGetMem (just (R , G , X , T)) = just X
cfgThdGetMem nothing = nothing

cfgThdSetMem : ∀ {ℂ} → CfgThd ℂ → Maybe Mem → CfgThd ℂ
cfgThdSetMem (just (R , G , X , T)) (just X') = just (R , G , X' , T)
cfgThdSetMem nothing (just X') = nothing
cfgThdSetMem (just (R , G , X , T)) nothing = nothing
cfgThdSetMem nothing nothing = nothing

CfgProg : Magma → Set
CfgProg ℂ = Maybe (REnvs (Carrier ℂ) × GEnvs (Carrier ℂ) × Mem × Prog ℂ)

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

data StepProg (ℂ : Magma) : CfgProg ℂ → CfgProg ℂ → Set where
  schd : ∀ i Rs Gs X Ts R G T R' G' X' T'
    → Rs i ≡ R
    → Gs i ≡ G
    → Ts i ≡ T
    → StepThd ℂ i (just (R , G , X , T)) (just (R' , G' , X' , T'))
    → StepProg ℂ (just (Rs , Gs , X , Ts)) (just (Rs [ i ↦ R' ] , Gs [ i ↦ G' ] , X' , Ts [ i ↦ T' ]))
  schdBad : ∀ i Rs Gs X Ts R G T
    → Rs i ≡ R
    → Gs i ≡ G
    → Ts i ≡ T
    → StepThd ℂ i (just (R , G , X , T)) nothing
    → StepProg ℂ (just (Rs , Gs , X , Ts)) nothing
  sync : ∀ I Rs Gs X Ts
    → (p : canSync I Ts)
    → StepProg ℂ (just (Rs , Gs , X , Ts)) (just (Rs , syncEnvs I X Gs , syncMem I X , syncStep I Ts p))

data StepProg* (ℂ : Magma) : CfgProg ℂ → CfgProg ℂ → Set where
  done : ∀ C
    → StepProg* ℂ C C
  step : ∀ C1 C2 C3
    → StepProg  ℂ C1 C2
    → StepProg* ℂ C2 C3
    → StepProg* ℂ C1 C3

data StepThdRefl (ℂ : Magma) (i : Tid) : CfgThd ℂ → CfgThd ℂ → Set where
  refl : ∀ C
    → StepThdRefl ℂ i C C
  const : ∀ R G X r c T
    → StepThdRefl ℂ i (just (R , G , X , const r c ⨟ T)) (just (R [ r ↦ c ] , G , X , T))
  binOp : ∀ R G X r r1 r2 T
    → StepThdRefl ℂ i (just (R , G , X , binOp r r1 r2 ⨟ T)) (just (R [ r ↦ ⊕ ℂ (R r1) (R r2) ] , G , X , T))
  rdReg : ∀ R G X r1 r2 T
    → StepThdRefl ℂ i (just (R , G , X , rdReg r1 r2 ⨟ T)) (just (R [ r1 ↦ R r2 ] , G , X , T))
  rdGbl : ∀ R G X r g T
    → noRacingWr i (MemEvs.wr (X g))
    → StepThdRefl ℂ i (just (R , G , X , rdGbl r g ⨟ T)) (just (R [ r ↦ G g ] , G , X [ g ↦ doRd (X g) i ] , T))
  rdGblBad : ∀ R G X r g T
    → ¬ noRacingWr i (MemEvs.wr (X g))
    → StepThdRefl ℂ i (just (R , G , X , rdGbl r g ⨟ T)) nothing
  wrGbl : ∀ R G X g r T
    → noRacingRd i (MemEvs.rd (X g))
    → noRacingWr i (MemEvs.wr (X g))
    → StepThdRefl ℂ i (just (R , G , X , wrGbl g r ⨟ T)) (just (R , G [ g ↦ R r ] , X [ g ↦ doWr (X g) i ] , T))
  wrGblBad : ∀ R G X g r T
    → ¬ noRacingRd i (MemEvs.rd (X g)) ⊎ ¬ noRacingWr i (MemEvs.wr (X g))
    → StepThdRefl ℂ i (just (R , G , X , wrGbl g r ⨟ T)) nothing

data StepProgRefl (ℂ : Magma) : CfgProg ℂ → CfgProg ℂ → Set where
  refl : ∀ C
    → StepProgRefl ℂ C C
  schd : ∀ i Rs Gs X Ts R G T R' G' X' T'
    → Rs i ≡ R
    → Gs i ≡ G
    → Ts i ≡ T
    → StepThdRefl ℂ i (just (R , G , X , T)) (just (R' , G' , X' , T'))
    → StepProgRefl ℂ (just (Rs , Gs , X , Ts)) (just (Rs [ i ↦ R' ] , Gs [ i ↦ G' ] , X' , Ts [ i ↦ T' ]))
  schdBad : ∀ i Rs Gs X Ts R G T
    → Rs i ≡ R
    → Gs i ≡ G
    → Ts i ≡ T
    → StepThdRefl ℂ i (just (R , G , X , T)) nothing
    → StepProgRefl ℂ (just (Rs , Gs , X , Ts)) nothing
  sync : ∀ I Rs Gs X Ts
    → (p : canSync I Ts)
    → StepProgRefl ℂ (just (Rs , Gs , X , Ts)) (just (Rs , syncEnvs I X Gs , syncMem I X , syncStep I Ts p))

data StepProgRefl* (ℂ : Magma) : CfgProg ℂ → CfgProg ℂ → Set where
  done : ∀ C
    → StepProgRefl* ℂ C C
  step : ∀ C1 C2 C3
    → StepProgRefl  ℂ C1 C2
    → StepProgRefl* ℂ C2 C3
    → StepProgRefl* ℂ C1 C3
