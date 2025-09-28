module KernelCheck.Prog where

open import Function.Base using (_∘_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Bool using (not; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum.Properties
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Negation using (¬_)

open import Relation.Binary.PropositionalEquality
open import KernelCheck.DecSet

record Magma : Set₁ where
  field
    Carrier : Set
    ⊕ : Carrier → Carrier → Carrier

open Magma

record Rid : Set where
  field
    val : ℕ

ridEq : DecidableEquality Rid
ridEq x y with Rid.val x ≟ Rid.val y
... | yes refl = yes refl
... | no !p = no (!p ∘ cong Rid.val)

record Gid : Set where
  field
    val : ℕ

gidEq : DecidableEquality Gid
gidEq x y with Gid.val x ≟ Gid.val y
... | yes refl = yes refl
... | no !p = no (!p ∘ cong Gid.val)

record Tid : Set where
  field
    val : ℕ

tidEq : DecidableEquality Tid
tidEq x y with Tid.val x ≟ Tid.val y
... | yes refl = yes refl
... | no !p = no (!p ∘ cong Tid.val)

TidSet = DecSet Tid

data Addr : Set where
  rid : Rid → Addr
  gid : Gid → Addr

addrEq : DecidableEquality Addr
addrEq (rid x) (rid y) with Rid.val x ≟ Rid.val y
... | yes refl = yes refl
... | no !p = no λ { refl → !p refl }
addrEq (rid x) (gid y) = no λ ()
addrEq (gid x) (rid y) = no λ ()
addrEq (gid x) (gid y) with Gid.val x ≟ Gid.val y
... | yes refl = yes refl
... | no !p = no λ { refl → !p refl }

Env : Set → Set
Env A = Addr → A

Envs : Set → Set
Envs A = Tid → Env A

data Stmt (ℂ : Magma) : Set where
  -- x ← c
  const : Rid → Magma.Carrier ℂ → Stmt ℂ
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
Wr = Maybe (Tid × TidSet)

record MemEvs : Set where
  constructor evs
  field
    rd : Rd
    wr : Wr

noRacingRd : Rd → Tid → Set
noRacingRd rd i = ∀ j → i ∉ rd j

noRacingWr : Wr → Tid → Set
noRacingWr wr i = wr ≡ nothing ⊎ ∃[ I ] wr ≡ just (i , I)

Mem : Set
Mem = Gid → MemEvs

updFun : {A B : Set} → DecidableEquality A → (A → B) → A → B → A → B
updFun _≟_ f x y x' = if Dec.does (x ≟ x') then y else f x'

_[_↦_] : {A : Set} → Env A → Addr → A → Addr → A
_[_↦_] = updFun addrEq

updMem : Mem → Gid → MemEvs → Gid → MemEvs
updMem = updFun gidEq

!_ : Tid → TidSet
(! i) j = not (Dec.does (Tid.val i ≟ Tid.val j))

doRd : MemEvs → Gid → Tid → MemEvs
doRd x g i = record x { rd = updFun tidEq (MemEvs.rd x) i (! i) }

doWr : MemEvs → Gid → Tid → MemEvs
doWr x g i = record x { wr = just (i , ! i) }

canSync : {ℂ : Magma} → TidSet → Prog ℂ → Set
canSync I P = ∀ i → i ∈ I → P i ≡ return ⊎ ∃[ T' ] P i ≡ sync I ⨟ T'

syncStep : {ℂ : Magma} (I : TidSet) (P : Prog ℂ) → canSync I P → Prog ℂ
syncStep I P p i with ∈-dec i I
syncStep I P p i | yes q with p i q
syncStep I P p i | yes q | inj₁ T = return
syncStep I P p i | yes q | inj₂ T = proj₁ T
syncStep I P p i | no ¬q = P i

syncEnvs : {A : Set} → TidSet → Mem → Envs A → Envs A
syncEnvs I X ℰ i (rid r) = ℰ i (rid r)
syncEnvs I X ℰ i (gid g) with (MemEvs.wr (X g))
... | nothing = ℰ i (gid g)
... | just (j , _) = ℰ j (gid g)

syncMem : TidSet → Mem → Mem
syncMem I X g = evs (newRd (MemEvs.rd (X g))) (newWr (MemEvs.wr (X g)))
  where
  newRd : Rd → Rd
  newRd rd i with ∈-dec i I
  newRd rd i | yes p = rd i - I
  newRd rd i | no ¬p = rd i

  newWr : Wr → Wr
  newWr nothing = nothing
  newWr (just (i , J)) with ∈-dec i I
  newWr (just (i , J)) | yes p with isEmpty (J - I)
  newWr (just (i , J)) | yes p | yes q = nothing
  newWr (just (i , J)) | yes p | no ¬q = just (i , J - I)
  newWr (just (i , J)) | no ¬p = just (i , J)

data StepThd (ℂ : Magma) (i : Tid) : Env (Carrier ℂ) → Mem → Thd ℂ → Env (Carrier ℂ) → Mem → Maybe (Thd ℂ) → Set where
  const : ∀ E X r c T
    → StepThd ℂ i E X (const r c ⨟ T) (E [ rid r ↦ c ]) X (just T)
  binOp : ∀ E X r r1 r2 T
    → StepThd ℂ i E X (binOp r r1 r2 ⨟ T) (E [ rid r ↦ ⊕ ℂ (E (rid r1)) (E (rid r2)) ]) X (just T)
  rdReg : ∀ E X r1 r2 T
    → StepThd ℂ i E X (rdReg r1 r2 ⨟ T) (E [ rid r1 ↦ E (rid r2) ]) X (just T)
  rdGbl : ∀ E X r g T
    → noRacingWr (MemEvs.wr (X g)) i
    → StepThd ℂ i E X (rdGbl r g ⨟ T) (E [ rid r ↦ E (gid g) ]) (updMem X g (doRd (X g) g i)) (just T)
  wrGbl : ∀ E X g r T
    → noRacingRd (MemEvs.rd (X g)) i
    → noRacingWr (MemEvs.wr (X g)) i
    → StepThd ℂ i E X (wrGbl g r ⨟ T) (E [ gid g ↦ E (rid r) ]) (updMem X g (doWr (X g) g i)) (just T)
  rdGblBad : ∀ E X r g T
    → ¬ noRacingWr (MemEvs.wr (X g)) i
    → StepThd ℂ i E X (rdGbl r g ⨟ T) (E [ rid r ↦ E (gid g) ]) (updMem X g (doRd (X g) g i)) nothing
  wrGblBad : ∀ E X g r T
    → ¬ noRacingRd (MemEvs.rd (X g)) i ⊎ ¬ noRacingWr (MemEvs.wr (X g)) i
    → StepThd ℂ i E X (wrGbl g r ⨟ T) (E [ gid g ↦ E (rid r) ]) (updMem X g (doWr (X g) g i)) nothing

data StepProg (ℂ : Magma) : Envs (Carrier ℂ) → Mem → Prog ℂ → Envs (Carrier ℂ) → Mem → Maybe (Prog ℂ) → Set where
  schd : ∀ i ℰ X P E' X' T'
    → StepThd ℂ i (ℰ i) X (P i) E' X' (just T')
    → StepProg ℂ ℰ X P (updFun tidEq ℰ i E') X' (just (updFun tidEq P i T'))
  schdBad : ∀ i ℰ X P E' X'
    → StepThd ℂ i (ℰ i) X (P i) E' X' nothing
    → StepProg ℂ ℰ X P (updFun tidEq ℰ i E') X' nothing
  sync : ∀ I ℰ X P
    → (p : canSync I P)
    → StepProg ℂ ℰ X P (syncEnvs I X ℰ) (syncMem I X) (just (syncStep I P p))

-- reflexive closure of StepProg
data StepProg+ (ℂ : Magma) : Envs (Carrier ℂ) → Mem → Prog ℂ → Envs (Carrier ℂ) → Mem → Maybe (Prog ℂ) → Set where
  refl : ∀ ℰ X P
    → StepProg+ ℂ ℰ X P ℰ X (just P)
  schd : ∀ i ℰ X P E' X' T'
    → StepThd ℂ i (ℰ i) X (P i) E' X' (just T')
    → StepProg+ ℂ ℰ X P (updFun tidEq ℰ i E') X' (just (updFun tidEq P i T'))
  schdBad : ∀ i ℰ X P E' X'
    → StepThd ℂ i (ℰ i) X (P i) E' X' nothing
    → StepProg+ ℂ ℰ X P (updFun tidEq ℰ i E') X' nothing
  sync : ∀ I ℰ X P
    → (p : canSync I P)
    → StepProg+ ℂ ℰ X P (syncEnvs I X ℰ) (syncMem I X) (just (syncStep I P p))

data StepProg+* (ℂ : Magma) : Envs (Carrier ℂ) → Mem → Prog ℂ → Envs (Carrier ℂ) → Mem → Maybe (Prog ℂ) → Set where
  done : ∀ ℰ X P
    → StepProg+* ℂ ℰ X P ℰ X (just P)
  step : ∀ ℰ1 X1 P1 ℰ2 X2 P2 ℰ3 X3 P3?
    → StepProg+ ℂ ℰ1 X1 P1 ℰ2 X2 (just P2)
    → StepProg+* ℂ ℰ2 X2 P2 ℰ3 X3 P3?
    → StepProg+* ℂ ℰ1 X1 P1 ℰ3 X3 P3?
