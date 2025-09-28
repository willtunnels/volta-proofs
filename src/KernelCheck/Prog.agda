module KernelCheck.Prog where

open import Function.Base using (_∘_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Bool using (not; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum.Properties
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
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

record MemEvs : Set where
  constructor evs
  field
    rd : Rd
    wr : Wr

noRacingRd : Tid → Rd → Set
noRacingRd i rd = ∀ j → i ∉ rd j

noRacingWr : Tid → Wr → Set
noRacingWr i (_ , J)  = i ∉ J

Mem : Set
Mem = Gid → MemEvs

updFun : {A B : Set} → DecidableEquality A → (A → B) → A → B → A → B
updFun _≟_ f x y x' = if Dec.does (x ≟ x') then y else f x'

updFun-comm : ∀ {A B : Set} {_≟_ f} {x1 x2 : A} {y1 y2 : B} → x1 ≢ x2 → updFun _≟_ (updFun _≟_ f x1 y1) x2 y2 ≡ updFun _≟_ (updFun _≟_ f x2 y2) x1 y1
updFun-comm {A} {B} {_≟_} {f} {x1} {x2} {y1} {y2} neq = funext lem
  where
  lem : (z : A) → updFun _≟_ (updFun _≟_ f x1 y1) x2 y2 z ≡ updFun _≟_ (updFun _≟_ f x2 y2) x1 y1 z
  lem z with x1 ≟ z | x2 ≟ z
  ... | yes p | yes q = ⊥-elim (neq (trans p (sym q)))
  ... | no ¬p | yes q = refl
  ... | yes p | no ¬q = refl
  ... | no ¬p | no ¬q = refl

_[_↦_] : {A : Set} → Env A → Addr → A → Addr → A
_[_↦_] = updFun addrEq

updMem : Mem → Gid → MemEvs → Gid → MemEvs
updMem = updFun gidEq

!_ : Tid → TidSet
(! i) j = not (Dec.does (Tid.val i ≟ Tid.val j))

doRd : MemEvs → Tid → MemEvs
doRd x i = record x { rd = updFun tidEq (MemEvs.rd x) i (! i) }

doWr : MemEvs → Tid → MemEvs
doWr x i = record x { wr = i , ! i }

canSync : {ℂ : Magma} → TidSet → Prog ℂ → Set
canSync I P = ∀ i → i ∈ I → P i ≡ return ⊎ ∃[ T ] P i ≡ sync I ⨟ T

syncStep : {ℂ : Magma} (I : TidSet) (P : Prog ℂ) → canSync I P → Prog ℂ
syncStep I P p i with ∈-dec i I
syncStep I P p i | yes q with p i q
syncStep I P p i | yes q | inj₁ T = return
syncStep I P p i | yes q | inj₂ T = proj₁ T
syncStep I P p i | no  _ = P i

syncEnvs : {A : Set} → TidSet → Mem → Envs A → Envs A
syncEnvs I X ℰ i (rid r) = ℰ i (rid r)
syncEnvs I X ℰ i (gid g) with ∈-dec i I | ∈-dec (proj₁ (MemEvs.wr (X g))) I
... | yes _ | yes _ = ℰ (proj₁ (MemEvs.wr (X g))) (gid g)
... | yes _ | no  _ = ℰ i (gid g)
... | no  _ | yes _ = ℰ i (gid g)
... | no  _ | no  _ = ℰ i (gid g)

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

data StepThd (ℂ : Magma) (i : Tid) : Env (Carrier ℂ) → Mem → Thd ℂ → Env (Carrier ℂ) → Mem → Thd ℂ → Set where
  const : ∀ E X r c T
    → StepThd ℂ i E X (const r c ⨟ T) (E [ rid r ↦ c ]) X T
  binOp : ∀ E X r r1 r2 T
    → StepThd ℂ i E X (binOp r r1 r2 ⨟ T) (E [ rid r ↦ ⊕ ℂ (E (rid r1)) (E (rid r2)) ]) X T
  rdReg : ∀ E X r1 r2 T
    → StepThd ℂ i E X (rdReg r1 r2 ⨟ T) (E [ rid r1 ↦ E (rid r2) ]) X T
  rdGbl : ∀ E X r g T
    → noRacingWr i (MemEvs.wr (X g))
    → StepThd ℂ i E X (rdGbl r g ⨟ T) (E [ rid r ↦ E (gid g) ]) (updMem X g (doRd (X g) i)) T
  wrGbl : ∀ E X g r T
    → noRacingRd i (MemEvs.rd (X g))
    → noRacingWr i (MemEvs.wr (X g))
    → StepThd ℂ i E X (wrGbl g r ⨟ T) (E [ gid g ↦ E (rid r) ]) (updMem X g (doWr (X g) i)) T

data StepProg (ℂ : Magma) : Envs (Carrier ℂ) → Mem → Prog ℂ → Envs (Carrier ℂ) → Mem → Prog ℂ → Set where
  schd : ∀ i ℰ X P E' X' T'
    → StepThd ℂ i (ℰ i) X (P i) E' X' T'
    → StepProg ℂ ℰ X P (updFun tidEq ℰ i E') X' (updFun tidEq P i T')
  sync : ∀ I ℰ X P
    → (p : canSync I P)
    → StepProg ℂ ℰ X P (syncEnvs I X ℰ) (syncMem I X) (syncStep I P p)

data StepProg* (ℂ : Magma) : Envs (Carrier ℂ) → Mem → Prog ℂ → Envs (Carrier ℂ) → Mem → Prog ℂ → Set where
  done : ∀ ℰ X P
    → StepProg* ℂ ℰ X P ℰ X P
  step : ∀ ℰ1 X1 P1 ℰ2 X2 P2 ℰ3 X3 P3
    → StepProg  ℂ ℰ1 X1 P1 ℰ2 X2 P2
    → StepProg* ℂ ℰ2 X2 P2 ℰ3 X3 P3
    → StepProg* ℂ ℰ1 X1 P1 ℰ3 X3 P3

data StepProgRefl (ℂ : Magma) : Envs (Carrier ℂ) → Mem → Prog ℂ → Envs (Carrier ℂ) → Mem → Prog ℂ → Set where
  refl : ∀ ℰ X P
    → StepProgRefl ℂ ℰ X P ℰ X P
  schd : ∀ i ℰ X P E' X' T'
    → StepThd ℂ i (ℰ i) X (P i) E' X' T'
    → StepProgRefl ℂ ℰ X P (updFun tidEq ℰ i E') X' (updFun tidEq P i T')
  sync : ∀ I ℰ X P
    → (p : canSync I P)
    → StepProgRefl ℂ ℰ X P (syncEnvs I X ℰ) (syncMem I X) (syncStep I P p)

data StepProgRefl* (ℂ : Magma) : Envs (Carrier ℂ) → Mem → Prog ℂ → Envs (Carrier ℂ) → Mem → Prog ℂ → Set where
  done : ∀ ℰ X P
    → StepProgRefl* ℂ ℰ X P ℰ X P
  step : ∀ ℰ1 X1 P1 ℰ2 X2 P2 ℰ3 X3 P3
    → StepProgRefl  ℂ ℰ1 X1 P1 ℰ2 X2 P2
    → StepProgRefl* ℂ ℰ2 X2 P2 ℰ3 X3 P3
    → StepProgRefl* ℂ ℰ1 X1 P1 ℰ3 X3 P3
