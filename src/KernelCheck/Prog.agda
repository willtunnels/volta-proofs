{-# OPTIONS --allow-unsolved-metas #-}
module KernelCheck.Prog where

open import Axiom.UniquenessOfIdentityProofs.WithK
open import Function.Base using (_∘_; _$_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Bool using (Bool; true; false; not; if_then_else_; _∧_)
import Data.Bool.Properties
open import Data.Sum using (_⊎_; inj₁; inj₂; map; map₁; map₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
import Data.Product.Properties
open import Relation.Nullary.Decidable using (Dec; yes; no; fromSum)
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

fmapStmt : ∀ {ℂ ℂ' : Magma} → (ℂ .Carrier → ℂ' .Carrier) → Stmt ℂ → Stmt ℂ'
fmapStmt f (const x x₁) = const x (f x₁)
fmapStmt f (binOp x x₁ x₂) = binOp x x₁ x₂
fmapStmt f (rdReg x x₁) = rdReg x x₁
fmapStmt f (rdGbl x x₁) = rdGbl x x₁
fmapStmt f (wrGbl x x₁) = wrGbl x x₁
fmapStmt f (sync x) = sync x

fmapThd : ∀ {ℂ ℂ' : Magma} → (ℂ .Carrier → ℂ' .Carrier) → Thd ℂ → Thd ℂ'
fmapThd f return = return
fmapThd f (x ⨟ x₁) = fmapStmt f x ⨟ fmapThd f x₁

return≢ : ∀ ℂ I T → return {ℂ} ≢ sync {ℂ} I ⨟ T
return≢ ℂ I T ()

⨟-injective1 : ∀ ℂ I I' T T' → (sync {ℂ} I ⨟ T) ≡ (sync {ℂ} I' ⨟ T') → I ≡ I'
⨟-injective1 ℂ I I' T T' refl = refl

⨟-injective2 : ∀ ℂ I I' T T' → (sync {ℂ} I ⨟ T) ≡ (sync {ℂ} I' ⨟ T') → T ≡ T'
⨟-injective2 ℂ I I' T T' refl = refl

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
... | p | q = ∉∧∈→⊥ i I i∉I i∈I

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

    [↦]-idem : (f : A → B) (x x' : A) (y : B) → ((f [ x ↦ y ]) [ x ↦ y ]) x' ≡ (f [ x ↦ y ]) x'
    [↦]-idem f x x' y with HasDecEq.eq eq x x'
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

doRd-getWr : ∀ X (g g' : Gid) i → (X [ g ↦ doRd (X g) i ]) g' .MemEvs.wr ≡ X g' .MemEvs.wr
doRd-getWr X g g' i with gidEq g g'
... | yes refl = cong MemEvs.wr ([↦]-simp-≡ X g (doRd (X g) i))
... | no g≢g' = cong MemEvs.wr ([↦]-simp-≢ X g g' (doRd (X g) i) g≢g')

doRd-noRace : ∀ i j g g' (X : Mem) → noRacingWr i ((X [ g ↦ doRd (X g) j ]) g' .MemEvs.wr) → noRacingWr i (X g' .MemEvs.wr)
doRd-noRace i j g g' X p = cast (cong (λ a → noRacingWr i a) (doRd-getWr X g g' j)) p

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

≤-Mem-doWr-other : ∀ i j X g → i ≢ j → ≤-Mem i X (X [ g ↦ doWr (X g) j ])
≤-Mem-doWr-other i j X g i≢j g' with gidEq g g'
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

≤-Mem-doWr-this : ∀ (i : Tid) (X : Mem) (g g' : Gid) → g ≢ g' → ≤-MemEvs i (X g') ((X [ g ↦ doWr (X g) i ]) g')
≤-Mem-doWr-this i X g g' g≢g' =
  (λ noRace j → cast (cong (λ a → i ≡ j ⊎ (i ∉ a .MemEvs.rd j)) ([↦]-simp-≢ X g g' (doWr (X g) i) g≢g')) (noRace j)) ,
  (λ noRace → cast (cong (λ a → noRacingWr i (a .MemEvs.wr)) ([↦]-simp-≢ X g g' (doWr (X g) i) g≢g')) noRace)

yesRacingRd-mono : ∀ i X X' g → ≤-Mem i X X' → yesRacingRd i (MemEvs.rd (X g)) → yesRacingRd i (MemEvs.rd (X' g))
yesRacingRd-mono i X X' g p q = ¬noRacingRd→yesRacingRd i (MemEvs.rd (X' g)) (λ noRaceX' → yesRacingRd→¬noRacingRd i (MemEvs.rd (X g)) q (p g .proj₁ noRaceX'))

yesRacingWr-mono : ∀ i X X' g → ≤-Mem i X X' → yesRacingWr i (MemEvs.wr (X g)) → yesRacingWr i (MemEvs.wr (X' g))
yesRacingWr-mono i X X' g p q = ¬noRacingWr→yesRacingWr i (MemEvs.wr (X' g)) (λ noRaceX' → yesRacingWr→¬noRacingWr i (MemEvs.wr (X g)) q (p g .proj₂ noRaceX'))

canSync : {ℂ : Magma} → TidSet → Prog ℂ → Set
canSync I Ts = ∀ i → i ∈ I → Ts i ≡ return ⊎ ∃[ T ] Ts i ≡ sync I ⨟ T

canSync-isProp : {ℂ : Magma} (I : TidSet) (Ts : Prog ℂ) → isProp (canSync I Ts)
canSync-isProp I Ts p q = funext' λ i → funext' λ i∈I → lem I Ts i (p i i∈I) (q i i∈I)
  where
  lem : {ℂ : Magma} (I : TidSet) (Ts : Prog ℂ) (i : Tid) (p q : (Ts i ≡ return) ⊎ (∃[ T ] Ts i ≡ (sync I ⨟ T))) → p ≡ q
  lem {ℂ} I Ts i (inj₁ x) (inj₁ y) = cong inj₁ (uip x y)
  lem {ℂ} I Ts i (inj₁ x) (inj₂ y) = ⊥-elim (return≢ ℂ I (y .proj₁) (sym x ∙ y .proj₂))
  lem {ℂ} I Ts i (inj₂ x) (inj₁ y) = ⊥-elim (return≢ ℂ I (x .proj₁) (sym y ∙ x .proj₂))
  lem {ℂ} I Ts i (inj₂ x) (inj₂ y) = cong inj₂ (case' (LEM (x .proj₁ ≡ y .proj₁))
    (λ e → Data.Product.Properties.Σ-≡,≡→≡ (e , uip (subst (λ a → Ts i ≡ (sync I ⨟ a)) e (x .proj₂)) (y .proj₂)))
    (λ e → ⊥-elim (e (⨟-injective2 ℂ I I (x .proj₁) (y .proj₁) (sym (x .proj₂) ∙ y .proj₂)))))

syncStep : {ℂ : Magma} (I : TidSet) (Ts : Prog ℂ) → canSync I Ts → Prog ℂ
syncStep I Ts p i with ∈-dec i I
syncStep I Ts p i | yes q with p i q
syncStep I Ts p i | yes q | inj₁ T = return
syncStep I Ts p i | yes q | inj₂ T = T .proj₁
syncStep I Ts p i | no  _ = Ts i

syncStep-return : {ℂ : Magma} (I : TidSet) (Ts : Prog ℂ) (p : canSync I Ts) (i : Tid)
  → Ts i ≡ return
  → syncStep I Ts p i ≡ return
syncStep-return {ℂ} I Ts p i isReturn with ∈-dec i I
syncStep-return {ℂ} I Ts p i isReturn | yes q with p i q
syncStep-return {ℂ} I Ts p i isReturn | yes q | inj₁ T = refl
syncStep-return {ℂ} I Ts p i isReturn | yes q | inj₂ T = ⊥-elim (return≢ ℂ I (T .proj₁) (sym isReturn ∙ T .proj₂))
syncStep-return {ℂ} I Ts p i isReturn | no _ = isReturn

syncStep-simp-∉ : ∀ {ℂ} I (Ts : Prog ℂ) (p : canSync I Ts) i → i ∉ I → syncStep I Ts p i ≡ Ts i
syncStep-simp-∉ I Ts p i i∉I with ∈-dec i I
... | yes i∈I = ∉∧∈→⊥ i I i∉I i∈I
... | no _ = refl

syncStep-simp-∈ : ∀ {ℂ} I (Ts : Prog ℂ) (p : canSync I Ts) (Ts' : Prog ℂ) (p' : canSync I Ts') i
  → i ∈ I
  → Ts i ≡ Ts' i
  → syncStep I Ts p i ≡ syncStep I Ts' p' i
syncStep-simp-∈ I Ts p Ts' p' i i∈I e with ∈-dec i I
syncStep-simp-∈ I Ts p Ts' p' i i∈I e | yes q with p i q | p' i q
syncStep-simp-∈ I Ts p Ts' p' i i∈I e | yes q | inj₁ Ti≡ | inj₁ Tj≡ = refl
syncStep-simp-∈ I Ts p Ts' p' i i∈I e | yes q | inj₁ Ti≡ | inj₂ Tj≡ = ⊥-elim (return≢ _ _ _ (sym Ti≡ ∙ e ∙ Tj≡ .proj₂))
syncStep-simp-∈ I Ts p Ts' p' i i∈I e | yes q | inj₂ Ti≡ | inj₁ Tj≡ = ⊥-elim (return≢ _ _ _ (sym Tj≡ ∙ sym e ∙ Ti≡ .proj₂))
syncStep-simp-∈ I Ts p Ts' p' i i∈I e | yes q | inj₂ Ti≡ | inj₂ Tj≡ = ⨟-injective2 _ I I (Ti≡ .proj₁) (Tj≡ .proj₁) (sym (Ti≡ .proj₂) ∙ e ∙ Tj≡ .proj₂)
syncStep-simp-∈ I Ts p Ts' p' i i∈I e | no i∉I = ∉∧∈→⊥ i I (¬∈→∉ i I i∉I) i∈I

syncStep-simp-≡ : ∀ {ℂ} I J (TsI TsJ : Prog ℂ) (p : canSync I TsI) (q : canSync J TsJ) i
  → i ∈ I
  → i ∈ J
  → TsI i ≡ TsJ i
  → syncStep I TsI p i ≡ syncStep J TsJ q i
syncStep-simp-≡ {ℂ} I J TsI TsJ p q i r s e with ∈-dec i I | ∈-dec i J
syncStep-simp-≡ {ℂ} I J TsI TsJ p q i r s e | yes i∈I | yes i∈J with p i i∈I | q i i∈J
syncStep-simp-≡ {ℂ} I J TsI TsJ p q i r s e | yes i∈I | yes i∈J | inj₁ Ti≡ | inj₁ Tj≡ = refl
syncStep-simp-≡ {ℂ} I J TsI TsJ p q i r s e | yes i∈I | yes i∈J | inj₁ Ti≡ | inj₂ Tj≡ = ⊥-elim (return≢ _ _ _ (sym Ti≡ ∙ e ∙ Tj≡ .proj₂)) 
syncStep-simp-≡ {ℂ} I J TsI TsJ p q i r s e | yes i∈I | yes i∈J | inj₂ Ti≡ | inj₁ Tj≡ = ⊥-elim (return≢ _ _ _ (sym Tj≡ ∙ sym e ∙ Ti≡ .proj₂))
syncStep-simp-≡ {ℂ} I J TsI TsJ p q i r s e | yes i∈I | yes i∈J | inj₂ Ti≡ | inj₂ Tj≡ = ⨟-injective2 ℂ I J (Ti≡ .proj₁) (Tj≡ .proj₁) (sym (Ti≡ .proj₂) ∙ e ∙ Tj≡ .proj₂)
syncStep-simp-≡ {ℂ} I J TsI TsJ p q i r s e | yes i∈I | no  i∉J = ⊥-elim (false≢true (sym (Data.Bool.Properties.¬-not i∉J) ∙ s))
syncStep-simp-≡ {ℂ} I J TsI TsJ p q i r s e | no  i∉I | yes i∈J = ⊥-elim (false≢true (sym (Data.Bool.Properties.¬-not i∉I) ∙ r))
syncStep-simp-≡ {ℂ} I J TsI TsJ p q i r s e | no  i∉I | no  i∉J = ⊥-elim (false≢true (sym (Data.Bool.Properties.¬-not i∉I) ∙ r))

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

syncMemRd-simp-∈ : ∀ I rd i → i ∈ I → syncMemRd I rd i ≡ rd i - I
syncMemRd-simp-∈ I rd i i∈I with ∈-dec i I
... | yes _ = refl
... | no i∉I = ⊥-elim (∉∧∈→⊥ i I (¬∈→∉ i I i∉I) i∈I)

syncMemRd-simp-∉ : ∀ I rd i → i ∉ I → syncMemRd I rd i ≡ rd i
syncMemRd-simp-∉ I rd i i∉I with ∈-dec i I
... | yes i∈I = ⊥-elim (∉∧∈→⊥ i I i∉I i∈I)
... | no _ = refl

syncMemWr-⊆ : ∀ I x → syncMemWr I x .proj₂ ⊆ x .proj₂
syncMemWr-⊆ I (i , J) j p with ∈-dec i I
... | yes _ = ∧-elim1 (J j) (not (I j)) p
... | no _ = p

syncMemWr-∉ : ∀ I x j → j ∉ I → j ∈ x .proj₂ → j ∈ syncMemWr I x .proj₂
syncMemWr-∉ I (i , J) j j∉I p with ∈-dec i I
... | yes _ = ∧-intro (J j) (not (I j)) (p , subst (λ a → not a ≡ true) (sym j∉I) refl)
... | no _ = p

syncMemWr-simp1 : ∀ I x → syncMemWr I x .proj₁ ≡ x .proj₁
syncMemWr-simp1 I (i , J) with ∈-dec i I
... | yes _ = refl
... | no _ = refl

syncMemWr-simp-∈ : ∀ I wr → wr .proj₁ ∈ I → syncMemWr I wr .proj₂ ≡ wr .proj₂ - I
syncMemWr-simp-∈ I (i , J) i∈I with ∈-dec i I
... | yes _ = refl
... | no i∉I = ⊥-elim (∉∧∈→⊥ i I (¬∈→∉ i I i∉I) i∈I)

syncMemWr-simp-∉ : ∀ I wr → wr .proj₁ ∉ I → syncMemWr I wr .proj₂ ≡ wr .proj₂
syncMemWr-simp-∉ I (i , J) i∉I with ∈-dec i I
... | yes i∈I = ⊥-elim (∉∧∈→⊥ i I i∉I i∈I)
... | no _ = refl

syncMemRd-cong : ∀ I rd rd' i j → rd i j ≡ rd' i j → syncMemRd I rd i j ≡ syncMemRd I rd' i j
syncMemRd-cong I rd rd' i j eq with ∈-dec i I
... | yes _ = cong (λ b → b ∧ not (I j)) eq
... | no _ = eq

syncMem : TidSet → Mem → Mem
syncMem I X g = evs (syncMemRd I (MemEvs.rd (X g))) (syncMemWr I (MemEvs.wr (X g)))

CfgThd : Magma → Set
CfgThd ℂ = Maybe (REnv (Carrier ℂ) × GEnv (Carrier ℂ) × Mem × Thd ℂ)

CfgProg : Magma → Set
CfgProg ℂ = Maybe (REnvs (Carrier ℂ) × GEnv (Carrier ℂ) × Mem × Prog ℂ)

CfgProg-≡-intro : ∀ {ℂ}
  {Rs  : REnvs (Carrier ℂ)} {G  : GEnv (Carrier ℂ)} {X  : Mem} {Ts  : Prog ℂ}
  {Rs' : REnvs (Carrier ℂ)} {G' : GEnv (Carrier ℂ)} {X' : Mem} {Ts' : Prog ℂ}
  → Rs ≡ Rs' → G ≡ G' → X ≡ X' → Ts ≡ Ts'
  → just (Rs , G , X , Ts) ≡ just (Rs' , G' , X' , Ts')
CfgProg-≡-intro {ℂ} {Rs} {Gs} {X} {Ts} {Rs' = Rs'} {G' = G'} {X' = X'} {Ts' = Ts'} refl refl refl refl = cong (λ a → just (Rs , Gs , X , a)) refl

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
  schd : ∀ i Rs X Ts R G T R' G' X' T'
    → Rs i ≡ R
    → Ts i ≡ T
    → StepThd ℂ i (just (R , G , X , T)) (just (R' , G' , X' , T'))
    → StepProg ℂ (just (Rs , G , X , Ts)) (just (Rs [ i ↦ R' ] , G' , X' , Ts [ i ↦ T' ]))
  schdBad : ∀ i Rs X Ts R G T
    → Rs i ≡ R
    → Ts i ≡ T
    → StepThd ℂ i (just (R , G , X , T)) nothing
    → StepProg ℂ (just (Rs , G , X , Ts)) nothing
  sync : ∀ I Rs G X Ts
    → (q : canSync I Ts)
    → StepProg ℂ (just (Rs , G , X , Ts)) (just (Rs , G , syncMem I X , syncStep I Ts q))

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
  schd : ∀ i Rs X Ts R G T R' G' X' T'
    → Rs i ≡ R
    → Ts i ≡ T
    → StepThd ℂ i (just (R , G , X , T)) (just (R' , G' , X' , T'))
    → StepProgRefl ℂ (just (Rs , G , X , Ts)) (just (Rs [ i ↦ R' ] , G' , X' , Ts [ i ↦ T' ]))
  schdBad : ∀ i Rs X Ts R G T
    → Rs i ≡ R
    → Ts i ≡ T
    → StepThd ℂ i (just (R , G , X , T)) nothing
    → StepProgRefl ℂ (just (Rs , G , X , Ts)) nothing
  sync : ∀ I Rs G X Ts
    → (q : canSync I Ts)
    → StepProgRefl ℂ (just (Rs , G , X , Ts)) (just (Rs , G , syncMem I X , syncStep I Ts q))

data StepProgRefl* (ℂ : Magma) : CfgProg ℂ → CfgProg ℂ → Set where
  done : ∀ C
    → StepProgRefl* ℂ C C
  step : ∀ C1 C2 C3
    → StepProgRefl  ℂ C1 C2
    → StepProgRefl* ℂ C2 C3
    → StepProgRefl* ℂ C1 C3
