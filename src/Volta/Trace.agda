module Volta.Trace where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Product using (_,_; _×_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec; yes; no; fromSum; ¬_)

open import Volta.Util
open import Volta.Prog

-- Given a trace, the action executed n steps ago
getStepS : ∀ {ℂ} C1 C2 → StepProgS* ℂ C1 C2 → ℕ → Maybe (∃[ C1' ] ∃[ C2' ] StepProgS ℂ C1' C2')
getStepS {ℂ} C1 C3 (done .C1) zero = nothing
getStepS {ℂ} C1 C3 (done .C1) (suc n) = nothing
getStepS {ℂ} C1 C3 (step .C1 C2 .C3 x xs) zero = just (C1 , C2 , x)
getStepS {ℂ} C1 C3 (step .C1 C2 .C3 x xs) (suc n) = getStepS C2 C3 xs n

getStep : ∀ {ℂ} C1 C2 → StepProg* ℂ C1 C2 → ℕ → Maybe (∃[ C1' ] ∃[ C2' ] StepProg ℂ C1' C2')
getStep {ℂ} C1 C3 (done .C1) zero = nothing
getStep {ℂ} C1 C3 (done .C1) (suc n) = nothing
getStep {ℂ} C1 C3 (step .C1 C2 .C3 x xs) zero = just (C1 , C2 , x)
getStep {ℂ} C1 C3 (step .C1 C2 .C3 x xs) (suc n) = getStep C2 C3 xs n

StepThd→StepThdS : ∀ {ℂ i R Gs X T R' Gs' X' T'}
  → StepThd ℂ i (just (R , Gs , X , T)) (just (R' , Gs' , X' , T'))
  → StepThdS ℂ i (R , Gs , T) (R' , Gs' , T')
StepThd→StepThdS (const Gs T R' r c T') = const Gs T r c T'
StepThd→StepThdS (binOp Gs T R' r r1 r2 T') = binOp Gs T r r1 r2 T'
StepThd→StepThdS (rdReg Gs T R' r1 r2 T') = rdReg Gs T r1 r2 T'
StepThd→StepThdS (rdGbl Gs T R' r g T' x) = rdGbl Gs T r g T'
StepThd→StepThdS (wrGbl Gs T R' g r T' x x₁) = wrGbl Gs T g r T'

StepProg→StepProgS : ∀ {ℂ Rs Gs X P Rs' Gs' X' P'}
  → StepProg ℂ (just (Rs , Gs , X , P)) (just (Rs' , Gs' , X' , P'))
  → StepProgS ℂ (Rs , Gs , P) (Rs' , Gs' , P')
StepProg→StepProgS (schd i Rs X P R Gs T R' Gs' X' T' x x₁ x₂) = schd i Rs P R Gs T R' Gs' T' x x₁ (StepThd→StepThdS x₂)
StepProg→StepProgS (sync I Rs Gs X P q) = sync I Rs Gs P q

StepProg*→StepProgS* : ∀ {ℂ Rs Gs X P Rs' Gs' X' P'}
  → StepProg* ℂ (just (Rs , Gs , X , P)) (just (Rs' , Gs' , X' , P'))
  → StepProgS* ℂ (Rs , Gs , P) (Rs' , Gs' , P')
StepProg*→StepProgS* (done (just _)) = done _
StepProg*→StepProgS* (step (just _) (just _) (just _) x xs) = step _ _ _ (StepProg→StepProgS x) (StepProg*→StepProgS* xs)
StepProg*→StepProgS* (step (just _) nothing (just _) x (step .nothing _ (just _) () xs))

StepThdS→StepThd : ∀ {ℂ i R Gs T R' Gs' T'}
  → StepThdS ℂ i (R , Gs , T) (R' , Gs' , T')
  → (X : Mem)
  → (Σ[ X' ∈ Mem ] StepThd ℂ i (just (R , Gs , X , T)) (just (R' , Gs' , X' , T'))) ⊎ StepThd ℂ i (just (R , Gs , X , T)) nothing
StepThdS→StepThd (const _ _ r c _) X = inj₁ (X , const _ _ X r c _)
StepThdS→StepThd (binOp _ _ r r1 r2 _) X = inj₁ (X , binOp _ _ X r r1 r2 _)
StepThdS→StepThd (rdReg R G r1 r2 T) X = inj₁ (X , rdReg R G X r1 r2 T)
StepThdS→StepThd {i = i} (rdGbl R G r g T) X = map
  (λ p → (X [ g ↦ doRd (X g) i ]) , rdGbl R G X r g T p)
  (λ p → rdGblBad R G X r g T p)
  (LEM (noRacingWr i (MemEvs.wr (X g))))
StepThdS→StepThd {i = i} (wrGbl R G g r T) X = map
  (λ (p , q) → (X [ g ↦ doWr (X g) i ]) , wrGbl R G X g r T p q)
  (λ p → wrGblBad R G X g r T (¬×→¬⊎¬ p))
  (LEM (noRacingRd i (MemEvs.rd (X g)) × noRacingWr i (MemEvs.wr (X g))))

StepProgS→StepProg : ∀ {ℂ Rs Gs P Rs' Gs' P'}
  → StepProgS ℂ (Rs , Gs , P) (Rs' , Gs' , P')
  → (X : Mem)
  → (Σ[ X' ∈ Mem ] StepProg ℂ (just (Rs , Gs , X , P)) (just (Rs' , Gs' , X' , P'))) ⊎ StepProg ℂ (just (Rs , Gs , X , P)) nothing
StepProgS→StepProg (schd i Rs Ts R G T R' G' T' x x₁ x₂) X = map
  (λ (X' , x₃) → X' , schd i Rs X Ts R G T R' G' X' T' x x₁ x₃)
  (λ x₃ → schdBad i Rs X Ts R G T x x₁ x₃)
  (StepThdS→StepThd x₂ X)
StepProgS→StepProg (sync I Rs G Ts q) X = inj₁ (syncMem I X , sync I Rs G X Ts q)

StepProgS*→StepProg* : ∀ {ℂ Rs Gs P Rs' Gs' P'}
  → StepProgS* ℂ (Rs , Gs , P) (Rs' , Gs' , P')
  → (X : Mem)
  → (∃[ X' ] StepProg* ℂ (just (Rs , Gs , X , P)) (just (Rs' , Gs' , X' , P'))) ⊎ StepProg* ℂ (just (Rs , Gs , X , P)) nothing
StepProgS*→StepProg* (done .(_ , _ , _)) X = inj₁ (X , done (just (_ , _ , X , _)))
StepProgS*→StepProg* {ℂ} {Rs} {Gs} {P} {Rs'} {Gs'} {P'} (step .(_ , _ , _) C2 .(_ , _ , _) x x₁) X = lem theStep
  where
  C2-with : Mem → CfgProg ℂ
  C2-with X = let (p1 , p2 , p3) = C2 in (just (p1 , p2 , X , p3))

  theStep : (Σ[ X' ∈ Mem ] StepProg ℂ (just (Rs , Gs , X , P)) (C2-with X')) ⊎ StepProg ℂ (just (Rs , Gs , X , P)) nothing
  theStep = StepProgS→StepProg x X

  theStep* : (X' : Mem) → (Σ[ X'' ∈ Mem ] StepProg* ℂ (C2-with X') (just (Rs' , Gs' , X'' , P'))) ⊎ StepProg* ℂ (C2-with X') nothing
  theStep* X' = StepProgS*→StepProg* x₁ X'

  lem : (Σ[ X' ∈ Mem ] StepProg ℂ (just (Rs , Gs , X , P)) (C2-with X')) ⊎ StepProg ℂ (just (Rs , Gs , X , P)) nothing
    → (Σ[ X'' ∈ Mem ] StepProg* ℂ (just (Rs , Gs , X , P)) (just (Rs' , Gs' , X'' , P'))) ⊎ StepProg* ℂ (just (Rs , Gs , X , P)) nothing
  lem (inj₁ (X' , p)) with (theStep* X')
  ... | inj₁ (X'' , q) = inj₁ (X'' , step (just (Rs , Gs , X , P)) (C2-with X') (just (Rs' , Gs' , X'' , P')) p q)
  ... | inj₂ q = inj₂ (step (just (Rs , Gs , X , P)) (C2-with X') nothing p q)
  lem (inj₂ p) = inj₂ (step (just (Rs , Gs , X , P)) nothing nothing p (done nothing))

isRdHelperS : ∀ {ℂ i C1 C2} → Gid → Thd ℂ → StepThdS ℂ i C1 C2 → Set
isRdHelperS g T (rdGbl R G r g' T') with gidEq g g' | (fromSum (LEM (T ≡ T')))
isRdHelperS g T (rdGbl R G r g' T') | yes _ | yes _ = ⊤
isRdHelperS g T (rdGbl R G r g' T') | no  _ | yes _ = ⊥
isRdHelperS g T (rdGbl R G r g' T') | yes _ | no  _ = ⊥
isRdHelperS g T (rdGbl R G r g' T') | no  _ | no  _ = ⊥
isRdHelperS g T (const R G r c T')     = ⊥
isRdHelperS g T (binOp R G r r1 r2 T') = ⊥
isRdHelperS g T (rdReg R G r1 r2 T')   = ⊥
isRdHelperS g T (wrGbl R G g₁ r T')    = ⊥

-- i uniquely identifies a thread, T uniquely identifies an instruction within a thread
isRdS : ∀ {ℂ C1 C2} → Gid → Tid → Thd ℂ → StepProgS ℂ C1 C2 → Set
isRdS g i T (schd j Rs Ts R G T' R' G' T'' e1 e2 thdStep) with tidEq i j
isRdS g i T (schd j Rs Ts R G T' R' G' T'' e1 e2 thdStep) | yes _ = isRdHelperS g T thdStep
isRdS g i T (schd j Rs Ts R G T' R' G' T'' e1 e2 thdStep) | no  _ = ⊥
isRdS g i T (sync I Rs G Ts q) = ⊥

isWrHelperS : ∀ {ℂ i C1 C2} → Gid → Thd ℂ → StepThdS ℂ i C1 C2 → Set
isWrHelperS g T (wrGbl R G g' r T') with gidEq g g' | (fromSum (LEM (T ≡ T')))
isWrHelperS g T (wrGbl R G g' r T') | yes _ | yes _ = ⊤
isWrHelperS g T (wrGbl R G g' r T') | no  _ | yes _ = ⊥
isWrHelperS g T (wrGbl R G g' r T') | yes _ | no  _ = ⊥
isWrHelperS g T (wrGbl R G g' r T') | no  _ | no  _ = ⊥
isWrHelperS g T (const R G r c T')     = ⊥
isWrHelperS g T (binOp R G r r1 r2 T') = ⊥
isWrHelperS g T (rdReg R G r1 r2 T')   = ⊥
isWrHelperS g T (rdGbl R G r g₁ T')    = ⊥

-- i uniquely identifies a thread, T uniquely identifies an instruction within a thread
isWrS : ∀ {ℂ C1 C2} → Gid → Tid → Thd ℂ → StepProgS ℂ C1 C2 → Set
isWrS g i T (schd j Rs Ts R G T' R' G' T'' e1 e2 thdStep) with tidEq i j
isWrS g i T (schd j Rs Ts R G T' R' G' T'' e1 e2 thdStep) | yes _ = isWrHelperS g T thdStep
isWrS g i T (schd j Rs Ts R G T' R' G' T'' e1 e2 thdStep) | no  _ = ⊥
isWrS g i T (sync I Rs G Ts q) = ⊥

isAccessS : ∀ {ℂ C1 C2} → Gid → Tid → Thd ℂ → StepProgS ℂ C1 C2 → Set
isAccessS g i T x = isRdS g i T x ⊎ isWrS g i T x

isRWPairS : ∀ {ℂ Ci1 Ci2 Cj1 Cj2} → Gid → Tid → Thd ℂ → StepProgS ℂ Ci1 Ci2 → Tid → Thd ℂ → StepProgS ℂ Cj1 Cj2 → Set
isRWPairS g i Ti xi j Tj xj = isAccessS g i Ti xi × isAccessS g j Tj xj × (isWrS g i Ti xi ⊎ isWrS g j Tj xj)

-- There are two traces starting at C, containing two access to the same address in different orders one of which is a write
hasRace : ∀ {ℂ} → CfgProgS ℂ → Set
hasRace {ℂ} C = ∃[ g ] ∃[ i ] ∃[ j ] ∃[ Ti ] ∃[ Tj ] 
    ∃[ C' ] Σ[ prefix ∈ StepProgS* ℂ C C' ]
    -- Possible order: i steps, then j
    ∃[ Ci1 ] ∃[ Cj1 ] Σ[ stepi1 ∈ StepProgS ℂ C' Ci1 ] Σ[ stepj1 ∈ StepProgS ℂ Ci1 Cj1 ]
    -- Possible order: j steps, then i
    ∃[ Cj2 ] ∃[ Ci2 ] Σ[ stepj2 ∈ StepProgS ℂ C' Cj2 ] Σ[ stepi2 ∈ StepProgS ℂ Cj2 Ci2 ]
    -- By passing i and Ti to both isRWPair calls, we ensure stepi1 and stepi2 represent execution of the same instruction
    isRWPairS g i Ti stepi1 j Tj stepj1 × isRWPairS g j Tj stepj2 i Ti stepi2

isRdHelper : ∀ {ℂ i C1 C2} → Gid → Thd ℂ → StepThd ℂ i C1 C2 → Set
isRdHelper g T (rdGbl R G _ r g' T' _) with gidEq g g' | (fromSum (LEM (T ≡ T')))
isRdHelper g T (rdGbl R G _ r g' T' _) | yes _ | yes _ = ⊤
isRdHelper g T (rdGbl R G _ r g' T' _) | no  _ | yes _ = ⊥
isRdHelper g T (rdGbl R G _ r g' T' _) | yes _ | no  _ = ⊥
isRdHelper g T (rdGbl R G _ r g' T' _) | no  _ | no  _ = ⊥
isRdHelper g T (const R G _ r c T')       = ⊥
isRdHelper g T (binOp R G _ r r1 r2 T')   = ⊥
isRdHelper g T (rdReg R G _ r1 r2 T')     = ⊥
isRdHelper g T (wrGbl R G _ g₁ r T' _ _)  = ⊥
isRdHelper g T (rdGblBad R G X r g₁ T₁ x) = ⊥
isRdHelper g T (wrGblBad R G X g₁ r T₁ x) = ⊥

-- i uniquely identifies a thread, T uniquely identifies an instruction within a thread
isRd : ∀ {ℂ C1 C2} → Gid → Tid → Thd ℂ → StepProg ℂ C1 C2 → Set
isRd g i T (schd j Rs _ Ts R G T' R' G' _ T'' e1 e2 thdStep) with tidEq i j
isRd g i T (schd j Rs _ Ts R G T' R' G' _ T'' e1 e2 thdStep) | yes _ = isRdHelper g T thdStep
isRd g i T (schd j Rs _ Ts R G T' R' G' _ T'' e1 e2 thdStep) | no  _ = ⊥
isRd g i T (sync I Rs _ G Ts q) = ⊥
isRd g i T (schdBad i₁ Rs X Ts R G T₁ x x₁ x₂) = ⊥

isWrHelper : ∀ {ℂ i C1 C2} → Gid → Thd ℂ → StepThd ℂ i C1 C2 → Set
isWrHelper g T (wrGbl R _ G g' r T' _ _) with gidEq g g' | (fromSum (LEM (T ≡ T')))
isWrHelper g T (wrGbl R _ G g' r T' _ _) | yes _ | yes _ = ⊤
isWrHelper g T (wrGbl R _ G g' r T' _ _) | no  _ | yes _ = ⊥
isWrHelper g T (wrGbl R _ G g' r T' _ _) | yes _ | no  _ = ⊥
isWrHelper g T (wrGbl R _ G g' r T' _ _) | no  _ | no  _ = ⊥
isWrHelper g T (const R _ G r c T')       = ⊥
isWrHelper g T (binOp R _ G r r1 r2 T')   = ⊥
isWrHelper g T (rdReg R _ G r1 r2 T')     = ⊥
isWrHelper g T (rdGbl R _ G r g₁ T' _)    = ⊥
isWrHelper g T (rdGblBad R G X r g₁ T₁ x) = ⊥
isWrHelper g T (wrGblBad R G X g₁ r T₁ x) = ⊥

-- i uniquely identifies a thread, T uniquely identifies an instruction within a thread
isWr : ∀ {ℂ C1 C2} → Gid → Tid → Thd ℂ → StepProg ℂ C1 C2 → Set
isWr g i T (schd j Rs _ Ts R G T' R' G' _ T'' e1 e2 thdStep) with tidEq i j
isWr g i T (schd j Rs _ Ts R G T' R' G' _ T'' e1 e2 thdStep) | yes _ = isWrHelper g T thdStep
isWr g i T (schd j Rs _ Ts R G T' R' G' _ T'' e1 e2 thdStep) | no  _ = ⊥
isWr g i T (sync I Rs _ G Ts q) = ⊥
isWr g i T (schdBad i₁ Rs X Ts R G T₁ x x₁ x₂) = ⊥

isSync : ∀ {ℂ C1 C2} → TidSet → StepProg ℂ C1 C2 → Set
isSync I (schd i Rs X Ts R G T R' G' X' T' x x₁ x₂) = ⊥
isSync I (schdBad i Rs X Ts R G T x x₁ x₂) = ⊥
isSync I (sync J Rs G X Ts q) with (fromSum (LEM (I ≡ J)))
isSync I (sync J Rs G X Ts q) | yes _ = ⊤
isSync I (sync J Rs G X Ts q) | no  _ = ⊥

isLastWr : ∀ {ℂ C1 C2} → StepProg* ℂ C1 C2 → Gid → ℕ → Set
isLastWr {ℂ} {C1} {C2} trace g n = ∀ m → n < m → ∀ C1' C2' step → getStep C1 C2 trace m ≡ just (C1' , C2' , step) → ∀ i T → ¬ isWr g i T step

isLastRd : ∀ {ℂ C1 C2} → StepProg* ℂ C1 C2 → Gid → ℕ → Set
isLastRd {ℂ} {C1} {C2} trace g n = ∀ m → n < m → ∀ C1' C2' step → getStep C1 C2 trace m ≡ just (C1' , C2' , step) → ∀ i T → ¬ isRd g i T step

lastWr-mono : ∀ {ℂ C1 C2} → StepProg* ℂ C1 C2 → Gid → ℕ → Set
lastWr-mono {ℂ} {C1} {C2} trace g n = isLastWr trace g n
  → ∀ m → n ≤ m
  → ∀ Cn1 Cn2 step-n → getStep {ℂ} C1 C2 trace n ≡ just (Cn1 , Cn2 , step-n)
  → ∀ Cm1 Cm2 step-m → getStep {ℂ} C1 C2 trace m ≡ just (Cm1 , Cm2 , step-m)
  → ∀ Xn → projMem Cn2 ≡ just Xn
  → ∀ Xm → projMem Cm2 ≡ just Xm
  → ∀ i → ≥-Wr i (Xn g .MemEvs.wr) (Xm g .MemEvs.wr)

lastRd-mono : ∀ {ℂ C1 C2} → StepProg* ℂ C1 C2 → Gid → ℕ → Set
lastRd-mono {ℂ} {C1} {C2} trace g n = isLastRd trace g n
  → ∀ m → n ≤ m
  → ∀ Cn1 Cn2 step-n → getStep {ℂ} C1 C2 trace n ≡ just (Cn1 , Cn2 , step-n)
  → ∀ Cm1 Cm2 step-m → getStep {ℂ} C1 C2 trace m ≡ just (Cm1 , Cm2 , step-m)
  → ∀ Xn → projMem Cn2 ≡ just Xn
  → ∀ Xm → projMem Cm2 ≡ just Xm
  → ∀ i → ≥-Rd i (Xn g .MemEvs.rd) (Xm g .MemEvs.rd)

errReason : ∀ {ℂ Rs Gs X P}
  → (x : StepProg* ℂ (just (Rs , Gs , X , P)) nothing)
  → ∃[ i ] ∃[ g ] Σ[ X ∈ Mem ] (¬ noRacingRd i (X g .MemEvs.rd) ⊎ ¬ noRacingWr i (X g .MemEvs.wr))
errReason (step .(just (_ , _ , _ , _)) (just x₂) .nothing x x₁) = errReason x₁
errReason (step .(just (_ , _ , _ , _)) nothing .nothing (schdBad i _ _ _ R _ T x x₂ (rdGblBad .R _ X r g T₁ x₃)) x₁) = i , g , X , inj₂ x₃
errReason (step .(just (_ , _ , _ , _)) nothing .nothing (schdBad i _ _ _ R _ T x x₂ (wrGblBad .R _ X g r T₁ x₃)) x₁) = i , g , X , x₃

truePositivesProperty : ∀ {ℂ Rs Gs P} → StepProg* ℂ (just (Rs , Gs , initMem , P)) nothing → hasRace (Rs , Gs , P)
truePositivesProperty x = {!!}

dataRaceFreedom : ∀ {ℂ Rs Gs P} → hasRace (Rs , Gs , P) → StepProg* ℂ (just (Rs , Gs , initMem , P)) nothing
dataRaceFreedom {ℂ} {Rs} {Gs} {P} (g , i , j , Ti , Tj , C' , prefix , Ci1 , Cj1 , stepi1 , stepj1 , Cj2 , Ci2 , stepj2 , stepi2 , isRW1 , isRW2) = lem (prefix' initMem)
  where
  C'-with : Mem → CfgProg ℂ
  C'-with X = let (p1 , p2 , p3) = C' in (just (p1 , p2 , X , p3))

  prefix' : (X : Mem) → (∃[ X' ] StepProg* ℂ (just (Rs , Gs , X , P)) (C'-with X')) ⊎ StepProg* ℂ (just (Rs , Gs , X , P)) nothing
  prefix' = StepProgS*→StepProg* prefix

  lem : (∃[ X' ] StepProg* ℂ (just (Rs , Gs , initMem , P)) (C'-with X')) ⊎ StepProg* ℂ (just (Rs , Gs , initMem , P)) nothing
    → StepProg* ℂ (just (Rs , Gs , initMem , P)) nothing
  lem (inj₁ (X' , theStep*)) = {!!}
  lem (inj₂ theStep*) = theStep*
