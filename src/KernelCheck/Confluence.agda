module KernelCheck.Confluence where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties
open import Data.Bool using (Bool; true; false; not)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Nullary.Decidable using (Dec; yes; no)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import KernelCheck.Prog
open import KernelCheck.Util
open import KernelCheck.DecSet

StepThd-i≡j : ∀ {ℂ i C C1 C2}
  → StepThd ℂ i C C1
  → StepThd ℂ i C C2
  → C1 ≡ C2
StepThd-i≡j (const R G X r c T) (const .R .G .X .r .c .T) = refl
StepThd-i≡j (binOp R G X r r1 r2 T) (binOp .R .G .X .r .r1 .r2 .T) = refl
StepThd-i≡j (rdReg R G X r1 r2 T) (rdReg .R .G .X .r1 .r2 .T) = refl
StepThd-i≡j (rdGbl R G X r g T x) (rdGbl .R .G .X .r .g .T x₁) = refl
StepThd-i≡j (rdGbl R G X r g T x) (rdGblBad .R .G .X .r .g .T x₁) = ⊥-elim (x₁ x)
StepThd-i≡j (rdGblBad R G X r g T x) (rdGbl .R .G .X .r .g .T x₁) = ⊥-elim (x x₁)
StepThd-i≡j (rdGblBad R G X r g T x) (rdGblBad .R .G .X .r .g .T x₁) = refl
StepThd-i≡j (wrGbl R G X g r T x x₁) (wrGbl .R .G .X .g .r .T x₂ x₃) = refl
StepThd-i≡j (wrGbl R G X g r T x x₁) (wrGblBad .R .G .X .g .r .T x₂) = case x₂ (λ y → ⊥-elim (y x)) (λ y → ⊥-elim (y x₁))
StepThd-i≡j (wrGblBad R G X g r T x) (wrGbl .R .G .X .g .r .T x₁ x₂) = case x (λ y → ⊥-elim (y x₁)) (λ y → ⊥-elim (y x₂))
StepThd-i≡j (wrGblBad R G X g r T x) (wrGblBad .R .G .X .g .r .T x₁) = refl

StepThd-i≢j : ∀ {i j} ℂ Rs Gs Ts X1 X2 R1 R2 G1 G2 T1 T2
  → i ≢ j
  → ∃[ C' ] StepProgRefl ℂ (just ((Rs [ i ↦ R1 ]) , (Gs [ i ↦ G1 ]) , X1 , (Ts [ i ↦ T1 ]))) C' ×
            StepProgRefl ℂ (just ((Rs [ j ↦ R2 ]) , (Gs [ j ↦ G2 ]) , X2 , (Ts [ j ↦ T2 ]))) C'
StepThd-i≢j {i} {j} ℂ Rs Gs Ts X1 X2 R1 R2 G1 G2 return return i≢j = just ((Rs [ i ↦ R1 ]) , (Gs [ i ↦ G1 ]) , X1 , (Ts [ i ↦ return ])) , refl _ , {!!}
StepThd-i≢j {i} {j} ℂ Rs Gs Ts X1 X2 R1 R2 G1 G2 return (x ⨟ T2) i≢j = {!!}
StepThd-i≢j {i} {j} ℂ Rs Gs Ts X1 X2 R1 R2 G1 G2 (x ⨟ T1) return i≢j = {!!}
StepThd-i≢j {i} {j} ℂ Rs Gs Ts X1 X2 R1 R2 G1 G2 (x ⨟ T1) (x₁ ⨟ T2) i≢j = {!!}

diamond : ∀ {ℂ C C1 C2}
  → StepProgRefl ℂ C C1
  → StepProgRefl ℂ C C2
  → ∃[ C' ] StepProgRefl ℂ C1 C' × StepProgRefl ℂ C2 C'
diamond {ℂ} {C} {C1} {C2} (refl .C) (refl .C) = C , refl C , refl C
diamond {ℂ} {C} {C1} {C2} (refl .(just (Rs , Gs , X , Ts))) (schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃) = C2 , schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃ , refl _
diamond {ℂ} {C} {C1} {C2} (refl .(just (Rs , Gs , X , Ts))) (schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃) = C2 ,  schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃ , refl _
diamond {ℂ} {C} {C1} {C2} (refl .(just (Rs , Gs , X , Ts))) (sync I Rs Gs X Ts p) = C2 , sync I Rs Gs X Ts p , refl _
diamond {ℂ} {C} {C1} {C2} (schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃) (refl .(just (Rs , Gs , X , Ts))) = C1 , refl _ , schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃
diamond {ℂ} {C} {C1} {C2} (schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃) (refl .(just (Rs , Gs , X , Ts))) = C1 , refl _ , schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃
diamond {ℂ} {C} {C1} {C2} (sync I Rs Gs X Ts p) (refl .(just (Rs , Gs , X , Ts))) = C1 , refl _ , sync I Rs Gs X Ts p
diamond {ℂ} {C} {C1} {C2} (schd i Rs Gs X Ts R G (x₈ ⨟ T) R' G' X' return x x₁ x₂ x₃) (schd i₁ .Rs .Gs .X .Ts R₁ G₁ (x₉ ⨟ T₁) R'' G'' X'' return x₄ x₅ x₆ x₇) = {!!}
diamond {ℂ} {C} {C1} {C2} (schd i Rs Gs X Ts R G (x₈ ⨟ T) R' G' X' return x x₁ x₂ x₃) (schd i₁ .Rs .Gs .X .Ts R₁ G₁ (x₉ ⨟ T₁) R'' G'' X'' (x₁₀ ⨟ T'') x₄ x₅ x₆ x₇) = {!!}
diamond {ℂ} {C} {C1} {C2} (schd i Rs Gs X Ts R G (x₈ ⨟ T) R' G' X' (x₉ ⨟ T') x x₁ x₂ x₃) (schd i₁ .Rs .Gs .X .Ts R₁ G₁ (x₁₀ ⨟ T₁) R'' G'' X'' return x₄ x₅ x₆ x₇) = {!!}
diamond {ℂ} {C} {C1} {C2} (schd i Rs Gs X Ts R G (x₈ ⨟ T) R' G' X' (x₉ ⨟ T') x x₁ x₂ x₃) (schd i₁ .Rs .Gs .X .Ts R₁ G₁ (x₁₀ ⨟ T₁) R'' G'' X'' (x₁₁ ⨟ T'') x₄ x₅ x₆ x₇) = {!!}
-- diamond {ℂ} {C} {C1} {C2} (schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃) (schd i₁ .Rs .Gs .X .Ts R₁ G₁ T₁ R'' G'' X'' T'' x₄ x₅ x₆ x₇) with tidEq i i₁
-- ... | yes refl = C1 , refl _ , rhs
--   where
--   R≡ : R ≡ R₁
--   R≡ = trans (sym x) x₄

--   G≡ : G ≡ G₁
--   G≡ = trans (sym x₁) x₅

--   T≡ : T ≡ T₁
--   T≡ = trans (sym x₂) x₆

--   eq : just (R' , G' , X' , T') ≡ just (R'' , G'' , X'' , T'') → C2 ≡ C1
--   eq refl = refl

--   eq' : C2 ≡ C1
--   eq' with R≡ | G≡ | T≡
--   ... | refl | refl | refl = eq (StepThd-i≡j x₃ x₇)

--   rhs : StepProgRefl ℂ C2 C1
--   rhs = cast (cong (λ a → StepProgRefl ℂ C2 a) eq') (refl _)
-- ... | no i≢i₁ = lem _ _ i≢i₁
--   where
--   lem : ∀ T' T''
--     → i ≢ i₁
--     → ∃[ C' ] StepProgRefl ℂ (just ((Rs [ i  ↦ R'  ]) , (Gs [ i  ↦ G'  ]) , X'  , (Ts [ i  ↦ T'  ]))) C' ×
--               StepProgRefl ℂ (just ((Rs [ i₁ ↦ R'' ]) , (Gs [ i₁ ↦ G'' ]) , X'' , (Ts [ i₁ ↦ T'' ]))) C'
--   lem return return = {!!}
--   lem return (x ⨟ TT) = {!!}
--   lem (x ⨟ TT) return = {!!}
--   lem (x ⨟ TT1) (x₁ ⨟ TT2) = {!!}
diamond {ℂ} {C} {C1} {C2} (schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃) (schdBad i₁ .Rs .Gs .X .Ts R₁ G₁ T₁ x₄ x₅ x₆ x₇) = {!!}
diamond {ℂ} {C} {C1} {C2} (schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃) (sync I .Rs .Gs .X .Ts p) = {!!}
diamond {ℂ} {C} {C1} {C2} (schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃) (schd i₁ .Rs .Gs .X .Ts R₁ G₁ T₁ R' G' X' T' x₄ x₅ x₆ x₇) = {!!}
diamond {ℂ} {C} {C1} {C2} (schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃) (schdBad i₁ .Rs .Gs .X .Ts R₁ G₁ T₁ x₄ x₅ x₆ x₇) = {!!}
diamond {ℂ} {C} {C1} {C2} (schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃) (sync I .Rs .Gs .X .Ts p) = {!!}
diamond {ℂ} {C} {C1} {C2} (sync I Rs Gs X Ts p) (schd i .Rs .Gs .X .Ts R G T R' G' X' T' x x₁ x₂ x₃) = {!!}
diamond {ℂ} {C} {C1} {C2} (sync I Rs Gs X Ts p) (schdBad i .Rs .Gs .X .Ts R G T x x₁ x₂ x₃) = {!!}
diamond {ℂ} {C} {C1} {C2} (sync I Rs Gs X Ts p) (sync I₁ .Rs .Gs .X .Ts p₁) = {!!}

-- StepThd-i≢j : ∀ {ℂ i j Ei Ti Ei1 Ti1 Ei2 Ti2 Ej Tj Ej1 Tj1 Ej2 Tj2 X X'1 X''1 X'2 X''2}
--   → i ≢ j
--   → StepThd ℂ i Ei X Ti Ei1 X'1 Ti1
--   → StepThd ℂ j Ej X'1 Tj Ej1 X''1 Tj1
--   → StepThd ℂ j Ej X Tj Ej2 X'2 Tj2
--   → StepThd ℂ i Ei X'2 Ti Ei2 X''2 Ti2
--   → Ei1 ≡ Ei2 × Ti1 ≡ Ti2 × Ej1 ≡ Ej2 × Tj1 ≡ Tj2 × X''1 ≡ X''2
-- StepThd-i≢j _ (const _ _ _ _ _) (const _ _ _ _ _) (const _ _ _ _ _) (const _ _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (const _ _ _ _ _) (binOp _ _ _ _ _ _) (binOp _ _ _ _ _ _) (const _ _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (const _ _ _ _ _) (rdReg _ _ _ _ _) (rdReg _ _ _ _ _) (const _ _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (const _ _ _ _ _) (rdGbl _ _ _ _ _ _) (rdGbl _ _ _ _ _ _) (const _ _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (const _ _ _ _ _) (wrGbl _ _ _ _ _ _ _) (wrGbl _ _ _ _ _ _ _) (const _ _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (binOp _ _ _ _ _ _) (const _ _ _ _ _) (const _ _ _ _ _) (binOp _ _ _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (binOp _ _ _ _ _ _) (binOp _ _ _ _ _ _) (binOp _ _ _ _ _ _) (binOp _ _ _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (binOp _ _ _ _ _ _) (rdReg _ _ _ _ _) (rdReg _ _ _ _ _) (binOp _ _ _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (binOp _ _ _ _ _ _) (rdGbl _ _ _ _ _ _) (rdGbl _ _ _ _ _ _) (binOp _ _ _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (binOp _ _ _ _ _ _) (wrGbl _ _ _ _ _ _ _) (wrGbl _ _ _ _ _ _ _) (binOp _ _ _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (rdReg _ _ _ _ _) (const _ _ _ _ _) (const _ _ _ _ _) (rdReg _ _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (rdReg _ _ _ _ _) (binOp _ _ _ _ _ _) (binOp _ _ _ _ _ _) (rdReg _ _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (rdReg _ _ _ _ _) (rdReg _ _ _ _ _) (rdReg _ _ _ _ _) (rdReg _ _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (rdReg _ _ _ _ _) (rdGbl _ _ _ _ _ _) (rdGbl _ _ _ _ _ _) (rdReg _ _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (rdReg _ _ _ _ _) (wrGbl _ _ _ _ _ _ _) (wrGbl _ _ _ _ _ _ _) (rdReg _ _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (rdGbl _ _ _ _ _ _) (const _ _ _ _ _) (const _ _ _ _ _) (rdGbl _ _ _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (rdGbl _ _ _ _ _ _) (binOp _ _ _ _ _ _) (binOp _ _ _ _ _ _) (rdGbl _ _ _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (rdGbl _ _ _ _ _ _) (rdReg _ _ _ _ _) (rdReg _ _ _ _ _) (rdGbl _ _ _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j {i = i} {j = j} {X = X} i≢j (rdGbl _ _ _ g1 _ _) (rdGbl _ _ _ g2 _ _) (rdGbl _ _ _ .g2 _ _) (rdGbl _ _ _ .g1 _ _) = refl , refl , refl , refl , funext (λ g → lem g (gidEq g g1) (gidEq g g2))
--   where
--   lem-yy-rd : ∀ g → MemEvs.rd (doRd (doRd (X g) i) j) ≡ MemEvs.rd (doRd (doRd (X g) j) i)
--   lem-yy-rd g = updFun-comm tidEq (MemEvs.rd (X g)) i≢j _ _

--   lem : ∀ g
--     → Dec (g ≡ g1)
--     → Dec (g ≡ g2)
--     → updFun gidEq (updFun gidEq X g1 (doRd (X g1) i)) g2 (doRd (updFun gidEq X g1 (doRd (X g1) i) g2) j) g ≡
--       updFun gidEq (updFun gidEq X g2 (doRd (X g2) j)) g1 (doRd (updFun gidEq X g2 (doRd (X g2) j) g1) i) g
--   lem g (yes refl) (yes refl) = begin
--       updFun gidEq (updFun gidEq X g (doRd (X g) i)) g (doRd (updFun gidEq X g (doRd (X g) i) g) j) g
--     ≡⟨ updFun-simp-≡ gidEq (updFun gidEq X g (doRd (X g) i)) g _ ⟩
--       doRd (updFun gidEq X g (doRd (X g) i) g) j
--     ≡⟨ cong (λ a → doRd a j) (updFun-simp-≡ gidEq X g _) ⟩
--       doRd (doRd (X g) i) j
--     ≡⟨ MemEvs-≡ (lem-yy-rd g) refl ⟩
--       doRd (doRd (X g) j) i
--     ≡⟨ sym (cong (λ a → doRd a i) (updFun-simp-≡ gidEq X g _)) ⟩
--       doRd (updFun gidEq X g (doRd (X g) j) g) i
--     ≡⟨ sym (updFun-simp-≡ gidEq (updFun gidEq X g (doRd (X g) j)) g _) ⟩
--       updFun gidEq (updFun gidEq X g (doRd (X g) j)) g (doRd (updFun gidEq X g (doRd (X g) j) g) i) g
--     ∎
--   lem g (yes refl) (no g≢g2) = begin
--       updFun gidEq (updFun gidEq X g (doRd (X g) i)) g2 (doRd (updFun gidEq X g (doRd (X g) i) g2) j) g
--     ≡⟨ updFun-simp-≢ gidEq (updFun gidEq X g (doRd (X g) i)) g2 g _ (≢-sym g≢g2) ⟩
--       (updFun gidEq X g (doRd (X g) i)) g
--     ≡⟨ updFun-simp-≡ gidEq X g _ ⟩
--       doRd (X g) i
--     ≡⟨ cong (λ a → doRd a i) (sym (updFun-simp-≢ gidEq X g2 g _ (≢-sym g≢g2))) ⟩
--       doRd (updFun gidEq X g2 (doRd (X g2) j) g) i
--     ≡⟨ sym (updFun-simp-≡ gidEq (updFun gidEq X g2 (doRd (X g2) j)) g _) ⟩
--       updFun gidEq (updFun gidEq X g2 (doRd (X g2) j)) g (doRd (updFun gidEq X g2 (doRd (X g2) j) g) i) g
--     ∎
--   lem g (no g≢g1) (yes refl) = begin
--       updFun gidEq (updFun gidEq X g1 (doRd (X g1) i)) g (doRd (updFun gidEq X g1 (doRd (X g1) i) g) j) g
--     ≡⟨ updFun-simp-≡ gidEq (updFun gidEq X g1 (doRd (X g1) i)) g _ ⟩
--       doRd (updFun gidEq X g1 (doRd (X g1) i) g) j
--     ≡⟨ cong (λ a → doRd a j) (updFun-simp-≢ gidEq X g1 g _ (≢-sym g≢g1)) ⟩
--       doRd (X g) j
--     ≡⟨ sym (updFun-simp-≡ gidEq X g _) ⟩
--       (updFun gidEq X g (doRd (X g) j)) g
--     ≡⟨ sym (updFun-simp-≢ gidEq (updFun gidEq X g (doRd (X g) j)) g1 g _ (≢-sym g≢g1)) ⟩
--       updFun gidEq (updFun gidEq X g (doRd (X g) j)) g1 (doRd (updFun gidEq X g (doRd (X g) j) g1) i) g
--     ∎
--   lem g (no g≢g1) (no g≢g2) = begin
--       updFun gidEq (updFun gidEq X g1 (doRd (X g1) i)) g2 (doRd (updFun gidEq X g1 (doRd (X g1) i) g2) j) g
--     ≡⟨ updFun-simp-≢ gidEq (updFun gidEq X g1 (doRd (X g1) i)) g2 g _ (≢-sym g≢g2) ⟩
--       updFun gidEq X g1 (doRd (X g1) i) g
--     ≡⟨ updFun-simp-≢ gidEq X g1 g _ (≢-sym g≢g1) ⟩
--       X g
--     ≡⟨ sym (updFun-simp-≢ gidEq X g2 g _ (≢-sym g≢g2)) ⟩
--       updFun gidEq X g2 (doRd (X g2) j) g
--     ≡⟨ sym (updFun-simp-≢ gidEq (updFun gidEq X g2 (doRd (X g2) j)) g1 g _ (≢-sym g≢g1)) ⟩
--       updFun gidEq (updFun gidEq X g2 (doRd (X g2) j)) g1 (doRd (updFun gidEq X g2 (doRd (X g2) j) g1) i) g
--     ∎
-- StepThd-i≢j {i = i} {j = j} {X = X} i≢j (rdGbl _ _ _ g1 _ _) (wrGbl _ _ g2 _ _ _ _) (wrGbl _ _ .g2 _ _ _ _) (rdGbl _ _ _ .g1 _ _) = refl , refl , refl , refl , funext (λ g → lem g (gidEq g g1) (gidEq g g2))
--   where
--   lem : ∀ g
--     → Dec (g ≡ g1)
--     → Dec (g ≡ g2)
--     → updFun gidEq (updFun gidEq X g1 (doRd (X g1) i)) g2 (doWr (updFun gidEq X g1 (doRd (X g1) i) g2) j) g ≡
--       updFun gidEq (updFun gidEq X g2 (doWr (X g2) j)) g1 (doRd (updFun gidEq X g2 (doWr (X g2) j) g1) i) g
--   lem g (yes refl) (yes refl) = begin
--       updFun gidEq (updFun gidEq X g (doRd (X g) i)) g (doWr (updFun gidEq X g (doRd (X g) i) g) j) g
--     ≡⟨ updFun-simp-≡ gidEq (updFun gidEq X g (doRd (X g) i)) g _ ⟩
--       doWr (updFun gidEq X g (doRd (X g) i) g) j
--     ≡⟨ cong (λ a → doWr a j) (updFun-simp-≡ gidEq X g _) ⟩
--       doWr (doRd (X g) i) j
--     ≡⟨ MemEvs-≡ refl refl ⟩
--       doRd (doWr (X g) j) i
--     ≡⟨ sym (cong (λ a → doRd a i) (updFun-simp-≡ gidEq X g _)) ⟩
--       doRd (updFun gidEq X g (doWr (X g) j) g) i
--     ≡⟨ sym (updFun-simp-≡ gidEq (updFun gidEq X g (doWr (X g) j)) g _) ⟩
--       updFun gidEq (updFun gidEq X g (doWr (X g) j)) g (doRd (updFun gidEq X g (doWr (X g) j) g) i) g
--     ∎
--   lem g (no g≢g1) (yes refl) = begin
--       updFun gidEq (updFun gidEq X g1 (doRd (X g1) i)) g (doWr (updFun gidEq X g1 (doRd (X g1) i) g) j) g
--     ≡⟨ updFun-simp-≡ gidEq (updFun gidEq X g1 (doRd (X g1) i)) g _ ⟩
--       doWr (updFun gidEq X g1 (doRd (X g1) i) g) j
--     ≡⟨ cong (λ a → doWr a j) (updFun-simp-≢ gidEq X g1 g _ (≢-sym g≢g1)) ⟩
--       doWr (X g) j
--     ≡⟨ sym (updFun-simp-≡ gidEq X g _) ⟩
--       (updFun gidEq X g (doWr (X g) j)) g
--     ≡⟨ sym (updFun-simp-≢ gidEq (updFun gidEq X g (doWr (X g) j)) g1 g _ (≢-sym g≢g1)) ⟩
--       updFun gidEq (updFun gidEq X g (doWr (X g) j)) g1 (doRd (updFun gidEq X g (doWr (X g) j) g1) i) g
--     ∎
--   lem g (yes refl) (no g≢g2) = begin
--       updFun gidEq (updFun gidEq X g (doRd (X g) i)) g2 (doWr (updFun gidEq X g (doRd (X g) i) g2) j) g
--     ≡⟨ updFun-simp-≢ gidEq (updFun gidEq X g (doRd (X g) i)) g2 g _ (≢-sym g≢g2) ⟩
--       (updFun gidEq X g (doRd (X g) i)) g
--     ≡⟨ updFun-simp-≡ gidEq X g _ ⟩
--       doRd (X g) i
--     ≡⟨ cong (λ a → doRd a i) (sym (updFun-simp-≢ gidEq X g2 g _ (≢-sym g≢g2))) ⟩
--       doRd (updFun gidEq X g2 (doWr (X g2) j) g) i
--     ≡⟨ sym (updFun-simp-≡ gidEq (updFun gidEq X g2 (doWr (X g2) j)) g _) ⟩
--       updFun gidEq (updFun gidEq X g2 (doWr (X g2) j)) g (doRd (updFun gidEq X g2 (doWr (X g2) j) g) i) g
--     ∎
--   lem g (no g≢g1) (no g≢g2) = begin
--       updFun gidEq (updFun gidEq X g1 (doRd (X g1) i)) g2 (doWr (updFun gidEq X g1 (doRd (X g1) i) g2) j) g
--     ≡⟨ updFun-simp-≢ gidEq (updFun gidEq X g1 (doRd (X g1) i)) g2 g _ (≢-sym g≢g2) ⟩
--       updFun gidEq X g1 (doRd (X g1) i) g
--     ≡⟨ updFun-simp-≢ gidEq X g1 g _ (≢-sym g≢g1) ⟩
--       X g
--     ≡⟨ sym (updFun-simp-≢ gidEq X g2 g _ (≢-sym g≢g2)) ⟩
--       updFun gidEq X g2 (doWr (X g2) j) g
--     ≡⟨ sym (updFun-simp-≢ gidEq (updFun gidEq X g2 (doWr (X g2) j)) g1 g _ (≢-sym g≢g1)) ⟩
--       updFun gidEq (updFun gidEq X g2 (doWr (X g2) j)) g1 (doRd (updFun gidEq X g2 (doWr (X g2) j) g1) i) g
--     ∎
-- StepThd-i≢j _ (wrGbl _ _ g1 _ _ _ _) (const _ _ _ _ _) (const _ _ _ _ _) (wrGbl _ _ .g1 _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (wrGbl _ _ g1 _ _ _ _) (binOp _ _ _ _ _ _) (binOp _ _ _ _ _ _) (wrGbl _ _ .g1 _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j _ (wrGbl _ _ g1 _ _ _ _) (rdReg _ _ _ _ _) (rdReg _ _ _ _ _) (wrGbl _ _ .g1 _ _ _ _) = refl , refl , refl , refl , refl
-- StepThd-i≢j {i = i} {j = j} {X = X} i≢j (wrGbl _ _ g1 _ _ _ _) (rdGbl _ _ _ g2 _ _) (rdGbl _ _ _ .g2 _ _) (wrGbl _ _ .g1 _ _ _ _) = refl , refl , refl , refl , funext (λ g → lem g (gidEq g g1) (gidEq g g2))
--   where
--   lem : ∀ g
--     → Dec (g ≡ g1)
--     → Dec (g ≡ g2)
--     → updFun gidEq (updFun gidEq X g1 (doWr (X g1) i)) g2 (doRd (updFun gidEq X g1 (doWr (X g1) i) g2) j) g ≡
--       updFun gidEq (updFun gidEq X g2 (doRd (X g2) j)) g1 (doWr (updFun gidEq X g2 (doRd (X g2) j) g1) i) g
--   lem g (yes refl) (yes refl) = begin
--       updFun gidEq (updFun gidEq X g (doWr (X g) i)) g (doRd (updFun gidEq X g (doWr (X g) i) g) j) g
--     ≡⟨ updFun-simp-≡ gidEq (updFun gidEq X g (doWr (X g) i)) g _ ⟩
--       doRd (updFun gidEq X g (doWr (X g) i) g) j
--     ≡⟨ cong (λ a → doRd a j) (updFun-simp-≡ gidEq X g _) ⟩
--       doRd (doWr (X g) i) j
--     ≡⟨ MemEvs-≡ refl refl ⟩
--       doWr (doRd (X g) j) i
--     ≡⟨ sym (cong (λ a → doWr a i) (updFun-simp-≡ gidEq X g _)) ⟩
--       doWr (updFun gidEq X g (doRd (X g) j) g) i
--     ≡⟨ sym (updFun-simp-≡ gidEq (updFun gidEq X g (doRd (X g) j)) g _) ⟩
--       updFun gidEq (updFun gidEq X g (doRd (X g) j)) g (doWr (updFun gidEq X g (doRd (X g) j) g) i) g
--     ∎
--   lem g (no g≢g1) (yes refl) = begin
--       updFun gidEq (updFun gidEq X g1 (doWr (X g1) i)) g (doRd (updFun gidEq X g1 (doWr (X g1) i) g) j) g
--     ≡⟨ updFun-simp-≡ gidEq (updFun gidEq X g1 (doWr (X g1) i)) g _ ⟩
--       doRd (updFun gidEq X g1 (doWr (X g1) i) g) j
--     ≡⟨ cong (λ a → doRd a j) (updFun-simp-≢ gidEq X g1 g _ (≢-sym g≢g1)) ⟩
--       doRd (X g) j
--     ≡⟨ sym (updFun-simp-≡ gidEq X g _) ⟩
--       (updFun gidEq X g (doRd (X g) j)) g
--     ≡⟨ sym (updFun-simp-≢ gidEq (updFun gidEq X g (doRd (X g) j)) g1 g _ (≢-sym g≢g1)) ⟩
--       updFun gidEq (updFun gidEq X g (doRd (X g) j)) g1 (doWr (updFun gidEq X g (doRd (X g) j) g1) i) g
--     ∎
--   lem g (yes refl) (no g≢g2) = begin
--       updFun gidEq (updFun gidEq X g (doWr (X g) i)) g2 (doRd (updFun gidEq X g (doWr (X g) i) g2) j) g
--     ≡⟨ updFun-simp-≢ gidEq (updFun gidEq X g (doWr (X g) i)) g2 g _ (≢-sym g≢g2) ⟩
--       (updFun gidEq X g (doWr (X g) i)) g
--     ≡⟨ updFun-simp-≡ gidEq X g _ ⟩
--       doWr (X g) i
--     ≡⟨ cong (λ a → doWr a i) (sym (updFun-simp-≢ gidEq X g2 g _ (≢-sym g≢g2))) ⟩
--       doWr (updFun gidEq X g2 (doRd (X g2) j) g) i
--     ≡⟨ sym (updFun-simp-≡ gidEq (updFun gidEq X g2 (doRd (X g2) j)) g _) ⟩
--       updFun gidEq (updFun gidEq X g2 (doRd (X g2) j)) g (doWr (updFun gidEq X g2 (doRd (X g2) j) g) i) g
--     ∎
--   lem g (no g≢g1) (no g≢g2) = begin
--       updFun gidEq (updFun gidEq X g1 (doWr (X g1) i)) g2 (doRd (updFun gidEq X g1 (doWr (X g1) i) g2) j) g
--     ≡⟨ updFun-simp-≢ gidEq (updFun gidEq X g1 (doWr (X g1) i)) g2 g _ (≢-sym g≢g2) ⟩
--       updFun gidEq X g1 (doWr (X g1) i) g
--     ≡⟨ updFun-simp-≢ gidEq X g1 g _ (≢-sym g≢g1) ⟩
--       X g
--     ≡⟨ sym (updFun-simp-≢ gidEq X g2 g _ (≢-sym g≢g2)) ⟩
--       updFun gidEq X g2 (doRd (X g2) j) g
--     ≡⟨ sym (updFun-simp-≢ gidEq (updFun gidEq X g2 (doRd (X g2) j)) g1 g _ (≢-sym g≢g1)) ⟩
--       updFun gidEq (updFun gidEq X g2 (doRd (X g2) j)) g1 (doWr (updFun gidEq X g2 (doRd (X g2) j) g1) i) g
--     ∎
-- StepThd-i≢j {i = i} {j = j} {X = X} i≢j (wrGbl _ _ g1 _ _ _ _) (wrGbl _ _ g2 _ _ _ no-race-ij) (wrGbl _ _ .g2 _ _ _ _) (wrGbl _ _ .g1 _ _ _ _) = refl , refl , refl , refl , funext (λ g → lem g (gidEq g g1) (gidEq g g2))
--   where
--   simp-wr : ∀ g → MemEvs.wr (updFun gidEq X g (doWr (X g) i) g) ≡ (i , ! i)
--   simp-wr g = begin
--       MemEvs.wr (updFun gidEq X g (doWr (X g) i) g)
--     ≡⟨ cong MemEvs.wr (updFun-simp-≡ gidEq X g _) ⟩
--       i , ! i
--     ∎

--   i≡j : ∀ g → noRacingWr j (MemEvs.wr (updFun gidEq X g (doWr (X g) i) g)) → i ≡ j
--   i≡j g p = cong mkTid step2
--     where
--     step1 : not (Dec.does (Tid.val i ≟ Tid.val j)) ≡ false
--     step1 = subst (λ a → noRacingWr j a) (simp-wr g) p

--     step2 : Tid.val i ≡ Tid.val j
--     step2 = from-does-true (Tid.val i ≡ Tid.val j) (Tid.val i ≟ Tid.val j) (not-false step1)

--   lem : ∀ g
--     → Dec (g ≡ g1)
--     → Dec (g ≡ g2)
--     → updFun gidEq (updFun gidEq X g1 (doWr (X g1) i)) g2 (doWr (updFun gidEq X g1 (doWr (X g1) i) g2) j) g ≡
--       updFun gidEq (updFun gidEq X g2 (doWr (X g2) j)) g1 (doWr (updFun gidEq X g2 (doWr (X g2) j) g1) i) g
--   lem g (yes refl) (yes refl) = begin
--       updFun gidEq (updFun gidEq X g (doWr (X g) i)) g (doWr (updFun gidEq X g (doWr (X g) i) g) j) g
--     ≡⟨ updFun-simp-≡ gidEq (updFun gidEq X g (doWr (X g) i)) g _ ⟩
--       doWr (updFun gidEq X g (doWr (X g) i) g) j
--     ≡⟨ cong (λ a → doWr a j) (updFun-simp-≡ gidEq X g _) ⟩
--       doWr (doWr (X g) i) j
--     ≡⟨ MemEvs-≡ refl (cong (λ k → k , ! k) (sym (i≡j g no-race-ij))) ⟩
--       doWr (doWr (X g) j) i
--     ≡⟨ sym (cong (λ a → doWr a i) (updFun-simp-≡ gidEq X g _)) ⟩
--       doWr (updFun gidEq X g (doWr (X g) j) g) i
--     ≡⟨ sym (updFun-simp-≡ gidEq (updFun gidEq X g (doWr (X g) j)) g _) ⟩
--       updFun gidEq (updFun gidEq X g (doWr (X g) j)) g (doWr (updFun gidEq X g (doWr (X g) j) g) i) g
--     ∎
--   lem g (no g≢g1) (yes refl) = begin
--       updFun gidEq (updFun gidEq X g1 (doWr (X g1) i)) g (doWr (updFun gidEq X g1 (doWr (X g1) i) g) j) g
--     ≡⟨ updFun-simp-≡ gidEq (updFun gidEq X g1 (doWr (X g1) i)) g _ ⟩
--       doWr (updFun gidEq X g1 (doWr (X g1) i) g) j
--     ≡⟨ cong (λ a → doWr a j) (updFun-simp-≢ gidEq X g1 g _ (≢-sym g≢g1)) ⟩
--       doWr (X g) j
--     ≡⟨ sym (updFun-simp-≡ gidEq X g _) ⟩
--       (updFun gidEq X g (doWr (X g) j)) g
--     ≡⟨ sym (updFun-simp-≢ gidEq (updFun gidEq X g (doWr (X g) j)) g1 g _ (≢-sym g≢g1)) ⟩
--       updFun gidEq (updFun gidEq X g (doWr (X g) j)) g1 (doWr (updFun gidEq X g (doWr (X g) j) g1) i) g
--     ∎
--   lem g (yes refl) (no g≢g2) = begin
--       updFun gidEq (updFun gidEq X g (doWr (X g) i)) g2 (doWr (updFun gidEq X g (doWr (X g) i) g2) j) g
--     ≡⟨ updFun-simp-≢ gidEq (updFun gidEq X g (doWr (X g) i)) g2 g _ (≢-sym g≢g2) ⟩
--       (updFun gidEq X g (doWr (X g) i)) g
--     ≡⟨ updFun-simp-≡ gidEq X g _ ⟩
--       doWr (X g) i
--     ≡⟨ cong (λ a → doWr a i) (sym (updFun-simp-≢ gidEq X g2 g _ (≢-sym g≢g2))) ⟩
--       doWr (updFun gidEq X g2 (doWr (X g2) j) g) i
--     ≡⟨ sym (updFun-simp-≡ gidEq (updFun gidEq X g2 (doWr (X g2) j)) g _) ⟩
--       updFun gidEq (updFun gidEq X g2 (doWr (X g2) j)) g (doWr (updFun gidEq X g2 (doWr (X g2) j) g) i) g
--     ∎
--   lem g (no g≢g1) (no g≢g2) = begin
--       updFun gidEq (updFun gidEq X g1 (doWr (X g1) i)) g2 (doWr (updFun gidEq X g1 (doWr (X g1) i) g2) j) g
--     ≡⟨ updFun-simp-≢ gidEq (updFun gidEq X g1 (doWr (X g1) i)) g2 g _ (≢-sym g≢g2) ⟩
--       updFun gidEq X g1 (doWr (X g1) i) g
--     ≡⟨ updFun-simp-≢ gidEq X g1 g _ (≢-sym g≢g1) ⟩
--       X g
--     ≡⟨ sym (updFun-simp-≢ gidEq X g2 g _ (≢-sym g≢g2)) ⟩
--       updFun gidEq X g2 (doWr (X g2) j) g
--     ≡⟨ sym (updFun-simp-≢ gidEq (updFun gidEq X g2 (doWr (X g2) j)) g1 g _ (≢-sym g≢g1)) ⟩
--       updFun gidEq (updFun gidEq X g2 (doWr (X g2) j)) g1 (doWr (updFun gidEq X g2 (doWr (X g2) j) g1) i) g
--     ∎

-- diamond : ∀ ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2
--   → StepProgRefl ℂ ℰ X P ℰ1 X1 P1
--   → StepProgRefl ℂ ℰ X P ℰ2 X2 P2
--   → ∃[ ℰ' ] ∃[ X' ] ∃[ P' ] StepProgRefl ℂ ℰ1 X1 P1 ℰ' X' P' × StepProgRefl ℂ ℰ2 X2 P2 ℰ' X' P'
-- diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (refl _ _ _) (refl _ _ _) = ℰ , X , P , refl _ _ _ , refl _ _ _
-- diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (refl _ _ _) (schd i .ℰ .X .P E T E' X' T' ℰi≡E Pi≡T x) = _ , _ , _ , schd i ℰ X P E T E' X' T' ℰi≡E Pi≡T x , refl _ _ _
-- diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (refl _ _ _) (sync I .ℰ .X .P p) = _ , _ , _ , sync I ℰ X P p , refl _ _ _
-- diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (schd i .ℰ .X .P E T E' X' T' ℰi≡E Pi≡T x) (refl _ _ _) = _ , _ , _ , refl _ _ _ , schd i ℰ X P E T E' X' T' ℰi≡E Pi≡T x
-- diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (sync I .ℰ .X .P p) (refl _ _ _) = _ , _ , _ , refl _ _ _ , sync I ℰ X P p
-- diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (schd i .ℰ .X .P E1 T1 E1' .X1 T1' ℰi≡E1 Pi≡T1 x1)
--                                   (schd j .ℰ .X .P E2 T2 E2' .X2 T2' ℰj≡E2 Pj≡T2 x2) with Tid.val i ≟ Tid.val j
-- ... | yes refl = ℰ1 , X1 , P1 , refl _ _ _ , rhs
--   where
--   E1≡E2 : E1 ≡ E2
--   E1≡E2 = trans (sym ℰi≡E1) ℰj≡E2

--   T1≡T2 : T1 ≡ T2
--   T1≡T2 = trans (sym Pi≡T1) Pj≡T2

--   eqs : E1' ≡ E2' × X1 ≡ X2 × T1' ≡ T2'
--   eqs with E1≡E2 | T1≡T2
--   ... | refl | refl = StepThd-i≡j x1 x2

--   ℰ1≡ℰ2 : E1' ≡ E2' → ℰ1 ≡ ℰ2
--   ℰ1≡ℰ2 refl = refl

--   P1≡P2 : T1' ≡ T2' → P1 ≡ P2
--   P1≡P2 refl = refl

--   rhs : StepProgRefl ℂ ℰ2 X2 P2 ℰ1 X1 P1
--   rhs = transport (cong₃ (λ a b c → StepProgRefl ℂ a b c ℰ1 X1 P1) (ℰ1≡ℰ2 (proj₁ eqs)) (proj₁ (proj₂ eqs)) (P1≡P2 (proj₂ (proj₂ eqs)))) (refl ℰ1 X1 P1)
-- ... | no i≢j = {!!}
-- diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (schd i ℰ₁ X₁ P₁ E T E' X' T' p q x) (sync I ℰ₂ X₂ P₂ r) = {!!}
-- diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (sync I ℰ₁ X₁ P₁ r) (schd i ℰ₂ X₂ P₂ E T E' X' T' p q x) = {!!}
-- diamond ℂ ℰ X P ℰ1 X1 P1 ℰ2 X2 P2 (sync I ℰ₁ X₁ P₁ r) (sync I₁ ℰ₂ X₂ P₂ r₁) = {!!}
