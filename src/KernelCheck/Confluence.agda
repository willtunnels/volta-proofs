module KernelCheck.Confluence where

open import Function.Base using (_∘_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; _≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
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

StepThdRefl-diamond-i≡j : ∀ {ℂ i C C1 C2}
  → StepThdRefl ℂ i C C1
  → StepThdRefl ℂ i C C2
  → ∃[ C' ] StepThdRefl ℂ i C1 C' × StepThdRefl ℂ i C2 C'
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (refl .C) (refl .C) = C , refl C , refl C
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (refl .(just (R , G , X , (const r c ⨟ T)))) (const R G X r c T) = _ , const R G X r c T , refl _
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (refl .(just (R , G , X , (binOp r r1 r2 ⨟ T)))) (binOp R G X r r1 r2 T) = _ , binOp R G X r r1 r2 T , refl _
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (refl .(just (R , G , X , (rdReg r1 r2 ⨟ T)))) (rdReg R G X r1 r2 T) = _ , rdReg R G X r1 r2 T , refl _
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (refl .(just (R , G , X , (rdGbl r g ⨟ T)))) (rdGbl R G X r g T x) = _ , rdGbl R G X r g T x , refl _
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (refl .(just (R , G , X , (rdGbl r g ⨟ T)))) (rdGblBad R G X r g T x) = nothing , rdGblBad R G X r g T x , refl nothing
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (refl .(just (R , G , X , (wrGbl g r ⨟ T)))) (wrGbl R G X g r T x x₁) = _ , wrGbl R G X g r T x x₁ , refl _
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (refl .(just (R , G , X , (wrGbl g r ⨟ T)))) (wrGblBad R G X g r T x) = nothing , wrGblBad R G X g r T x , refl nothing
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (const R G X r c T) (refl .(just (R , G , X , (const r c ⨟ T)))) = _ , refl _ , const R G X r c T
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (const R G X r c T) (const .R .G .X .r .c .T) = just ((R [ r ↦ c ]) , G , X , T) , refl _ , refl _
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (binOp R G X r r1 r2 T) (refl .(just (R , G , X , (binOp r r1 r2 ⨟ T)))) = _ , refl _ , binOp R G X r r1 r2 T
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (binOp R G X r r1 r2 T) (binOp .R .G .X .r .r1 .r2 .T) = just ((R [ r ↦ Magma.⊕ ℂ (R r1) (R r2) ]) , G , X , T) , refl _ , refl _
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (rdReg R G X r1 r2 T) (refl .(just (R , G , X , (rdReg r1 r2 ⨟ T)))) = _ , refl _ , rdReg R G X r1 r2 T
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (rdReg R G X r1 r2 T) (rdReg .R .G .X .r1 .r2 .T) = just ((R [ r1 ↦ R r2 ]) , G , X , T) , refl _ , refl _
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (rdGbl R G X r g T x) (refl .(just (R , G , X , (rdGbl r g ⨟ T)))) = _ , refl _ , rdGbl R G X r g T x
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (rdGbl R G X r g T x) (rdGbl .R .G .X .r .g .T x₁) = just ((R [ r ↦ G g ]) , G , (X [ g ↦ doRd (X g) i ]) , T) , refl _ , refl _
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (rdGbl R G X r g T x) (rdGblBad .R .G .X .r .g .T x₁) = ⊥-elim (x₁ x)
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (rdGblBad R G X r g T x) (refl .(just (R , G , X , (rdGbl r g ⨟ T)))) = nothing , refl nothing , rdGblBad R G X r g T x
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (rdGblBad R G X r g T x) (rdGbl .R .G .X .r .g .T x₁) = ⊥-elim (x x₁)
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (rdGblBad R G X r g T x) (rdGblBad .R .G .X .r .g .T x₁) = nothing , refl nothing , refl nothing
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (wrGbl R G X g r T x x₁) (refl .(just (R , G , X , (wrGbl g r ⨟ T)))) = _ , refl _ , wrGbl R G X g r T x x₁
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (wrGbl R G X g r T x x₁) (wrGbl .R .G .X .g .r .T x₂ x₃) = just (R , (G [ g ↦ R r ]) , (X [ g ↦ doWr (X g) i ]) , T) , refl _ , refl _
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (wrGbl R G X g r T x x₁) (wrGblBad .R .G .X .g .r .T x₂) = ⊥-elim (case x₂ (λ x₃ → x₃ x) (λ x₃ → x₃ x₁))
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (wrGblBad R G X g r T x) (refl .(just (R , G , X , (wrGbl g r ⨟ T)))) = nothing , refl nothing , wrGblBad R G X g r T x
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (wrGblBad R G X g r T x) (wrGbl .R .G .X .g .r .T x₁ x₂) = ⊥-elim (case x (λ x₃ → x₃ x₁) λ x₃ → x₃ x₂)
StepThdRefl-diamond-i≡j {ℂ} {i} {C} {C1} {C2} (wrGblBad R G X g r T x) (wrGblBad .R .G .X .g .r .T x₁) = C1 , refl nothing , refl nothing

StepThdRefl-diamond-i≢j : ∀ {ℂ i j C1 C1' C2 C2'}
  → i ≢ j
  → cfgThdGetMem C1 ≡ cfgThdGetMem C2
  → StepThdRefl ℂ i C1 C1'
  → StepThdRefl ℂ j C2 C2'
  → ∃[ X' ] StepThdRefl ℂ i (cfgThdSetMem C1 (cfgThdGetMem C2')) (cfgThdSetMem C1' X') ×
            StepThdRefl ℂ j (cfgThdSetMem C2 (cfgThdGetMem C1')) (cfgThdSetMem C2' X')
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j mem≡ (refl .C1) (refl .C2) = cfgThdGetMem C2' , refl _ , subst-mem (refl _)
  where
  subst-mem = subst (λ a → StepThdRefl ℂ j (cfgThdSetMem C2 a) (cfgThdSetMem C2' (cfgThdGetMem C2'))) (sym mem≡)
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j mem≡ (refl .C1) (const R G X r c T) with C1 | mem≡
... | just C1₁ | refl = cfgThdGetMem C2' , refl _ , const R G X r c T
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j mem≡ (refl .C1) (binOp R G X r r1 r2 T) with C1 | mem≡
... | just C1₁ | refl = cfgThdGetMem C2' , refl _ , binOp R G X r r1 r2 T
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j mem≡ (refl .C1) (rdReg R G X r1 r2 T) with C1 | mem≡
... | just C1₁ | refl = cfgThdGetMem C2' , refl _ , rdReg R G X r1 r2 T
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j mem≡ (refl .C1) (rdGbl R G X r g T x) with C1 | mem≡
... | just C1₁ | refl = cfgThdGetMem C2' , refl _ , rdGbl R G X r g T x
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j mem≡ (refl .C1) (rdGblBad R G X r g T x) with C1 | mem≡
... | just C1₁ | refl = cfgThdGetMem C2' , refl _ , rdGblBad R G X r g T x
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j mem≡ (refl .C1) (wrGbl R G X g r T x x₁) with C1 | mem≡
... | just C1₁ | refl = cfgThdGetMem C2' , refl _ , wrGbl R G X g r T x x₁
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j mem≡ (refl .C1) (wrGblBad R G X g r T x) with C1 | mem≡
... | just C1₁ | refl = cfgThdGetMem C2' , refl _ , wrGblBad R G X g r T x
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j mem≡ (const R G X r c T) (refl .C2) with C2 | mem≡
... | just C2₁ | refl = cfgThdGetMem C1' , const R G X r c T , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j mem≡ (binOp R G X r r1 r2 T) (refl .C2) with C2 | mem≡
... | just C2₁ | refl = cfgThdGetMem C1' , binOp R G X r r1 r2 T , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j mem≡ (rdReg R G X r1 r2 T) (refl .C2) with C2 | mem≡
... | just C2₁ | refl = cfgThdGetMem C1' , rdReg R G X r1 r2 T , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j mem≡ (rdGbl R G X r g T x) (refl .C2) with C2 | mem≡
... | just C2₁ | refl = cfgThdGetMem C1' , rdGbl R G X r g T x , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j mem≡ (rdGblBad R G X r g T x) (refl .C2) with C2 | mem≡
... | just C2₁ | refl = cfgThdGetMem C1' , rdGblBad R G X r g T x , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j mem≡ (wrGbl R G X g r T x x₁) (refl .C2) with C2 | mem≡
... | just C2₁ | refl = cfgThdGetMem C1' , wrGbl R G X g r T x x₁ , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j mem≡ (wrGblBad R G X g r T x) (refl .C2) with C2 | mem≡
... | just C2₁ | refl = cfgThdGetMem C1' , wrGblBad R G X g r T x , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (const R G X r c T) (const R₁ G₁ X₁ r₁ c₁ T₁)
  = just X , const R G X r c T , const R₁ G₁ X r₁ c₁ T₁
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (const R G X r c T) (binOp R₁ G₁ X₁ r₁ r1 r2 T₁)
  = just X , const R G X r c T , binOp R₁ G₁ X r₁ r1 r2 T₁
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (const R G X r c T) (rdReg R₁ G₁ X₁ r1 r2 T₁)
  = just X , const R G X r c T , rdReg R₁ G₁ X r1 r2 T₁
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (const R G X r c T) (rdGbl R₁ G₁ X₁ r₁ g T₁ x)
  = just (X [ g ↦ doRd (X g) j ]) , const R G (X [ g ↦ doRd (X g) j ]) r c T , rdGbl R₁ G₁ X r₁ g T₁ x
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (const R G X r c T) (rdGblBad R₁ G₁ X₁ r₁ g T₁ x)
  = nothing , refl nothing , rdGblBad R₁ G₁ X r₁ g T₁ x
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (const R G X r c T) (wrGbl R₁ G₁ X₁ g r₁ T₁ x x₁)
  = just (X [ g ↦ doWr (X g) j ]) , const R G (X [ g ↦ doWr (X g) j ]) r c T , wrGbl R₁ G₁ X g r₁ T₁ x x₁
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (const R G X r c T) (wrGblBad R₁ G₁ X₁ g r₁ T₁ x)
  = nothing , refl nothing , wrGblBad R₁ G₁ X g r₁ T₁ x
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (binOp R G X r r1 r2 T) (const R₁ G₁ X₁ r₁ c T₁)
  = just X , binOp R G X r r1 r2 T , const R₁ G₁ X r₁ c T₁
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (binOp R G X r r1 r2 T) (binOp R₁ G₁ X₁ r₁ r3 r4 T₁)
  = just X , binOp R G X r r1 r2 T , binOp R₁ G₁ X r₁ r3 r4 T₁
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (binOp R G X r r1 r2 T) (rdReg R₁ G₁ X₁ r3 r4 T₁)
  = just X , binOp R G X r r1 r2 T , rdReg R₁ G₁ X r3 r4 T₁
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (binOp R G X r r1 r2 T) (rdGbl R₁ G₁ X₁ r₁ g T₁ x)
  = just (X [ g ↦ doRd (X g) j ]) , binOp R G (X [ g ↦ doRd (X g) j ]) r r1 r2 T , rdGbl R₁ G₁ X r₁ g T₁ x
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (binOp R G X r r1 r2 T) (rdGblBad R₁ G₁ X₁ r₁ g T₁ x)
  = nothing , refl nothing , rdGblBad R₁ G₁ X r₁ g T₁ x
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (binOp R G X r r1 r2 T) (wrGbl R₁ G₁ X₁ g r₁ T₁ x x₁)
  = just (X [ g ↦ doWr (X g) j ]) , binOp R G (X [ g ↦ doWr (X g) j ]) r r1 r2 T , wrGbl R₁ G₁ X g r₁ T₁ x x₁
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (binOp R G X r r1 r2 T) (wrGblBad R₁ G₁ X₁ g r₁ T₁ x)
  = nothing , refl nothing , wrGblBad R₁ G₁ X g r₁ T₁ x
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdReg R G X r1 r2 T) (const R₁ G₁ X₁ r c T₁)
  = just X , rdReg R G X r1 r2 T , const R₁ G₁ X r c T₁
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdReg R G X r1 r2 T) (binOp R₁ G₁ X₁ r r3 r4 T₁)
  = just X , rdReg R G X r1 r2 T , binOp R₁ G₁ X r r3 r4 T₁
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdReg R G X r1 r2 T) (rdReg R₁ G₁ X₁ r3 r4 T₁)
  = just X , rdReg R G X r1 r2 T , rdReg R₁ G₁ X r3 r4 T₁
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdReg R G X r1 r2 T) (rdGbl R₁ G₁ X₁ r g T₁ x)
  = just (X [ g ↦ doRd (X g) j ]) , rdReg R G (X [ g ↦ doRd (X g) j ]) r1 r2 T , rdGbl R₁ G₁ X r g T₁ x
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdReg R G X r1 r2 T) (rdGblBad R₁ G₁ X₁ r g T₁ x)
  = nothing , refl nothing , rdGblBad R₁ G₁ X r g T₁ x
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdReg R G X r1 r2 T) (wrGbl R₁ G₁ X₁ g r T₁ x x₁)
  = just (X [ g ↦ doWr (X g) j ]) , rdReg R G (X [ g ↦ doWr (X g) j ]) r1 r2 T , wrGbl R₁ G₁ X g r T₁ x x₁
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdReg R G X r1 r2 T) (wrGblBad R₁ G₁ X₁ g r T₁ x)
  = nothing , refl nothing , wrGblBad R₁ G₁ X g r T₁ x
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdGbl R G X r g T x) (const R₁ G₁ X₁ r₁ c T₁)
  = just (X [ g ↦ doRd (X g) i ]) , rdGbl R G X r g T x , const R₁ G₁ (X [ g ↦ doRd (X g) i ]) r₁ c T₁
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdGbl R G X r g T x) (binOp R₁ G₁ X₁ r₁ r1 r2 T₁)
  = just (X [ g ↦ doRd (X g) i ]) , rdGbl R G X r g T x , binOp R₁ G₁ (X [ g ↦ doRd (X g) i ]) r₁ r1 r2 T₁
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdGbl R G X r g T x) (rdReg R₁ G₁ X₁ r1 r2 T₁)
  = just (X [ g ↦ doRd (X g) i ]) , rdGbl R G X r g T x , rdReg R₁ G₁ (X [ g ↦ doRd (X g) i ]) r1 r2 T₁
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdGbl R G X r g T x) (rdGbl R₁ G₁ X₁ r₁ g₁ T₁ x₁) = {!!}
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdGbl R G X r g T x) (rdGblBad R₁ G₁ .X r₁ g₁ T₁ x₁) = nothing , refl _ , {!!}
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdGbl R G X r g T x) (wrGbl R₁ G₁ .X g₁ r₁ T₁ x₁ x₂) = {!!}
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdGbl R G X r g T x) (wrGblBad R₁ G₁ .X g₁ r₁ T₁ x₁) = nothing , refl _ , {!!}
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdGblBad R G X r g T x) (const R₁ G₁ .X r₁ c T₁) = nothing , {!!} , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdGblBad R G X r g T x) (binOp R₁ G₁ .X r₁ r1 r2 T₁) = nothing , {!!} , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdGblBad R G X r g T x) (rdReg R₁ G₁ .X r1 r2 T₁) = nothing , {!!} , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdGblBad R G X r g T x) (rdGbl R₁ G₁ .X r₁ g₁ T₁ x₁) = nothing , {!!} , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdGblBad R G X r g T x) (rdGblBad R₁ G₁ .X r₁ g₁ T₁ x₁) = nothing , refl _ , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdGblBad R G X r g T x) (wrGbl R₁ G₁ .X g₁ r₁ T₁ x₁ x₂) = nothing , {!!} , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (rdGblBad R G X r g T x) (wrGblBad R₁ G₁ .X g₁ r₁ T₁ x₁) = nothing , refl _ , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (wrGbl R G X g r T x x₁) (const R₁ G₁ .X r₁ c T₁) = {!!}
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (wrGbl R G X g r T x x₁) (binOp R₁ G₁ .X r₁ r1 r2 T₁) = {!!}
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (wrGbl R G X g r T x x₁) (rdReg R₁ G₁ .X r1 r2 T₁) = {!!}
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (wrGbl R G X g r T x x₁) (rdGbl R₁ G₁ .X r₁ g₁ T₁ x₂) = {!!}
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (wrGbl R G X g r T x x₁) (rdGblBad R₁ G₁ .X r₁ g₁ T₁ x₂) = nothing , refl _ , {!!}
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (wrGbl R G X g r T x x₁) (wrGbl R₁ G₁ .X g₁ r₁ T₁ x₂ x₃) = {!!}
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (wrGbl R G X g r T x x₁) (wrGblBad R₁ G₁ .X g₁ r₁ T₁ x₂) = nothing , refl _ , {!!}
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (wrGblBad R G X g r T x) (const R₁ G₁ .X r₁ c T₁) = nothing , {!!} , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (wrGblBad R G X g r T x) (binOp R₁ G₁ .X r₁ r1 r2 T₁) = nothing , {!!} , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (wrGblBad R G X g r T x) (rdReg R₁ G₁ .X r1 r2 T₁) = nothing , {!!} , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (wrGblBad R G X g r T x) (rdGbl R₁ G₁ .X r₁ g₁ T₁ x₁) = nothing , {!!} , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (wrGblBad R G X g r T x) (rdGblBad R₁ G₁ .X r₁ g₁ T₁ x₁) = nothing , refl _ , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (wrGblBad R G X g r T x) (wrGbl R₁ G₁ .X g₁ r₁ T₁ x₁ x₂) = nothing , {!!} , refl _
StepThdRefl-diamond-i≢j {ℂ} {i} {j} {C1} {C1'} {C2} {C2'} i≢j refl (wrGblBad R G X g r T x) (wrGblBad R₁ G₁ .X g₁ r₁ T₁ x₁) = nothing , refl _ , refl _

diamond : ∀ {ℂ C C1 C2}
  → StepProgRefl ℂ C C1
  → StepProgRefl ℂ C C2
  → ∃[ C' ] StepProgRefl ℂ C1 C' × StepProgRefl ℂ C2 C'
diamond {ℂ} {C} {C1} {C2} (refl .C) (refl .C) = {!!}
diamond {ℂ} {C} {C1} {C2} (refl .(just (Rs , Gs , X , Ts))) (schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃) = {!!}
diamond {ℂ} {C} {C1} {C2} (refl .(just (Rs , Gs , X , Ts))) (schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃) = {!!}
diamond {ℂ} {C} {C1} {C2} (refl .(just (Rs , Gs , X , Ts))) (sync I Rs Gs X Ts p) = {!!}
diamond {ℂ} {C} {C1} {C2} (schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃) (refl .(just (Rs , Gs , X , Ts))) = {!!}
diamond {ℂ} {C} {C1} {C2} (schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃) (schd i₁ .Rs .Gs .X .Ts R₁ G₁ T₁ R'' G'' X'' T'' x₄ x₅ x₆ x₇) with tidEq i i₁
... | no i≢i₁ = C' {!!}
  where
  stepEv : ∃[ X''' ]
    StepThdRefl ℂ i (cfgThdSetMem (just (R , G , X , T)) (cfgThdGetMem (just (R'' , G'' , X'' , T'')))) (cfgThdSetMem (just (R' , G' , X' , T')) X''') ×
    StepThdRefl ℂ i₁ (cfgThdSetMem (just (R₁ , G₁ , X , T₁)) (cfgThdGetMem (just (R' , G' , X' , T')))) (cfgThdSetMem (just (R'' , G'' , X'' , T'')) X''')
  stepEv = StepThdRefl-diamond-i≢j i≢i₁ refl x₃ x₇

  X''' : Maybe Mem
  X''' = stepEv .proj₁

  C' : (∃[ X'''₁ ] X''' ≡ just X'''₁) → ∃[ C' ] StepProgRefl ℂ C1 C' × StepProgRefl ℂ C2 C'
  C' (X'''₁ , p) = just ((Rs [ i ↦ R' ] [ i₁ ↦ R'' ]) , (Gs [ i ↦ G' ] [ i₁ ↦ G'' ]) , X'''₁ , (Ts [ i ↦ T' ] [ i₁ ↦ T'' ])) , {!!} , {!!}
    where
    thing = schd i₁ (Rs [ i ↦ R' ]) (Gs [ i ↦ G' ]) X' (Ts [ i ↦ T' ]) R₁ G₁ T₁ R'' G'' X'''₁ T'' {!!} {!!} {!!} (stepEv .proj₂ .proj₁)
... | yes refl = {!!} -- C' , lhs , rhs
  where
  R≡ : R ≡ R₁
  R≡ = trans (sym x) x₄

  G≡ : G ≡ G₁
  G≡ = trans (sym x₁) x₅

  T≡ : T ≡ T₁
  T≡ = trans (sym x₂) x₆

  stepEv : ∃[ C' ] StepThdRefl ℂ i (just (R' , G' , X' , T')) C' × StepThdRefl ℂ i (just (R'' , G'' , X'' , T'')) C'
  stepEv with R≡ | G≡ | T≡
  ... | refl | refl | refl = StepThdRefl-diamond-i≡j x₃ x₇

  -- thdCfgToProgCfg : CfgThd ℂ → CfgProg ℂ
  -- thdCfgToProgCfg (just (R , G , X , T)) = just (Rs [ i ↦ R ] , Gs [ i ↦ G ] , X , Ts [ i ↦ T ])
  -- thdCfgToProgCfg nothing = nothing

  -- C' : CfgProg ℂ
  -- C' = thdCfgToProgCfg (stepEv .proj₁)

  -- lhs : StepProgRefl ℂ (just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , (Ts [ i ↦ T' ]))) C'
  -- lhs with C'
  -- ... | just (_ , _ , _ , _) = {!!}
  -- ... | nothing = {!schdBad i _ _ _ _ _ _ _ x₄ x₅ x₆ (stepEv .proj₂ .proj₁) !}
  --   where
  --   thing : StepProgRefl ℂ
  --     (just ((Rs [ i ↦ R' ]) , (Gs [ i ↦ G' ]) , X' , (Ts [ i ↦ T' ])))
  --     nothing
  --   thing = schdBad i (Rs [ i ↦ R' ]) (Gs [ i ↦ G' ]) X' (Ts [ i ↦ T' ]) R G T {!!} {!!} {!!} {!stepEv!}

  -- rhs : StepProgRefl ℂ (just ((Rs [ i ↦ R'' ]) , (Gs [ i ↦ G'' ]) , X'' , (Ts [ i ↦ T'' ]))) C'
  -- rhs = {!!}
diamond {ℂ} {C} {C1} {C2} (schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃) (schdBad i₁ .Rs .Gs .X .Ts R₁ G₁ T₁ x₄ x₅ x₆ x₇) = {!!}
diamond {ℂ} {C} {C1} {C2} (schd i Rs Gs X Ts R G T R' G' X' T' x x₁ x₂ x₃) (sync I .Rs .Gs .X .Ts p) = {!!}
diamond {ℂ} {C} {C1} {C2} (schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃) (refl .(just (Rs , Gs , X , Ts))) = {!!}
diamond {ℂ} {C} {C1} {C2} (schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃) (schd i₁ .Rs .Gs .X .Ts R₁ G₁ T₁ R' G' X' T' x₄ x₅ x₆ x₇) = {!!}
diamond {ℂ} {C} {C1} {C2} (schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃) (schdBad i₁ .Rs .Gs .X .Ts R₁ G₁ T₁ x₄ x₅ x₆ x₇) = {!!}
diamond {ℂ} {C} {C1} {C2} (schdBad i Rs Gs X Ts R G T x x₁ x₂ x₃) (sync I .Rs .Gs .X .Ts p) = {!!}
diamond {ℂ} {C} {C1} {C2} (sync I Rs Gs X Ts p) (refl .(just (Rs , Gs , X , Ts))) = {!!}
diamond {ℂ} {C} {C1} {C2} (sync I Rs Gs X Ts p) (schd i .Rs .Gs .X .Ts R G T R' G' X' T' x x₁ x₂ x₃) = {!!}
diamond {ℂ} {C} {C1} {C2} (sync I Rs Gs X Ts p) (schdBad i .Rs .Gs .X .Ts R G T x x₁ x₂ x₃) = {!!}
diamond {ℂ} {C} {C1} {C2} (sync I Rs Gs X Ts p) (sync I₁ .Rs .Gs .X .Ts p₁) = {!!}
