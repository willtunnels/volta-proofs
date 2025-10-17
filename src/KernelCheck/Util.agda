module KernelCheck.Util where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Data.Empty using (⊥; ⊥-elim)

open import Relation.Binary.PropositionalEquality
import Relation.Binary.HeterogeneousEquality as H

postulate
  funext : ∀ {a} {A B : Set a} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
  LEM : ∀ {a} (A : Set a) → A ⊎ ¬ A

funext' : ∀ {A : Set} {B : A → Set} {f g : ∀ a → B a} → (∀ x → f x ≡ g x) → f ≡ g
funext' {A} {B} {f} {g} h =
    H.≅-to-≡ (H.cong (λ f x → proj₂ (f x)) (H.≡-to-≅ (funext λ a → cong (a ,_) (h a))))

¬∀→∃¬ : ∀ {a} {A : Set a} {P : A → Set} → ¬ (∀ x → P x) → ∃[ x ] ¬ P x
¬∀→∃¬ {A = A} {P = P} ¬∀ with LEM (∃[ x ] ¬ P x)
... | inj₁ ∃¬ = ∃¬
... | inj₂ ¬∃¬ = ⊥-elim (¬∀ (λ x → helper x ¬∃¬))
  where
    helper : ∀ x → ¬ (∃[ x ] ¬ P x) → P x
    helper x ¬∃¬ with LEM (P x)
    ... | inj₁ px = px
    ... | inj₂ ¬px = ⊥-elim (¬∃¬ (x , ¬px))

contraposition : ∀ {A B : Set} → (A → B) → ¬ B → ¬ A
contraposition P ¬b a = ¬b (P a)

record HasDecEq (A : Set) : Set where
  field
    eq : DecidableEquality A

_∙_ = trans
infixr 30 _∙_

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} (f : A → B → C → D) {x1 x2 y1 y2 z1 z2} → x1 ≡ x2 → y1 ≡ y2 → z1 ≡ z2 → f x1 y1 z1 ≡ f x2 y2 z2
cong₃ f refl refl refl = refl

cast : ∀ {a} {A B : Set a} → A ≡ B → A → B
cast refl x = x

case : ∀ {A B : Set} {C : A ⊎ B → Set} → (x : A ⊎ B) → ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) → C x
case {C = C} x f g = Data.Sum.[_,_] {C = C} f g x

not-true : ∀ {x} → not x ≡ true → x ≡ false
not-true {false} _ = refl

not-false : ∀ {x} → not x ≡ false → x ≡ true
not-false {true} _ = refl

from-does-true : (A : Set) (x : Dec A) → Dec.does x ≡ true → A
from-does-true A (yes p) _ = p
from-does-true A (no _) ()

from-does-false : (A : Set) (x : Dec A) → Dec.does x ≡ false → ¬ A
from-does-false A (yes _) ()
from-does-false A (no ¬p) _ = ¬p

∧-intro : ∀ x y → x ≡ true × y ≡ true → x ∧ y ≡ true
∧-intro x y (refl , refl) = refl

∧-elim1 : ∀ x y → x ∧ y ≡ true → x ≡ true
∧-elim1 true true p = refl

∧-elim2 : ∀ x y → x ∧ y ≡ true → y ≡ true
∧-elim2 true true p = refl

false≢true : false ≢ true
false≢true ()

nothing≢just : ∀ {a} {A : Set a} {x : A} → nothing ≢ just x
nothing≢just ()
