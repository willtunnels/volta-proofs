module KernelCheck.Util where

open import Data.Bool using (Bool; true; false; not)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.Definitions using (DecidableEquality)

open import Relation.Binary.PropositionalEquality

postulate
  funext : ∀ {a} {A B : Set a} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

record HasDecEq (A : Set) : Set where
  field
    eq : DecidableEquality A

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} (f : A → B → C → D) {x1 x2 y1 y2 z1 z2} → x1 ≡ x2 → y1 ≡ y2 → z1 ≡ z2 → f x1 y1 z1 ≡ f x2 y2 z2
cong₃ f refl refl refl = refl

cast : ∀ {a} {A B : Set a} → A ≡ B → A → B
cast refl x = x

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

case : ∀ {A B : Set} {C : A ⊎ B → Set} → (x : A ⊎ B) → ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) → C x
case {C = C} x f g = Data.Sum.[_,_] {C = C} f g x
