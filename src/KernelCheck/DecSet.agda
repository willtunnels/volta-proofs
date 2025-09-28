module KernelCheck.DecSet where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality

DecSet : Set → Set
DecSet A = A → Bool

∅ : {A : Set} → DecSet A
∅ _ = false

mkSet : {A : Set} → DecidableEquality A → A → DecSet A
mkSet _≟_ x y = Dec.does (x ≟ y)

_∈_ : {A : Set} → (x : A) (s : DecSet A) → Set
x ∈ s = s x ≡ true

_∉_ : {A : Set} → (x : A) (s : DecSet A) → Set
x ∉ s = s x ≡ false

∈-dec : {A : Set} → (x : A) (s : DecSet A) → Dec (x ∈ s)
∈-dec x s with s x
... | true = yes refl
... | false = no λ ()

∉-dec : {A : Set} → (x : A) (s : DecSet A) → Dec (x ∉ s)
∉-dec x s with s x
... | true = no λ ()
... | false = yes refl

_∪_ : {A : Set} → DecSet A → DecSet A → DecSet A
(s1 ∪ s2) a = s1 a ∨ s2 a

_∩_ : {A : Set} → DecSet A → DecSet A → DecSet A
(s1 ∩ s2) a = s1 a ∧ s2 a

_-_ : {A : Set} → DecSet A → DecSet A → DecSet A
(s1 - s2) a = s1 a ∧ not (s2 a)
