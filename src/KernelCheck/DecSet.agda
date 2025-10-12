module KernelCheck.DecSet where

open import Function.Base using (_∘_)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation using (¬_)
open import Data.Empty using (⊥; ⊥-elim)

open import KernelCheck.Util

DecSet : Set → Set
DecSet A = A → Bool

∅ : {A : Set} → DecSet A
∅ _ = false

all : {A : Set} → DecSet A
all _ = true

singleton : {A : Set} → DecidableEquality A → A → DecSet A
singleton _≟_ x y = Dec.does (x ≟ y)

_∈_ : {A : Set} (x : A) (s : DecSet A) → Set
x ∈ s = s x ≡ true

_∉_ : {A : Set} (x : A) (s : DecSet A) → Set
x ∉ s = s x ≡ false

∈-dec : {A : Set} (x : A) (s : DecSet A) → Dec (x ∈ s)
∈-dec x s with s x
... | true = yes refl
... | false = no λ ()

∉-dec : {A : Set} (x : A) (s : DecSet A) → Dec (x ∉ s)
∉-dec x s with s x
... | true = no λ ()
... | false = yes refl

¬∉→∈ : {A : Set} (x : A) (s : DecSet A) → ¬ (x ∉ s) → x ∈ s
¬∉→∈ x s p with s x
... | true = refl
... | false = ⊥-elim (p refl)

∈→¬∉ : {A : Set} (x : A) (s : DecSet A) → x ∈ s → ¬ (x ∉ s)
∈→¬∉ x s p with s x
... | true = λ ()
... | false = ⊥-elim (false≢true p)

¬∈→∉ : {A : Set} (x : A) (s : DecSet A) → ¬ (x ∈ s) → x ∉ s
¬∈→∉ x s p with s x
... | true = ⊥-elim (p refl)
... | false = refl

∉→¬∈ : {A : Set} (x : A) (s : DecSet A) → x ∉ s → ¬ (x ∈ s)
∉→¬∈ x s p with s x
... | true = ⊥-elim (false≢true (sym p))
... | false = ⊥-elim ∘ false≢true

∈→∈-flip : {A : Set} (x : A) (s1 s2 : DecSet A) → (x ∈ s1 → x ∈ s2) → (x ∉ s2 → x ∉ s1)
∈→∈-flip {A} x s1 s2 p q = ¬∈→∉ x s1 λ r → ∉→¬∈ x s2 q (p r)

_⊆_ : {A : Set} → DecSet A → DecSet A → Set
s1 ⊆ s2 = ∀ i → i ∈ s1 → i ∈ s2

_⊇_ : {A : Set} → DecSet A → DecSet A → Set
s1 ⊇ s2 = ∀ i → i ∈ s2 → i ∈ s1

_∪_ : {A : Set} → DecSet A → DecSet A → DecSet A
(s1 ∪ s2) a = s1 a ∨ s2 a

_∩_ : {A : Set} → DecSet A → DecSet A → DecSet A
(s1 ∩ s2) a = s1 a ∧ s2 a

_-_ : {A : Set} → DecSet A → DecSet A → DecSet A
(s1 - s2) a = s1 a ∧ not (s2 a)
