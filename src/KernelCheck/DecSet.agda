module KernelCheck.DecSet where

open import Function.Base using (_∘_)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
import Data.Bool.Properties
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

∩-intro : {A : Set} (i : A) (I : DecSet A) (J : DecSet A) → i ∈ I → i ∈ J → i ∈ (I ∩ J)
∩-intro {A} i I J i∈I i∈J = subst₂ (λ a b → a ∧ b ≡ true) (sym i∈I) (sym i∈J) refl

∩-elim1 : {A : Set} (i : A) (I : DecSet A) (J : DecSet A) → i ∈ (I ∩ J) → i ∈ I
∩-elim1 {A} i I J i∈I∩J = Data.Bool.Properties.∧-conicalˡ (I i) (J i) i∈I∩J 

∩-elim2 : {A : Set} (i : A) (I : DecSet A) (J : DecSet A) → i ∈ (I ∩ J) → i ∈ J
∩-elim2 {A} i I J i∈I∩J = Data.Bool.Properties.∧-conicalʳ (I i) (J i) i∈I∩J 

_-_ : {A : Set} → DecSet A → DecSet A → DecSet A
(s1 - s2) a = s1 a ∧ not (s2 a)

setMinus-comm : {A : Set} (I J K : DecSet A) → ((I - J) - K) ≡ ((I - K) - J)
setMinus-comm {A} I J K = funext lem
  where
  lem : (x : A) → ((I - J) - K) x ≡ ((I - K) - J) x
  lem x with ∈-dec x I | ∈-dec x J | ∈-dec x K
  ... | yes p | yes q | yes r = subst₃ (λ i j k → (i ∧ not j) ∧ not k ≡ (i ∧ not k) ∧ not j) (sym p) (sym q) (sym r) refl
  ... | no  p | yes q | yes r = subst₃ (λ i j k → (i ∧ not j) ∧ not k ≡ (i ∧ not k) ∧ not j) (sym (¬∈→∉ x I p)) (sym q) (sym r) refl
  ... | yes p | no  q | yes r = subst₃ (λ i j k → (i ∧ not j) ∧ not k ≡ (i ∧ not k) ∧ not j) (sym p) (sym (¬∈→∉ x J q)) (sym r) refl
  ... | yes p | yes q | no  r = subst₃ (λ i j k → (i ∧ not j) ∧ not k ≡ (i ∧ not k) ∧ not j) (sym p) (sym q) (sym (¬∈→∉ x K r)) refl
  ... | no  p | no  q | yes r = subst₃ (λ i j k → (i ∧ not j) ∧ not k ≡ (i ∧ not k) ∧ not j) (sym (¬∈→∉ x I p)) (sym (¬∈→∉ x J q)) (sym r) refl
  ... | yes p | no  q | no  r = subst₃ (λ i j k → (i ∧ not j) ∧ not k ≡ (i ∧ not k) ∧ not j) (sym p) (sym (¬∈→∉ x J q)) (sym (¬∈→∉ x K r)) refl
  ... | no  p | yes q | no  r = subst₃ (λ i j k → (i ∧ not j) ∧ not k ≡ (i ∧ not k) ∧ not j) (sym (¬∈→∉ x I p)) (sym q) (sym (¬∈→∉ x K r)) refl
  ... | no  p | no  q | no  r = subst₃ (λ i j k → (i ∧ not j) ∧ not k ≡ (i ∧ not k) ∧ not j) (sym (¬∈→∉ x I p)) (sym (¬∈→∉ x J q)) (sym (¬∈→∉ x K r)) refl

∉-split : {A : Set} (x : A) (part whole : DecSet A) → x ∉ part → x ∉ (whole - part) → x ∉ whole
∉-split x part whole p q = sym (Data.Bool.Properties.∧-identityʳ (whole x)) ∙ sym (cong (λ y → whole x ∧ not y) p) ∙ q

∉∧∈→≢ : {A : Set} (x y : A) (s : DecSet A) → x ∉ s → y ∈ s → x ≢ y
∉∧∈→≢ x y s x∉s y∈s refl = false≢true (sym x∉s ∙ y∈s)

∉∧∈→⊥ : {A : Set} (x : A) (s : DecSet A) {Whatever : Set} → x ∉ s → x ∈ s → Whatever
∉∧∈→⊥ x s x∉s x∈s = ⊥-elim (∉∧∈→≢ x x s x∉s x∈s refl)
