open import Data.List as List
open import Data.List.Relation.Unary.Any
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Level
open import Data.Empty

variable
  ℓ₁ ℓ₂ : Level
  A : Set ℓ₁
  B : Set ℓ₂

data NonRepeatingKey {A : Set ℓ₁} {B : Set ℓ₂} : (l : List (A × B)) → Set (ℓ₁ ⊔ ℓ₂) where
  done : NonRepeatingKey []
  rest : ∀ {k v xs} → ¬ Any (k ≡_) (List.map proj₁ xs) → NonRepeatingKey xs → NonRepeatingKey ((k , v) ∷ xs)

record AssociationList (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor _//_
  field
    l : List (A × B)
    wf : NonRepeatingKey l

open AssociationList

_∈_ : (kv : A × B) (d : AssociationList A B) → Set _
_∈_ kv d = Any (kv ≡_) (l d)

_∈ₖ_ : (k : A) (d : AssociationList A B) → Set _
_∈ₖ_ k d = Any (k ≡_) (List.map proj₁ (l d))

module Decidable (_≟_ : Decidable {A = A} _≡_) where
  private
    insert-loop : (k : A) (v : B) (q : AssociationList A B) →
           ∃ (λ (q' : AssociationList A B) →
                (k , v) ∈ q' × k ∈ₖ q' × List.map proj₁ (l q) ≡ List.map proj₁ (l q'))
           ⊎ ¬ (k , v) ∈ q × ¬ k ∈ₖ q
    insert-loop k v ([] // done) = inj₂ ((λ ()) , (λ ()))
    insert-loop k v (((k' , v') ∷ xs) // rest x wf) with k ≟ k' | insert-loop k v (xs // wf)
    insert-loop k v (((k' , v') ∷ xs) // rest ¬k'∈xsₚ wf) | yes refl | inj₁ (xs' // wf' , kv∈xs' , k∈xs'ₚ , xsₚ≡xs'ₚ) =
      ⊥-elim (¬k'∈xsₚ (res xsₚ≡xs'ₚ k∈xs'ₚ)) where
        res : ∀ {f xsₚ xs'ₚ} → xsₚ ≡ xs'ₚ → Any f xs'ₚ → Any f xsₚ
        res refl a = a
    insert-loop k v (((k' , v') ∷ xs) // rest ¬k'∈xsₚ wf) | no ¬p | inj₁ (xs' // wf' , kv∈xs' , k∈xs'ₚ , xsₚ≡xs'ₚ) =
      inj₁ (((k' , v') ∷ xs') // rest (res xsₚ≡xs'ₚ ¬k'∈xsₚ) wf' , there kv∈xs' , (there k∈xs'ₚ , cong (k' ∷_) xsₚ≡xs'ₚ)) where
        res : ∀ {f xsₚ xs'ₚ} → xsₚ ≡ xs'ₚ → ¬ Any f xsₚ → ¬ Any f xs'ₚ
        res refl x = x
    insert-loop .k' v (((k' , v') ∷ xs) // rest ¬k'∈xsₚ wf) | yes refl | inj₂ y =
      inj₁ ((((k' , v) ∷ xs)) // rest ¬k'∈xsₚ wf , here refl , (here refl , refl))
    insert-loop k v (((k' , v') ∷ xs) // rest ¬k'∈xsₚ wf) | no ¬p | inj₂ (¬kv∈xs , ¬k∈xsₚ) =
      inj₂ ((λ { (here refl) → ¬p refl ; (there kv∈xs) → ¬kv∈xs kv∈xs}) , λ { (here refl) → ¬p refl ; (there k∈xsₚ) → ¬k∈xsₚ k∈xsₚ})


  insert : (k : A) (v : B) (q : AssociationList A B) → ∃ (λ (q' : AssociationList A B) → (k , v) ∈ q')
  insert k v q with insert-loop k v q
  insert k v q | inj₁ (l , kv∈l , _) = l , kv∈l
  insert k v (l // wf) | inj₂ (¬kv∈l , ¬k∈lₚ) = (((k , v) ∷ l) // (rest ¬k∈lₚ wf)) , (here refl) 
    
