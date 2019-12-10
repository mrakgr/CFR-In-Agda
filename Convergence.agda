open import Data.Product
open import Data.Empty
open import Data.Nat using (ℕ;suc;zero) renaming (_+_ to _+ⁿ_;_*_ to _*ⁿ_)
open import Data.Integer using (+_;sign;_◃_) renaming (_≤_ to _≤ⁱ_;_*_ to _*ⁱ_;∣_∣ to ∣_∣ⁱ)
open import Data.Rational
open import Data.Rational.Properties using (≤-antisym;≤-irrelevant;≤-trans;≤-refl)
open import Level using (Level)
open import Relation.Nullary
open import Relation.Binary
open import Data.Bool using (Bool;false;true)
open import Relation.Binary.PropositionalEquality
open import Data.Sign using () renaming (_*_ to _*ˢ_)
open ℚ

∣_∣ : ℚ → ℚ
∣ x ∣ with x <? 0ℚ
∣ x ∣ | no ¬p = x
∣ x ∣ | yes p = - x

Range = ∃[ lower ] ∃[ higher ] (lower ≤ higher)
_∈_ : ℚ → Range → Set
x ∈ (lower , higher , _) = lower ≤ x × x ≤ higher
_⊆_ : Range → Range → Set
(lower' , higher' , _) ⊆ (lower , higher , _) = lower ≤ lower' × higher' ≤ higher
_⊇_ : Range → Range → Set
a ⊇ b = b ⊆ a

⊇-antisym : ∀ {a b} → a ⊇ b → b ⊇ a → a ≡ b
⊇-antisym {a⁻ , a⁺ , a⁻≤a⁺} {b⁻ , b⁺ , b⁻≤b⁺} (a⁻≤b⁻ , b⁺≤a⁺) (b⁻≤a⁻ , a⁺≤b⁺) with ≤-antisym a⁻≤b⁻ b⁻≤a⁻ | ≤-antisym b⁺≤a⁺ a⁺≤b⁺
⊇-antisym {a⁻ , a⁺ , a⁻≤a⁺} {.a⁻ , .a⁺ , b⁻≤b⁺} _ _ | refl | refl with ≤-irrelevant a⁻≤a⁺ b⁻≤b⁺
⊇-antisym {a⁻ , a⁺ , a⁻≤a⁺} {.a⁻ , .a⁺ , .a⁻≤a⁺} _ _ | refl | refl | refl = refl

-- Some function f converges to g, as its precision p increases.
_~>_ : ∀ (f : ℕ → Range) → (g : ℕ → Range) → Set
f ~> g = ∀ (p : ℕ) → ∃[ p' ] (f p ⊇ g p')

~>-refl : ∀ {x} → x ~> x
~>-refl {x} p = p , ≤-refl , ≤-refl

~>-trans : ∀ {a b c} → a ~> b → b ~> c → a ~> c
~>-trans {a} {b} {c} f g p with f p
~>-trans {a} {b} {c} f g p | p' , f⁻ , f⁺ with g p'
~>-trans {a} {b} {c} f g p | p' , f⁻ , f⁺ | p'' , g⁻ , g⁺ = p'' , ≤-trans f⁻ g⁻ , ≤-trans g⁺ f⁺

const : ℚ → ℕ → Range
const x p = x , x , ≤-refl

postulate sqr-≤0 : ∀ t → 0ℚ ≤ t * t
postulate sqr-≤t : ∀ {t} → 1ℚ ≤ t → t ≤ t * t

postulate 1≤l≤m→ll≤mm : ∀ {l m} → 1ℚ ≤ l → l ≤ m → l * l ≤ m * m
postulate l≤m≤h : ∀ {l h} → l ≤ h → l ≤ (l + h) * ½ × (l + h) * ½ ≤ h
postulate ¬a≤b→b≤a : ∀ {a b} → ¬ (a ≤ b) → b ≤ a

sqrt' : (t : ℚ) → 1ℚ ≤ t → ℕ → ∃[ l ] ∃[ h ] (1ℚ ≤ l × l ≤ h × l * l ≤ t × t ≤ h * h)
sqrt' t 1≤t zero = 1ℚ , t , ≤-refl , 1≤t , 1≤t , sqr-≤t 1≤t
sqrt' t 1≤t (suc p) with sqrt' t 1≤t p
sqrt' t _ (suc _) | l , h , 1≤l , l≤h , ll≤t , t≤hh with (l + h) * (+ 1 / 2) | l≤m≤h l≤h
... | m | l≤m , m≤h with m * m ≤? t
sqrt' t _ (suc _) | l , h , 1≤l , l≤h , ll≤t , t≤hh | m | l≤m , m≤h | .true because ofʸ mm≤t = m , h , ≤-trans 1≤l l≤m , m≤h , mm≤t , t≤hh
sqrt' t _ (suc _) | l , h , 1≤l , l≤h , ll≤t , t≤hh | m | l≤m , m≤h | .false because ofⁿ ¬mm≤t = l , m , 1≤l , l≤m , ll≤t , ¬a≤b→b≤a ¬mm≤t

sqrt : (t : ℚ) → 1ℚ ≤ t → ℕ → Range
sqrt t 1≤t p with sqrt' t 1≤t p
sqrt t 1≤t p | l , h , 1≤l , l≤h , _ = l , h , l≤h

sqr-≤1 : ∀ {t} → 1ℚ ≤ t → 1ℚ ≤ t * t
sqr-≤1 1≤t = ≤-trans 1≤t (sqr-≤t 1≤t)

postulate sqrt-squeeze : ∀ {l t h} → 1ℚ ≤ l → l ≤ h → l * l ≤ t * t → t * t ≤ h * h → l ≤ t × t ≤ h

sqrt-sqr~>id : (t : ℚ) → (1≤t : 1ℚ ≤ t) → sqrt (t * t) (sqr-≤1 1≤t) ~> const t
sqrt-sqr~>id t 1≤t p with sqrt' (t * t) (sqr-≤1 1≤t) p
sqrt-sqr~>id t 1≤t p | l , h , 1≤l , l≤h , ll≤tt , tt≤hh with sqrt-squeeze 1≤l l≤h ll≤tt tt≤hh
sqrt-sqr~>id t 1≤t p | l , h , 1≤l , l≤h , ll≤tt , tt≤hh | l≤t , t≤h = 0 , l≤t , t≤h

_*ʳ_ : Range → Range → Range
(al , ah , al≤h) *ʳ (bl , bh , bl≤h) with al * bl ≤? ah * bh
(al , ah , al≤h) *ʳ (bl , bh , bl≤h) | .true because ofʸ p = al * bl , ah * bh , p
(al , ah , al≤h) *ʳ (bl , bh , bl≤h) | .false because ofⁿ ¬p = ah * bh , al * bl , ¬a≤b→b≤a ¬p

sqr-sqrt~>id : (t : ℚ) → (1≤t : 1ℚ ≤ t) → (λ p → sqrt t 1≤t p *ʳ sqrt t 1≤t p) ~> const t
sqr-sqrt~>id t 1≤t p with sqrt' t 1≤t p
... | l , h , 1≤l , l≤h , ll≤t , t≤hh with l * l ≤? h * h
sqr-sqrt~>id t 1≤t p | l , h , 1≤l , l≤h , ll≤t , t≤hh | .true because ofʸ ll≤hh = 0 , ll≤t , t≤hh
sqr-sqrt~>id t 1≤t p | l , h , 1≤l , l≤h , ll≤t , t≤hh | .false because ofⁿ ¬ll≤hh = ⊥-elim (¬ll≤hh (≤-trans ll≤t t≤hh))

_⊇?_ : Decidable _⊇_
(a⁻ , a⁺ , a⁻≤a⁺) ⊇? (b⁻ , b⁺ , b⁻≤b⁺) with a⁻ ≤? b⁻ | b⁺ ≤? a⁺
((a⁻ , a⁺ , a⁻≤a⁺) ⊇? (b⁻ , b⁺ , b⁻≤b⁺)) | .true because ofʸ a⁻≤b⁻ | .true because ofʸ b⁺≤a⁺ = true because ofʸ (a⁻≤b⁻ , b⁺≤a⁺)
((a⁻ , a⁺ , a⁻≤a⁺) ⊇? (b⁻ , b⁺ , b⁻≤b⁺)) | .true because ofʸ a⁻≤b⁻ | .false because ofⁿ ¬b⁺≤a⁺ = false because ofⁿ λ { (a⁻≤b⁻ , b⁺≤a⁺) → ⊥-elim (¬b⁺≤a⁺ b⁺≤a⁺)}
((a⁻ , a⁺ , a⁻≤a⁺) ⊇? (b⁻ , b⁺ , b⁻≤b⁺)) | .false because ofⁿ ¬a⁻≤b⁻ | b⁺≤a⁺ = false because ofⁿ λ { (a⁻≤b⁻ , _) → ⊥-elim (¬a⁻≤b⁻ a⁻≤b⁻)}

-- I do not see any way to actually prove the termination of this function.
-- Nevertheless, this is different from the postulates in that if it does not diverge it really will
-- construct a proof of convergence.
{-# TERMINATING #-}
sqr-sqrt~>sqrt-sqr : (t : ℚ) → (1≤t : 1ℚ ≤ t) → (λ p → sqrt t 1≤t p *ʳ sqrt t 1≤t p) ~> sqrt (t * t) (sqr-≤1 1≤t)
sqr-sqrt~>sqrt-sqr t 1≤t p = h 0 where
  h : ℕ → ∃[ p' ] ((sqrt t 1≤t p *ʳ sqrt t 1≤t p) ⊇ (sqrt (t * t) (sqr-≤1 1≤t) p'))
  h p' with (sqrt t 1≤t p *ʳ sqrt t 1≤t p) ⊇? (sqrt (t * t) (sqr-≤1 1≤t) p')
  h p' | .true because ofʸ prf = p' , prf
  h p' | .false because ofⁿ ¬prf = h (suc p')

-- Likewise for the following one. This general method will prove convergence for any kind of function. 
-- That having said, I am decently sure that the following should not diverge. Still, this is dubious as a proof method.
{-# TERMINATING #-}
sqrt-sqr~>sqr-sqrt : (t : ℚ) → (1≤t : 1ℚ ≤ t) → sqrt (t * t) (sqr-≤1 1≤t) ~> (λ p → sqrt t 1≤t p *ʳ sqrt t 1≤t p)
sqrt-sqr~>sqr-sqrt t 1≤t p = h 0 where
  h : ℕ → ∃[ p' ] (sqrt (t * t) (sqr-≤1 1≤t) p ⊇ (sqrt t 1≤t p' *ʳ sqrt t 1≤t p'))
  h p' with (sqrt (t * t) (sqr-≤1 1≤t) p) ⊇? (sqrt t 1≤t p' *ʳ sqrt t 1≤t p')
  h p' | .true because ofʸ prf = p' , prf
  h p' | .false because ofⁿ ¬prf = h (suc p')
