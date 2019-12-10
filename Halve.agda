-- https://stackoverflow.com/questions/59263530/how-to-prove-that-the-halving-function-over-positive-rationals-always-has-an-exi

open import Data.Nat using (ℕ;suc;zero)
open import Data.Rational
open import Data.Product
open import Relation.Nullary
open import Data.Bool using (Bool;false;true)

halve : ℕ → ℚ
halve zero = 1ℚ
halve (suc p) = ½ * halve p

∃-halve : ∀ {a b} → 0ℚ < a → a < b → ∃[ p ] (halve p * b < a)
∃-halve {a} {b} 0<a a<b = h 1 where
  h : ℕ → ∃[ p ] (halve p * b < a)
  h p with halve p * b <? a
  h p | .true because ofʸ b'<a = p , b'<a
  h p | .false because ofⁿ ¬b'<a = h (suc p)
