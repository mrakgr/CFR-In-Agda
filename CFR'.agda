-- Formalization of the 'Regret Minimization in Games with Incomplete Information' paper.

open import Data.List as List
open import Data.Vec as Vec
open import Data.Nat as Nat
open import Data.Fin
open import Data.Integer as Int
open import Data.Rational as Rat
open import Data.Rational.Properties as RatP
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Nullary as Nullary
open import Data.List.Relation.Unary.Any as Any

data NonRepeating {a} {A : Set a} : (l : List A) → Set a where
  done : NonRepeating []
  rest : ∀ {x xs} → ¬ Any (x ≡_) xs → NonRepeating xs → NonRepeating (x ∷ xs)

record UniqueList {a} (A : Set a) : Set a where
  constructor _//_
  field
    l : List A
    wf : NonRepeating l

Infoset = ℕ
Size = ℕ
Player = ℤ

data GameTree (infoset-size : Infoset → Size) : Set where
  Terminal : (reward : ℚ) → GameTree infoset-size
  Response : (id : Infoset) → (branches : Vec (GameTree infoset-size) (infoset-size id)) → (wf : 0 Nat.< infoset-size id) → GameTree infoset-size

record PolicyAtNode (n : ℕ) : Set where
  constructor _//_//_
  field
    σ : Vec ℚ n
    .wf-elem : ∀ {i : Fin n} {x : ℚ} (_ : σ [ i ]= x) → 0ℚ Rat.≤ x × x Rat.≤ 1ℚ
    .wf-dist : Vec.foldl _ (Rat._+_) 0ℚ σ ≡ 1ℚ

data Node {infoset-size : Infoset → Size} : GameTree infoset-size → Set where
  here : ∀ tree → Node tree
  there : ∀ id wf {i branches branch} → branches [ i ]= branch → Node branch → Node (Response id branches wf)

variable
  infoset-size : Infoset → Size
  tree : GameTree infoset-size

Policy : (Infoset → Size) → Set
Policy infoset-size = ∀ (id : Infoset) → PolicyAtNode (infoset-size id)

Vec-foldl2 : ∀ {a b s} {A : Set a} {B : Set b} (S : ℕ → Set s) {m} →
        (∀ {n} → S n → A → B → S (Nat.suc n)) →
        S zero →
        Vec A m →
        Vec B m → S m
Vec-foldl2 S _ n [] [] = n
Vec-foldl2 S f n (x₁ ∷ l₁) (x₂ ∷ l₂) = Vec-foldl2 (λ n → S (Nat.suc n)) f (f n x₁ x₂) l₁ l₂

{-# TERMINATING #-}
u-tree : (tree : GameTree infoset-size) → (policy : Policy infoset-size) → ℚ
u-tree (Terminal reward) _ = reward
u-tree (Response id branches wf) policy with policy id
u-tree (Response id branches wf) policy | σ // wf-elem // wf-dist =
  Vec-foldl2 _ (λ s a b → s Rat.+ u-tree a policy Rat.* b) 0ℚ branches σ

u : {tree : GameTree infoset-size} → (node : Node tree) → (policy : Policy infoset-size) → ℚ
u (here tree) policy = u-tree tree policy
u (there id wf mem node) = u node

cfr-reach : {tree : GameTree infoset-size} → (node : Node tree) → (policy : Policy infoset-size) → ℚ
cfr-reach-skip : {tree : GameTree infoset-size} → (node : Node tree) → (policy : Policy infoset-size) → ℚ

cfr-reach (here tree) policy = 1ℚ
cfr-reach (there id wf {i} mem node) policy with policy id
cfr-reach (there id wf {i} mem node) policy | σ // wf-elem // wf-dist = Vec.lookup σ i Rat.* cfr-reach-skip node policy

cfr-reach-skip (here tree) policy = 1ℚ
cfr-reach-skip (there id wf mem node) policy = cfr-reach node policy

Vec-mem-map : ∀ {a} {A : Set a} {b} {B : Set b} {n} → (l : Vec A n) → (∀ {i} x → l [ i ]= x → B) → Vec B n
Vec-mem-map [] f = []
Vec-mem-map (x ∷ l) f = (f x here) ∷ Vec-mem-map l (λ x mem → f x (there mem))

{-# TERMINATING #-}
Infoset→Nodes : (tree : GameTree infoset-size) → Infoset → List (Node tree)
Infoset→Nodes (Terminal reward) id = []
Infoset→Nodes (Response id' branches wf) id with id' Nat.≟ id
Infoset→Nodes tree@(Response id' branches wf) .id' | yes refl = List.[ here tree ]
Infoset→Nodes (Response id' branches wf) id | no ¬p =
  let nodes = Vec-mem-map branches (λ branch mem → List.map (there id' wf mem) (Infoset→Nodes branch id)) in
  List.concat (Vec.toList nodes)

List-ℚmax : (ℚ × List ℚ) → ℚ
List-ℚmax (fst , snd) = List.foldl max fst snd where
  max : ℚ → ℚ → ℚ
  max x x' with x RatP.≤? x'
  max x x' | yes p = x'
  max x x' | no ¬p = x

maximize : ∀ {a} {A : Set a} → (A → ℚ) → A × List A → ℚ
maximize f (fst , snd) = List-ℚmax (f fst , List.map f snd)
