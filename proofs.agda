{-# OPTIONS --no-unicode #-} -- turn off automatic unicode insertion

module proofs where

data _+_ (A B : Set) : Set where -- A || B
  inl : A -> A + B
  inr : B -> A + B

record _><_ (A : Set) (P : A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : P fst

infixr 15 _><_
open _><_

_*_ : (A B : Set) -> Set -- A && B
A * B = A >< \_ -> B
infixr 15 _*_

data ⊥ : Set where

postulate
  doubleNegation : {A : Set} -> ((A -> ⊥) -> ⊥) -> A

-- 4.6.1
deMorgan : {A B : Set} -> (A * B -> ⊥) -> (A -> ⊥) + (B -> ⊥)
deMorgan f = doubleNegation \y -> y (inl \z -> y (inr \t -> f (z , t)))

deMorganRev : {A B : Set} -> (A -> ⊥) + (B -> ⊥) -> (A * B -> ⊥)
deMorganRev (inl x) (fst , _) = x fst
deMorganRev (inr x) (_ , snd) = x snd


-- 4.6.2
deMorgan2 : {A B : Set} -> (A + B -> ⊥) -> (A -> ⊥) * (B -> ⊥)
deMorgan2 x = (\q -> x (inl q)) , (\p -> x (inr p))

deMorgan2Rev : {A B : Set} -> (A -> ⊥) * (B -> ⊥) -> (A + B -> ⊥)
deMorgan2Rev (fst , _) (inl x) = fst x
deMorgan2Rev (_ , snd) (inr x) = snd x

postulate
  lem : (X : Set) -> X + (X -> ⊥)

naughtExp : {A : Set} -> ⊥ -> A
naughtExp ()

--4.8.4
Peirce : {A B : Set} -> ((A -> B) -> A) -> A
Peirce {A} x with lem A
Peirce {A} x    | (inl t) = t
Peirce {A} x    | (inr t) = x \y -> naughtExp(t y)

-- 4.8.3
Proof1 : {A B : Set} -> (A -> B) + (B -> A)
Proof1 {A} with lem A
Proof1 {A}    | (inl x) = inr (\ y -> x)
Proof1 {A}    | (inr x) = inl \y -> naughtExp (x y)

-- 4.8.2
Proof2 : {A B C : Set} -> ((A -> B) -> C) -> (A -> C) -> C
Proof2 {A} x y with lem A
Proof2 {A} x y    | (inl t) = y t
Proof2 {A} x y    | (inr t) = x \p -> naughtExp (t p)

data ∃ {A : Set} (B : A -> Set) : Set where
  ∃-add : (x : A) -> B x -> ∃ B

-- 4.6.3
deMorgan3 : {A : Set} {P : A -> Set} -> (∀ (x : A) -> P x -> ⊥) -> (∃ P -> ⊥)
deMorgan3 p (∃-add x y) =  p x y

deMorgan3Rev : {A : Set} {P : A -> Set} -> (∃ P -> ⊥) -> ∀ (x : A) -> P x -> ⊥
deMorgan3Rev f x p = f (∃-add x p)

-- 4.6.4
deMorgan4 : {A : Set} {P : A -> Set} -> ∃ (\x -> P x -> ⊥) -> (∀ (x : A) -> P x) -> ⊥
deMorgan4 (∃-add x p) y =  p (y x)

deMorgan4Rev : {A : Set} {P : A -> Set} -> ((∀ (x : A) -> P x) -> ⊥) -> ∃ (\x -> P x -> ⊥)
deMorgan4Rev = {!!}

-- 4.9.2
Proof3 : {A B C : Set} -> (A + B -> C) -> (A -> C) * (B -> C)
Proof3 {A} x with lem A
Proof3 {A} x    | (inl t) = (\z -> x (inl z)) , \z -> x (inl t)
Proof3 {A} x    | (inr t) = (\z -> x (inl z)) , \z -> x (inr z)

-- 4.9.1
Proof4 : {A B C : Set} -> (A -> B) + (A -> C) -> A -> (B + C)
Proof4 (inl x) a = inl (x a)
Proof4 (inr x) a = inr (x a)