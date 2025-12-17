module task24 where

open import Agda.Builtin.Nat using (Nat; _*_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Nat.Base using (_!)
open import Data.Nat.Properties using (_<?_)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec using (Vec; []; _∷_; toList)
open import Data.Product using (_×_; _,_)
open import Data.List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- //
{-# TERMINATING #-} -- тут несколько раз эта штука без нее терминэйшн чек падал
divNat : ℕ → ℕ → ℕ
divNat n zero = 0
divNat n d with n <? d
... | yes _ = 0
... | no  _ = suc (divNat (n ∸ d) d)

-- %
{-# TERMINATING #-}
modNat : ℕ → ℕ → ℕ
modNat n zero = n
modNat n d with n <? d
... | yes _ = n
... | no  _ = modNat (n ∸ d) d

-- выбирает i-ый элемент вектор, возращает его и вектор (уже без элемента)
pickAt : ∀ {ℓ m} {A : Set ℓ} → ℕ → Vec A (suc m) → Maybe (A × Vec A m)
pickAt zero  (x ∷ xs) = just (x , xs)
pickAt (suc i) (x ∷ []) = nothing
pickAt (suc i) (x ∷ y ∷ ys) with pickAt i (y ∷ ys)
... | nothing         = nothing
... | just (p , rest) = just (p , x ∷ rest)

-- кастомный факториал, который пользует хвостовую рекурсию
factAcc : ℕ → ℕ → ℕ
factAcc zero acc      = acc
factAcc (suc n) acc   = factAcc n (acc * suc n)

factTail : ℕ → ℕ
factTail n = factAcc n 1

-- n-ая перестановка
{-# TERMINATING #-}
nthPermVecMaybe : ∀ {m} → (fact : ℕ → ℕ) → ℕ → Vec ℕ m → Maybe (Vec ℕ m)
nthPermVecMaybe {m = zero} fact _ [] = just []
nthPermVecMaybe {m = suc n} fact k v@(x ∷ xs)
  with pickAt (divNat k (fact n)) v
... | nothing = nothing
... | just (d , rest)
  with nthPermVecMaybe fact (modNat k (fact n)) rest
... | nothing = nothing
... | just tail = just (d ∷ tail)

-- интересующие меня цифры
digitsVec : Vec ℕ 10
digitsVec = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []

--перевод Maybe Vec в List
maybeVecToList : ∀ {m} → Maybe (Vec ℕ m) → List ℕ
maybeVecToList nothing = List.[]
maybeVecToList (just v) = toList v
