{-# OPTIONS --guardedness #-}
module main24 where

open import task24

open import IO
open import System.Environment
open import Data.String.Base using (String; _++_)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show; readMaybe)
open import Data.List using (List; []; _∷_)
open import Data.List.Base using (foldr)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Function using (_$_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Agda.Primitive using (lzero)

-- парсинг String в ℕ
parseNat : String → Maybe ℕ
parseNat s = readMaybe 10 s

-- печать списка
showListℕ : List ℕ → String
showListℕ [] = "[]"
showListℕ (x ∷ xs) =
  "[" ++ show x ++ go xs
  where
    go : List ℕ → String
    go [] = "]"
    go (y ∷ ys) = ", " ++ show y ++ go ys

printListℕ : List ℕ → IO (⊤ {lzero})
printListℕ xs =
  putStrLn ("result: " ++ showListℕ xs)

-- обработка аргументов командной строки
processArgs : List String → IO (⊤ {lzero})
processArgs (nStr ∷ _) =
  let n      = fromMaybe 0 (parseNat nStr)
      result = maybeVecToList (nthPermVecMaybe n digitsVec)
  in printListℕ result
processArgs [] = putStrLn "usage: <executable> <n>"

main : Main
main = run $ getArgs >>= processArgs
