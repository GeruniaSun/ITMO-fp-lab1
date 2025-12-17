{-# OPTIONS --guardedness #-}
module main7 where

open import task7
open import IO
open import System.Environment
open import Data.String.Base using (String; _++_)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show; readMaybe)
open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat.Primality using (prime?)
open import Function using (_$_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Agda.Primitive using (lzero)

-- парсинг строки(аргумента команды) в ℕ
parseNat : String → Maybe ℕ
parseNat s = readMaybe 10 s

printMaybe : Maybe ℕ → IO (⊤ {lzero})
printMaybe (just x) = putStrLn ("your prime number is: " ++ show x)
printMaybe nothing  = putStrLn "bound was reached"

-- обработка командной строки
processArgs : List String → IO (⊤ {lzero})
processArgs (nStr ∷ boundStr ∷ _) =
  let n     = fromMaybe 0 (parseNat nStr)
      bound = fromMaybe 0 (parseNat boundStr)
  in printMaybe (nthPrime prime? n bound)
processArgs _ = putStrLn "usage: <executable> <n> <bound>"

main : Main
main = run $ getArgs >>= processArgs
