{-# OPTIONS --guardedness #-}
module main where

open import task7

open import IO
open import Data.String.Base using (_++_)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat.Primality using (prime?)

-- для печати Maybe ℕ
printMaybe : Maybe ℕ → Main
printMaybe (just x) = run (putStrLn ("your prime number is: " ++ show x))
printMaybe nothing  = run (putStrLn "bound was reached")

main : Main
main = printMaybe (nthPrime prime? 10001 120000)
