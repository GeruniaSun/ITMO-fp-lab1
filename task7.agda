module task7 where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat.Primality using (Prime; prime?)

-- =============================================================================
-- nthPrime
-- =============================================================================
-- nthPrime принимает:
-- функцию проверки на простоту
-- i : ℕ — номер искомого простого
-- bound : ℕ — верхняя граница поиска
-- =============================================================================

nthPrime : ((n : ℕ) → Dec (Prime n)) → ℕ → ℕ → Maybe ℕ
nthPrime isPrimeDec i bound = aux 2 i (bound ∸ 1)
  where
  aux : ℕ → ℕ → ℕ → Maybe ℕ

  -- 1) Если i = 0 — значит уже найдено
  aux candidate zero (suc gas) = just candidate

  -- 2) Дошли до граница не найдя нужного числа
  aux _ _ zero = nothing

  -- 3) i = 1 (ищем последнее простое)
  aux candidate (suc zero) (suc gas) with isPrimeDec candidate
  ... | yes _ = just candidate
  ... | no  _ = aux (suc candidate) (suc zero) gas

  -- 4) i > 1
  aux candidate (suc (suc k)) (suc gas) with isPrimeDec candidate
  ... | yes _ = aux (suc candidate) (suc k) gas
  ... | no  _ = aux (suc candidate) (suc (suc k)) gas
