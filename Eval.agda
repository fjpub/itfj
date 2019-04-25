------------------------------------------
-- Evaluation of FJ expressions in Agda --
-- Author: Samuel da Silva Feitosa      --
--         Alejandro Serrano Mena       --
-- Date: Between Feb and Apr / 2019     --
------------------------------------------
import ClassTable as CT

module Eval {n} (Δ : CT.WFCT n) where

open import Data.Nat
open import Data.List.All
open import Data.Product
open import Data.Maybe hiding (All)
open import Data.Vec.All renaming (All to AllV ; lookup to lookupV)
open import Syntax Δ
open import Implementation Δ

open CT n
open CSig
open CImpl

-- Values associated to their types on a given context
------------------------------------------------------

Env : Ctx → Set
Env Γ = All Val Γ

-- Mutual recursive evaluation functions definition
---------------------------------------------------

eval      : ∀ {Γ τ c}  → ℕ → Maybe (Val τ) → CTImpl → Env Γ
                       → Expr Γ (just τ) c → Maybe (Val c)
eval-list : ∀ {Γ τ cs} → ℕ → Maybe (Val τ) → CTImpl → Env Γ
                       → All (Expr Γ (just τ)) cs → Maybe (All Val cs)

-- Fuel based evaluation for a single expression
------------------------------------------------

-- out of fuel
eval zero _ _ _ _ = nothing
-- R-This (workaround)
eval (suc fuel) τ δ γ This = τ
-- R-Var
eval (suc fuel) τ δ γ (Var x) = just (lookup γ x)
-- RC-Field and R-Field
eval (suc fuel) τ δ γ (Field e f) with eval fuel τ δ γ e 
... | nothing = nothing
... | just (VNew p cp) = just (lookup cp (∈-lift p cp f))
-- RC-Invk-Recv, RC-Invk-Arg and R-Invk
eval (suc fuel) τ δ γ (Invk e m mp) with eval-list fuel τ δ γ mp
... | nothing = nothing
... | just mp' with eval fuel τ δ γ e
...   | nothing = nothing
...   | just v@(VNew {C} {D} p cp) =
          let mi = lookup (implementations D δ) m
            in eval fuel (just v) δ mp' mi
-- RC-New-Arg
eval (suc fuel) τ δ γ (New c cp) with eval-list fuel τ δ γ cp
... | nothing = nothing
... | just cp' = just (VNew refl cp')
-- R-Cast
eval (suc fuel) τ δ γ (UCast p e) with eval fuel τ δ γ e
... | nothing = nothing
... | just (VNew p' cp) = just (VNew (<:-trans p' p) cp)

-- Fuel based evaluation for a list of expressions
--------------------------------------------------

-- Out of fuel
eval-list zero _ _ _ _ = nothing
-- Empty list
eval-list (suc fuel) τ δ γ [] = just []
-- Recursive definition
eval-list (suc fuel) τ δ γ (p ∷ ps) with eval fuel τ δ γ p
... | nothing = nothing 
... | just v with eval-list fuel τ δ γ ps
...   | nothing = nothing
...   | just vs = just (v ∷ vs)
