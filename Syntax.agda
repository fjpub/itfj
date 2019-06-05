--------------------------------------------
-- Inherently-typed syntax for FJ in Agda --
-- Author: Samuel da Silva Feitosa        --
--         Alejandro Serrano Mena         --
-- Date: Between Feb and Apr / 2019       --
--------------------------------------------
import ClassTable as CT

module Syntax {n} (Δ : CT.WFCT n) where

open import Agda.Primitive
open import Data.List hiding (lookup)
open import Data.List.Membership.Propositional
open import Data.Vec
open import Data.Vec.All renaming (lookup to lookupV) hiding (All)
open import Data.Maybe
open import Data.Product
open import Data.List.All hiding (lookup)
open import Data.List.Relation.Sublist.Propositional renaming (lookup to ∈-lookup)
  
open CT n
open CSig
open WFCT
    
-- Context definition
---------------------
  
Ctx : Set
Ctx = List Ty
  
-- Subtyping definition
-----------------------
  
infix 3 _<:_
  
data _<:_ : Ty → Ty → Set where
  refl : ∀ {τ} → τ <: τ
  exts : ∀ {τ₁ τ₂} → τ₂ ∈ supers (lookup (ξ Δ) τ₁) → τ₁ <: τ₂

-- Inherently-typed expression definition
-----------------------------------------
  
data Expr (Γ : Ctx) : Maybe Ty → Ty → Set where
  This  : ∀ {c}   → Expr Γ (just c) c
  Var   : ∀ {x τ}   → x ∈ Γ → Expr Γ τ x
  Field : ∀ {c f τ} → Expr Γ τ c → f ∈ (fields (ξ Δ) c) → Expr Γ τ f
  Invk  : ∀ {c m τ} → Expr Γ τ c → m ∈ (signatures (ξ Δ) c)
                    → All (Expr Γ τ) (proj₁ m) → Expr Γ τ (proj₂ m)
  New   : ∀ {τ} c   → All (Expr Γ τ) (fields (ξ Δ) c) → Expr Γ τ c
  UCast : ∀ {c d τ} → c <: d → Expr Γ τ c → Expr Γ τ d
  
-- Inherently-typed values
--------------------------
  
data Val : Ty → Set where
  VNew : ∀ {c d} → c <: d → All Val (fields (ξ Δ) c) → Val d
  
-- Liftting de Bruijn index for 'fields'
----------------------------------------
  
∈-lift : ∀ {C D f} → C <: D → All Val (fields (ξ Δ) C)
       → f ∈ (fields (ξ Δ) D) → f ∈ (fields (ξ Δ) C)
∈-lift refl l i = i
∈-lift {C} {D} (exts x) l i = ∈-lookup ((wf-fields Δ) x) i

-- Proof of transitivity fort the inheritance relation
------------------------------------------------------

<:-trans : ∀ {τ₁ τ₂ τ₃} → τ₁ <: τ₂ → τ₂ <: τ₃ → τ₁ <: τ₃
<:-trans refl p = p
<:-trans (exts x) refl = exts x
<:-trans {τ₁} {τ₂} {τ₃} (exts x) (exts x') = exts (∈-lookup ((wf-inheritance Δ) x) x')

