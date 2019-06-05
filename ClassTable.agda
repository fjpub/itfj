-----------------------------------------------
-- Class table representation for FJ in Agda --
-- Author: Samuel da Silva Feitosa           --
--         Alejandro Serrano Mena            --
-- Date: Between Feb and Apr / 2019          --
-----------------------------------------------

open import Data.Nat

module ClassTable (n : ℕ) where

open import Data.Fin
open import Data.List hiding (lookup ; allFin)
open import Data.Product hiding (map)
open import Data.Vec using (allFin ; Vec ; lookup)
open import Data.Vec.All using ()
open import Data.List.Membership.Propositional
open import Data.List.Relation.Sublist.Propositional hiding (lookup)

-- Featherweight Java Nominal Types
-----------------------------------

Ty = Fin n

-- Class Signature Definition
-----------------------------

record CSig : Set where
  field
    supers : List Ty -- Inheritance Hierarchy 
    flds   : List Ty
    signs  : List (List Ty × Ty)

-- Table with Class Signatures
------------------------------

CTSig : Set
CTSig = Vec CSig n

---------------------------
-- Auxiliary definitions --
---------------------------

-- Obtaining fields from a given class
--------------------------------------

fields : CTSig → Ty → List Ty
fields ξ τ =
  concatMap (λ τ₁ → CSig.flds (lookup ξ τ₁)) (CSig.supers (lookup ξ τ)) ++ CSig.flds (lookup ξ τ)

-- Obtaining method types form a class
--------------------------------------

signatures : CTSig → Ty → List (List Ty × Ty)
signatures ξ τ =
  concatMap (λ τ₁ → CSig.signs (lookup ξ τ₁)) (CSig.supers (lookup ξ τ)) ++ CSig.signs (lookup ξ τ)

signatures' : CTSig → Ty → List (List Ty × Ty)
signatures' ξ τ = CSig.signs (lookup ξ τ)

-- Well-formed class table definition
-------------------------------------

record WFCT : Set where
  field
    ξ : CTSig
    wf-fields :
      ∀ {τ₁ τ₂} → τ₂ ∈ CSig.supers (lookup ξ τ₁)
                → (fields ξ τ₂) ⊆ (fields ξ τ₁)
    wf-inheritance :
      ∀ {τ₁ τ₂} → τ₂ ∈ CSig.supers (lookup ξ τ₁)
                 → CSig.supers (lookup ξ τ₂) ⊆
                    CSig.supers (lookup ξ τ₁)

