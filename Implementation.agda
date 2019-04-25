-----------------------------------------------
-- Class table implementation for FJ in Agda --
-- Author: Samuel da Silva Feitosa           --
--         Alejandro Serrano Mena            --
-- Date: Between Feb and Apr / 2019          --
-----------------------------------------------
import ClassTable as CT

module Implementation {n} (Δ : CT.WFCT n) where

open import Data.Maybe using (just ; nothing) 
open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂) 
open import Data.List using (List ; concatMap ; [] ; _∷_ ) 
open import Data.List.All using (All ; [] ; _∷_ ; map) 
open import Data.List.All.Properties using (++⁺)
open import Data.Vec.All renaming (All to AllV ; lookup to lookupV) using () 
open import Data.Vec using (allFin ; lookup)
open import Relation.Binary.PropositionalEquality using (sym ; _≡_ ; cong ; refl)
open import Data.Vec.Properties using (lookup-allFin)
open import Data.List.Membership.Propositional using (_∈_ ; mapWith∈)
open import Data.List.Any using (there)
open import Syntax Δ

open CT n
open CSig
open WFCT

-- Representation of class implementation
-----------------------------------------

record CImpl (τ : Ty) : Set where
  field
    impls : All (λ s → Expr (proj₁ s) (just τ) (proj₂ s)) (signs (lookup τ (ξ Δ)))

open CImpl

-- Associates the class implementation with its signatures
----------------------------------------------------------

CTImpl = AllV CImpl (allFin n)

-- Mutual recursive definition for casting the 'this' pointer
-------------------------------------------------------------

cast-this : ∀ {Γ τ c d} → c <: d → Expr Γ (just d) τ → Expr Γ (just c) τ
cast-this-list : ∀ {Γ cs c d} → c <: d → All (Expr Γ (just d)) cs → All (Expr Γ (just c)) cs

-- Casting the 'this' pointer for a single expression
-----------------------------------------------------

cast-this p This = UCast p This
cast-this p (Var x) = Var x
cast-this p (Field e f) = Field (cast-this p e) f
cast-this p (Invk e m mp) = Invk (cast-this p e) m (cast-this-list p mp)
cast-this p (New c cp) = New c (cast-this-list p cp)
cast-this p (UCast p' e) = UCast p' (cast-this p e)

-- Casting the 'this' pointer for a list of expressions
-------------------------------------------------------

cast-this-list p [] = []
cast-this-list p (x ∷ xs) = cast-this p x ∷ cast-this-list p xs

-- Getting the implementation of a given class
----------------------------------------------

impl-this : (τ : Ty) → CTImpl 
               → All (λ s → Expr (proj₁ s) (just τ) (proj₂ s)) (signs (lookup τ (ξ Δ)))
impl-this τ δ rewrite sym (lookup-allFin τ) = impls (lookupV τ δ)

-- Getting the implementation of super classes
----------------------------------------------

impl-supers : (τ : Ty) → CTImpl → (l : List (Σ Ty (λ σ → τ <: σ)))
    → All (λ s → Expr (proj₁ s) (just τ) (proj₂ s))
           (concatMap (λ s → signs (lookup s (ξ Δ))) (Data.List.map proj₁ l))
impl-supers τ δ [] = []
impl-supers τ δ ((c , p) ∷ xs) rewrite sym (lookup-allFin c) =
  ++⁺ (Data.List.All.map (λ s → cast-this p s) (impls (lookupV c δ))) (impl-supers τ δ xs)

---------------------------------
-- Auxiliary lemmas and proofs --
---------------------------------

-- Provides a super class and a proof of subtyping
--------------------------------------------------

mapSuperProofs : (τ : Ty) → List (Σ Ty (λ σ → τ <: σ))
mapSuperProofs τ = mapWith∈ (supers (lookup τ (ξ Δ))) (λ {s} idx → (s , exts idx))

-- Equality between a list and the first projection 
---------------------------------------------------

eqMapProj : ∀ {A : Ty → Set} → (l : List Ty) → (f : ∀ {t} → t ∈ l → A t)
         → Data.List.map proj₁ (mapWith∈ l (λ {s} idx → (s , f idx))) ≡ l
eqMapProj [] f = refl
eqMapProj (x ∷ l) f = cong (λ p → x ∷ p) (eqMapProj l (λ x → f (there x)))

-- Equality between the super classes and the first projection
--------------------------------------------------------------

eqSupers : (τ : Ty) → Data.List.map proj₁ (mapSuperProofs τ) ≡ supers (lookup τ (ξ Δ))
eqSupers τ = eqMapProj (supers (lookup τ (ξ Δ))) (λ {t} idx → exts {τ} {t} idx)

-----------------------------------------------------------------------
-- Getting all the implementations of a class (this + super classes) --
-----------------------------------------------------------------------

implementations : (τ : Ty) → CTImpl 
               → All (λ s → Expr (proj₁ s) (just τ) (proj₂ s)) (signatures (ξ Δ) τ)
implementations τ δ rewrite sym (eqSupers τ) = ++⁺ (impl-supers τ δ (mapSuperProofs τ)) (impl-this τ δ)

