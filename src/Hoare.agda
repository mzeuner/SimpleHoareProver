{-

  This is a very ad-hoc implementation of a
  Hoare triple prover, following C.A.R. Hoare's
  classic paper "An Axiomatic Basis for Computer Programming".

  Its original purpose is to serve as a demo in
  a reading course on "Classical Papers in Computer Science".

  The original example from the paper can be found in Example.agda.

  Note that we don't have quantifiers in our logic, but free variables
  should be thought of as universally quantified.

-}

{-# OPTIONS --safe #-}

module Hoare where
open import Data.Bool hiding (_≟_)
                      renaming (not to ¬)
open import Data.Integer renaming (_+_ to _+ℤ_; _*_ to _·ℤ_; _-_ to _-ℤ_; _≤ᵇ_ to _≤ⁱ_)
open import Data.Nat hiding (_+_; _≟_)
                     renaming (_≡ᵇ_ to _≡ⁿ_)
open import Data.Unit hiding (_≟_)
open import Relation.Nullary.Decidable.Core hiding (True ; False)


-- port from Haskell to Agda
data IntExpr : Set where
  C : ℤ → IntExpr -- constants
  X : ℕ → IntExpr -- countably many variables X₁ , X₂ ,...
  _+_ : IntExpr → IntExpr → IntExpr -- addition
  _-_ : IntExpr → IntExpr → IntExpr -- subtraction
  _·_ : IntExpr → IntExpr → IntExpr -- multiplication

infixl 8 _+_
infixl 8 _-_
infixl 9 _·_


data BoolExpr : Set where
  _==_ : IntExpr → IntExpr → BoolExpr
  _<=_ : IntExpr → IntExpr → BoolExpr
  not_ : BoolExpr → BoolExpr
  _and_ : BoolExpr → BoolExpr → BoolExpr
  _or_ : BoolExpr → BoolExpr → BoolExpr
  True : BoolExpr
  False : BoolExpr


pattern _⊃_ φ ψ = (not φ) or ψ

infixr 4 _or_
infixr 4 _⊃_
infixr 5 _and_
infix 6 not_
infixr 7 _==_
infixr 7 _<=_


-- substitution
_[X_↦_]ⁱ : IntExpr → ℕ → IntExpr → IntExpr
(C i) [X n ↦ y ]ⁱ = C i
(X m) [X n ↦ y ]ⁱ = if (n ≡ⁿ m) then y else (X m)
(x + z) [X n ↦ y ]ⁱ = (x [X n ↦ y ]ⁱ) + (z [X n ↦ y ]ⁱ)
(x - z) [X n ↦ y ]ⁱ = (x [X n ↦ y ]ⁱ) - (z [X n ↦ y ]ⁱ)
(x · z) [X n ↦ y ]ⁱ = (x [X n ↦ y ]ⁱ) · (z [X n ↦ y ]ⁱ)

_[X_↦_] : BoolExpr → ℕ → IntExpr → BoolExpr
(x == y) [X n ↦ z ] = (x [X n ↦ y ]ⁱ) == (y [X n ↦ z ]ⁱ)
(x <= y) [X n ↦ z ] = (x [X n ↦ y ]ⁱ) <= (y [X n ↦ z ]ⁱ)
(not φ) [X n ↦ z ] = not (φ [X n ↦ z ])
(φ and ψ) [X n ↦ z ] = (φ [X n ↦ z ]) and (ψ [X n ↦ z ])
(φ or ψ) [X n ↦ z ] = (φ [X n ↦ z ]) and (ψ [X n ↦ z ])
True [X n ↦ z ] = True
False [X n ↦ z ] = False



-- interpretation of expressions in an environment
Env = ℕ → ℤ

⟦_⟧ⁱ_ : IntExpr → Env → ℤ
⟦ C i ⟧ⁱ Γ = i
⟦ X n ⟧ⁱ Γ = Γ n
⟦ y + z ⟧ⁱ Γ = ⟦ y ⟧ⁱ Γ +ℤ ⟦ y ⟧ⁱ Γ
⟦ y - z ⟧ⁱ Γ = ⟦ y ⟧ⁱ Γ -ℤ ⟦ y ⟧ⁱ Γ
⟦ y · z ⟧ⁱ Γ = ⟦ y ⟧ⁱ Γ ·ℤ ⟦ y ⟧ⁱ Γ


⟦_⟧_ : BoolExpr → Env → Bool
⟦ x == y ⟧ Γ = ⌊ (⟦ x ⟧ⁱ Γ) ≟ (⟦ y ⟧ⁱ Γ) ⌋ -- is there no ℤ → ℤ → Bool in std-lib?
⟦ x <= y ⟧ Γ = ⟦ x ⟧ⁱ Γ ≤ⁱ ⟦ y ⟧ⁱ Γ
⟦ not φ ⟧ Γ = ¬ (⟦ φ ⟧ Γ)
⟦ φ and ψ ⟧ Γ = (⟦ φ ⟧ Γ) ∧ (⟦ ψ ⟧ Γ)
⟦ φ or ψ ⟧ Γ = (⟦ φ ⟧ Γ) ∨ (⟦ ψ ⟧ Γ)
⟦ True ⟧ Γ = true
⟦ False ⟧ Γ = false


⊨ : BoolExpr → Set
⊨ φ = ∀ (Γ : Env) → T (⟦ φ ⟧ Γ)

-- a little lemma that's used implicitly in Hoare's paper
⊃-refl : ∀ φ → ⊨ (φ ⊃ φ)
⊃-refl φ Γ with ⟦ φ ⟧ Γ
... | true = tt
... | false = tt




-- programs
data Prog : Set where
  skip : Prog
  _;_ : Prog → Prog → Prog --type \; and choose "(2/2) 1."
  X_:=_ : ℕ → IntExpr → Prog
  If_Then_Else_ : BoolExpr → Prog → Prog → Prog
  While_Do_ : BoolExpr → Prog → Prog

infixl 3 _;_


-- proofs of Hoare triples
data ⊢_⟪_⟫_ : BoolExpr → Prog → BoolExpr → Set where

  SKIP : ∀ (φ : BoolExpr)
       -------------------
       → ⊢ φ ⟪ skip ⟫ φ


  COMP : ∀ (φ ψ χ : BoolExpr) (C₁ C₂ : Prog)
       → ⊢ φ ⟪ C₁ ⟫ ψ
       → ⊢ ψ ⟪ C₂ ⟫ χ
      ---------------------------------------
       → ⊢ φ ⟪ C₁ ; C₂ ⟫ χ


  ASSIGN : ∀ (φ : BoolExpr) (n : ℕ) (y : IntExpr)
        ------------------------------------------
         → ⊢ (φ [X n ↦ y ]) ⟪ X n := y ⟫ φ


  IF : ∀ (φ ψ b : BoolExpr) (C₁ C₂ : Prog)
     → ⊢ (b and φ) ⟪ C₁ ⟫ ψ
     → ⊢ (not b and φ) ⟪ C₂ ⟫ ψ
    --------------------------------------
     → ⊢ φ ⟪ If b Then C₁ Else C₂ ⟫ ψ


  WHILE : ∀ (φ b : BoolExpr) (C : Prog)
        → ⊢ (φ and b) ⟪ C ⟫ φ
       -------------------------------------
        → ⊢ φ ⟪ While b Do C ⟫ (not b and φ)


  CONS : ∀ (φ₁ φ₂ ψ₁ ψ₂ : BoolExpr) (C : Prog)
       → ⊨ (φ₁ ⊃ φ₂)
       → ⊨ (ψ₁ ⊃ ψ₂)
       → ⊢ φ₂ ⟪ C ⟫ ψ₁
      --------------------------------------
       → ⊢ φ₁ ⟪ C ⟫ ψ₂
