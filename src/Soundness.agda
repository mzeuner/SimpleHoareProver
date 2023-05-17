{-

   Defining correctness of Hoare triples (in an environment) and stating soundness.
   Proving soundness could be a topic for a BA thesis?

-}

{-# OPTIONS --allow-unsolved-metas #-} -- not safe !!

module Soundness where

open import Data.Bool renaming (not to ¬)
open import Data.Nat hiding (_+_) renaming (_≡ᵇ_ to _≡ⁿ_)

open import Hoare



-- programs act on environments
{-# NON_TERMINATING #-}
run_on : Prog → Env → Env
run skip on Γ = Γ
run (P ; Q) on Γ = run Q on (run P on Γ)
run (X n := y) on Γ m = if (n ≡ⁿ m) then (⟦ y ⟧ⁱ Γ) else (Γ m)
run (If b Then P Else Q) on Γ = if ⟦ b ⟧ Γ then (run P on Γ) else (run Q on Γ)
run (While b Do P) on Γ = if ⟦ b ⟧ Γ then (run (P ; (While b Do P)) on Γ) else Γ


-- correct Hoare triples
⟦_⟪_⟫_⟧_ : BoolExpr → Prog → BoolExpr → Env → Bool
⟦ φ ⟪ P ⟫ ψ ⟧ Γ = ¬ (⟦ φ ⟧ Γ)  ∨ (⟦ ψ ⟧ (run P on Γ))

⊨_⟪_⟫_ : BoolExpr → Prog → BoolExpr → Set
⊨ φ ⟪ P ⟫ ψ = ∀ Γ → T (⟦ φ ⟪ P ⟫ ψ ⟧ Γ)


{-# NON_TERMINATING #-} -- presumably
soundness : ∀ {φ ψ : BoolExpr} {P : Prog} → ⊢ φ ⟪ P ⟫ ψ → ⊨ φ ⟪ P ⟫ ψ
soundness = {!!}
