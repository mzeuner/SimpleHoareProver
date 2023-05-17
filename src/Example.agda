{-

    The original example (Table III) from Hoare's
    "An Axiomatic Basis for Computer Programming"

    Note that we translated the variables from the paper to our setting as follows:

      x → X 0
      y → X 1
      r → X 2
      q → X 3

-}

{-# OPTIONS #-}

module Example where
open import Data.Integer using (+_ ; +0)
open import Hoare


private
  -- the program
  Q : Prog
  Q = X 2 := (X 0) ;
      X 3 := (C +0) ;
      While (X 1 <= X 2) Do
        (X 2 := (X 2 - X 1) ;
         X 3 := (C (+ 1) + X 3))

  -- TODO: prove arithmetic assumptions
  postulate
    lemma1 : ⊨ (True ⊃ X 0 == X 0 + (X 1 · C +0))
    lemma2 : ⊨ (X 0 == X 2 + X 1 · X 3 and X 1 <= X 2
                    ⊃ X 0 == (X 2 - X 1) + X 1 · (C (+ 1) + X 3))



correctDiv : ⊢ True ⟪ Q ⟫ (not X 1 <= X 2 and X 0 == X 2 + X 1 · X 3)
correctDiv = COMP _ ψ _ Q₁ Q₂ correctInit correctWhile
  where
  ψ = X 0 == X 2 + X 1 · X 3

  Q₁ = X 2 := (X 0) ; X 3 := (C +0)

  Q₂ =  While (X 1 <= X 2) Do
          (X 2 := (X 2 - X 1) ;
           X 3 := (C (+ 1) + X 3))

  correctInit : ⊢ True ⟪ Q₁ ⟫ ψ
  correctInit = COMP _ χ _ _ _ correctInit1 correctInit2
    where
    χ = X 0 == X 2 + X 1 · C +0

    correctInit1 : ⊢ True ⟪ X 2 := X 0 ⟫ χ
    correctInit1 = CONS _ _ _ _ _ lemma1 (⊃-refl χ) correctAssign
      where
      correctAssign : ⊢ (X 0 == X 0 + X 1 · C +0) ⟪ X 2 := X 0 ⟫ χ
      correctAssign = ASSIGN _ _ _

    correctInit2 : ⊢ χ ⟪ X 3 := C +0 ⟫ ψ
    correctInit2 = ASSIGN _ _ _

  correctWhile : ⊢ ψ ⟪ Q₂ ⟫ (not X 1 <= X 2 and X 0 == X 2 + X 1 · X 3)
  correctWhile = WHILE _ _ Q₃ correctLoop
    where
    Q₃ = X 2 := (X 2 - X 1) ;
         X 3 := (C (+ 1) + X 3)

    correctLoop : ⊢ ψ and X 1 <= X 2 ⟪ Q₃ ⟫ ψ
    correctLoop = CONS _ _ _ _ _ lemma2 (⊃-refl ψ) correctLoop2
      where
      θ = X 0 == (X 2 - X 1) + X 1 · (C (+ 1) + X 3)

      correctLoop2 : ⊢ θ ⟪ Q₃ ⟫ ψ
      correctLoop2 = COMP _ ζ _ _ _ (ASSIGN _ _ _) (ASSIGN _ _ _)
        where
        ζ = X 0 == X 2 + X 1 · (C (+ 1) + X 3)
