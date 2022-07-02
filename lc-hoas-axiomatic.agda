open import Data.Nat
open import Data.Bool
open import Relation.Nullary
open import Relation.Nullary.Decidable using (isYes)
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Empty
open import Data.List using (List; _∷_; [])
open import Data.String using (String; _==_)
open import Data.Product using (_×_; _,_; Σ) renaming (proj₁ to fst) renaming (proj₂ to snd)

-- Work completely equationally with the syntax of the untyped λ-calculus
-- axiomatized.
-- To represent binding, we use HOAS.
-- This requires we restrict the universe of values to our universe, U, instead
-- of all Agda terms.

postulate
  U : Set
  tlam : (U -> U) -> U
  tapp : U -> U -> U
  tnat : ℕ -> U
  tplus : U -> U -> U
  tbool : Bool -> U
  tif : U -> U -> U -> U

  tβ : {f : U -> U} {e' : U} -> (tapp (tlam f) e') ≡ (f e')
  tiftrue : {e1 e2 : U} -> (tif (tbool true) e1 e2) ≡ e1
  tiffalse : {e1 e2 : U} -> (tif (tbool false) e1 e2) ≡ e2
  tpluseq : {n m : ℕ} -> (tplus (tnat n) (tnat m)) ≡ tnat (n + m)

eg1 : U
eg1 = tlam (λ x -> x)

eg2 : U
eg2 = (tapp eg1 (tnat 5))

eg3 : eg2 ≡ tnat 5
eg3 = tβ

-- We get congrence rules "for free" from the meta-language...
-- the cost is high tedium.
eg4 : (tapp (tapp (tlam (λ x -> tlam (λ y -> x))) (tnat 5)) (tnat 6)) ≡ tnat 5
-- eg4 rewrite tβ = ?
-- eg4 rewrite tβ {_} {_} = {!!}
-- eg4 = trans (cong {!!} {!!}) tβ
eg4 = trans (cong (λ v -> (tapp v (tnat 6))) tβ) tβ

-- bah so tedious
eg5 : (tapp (tapp (tlam (λ x -> tlam (λ y -> x))) (tplus (tnat 2) (tnat 2)))) (tnat 5)
      ≡
      tnat 4
eg5 = {!!}

eg6 : ¬(tnat 5 ≡ tnat 4)
-- eg6 ()
eg6 = {!!}
