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


-- Okay, I really want equality for terms to just be computations, i.e.,
-- equality in the meta-language.
--
-- So, we'll represent values as a data type, and computations as
-- shallow-embedded computations over those values.
-- To get binding, we'll use HOAS.
-- This isn't strictly positive, so we can't use induction over our universe of
-- values.
-- But that's okay, I don't want to; I just want equality over the computations
-- over those values.

{-# NO_POSITIVITY_CHECK #-}
data U : Set where
  tlam : (U -> U) -> U
  tnat : ℕ -> U
  tbool : Bool -> U
  err : String -> U

tapp : U -> U -> U
tapp (tlam f) e = (f e)
tapp _ _ = err "bad app"

tif : U -> U -> U -> U
tif (tbool false) e1 e2 = e1
tif (tbool true) e1 e2 = e2
tif _ _ _ = err "bad if"

tplus : U -> U -> U
tplus (tnat n) (tnat m) = (tnat (n + m))
tplus _ _ = err "bad plus"

eg1 : U
eg1 = tlam (λ x -> x)

eg2 : U
eg2 = (tapp eg1 (tnat 5))

eg3 : eg2 ≡ tnat 5
eg3 = refl

eg4 : (tapp (tapp (tlam (λ x -> tlam (λ y -> x))) (tnat 5)) (tnat 6)) ≡ tnat 5
eg4 = refl

eg5 : (tapp (tapp (tlam (λ x -> tlam (λ y -> x))) (tplus (tnat 2) (tnat 2))) (tnat 5))
      ≡
      tnat 4
eg5 = refl

eg6 : ¬((tnat 5) ≡ (tnat 44))
eg6 ()


witness : {f g : U -> U} → (w : U) → ¬ (f w ≡ g w)
        → ¬ (f ≡ g)
witness w fw≢gw refl = fw≢gw refl

witnessU : {f g : U -> U} → (w : U) → ¬ (tapp (tlam f) w ≡ tapp (tlam g) w)
         → ¬ (tlam f ≡ tlam g)
witnessU w fw≢gw refl = fw≢gw refl

eg7 : ¬((tlam (λ x -> x)) ≡ (tlam (λ x -> (tnat 5))))
-- auto completes with C-c C-a after witnessU ? ?
eg7 = witnessU (tlam (λ z → z)) λ ()
