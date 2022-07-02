open import Data.Nat
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Env using (Name)

-- An untyped λ-calculus with nats and bools, using PHOAS.
-- See https://doi.org/10.1145/1411204.1411226

-- V represents the set of "variables", which really should be thought of as
-- some meta-language value that can be explicitly embedded into the object
-- language.
-- Binding is then represented by a meta-language function that quantifies over
-- V.

-- Note: The paper uses a module-level parameter, but that didn't seem to save
-- me anything, so I just use an implicit parameter.

data tTerm {V : Set} : Set where
  tvar : V -> tTerm
  tnlit : ℕ -> tTerm
  tblit : Bool -> tTerm
  tif : tTerm {V} -> tTerm {V} -> tTerm {V}
        --------------
        -> tTerm
  tlam : (V -> tTerm {V})
         -------------------
         -> tTerm
  tapp : tTerm {V} -> tTerm {V}
       ----------
       -> tTerm

eg1 : {V : Set} -> tTerm {V}
eg1 = tlam (λ x -> tvar x)

eg2 : {V : Set} -> tTerm {V}
eg2 = (tapp eg1 (tnlit 5))

-- Substitution takes terms whose variables are themselves terms, to terms
-- parametric in their variables.
tsubst : {V : Set} -> tTerm {tTerm {V}} -> tTerm {V}
tsubst (tvar e) = e
tsubst (tnlit x) = tnlit x
tsubst (tblit x) = tblit x
tsubst (tif e e₁ e₂) = tif (tsubst e) (tsubst e₁) (tsubst e₂)
tsubst (tlam f) = tlam (λ x -> tsubst (f (tvar x)))
tsubst (tapp e e₁) = tapp (tsubst e) (tsubst e₁)
tsubst tnil = tnil
tsubst (textend e x e₁) = textend (tsubst e) x (tsubst e₁)
tsubst (tlookup e x) = tlookup (tsubst e) x

-- A term with 1 free variable. Type corresponds to Term1 in the paper.
eg3' : {V : Set} -> tTerm {V} -> tTerm {tTerm {V}}
eg3' = λ v -> (tapp (tlam (λ x -> tvar x)) (tvar v))

-- Subst the free var
eg3 : {V : Set} -> tsubst {V} (eg3' (tnlit 5)) ≡ (tapp (tlam (λ x -> tvar x)) (tnlit 5))
eg3 = refl

-- The equational theory.
-- I'm not exactly sure how the parameter V behaves....

data tEq : tTerm -> tTerm -> Set where
   t=β : {e : tTerm} {f : tTerm -> tTerm}
      -> tEq (tapp (tlam f) e) (tsubst (f e))
   t=if-true : {e1 e2 : tTerm} -> tEq (tif (tblit true) e1 e2) e1
   t=if-false : {e1 e2 : tTerm} -> tEq (tif (tblit false) e1 e2) e1

-- Fails with unification error, due to issues with parameter V.
-- V needs to be both abstract and equal to tTerm {V}...
test1 : tEq (tapp (tlam (λ x -> tvar x)) (tblit true)) (tblit true)
test1 = t=β
