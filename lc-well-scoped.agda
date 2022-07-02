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
open import Env

-- An untyped λ-calculus with nats and bools, using variables as strings and a
-- well-scoped representation.
-- It could be extended to a well-typed representation, by indexing by both a
-- scope and an environment.
-- This is inspirsed by the following papers, but is probably more naïve than
-- any of them.
--
-- * https://doi.org/10.1145/2914770.2837620
-- * https://doi.org/10.1145/3236785
-- * https://doi.org/10.1145/3018610.3018613
-- * http://tydeworkshop.org/2019-abstracts/paper16.pdf
--
-- The main difference is that it's a named representation; I don't believe in
-- nameless.
--
-- The implementation of named environments and scopes is in Env.agda

lcScope = Scope ⊤

data tTerm  : {S : lcScope} -> Set where
  tvar : {S : lcScope} (n : Name) -> InScope S n tt -> tTerm {S}
  tnlit : {S : lcScope} -> ℕ -> tTerm {S}
  tblit : {S : lcScope} -> Bool -> tTerm {S}
  tif : {S : lcScope} -> tTerm {S} -> tTerm {S} -> tTerm {S}
        --------------
        -> tTerm {S}
  tlam : {S : lcScope} -> (n : Name) -> (tTerm {(n , tt) ∷ (close-scope S n)})
       -------------------
       -> tTerm {(close-scope S n)}
  tapp : {S : lcScope} -> tTerm {S} -> tTerm {S}
       ----------
       -> tTerm {S}

eg1 : tTerm {[]}
eg1 = tlam {[]} "x" (tvar "x" (scope-found [] refl))

eg2 : tTerm
eg2 = (tapp eg1 (tnlit 5))

tsubst : {S : lcScope} -> tTerm {S} -> (n : Name) -> tTerm {(close-scope S n)} -> tTerm {(close-scope S n)}
tsubst (tvar n' pf) n t' with (n' Data.String.≟ n)
... | yes p' = t'
... | no p' = (tvar n' (strengthen-in-scope pf p'))
tsubst (tnlit x) n t' = t'
tsubst (tblit x) n t' = t'
tsubst (tif t t₁ t₂) n t' = (tif (tsubst t n t') (tsubst t₁ n t') (tsubst t₂ n t'))
tsubst {S} (tlam n' t) n t' with (n' Data.String.≟ n)
... | yes p' = (tlam n' t)
--- This should work, but Agda can't seem to conclude that n == n' ≡ false during unification.
... | no p' = {!!} (tlam n' (tsubst t n t'))
tsubst (tapp t t₁) n t' = (tapp (tsubst t n t') (tsubst t₁ n t'))
