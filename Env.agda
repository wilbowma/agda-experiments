open import Data.Nat
open import Data.Product using (_×_; _,_; Σ) renaming (proj₁ to fst) renaming (proj₂ to snd)
open import Data.Bool
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Level renaming (_⊔_ to lmax; suc to lsuc)
open import Data.String using (String; _==_)
open import Data.List using (List; _∷_; [])
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

module Env where

Name = String

-- A Scope is a map from Names to some Type
Scope : ∀ {l} -> (Set l) -> (Set l)
Scope A = List (Name × A)

close-scope : {A : Set} -> Scope A -> Name -> Scope A
close-scope [] n = []
close-scope ((x , a) ∷ S) n = if (x == n) then S else ((x , a) ∷ (close-scope S n))

-- A well-scoped Environment is a map from Names to *elements* of the Type
-- indicated by the Scope.
data Env {l : Level} {U : Set l} {El : U -> Set l} :
         (scope : Scope U) -> Set l
  where
  env-empty : Env []
  env-add : {A : U} {scope : Scope U}
          -> Env {El = El} scope -> (key : String) -> (El A)
          -> Env ((key , A) ∷ scope)

module Examples where
  -- A scope mapping names to types
  test-scope : Scope Set
  test-scope = (("meow" , ℕ) ∷ [])

  -- A scope mapping names to higher types
  test-scope1 : Scope Set₁
  test-scope1 = (("meow" , Set) ∷ [])

  -- A scope mapping names to nats
  -- Note that Scopes are meant to be type-level, so, these are type-level nat.
  -- The nats do not live in the environment.
  -- This would be a weird scope.
  test-scope2 : Scope ℕ
  test-scope2 = (("meow" , 5) ∷ [])

  -- A typing environment, mapping Names to Types
  -- only valid with cumulativity
  -- test-env : Env {El = λ x -> Set} (("meow" , Set₁) ∷ [])
  -- test-env = env-add env-empty "meow" ℕ

  -- A store. The scope maps Names to Types, while the environment maps each
  -- Names to an elements of those Types.
  -- only valid with cumulativity
  -- test-env1 : Env {El = λ x -> ℕ} (("meow" , Set) ∷ [])
  -- test-env1 = env-add env-empty "meow" 5

  -- Extremely weird environment, where we large eliminate numbers to types
  weirdEl : ℕ -> Set
  weirdEl 5 = ℕ
  weirdEl x = Bool

  -- So the type "5" actually means a value of type ℕ
  test-env2 : Env {El = weirdEl} (("meow" , 5) ∷ [])
  test-env2 = env-add env-empty "meow" 0

  -- The type "1", or any other nat, actually means a value of type Bool
  test-env3 : Env {El = weirdEl} (("meow" , 1) ∷ [])
  test-env3 = env-add env-empty "meow" true

-- eom

-- InScope is a proof that key is bound to A in scope.
-- Probably could replaced with Decidability.
data InScope {l : Level} {U : Set l}
     (scope : Scope U) (key : Name) (A : U) : (Set l)
  where
  scope-found : (S : Scope U) -> scope ≡ ((key , A) ∷ S)
              -> InScope scope key A
  scope-cons : {C : U} -> (S : Scope U) (key' : Name)
             -> scope ≡ (key' , C) ∷ S -> ((key' ≡ key) -> ⊥)
             -> InScope S key A -> InScope scope key A

impossibleScope : {l : Level} {key : Name} {U : Set l} {A : U} -> InScope [] key A -> ⊥
impossibleScope (scope-found S ())
impossibleScope (scope-cons S key' () x₁ pf)


strengthen-in-scope : {A : Set} {S : Scope A} {n n' : Name} {a : A}
                    -> InScope S n a -> ¬(n ≡ n') -> InScope (close-scope S n') n a
strengthen-in-scope {S = []} {n' = n'} pf p with impossibleScope pf
... | ()
strengthen-in-scope {S = (n , a) ∷ S} {n' = n'} (scope-found S₁ x) p with (n Data.String.≟ n')
strengthen-in-scope {_} {(n , a) ∷ S} {n' = n'} (scope-found .S refl) p | no p' =
  scope-found (close-scope S n') refl
strengthen-in-scope {_} {(n , a) ∷ S} {n' = n'} (scope-found .S refl) p | yes p' =
  (⊥-elim (p p'))
strengthen-in-scope {S = (n , a) ∷ S} {n' = n'} (scope-cons .S .n refl x₁ pf) p with (n Data.String.≟ n')
... | no p' = scope-cons (close-scope S n') n refl x₁ (strengthen-in-scope pf p)
... | yes refl = pf


module Test where
  test-InScope : InScope (("meow" , Set) ∷ []) "meow" Set
  test-InScope = scope-found [] refl

  -- only valid with cumulativity
  -- test-InScope1 : InScope {U = Set₁} (("bark", Bool) ∷ ("meow" , Set) ∷ []) "meow" Set
  -- test-InScope1 = scope-cons (("meow" , Set) ∷ []) "bark" refl absurd test-InScope
  --   where
  --   absurd : "bark" ≡ "meow" -> ⊥
  --   absurd ()

  test-InScope2 : {k1 k2 : String} {A : Set}
                -> InScope (("bark" , A) ∷ (k1 , A) ∷ []) k2 A
                -> (k2 ≡ k1) ⊎ (k2 ≡ "bark")
  test-InScope2 {k1} {."bark"} {A} (scope-found .((k1 , A) ∷ []) refl) =
    inj₂ refl
  test-InScope2 {k1} {.k1} {A}
    (scope-cons .((k1 , A) ∷ []) ."bark" refl x₁ (scope-found .[] refl))
    = inj₁ refl
  test-InScope2 {.key'} {k2} {A}
    (scope-cons .((key' , A) ∷ []) ."bark" refl x₁
      (scope-cons .[] key' refl x₂ pf)) with impossibleScope {key = k2} pf
  ... | ()

-- eom

env-get : {l : Level} {U : Set l} {A : U} {S : Scope U} {El : U -> Set l}
        -> Env {El = El} S -> (key : String) -> (InScope S key A)
        -> El A
env-get (env-add env key₁ x) .key₁ (scope-found S refl) = x
env-get (env-add env key₁ x) key (scope-cons S .key₁ refl x₂ in-scope) =
  env-get env key in-scope
env-get {S = .[]} env-empty key scope with impossibleScope scope
... | ()
