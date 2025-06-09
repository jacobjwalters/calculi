module STLC.TermLevelMetavars.Types

import Data.SnocList


Ty : Type
Ty = String

Context : Type
Context = SnocList Ty

Holes : Type
Holes = List String

Term : Holes -> Type
Term h = Int

-- Thinnings
data Thinning : (delta : Context) -> (gamma : Context) -> Type where
  None : Thinning [<] [<]
  Keep : (c : Ty) -> Thinning delta gamma -> Thinning (delta :< c) (gamma :< c)
  Drop : (c : Ty) -> Thinning delta gamma -> Thinning (delta :< c) (gamma)

C1, C2 : Context
C1 = [< "String"]
C2 = [< "Int", "String", "Int"]

ThC2C1 : Thinning C2 C1
ThC2C1 = Drop "Int" (Keep "String" (Drop "Int" None))

failing
  ThC1C2 : Thinning C1 C2
  ThC1C2 = %search


-- Permutations
permute : Nat -> Nat -> Context -> Context
permute to from ctx = ?p  -- Ugly; we're computing. I read a SO answer
-- https://stackoverflow.com/questions/30551033/swap-two-elements-in-a-list-by-its-indices
-- which seems to indicate that differentiable functors should help here,
-- but I don't have the time/energy in the late afternoon to implement all of this.

data Permutation : (delta : Context) -> (gamma : Context) -> Type where
  Done : Permutation gamma gamma
  Swap : (to, from : Nat) -> Permutation (permute to from delta) gamma


-- Renamings
Var : Ty -> Context -> Type
Var a gamma = Nat

-- TODO: not sure about this one
Rename : (gamma, delta : Context) -> (a : Ty) {- (x : A) \in delta -}
      -> Var a gamma -> Var a delta



-- Capture avoiding subst
-- -[-]
Subst : (gamma, delta : Context)
     -> Term []
