module STLC.TermLevelMetavars.Types

import Data.SnocList


Ty : Type
Ty = String

Context : Type
Context = SnocList Ty

-- TODO: better type
Holes : Type
Holes = List String

-- TODO: what should this look like? This is the biggest hurdle imo
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
  -- There shouldn't be a thinning from C1 to C2
  ThC1C2 : Thinning C1 C2
  ThC1C2 = %search



-- Renamings
Var : Ty -> Context -> Type
Var a gamma = Nat  -- dummy type while i figure things out

-- TODO: not sure about this one
Rename : (gamma, delta : Context) -> (a : Ty) {- (x : A) \in delta -}
      -> Var a gamma -> Var a delta



-- Capture avoiding subst
-- -[-]
Subst : (gamma, delta : Context)
     -> Term []


-- Meta-variable subst (bind)
MVarSubst : h -> s -> delta -> b
         -> Term h b delta -> (f : forall a. forall gamma. h a gamma -> Term s {-- _a (delta, gamma) -}) -> Term s {-- _b delta -}
