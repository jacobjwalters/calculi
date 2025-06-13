module STLC.TermLevelMetavars.Types

import Data.SnocList
import Data.SnocList.Elem
import Data.SnocList.Quantifiers

||| The usual types for STLC.
data Ty : Type where
  Base : Ty
  Fn : Ty -> Ty -> Ty

||| Convertibility relation on types. In our language, this is just Eq.
data Conv : (a, b : Ty) -> Type where
  ConvBase : Conv Base Base
  ConvFn : Conv a a' -> Conv b b' -> Conv (Fn a b) (Fn a' b')

export infixr 8 ~>
||| Shorthand for Conv.
(~>) : Ty -> Ty -> Type
a ~> b = Conv a b

||| A context is a snoclist of types. We use de Bruijn indexing.
Context : Type
Context = SnocList Ty

||| A family is a set indexed by a context.
Family : Type
Family = Context -> Type

||| An S-sorted family is a family indexed by a sort S. In our language, our sorts are our types.
||| Effectively, a sorted family is a set indexed by a particular type, and a particular context.
||| We use sorted families to represent holes and terms.
||| Holes are directly sorted families.
||| Terms are actually additionally indexed by holes, making them effectively of type SortedFamily -> Ty -> Context -> Type.
SortedFamily : Type
SortedFamily = Ty -> Family

||| Sorted family substitution. Gamma |- theta : Delta
||| This asserts that all elements in delta are also present in gamma.
||| In effect, delta is a subset of gamma.
(.subst) : SortedFamily -> Context -> Family
s.subst delta gamma = All (\ty => s ty gamma) delta

data Term : SortedFamily -> SortedFamily where
  ||| Var assers that there is a variable with type ty in gamma, and produces a term.
  Var : Elem ty gamma
     -> Term hole ty gamma
  ||| Abs is lambda abstraction.
  ||| We take a term of type sigma with gamma extended with type tau, and produce a term of type tau -> sigma in gamma.
  Abs : Term hole sigma (gamma :< tau)
     -> Term hole (Fn tau sigma) gamma
  ||| Application. We force convertibility between the types of each term.
  App : Term hole sigma_to_tau gamma -> Term hole sigma' gamma -> sigma_to_tau ~> (Fn sigma' tau)
     -> Term hole tau gamma
  ||| Meta-variables (?m).
  ||| m is a hole of type ty in some context delta, and there exists a subsitution from delta to gamma.
  ||| Given these, we can produce a term ?m in gamma.
  MVar : {0 hole : SortedFamily}
      -> (m : hole ty delta) -> (Term hole).subst delta gamma
      -> Term hole ty gamma

-- Thinnings
data Thinning : (delta : Context) -> (gamma : Context) -> Type where
  None : Thinning [<] [<]
  Keep : (c : Ty) -> Thinning delta gamma -> Thinning (delta :< c) (gamma :< c)
  Drop : (c : Ty) -> Thinning delta gamma -> Thinning (delta :< c) (gamma)

||| Example contexts.
C1, C2 : Context
C1 = [< Base]
C2 = [< Fn Base Base, Base, Fn (Fn Base Base) Base, Base]

||| An example thinning from C2 to C1.
ThC2C1a : Thinning C2 C1
ThC2C1a = Keep Base
       $ Drop (Fn (Fn Base Base) Base)
       $ Drop Base
       $ Drop (Fn Base Base)
       $ None

||| Multiple thinnings from C2 to C1 exist.
ThC2C1b : Thinning C2 C1
ThC2C1b = Drop Base
        $ Drop (Fn (Fn Base Base) Base)
        $ Keep Base
        $ Drop (Fn Base Base)
        $ None

failing
  ||| There is no thinning from C1 to C2.
  ThC1C2 : Thinning C1 C2
  ThC1C2 = %search

-- Renaming  plfa de bruijn
weaken : (rho : Elem a gamma -> Elem a delta) -> (Elem a (gamma :< b) -> Elem a (delta :< b))
weaken rho Here = Here
weaken rho (There x) = There (rho x)

rename : (rho : {0 a : Ty} -> Elem a gamma -> Elem a delta) -> (Term hole a gamma -> Term hole a delta)
rename rho (Var x) = Var (rho x)
rename rho (Abs b) = Abs (rename (weaken rho) b)
rename rho (App f x c) = App (rename rho f) (rename rho x) c
rename rho (MVar m x) = MVar ?mr ?xr

-- Capture avoiding subst
-- -[-]
subweaken : (sigma : Elem a gamma -> Term hole a delta) -> (Elem a (gamma :< b) -> Term hole a (delta :< b))
subweaken sigma Here = Var Here
subweaken sigma (There x) = rename There (sigma x)

subst : Term hole b gamma -> (sigma : {0 a : Ty} -> Elem a gamma -> Term hole a delta) -> Term hole b delta
subst (Var x) sigma = sigma x
subst (Abs b) sigma = Abs (subst b (subweaken sigma))
subst (App f x c) sigma = App (subst f sigma) (subst x sigma) c
subst (MVar m theta) sigma = ?sm


-- Meta-variable subst (bind)
--MVarSubst : h -> s -> delta -> b
         ---> Term (?hl) b delta -> (f : forall a. forall gamma. h a gamma -> Term s {-- _a (delta, gamma) -}) -> Term s {-- _b delta -}
