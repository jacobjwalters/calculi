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

Holes = SortedFamily

data Hole : Holes where
  Poke : (ty : Ty) -> (gamma : Context) -> Hole ty gamma

||| Sorted family substitution. Gamma |- theta : Delta
||| This asserts that all elements in delta are also present in gamma.
||| In effect, delta is a subset of gamma.
||| Also called renaming.
(.subst) : SortedFamily -> Context -> Family
s.subst delta gamma = All (\ty => s ty gamma) delta

data Term : Holes -> SortedFamily where
  ||| Var assers that there is a variable with type ty in gamma, and produces a term.
  Var : Elem ty gamma
     -> Term hole ty gamma
  ||| Abs is lambda abstraction.
  ||| We take a term of type sigma with gamma extended with type tau, and produce a term of type tau -> sigma in gamma.
  Abs : {tau : Ty}
     -> Term hole sigma (gamma :< tau)
     -> Term hole (Fn tau sigma) gamma
  ||| Application. We force convertibility between the types of each term.
  App : {sigma_to_tau, sigma' : Ty}  -- Needs to be accessible for MVarSubst
     -> Term hole sigma_to_tau gamma -> Term hole sigma' gamma -> (0 conv : sigma_to_tau ~> (Fn sigma' tau))
     -> Term hole tau gamma
  ||| Meta-variables (?m).
  ||| m is a hole of type ty in some context delta, and there exists a subsitution from delta to gamma.
  ||| Given these, we can produce a term ?m in gamma.
  MVar : {delta, gamma : Context}
      -> (m : hole ty delta) -> (theta : (Term hole).subst delta gamma)
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

||| There are renamings from C1 to C2, by embedding the singular Base type in C1 to a variable term in C2, which points to either of the Base types in C2.
Renaming1a, Renaming1b : (Term hole).subst C1 C2
Renaming1a = [<Var Here]
Renaming1b = [<Var (There (There Here))]

||| There is a renaming from C2 to C1, by mapping all of the Base types in C2 to variable terms referring to the singular Base type in C1, and creating lambda terms for the function types in C2.
||| The first function is the identity, and doesn't know about the Base type in C1. The second function is the constant function on the Base type in C1, discarding its argument (of type Base -> Base).
Renaming2 : (Term hole).subst C2 C1
Renaming2 = [<Abs (Var Here), Var Here, Abs (Var (There Here)), Var Here]

-- Extend the context within a term
extTerm : (tau : Ty) -> Term h a gamma -> Term h a (gamma :< tau)
extTerm tau (Var x) = Var (There x)
extTerm t (Abs x) = ?eab  -- TODO: stuck here
extTerm tau (App x y conv) = App (extTerm tau x) (extTerm tau y) conv
extTerm tau (MVar m theta) = MVar m theta'
  where theta' : All (\ty => Term h ty (gamma :< tau)) delta
        theta' = mapProperty (\p => ?pr) ?thetaa  -- TODO: convince idris that theta delta is theta' delta. Maybe we make delta explicit in the MVar constructor?

-- Meta-variable subst (bind)
MVarSubst : {H, S : Holes} -> {B : Ty} -> {Delta : Context}
         -> Term H B Delta -> (f : {A : Ty} -> {Gamma : Context} -> H A Gamma -> Term S A (Gamma ++ Delta))
         -> Term S B Delta
MVarSubst (Var x) f = Var x
MVarSubst (Abs x) f = Abs (MVarSubst x ?mvs)
MVarSubst (App x y conv) f = App (MVarSubst x f) (MVarSubst y f) conv
MVarSubst (MVar m theta) f = ?mv
--MVarSubst (MVar m x) f = f (?mm)  -- TODO: m : H B delta; mm : H B Delta. How to convince Idris these are the same?

{-
Here's a test metavariable, using our stubbed hole definition.
Our metavariable is of type Base, and has the context Delta := [<Fn Base Base].
Our substitution sends the Base in Gamma := [<Base] (from the type signature) to a constant function.
-}
testmv : Term Hole Base [<Base]
testmv = MVar (Poke Base [<Fn Base Base]) [<Abs (Var $ There Here)]

{-
Now, here's a meta variable substitution function f. We're mapping to the same type of hole because I'm lazy.
idRename is the identity renaming, which sends a context to itself
testf is a meta substitution which applies idRename to the context, and creates an MVar term for each hole.
-}
idRename : (delta : Context) -> All (\ty => Term Hole ty delta) delta
idRename [<] = [<]
idRename (sx :< x) = mapProperty (\p => extTerm x $ p) (idRename sx) :< Var Here

testf : {delta : Context} -> Hole a delta -> Term Hole a delta
testf (Poke a delta) = MVar (Poke a delta) (idRename delta)
