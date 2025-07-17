module STLC.TermLevelMetavars.Core

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

Variable : Ty -> Context -> Type
Variable = Elem

data Term : Holes -> SortedFamily where
  ||| Var asserts that there is a variable with type ty in gamma, and produces a term.
  Var : Variable ty gamma
     -> Term hole ty gamma
  ||| Abs is lambda abstraction.
  ||| We take a term of type sigma with gamma extended with type tau, and produce a term of type tau -> sigma in gamma.
  Abs : (tau : Ty)
     -> Term hole sigma (gamma :< tau)
     -> Term hole (Fn tau sigma) gamma
  ||| Application. We force convertibility between the types of each term.
  App : {sigma_to_tau, sigma' : Ty}  -- Needs to be accessible for MVarSubst
     -> Term hole sigma_to_tau gamma -> Term hole sigma' gamma -> (0 conv : sigma_to_tau ~> (Fn sigma' tau))
     -> Term hole tau gamma
  ||| Meta-variables (?m).
  ||| m is a hole of type ty in some context delta, and there exists a subsitution from delta to gamma.
  ||| Given these, we can produce a term ?m in gamma.
  MVar : {0 delta, gamma : Context}
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

idThinning : (delta : Context) -> Thinning delta delta
idThinning [<] = None
idThinning (sx :< x) = Keep x (idThinning sx)

dropOne : (tau : Ty) -> (delta : Context) -> Thinning (delta :< tau) delta
dropOne tau delta = Drop tau (idThinning delta)

||| There are renamings from C1 to C2, by embedding the singular Base type in C1 to a variable term in C2, which points to either of the Base types in C2.
Renaming1a, Renaming1b : (Term hole).subst C1 C2
Renaming1a = [<Var Here]
Renaming1b = [<Var (There (There Here))]

||| There is a renaming from C2 to C1, by mapping all of the Base types in C2 to variable terms referring to the singular Base type in C1, and creating lambda terms for the function types in C2.
||| The first function is the identity, and doesn't know about the Base type in C1. The second function is the constant function on the Base type in C1, discarding its argument (of type Base -> Base).
Renaming2 : (Term hole).subst C2 C1
Renaming2 = [<Abs Base (Var Here), Var Here, Abs (Fn Base Base) (Var (There Here)), Var Here]

Renaming : {hole : Holes} -> (delta, gamma : Context) -> Type
Renaming delta gamma = (Term hole).subst delta gamma

thinVar : (thn : Thinning delta gamma) -> Variable ty gamma -> Variable ty delta
thinVar (Drop ty tau) x = There (thinVar tau x)
thinVar (Keep ty tau) Here = Here
thinVar (Keep ty tau) (There x) = There (thinVar tau x)

||| A simultaneous substitution. It maps from variables in one context to terms in another.
0 Substitution : (h : Holes) -> (Gamma, Delta : Context) -> Type
Substitution h gamma delta = (0 ty : Ty) -> Variable ty gamma -> Term h ty delta

RenamingToSubstitution : Renaming {hole=h} delta gamma -> Substitution h delta gamma
RenamingToSubstitution (r :< y) ty Here = y
RenamingToSubstitution (r :< y) ty (There v) = RenamingToSubstitution r ty v

||| Weaken a context by a term
thinTerm : (thn : Thinning delta gamma) -> Term h a gamma -> Term h a delta
thinTerm thn (Var x) = Var (thinVar thn x)
thinTerm thn (Abs tau body) = Abs tau (thinTerm (Keep tau thn) body)
thinTerm thn (App f x conv) = App (thinTerm thn f) (thinTerm thn x) conv
thinTerm thn (MVar m theta) = MVar m $ mapProperty (thinTerm thn) theta

||| Map between substitutions via a thinning (codomain)
thinSub : Thinning gamma gamma' -> Substitution h gamma delta -> Substitution h gamma' delta
thinSub thn sigma ty v = sigma ty (thinVar thn v)

||| Map between substitutions via a thinning (domain)
thinSub' : Thinning delta' delta -> Substitution h gamma delta -> Substitution h gamma delta'
thinSub' thn sigma ty v = thinTerm thn (sigma ty v)

||| Given a map from Gamma to Delta, produce a map from Gamma, tau to Delta, tau.
weakenVar : (rho : Variable ty gamma -> Variable ty delta) -> Variable ty (gamma :< tau) -> Variable ty (delta :< tau)
weakenVar rho Here = Here
weakenVar rho (There x) = There (rho x)

||| Given a map from vars in Gamma to vars in Delta, promote it to terms.
weakenTerm : (rho : {0 ty : Ty} -> Variable ty gamma -> Variable ty delta) -> Term h a gamma -> Term h a delta
weakenTerm rho (Var x) = Var (rho {ty=a} x)
weakenTerm rho (Abs t b) = Abs t (weakenTerm (weakenVar rho) b)
weakenTerm rho (App f x conv) = App (weakenTerm rho f) (weakenTerm rho x) conv
weakenTerm rho (MVar m theta) = MVar m $ mapProperty (weakenTerm rho) theta

||| Given a simultaneous substitution from Delta to Gamma, produce a map from the first context extended to the second context extended.
weakenSub : {tau : Ty} -> Substitution h gamma delta -> Substitution h (gamma :< tau) (delta :< tau)
weakenSub sigma tau Here     = Var Here
weakenSub sigma ty (There x) = weakenTerm There (sigma ty x)  -- Take the term from the provided sigma

--extendSub : Substitution h gamma gamma' -> Substitution

||| Capture avoiding substitution. Given a map from vars in gamma to terms in delta, we can take a term in gamma and produce a term in delta.
subst : {delta : Context} -> (sigma : Substitution h gamma delta) -> Term h a gamma -> Term h a delta
subst sigma (Var x) = sigma a x
subst sigma (Abs tau b) = Abs tau (subst (weakenSub sigma) b)
subst sigma (App f x conv) = App (subst sigma f) (subst sigma x) conv
subst sigma (MVar m theta) = MVar m $ mapProperty (subst sigma) theta

idRenaming : (gamma : Context) -> Renaming gamma gamma
idRenaming [<] = [<]
idRenaming (sx :< x) = mapProperty (weakenTerm There) (idRenaming sx) :< Var Here

idSubstitution : (gamma : Context) -> Substitution h gamma gamma
idSubstitution _ _ x = Var x

||| Given two contexts, and a variable that can be in either, return a variable that's in just one.
splitVar : (delta : Context) -> (v : Variable ty (gamma ++ delta)) -> Either (Variable ty gamma) (Variable ty delta)
splitVar [<] v = Left v
splitVar (sx :< ty) Here = Right Here
splitVar (sx :< x) (There v) = There <$> splitVar sx v

joinSubstitution : (delta : Context) -> Substitution h gamma delta -> Substitution h (gamma ++ delta) delta
joinSubstitution delta gf ty v =
  let df = idSubstitution delta
      v = splitVar delta v
  in case v of
          Left  v => gf ty v
          Right v => df ty v

||| Meta-variable subst (bind).
||| Given a term with holes in H over Delta, and a substitution from a hole in H over Gamma to a term with holes in S over Gamma, Delta; produce a term with holes in S over Delta.
MVarSubst : {0 H, S : Holes} -> {0 B : Ty} -> {Delta : Context}
         -> Term H B Delta -> (f : {0 A : Ty} -> {0 Gamma : Context} -> H A Gamma -> Term S A (Gamma ++ Delta))
         -> Term S B Delta
MVarSubst (Var x) f = Var x
MVarSubst (Abs tau x) f = Abs tau (MVarSubst x (weakenTerm There . f))
MVarSubst (App fn arg conv) f = App (MVarSubst fn f) (MVarSubst arg f) conv
MVarSubst (MVar m theta) f =
  let theta' = RenamingToSubstitution $ mapProperty (`MVarSubst` f) theta
  in subst (joinSubstitution Delta theta') (f m)

data MyHoles : SortedFamily where
  M0 : MyHoles (Base) [<Base `Fn` Base]
  M1 : MyHoles (Base `Fn` Base) [<Base, Base `Fn` Base]

0
Coprod : (f : a -> SortedFamily) -> SortedFamily
Coprod {a} f ty ctx = (i : a ** f i ty ctx)

0
MyHoles' : SortedFamily
MyHoles' = Coprod {a = Nat} (\n => MyHoles)

IdTerm : Term hole (Base `Fn` Base) ctx
IdTerm = Abs Base $ Var Here

Ex1 : Term MyHoles' Base [<]
Ex1 = App (MVar (500 ** M1) [< MVar (0 ** M0) [< IdTerm ], IdTerm])
          (MVar (1 ** M0) [< IdTerm ])
      (ConvFn ConvBase ConvBase)

RepId : (n : Nat) -> Term holes (Base `Fn` Base) ctx
RepId 0 = IdTerm
RepId (S k) = App (Abs (Base `Fn` Base) $ Var Here) (RepId k)
  (ConvFn (ConvFn ConvBase ConvBase) (ConvFn ConvBase ConvBase))

Ex2 : Term MyHoles Base [<]
Ex2 = MVarSubst Ex1 $ \case
  (i ** M0) => MVar M0 [< Var Here]
  (i ** M1) => RepId i
