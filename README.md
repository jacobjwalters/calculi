# calculi

This project is a set of different implementations and extensions of type systems for the simply typed lambda calculus (STLC).
Generally, there is a focus on meta variables (metavars).

Currently, the following calculi have been implemented:
- [Basic STLC](https://github.com/jacobjwalters/calculi/blob/main/src/STLCBasic.idr);
- [Intrinsically scoped STLC](https://github.com/jacobjwalters/calculi/blob/main/src/STLCScoped.idr);
- [Intrinsically scoped and typed STLC](https://github.com/jacobjwalters/calculi/blob/main/src/STLCTyped.idr);
- [Intrinsically scoped STLC with type metavars](https://github.com/jacobjwalters/calculi/blob/main/src/STLCScopedMTyVar.idr).

You can play around with the implementations by loading the files in the `src/` directory into an Idris2 session.
