# calculi

This project is a set of different type systems, and implementations of corresponding type checkers, for the simply typed lambda calculus (STLC).
Generally, there is a focus on meta variables (metavars).

Currently, the following calculi have been implemented:
- [Basic STLC](https://github.com/jacobjwalters/calculi/blob/main/src/STLC/Basic/Core.idr);
- [Intrinsically scoped STLC](https://github.com/jacobjwalters/calculi/blob/main/src/STLC/IntrinsicallyScoped/Core.idr);
- [Intrinsically scoped and typed STLC](https://github.com/jacobjwalters/calculi/blob/main/src/STLC/IntrinsicallyTyped/Core.idr);
- [Intrinsically scoped STLC with type-level meta variables](https://github.com/jacobjwalters/calculi/blob/main/src/STLC/TypeLevelMetavars/Core.idr).
- [Intrinsically scoped STLC with term-level meta variables](https://github.com/jacobjwalters/calculi/blob/main/src/STLC/TermLevelMetavars/Core.idr).

You can play around with the implementations by loading the files in the `src/` directory into an Idris2 session.

The notes for this project are available on the releases page. You can download the latest version by clicking [here](https://github.com/jacobjwalters/calculi/releases/download/latest/main.pdf).