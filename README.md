This project is [Ryan Hota](https://github.com/Ryan-Hota) and [Soham Saha](https://github.com/Soham-Saha)'s submission for the course **Introduction to Formal Proofs with Lean** at CMI in Jan-Apr, 2026.

This project attempts to implement a formal framework for doing category theory in Lean from scratch (i.e., without using any `import`s). 

#### `Attempt_1.lean`

This is the base code that we came up with, and in this file we have:
- Definition of a category
- Certain basic category theoretical definitions (initial and terminal objects, functors, natural transformations, exponential objects, Cartesian closed categories, etc.)
- Some basic theorems to get started working with them
- An example implementation of a category (the posetal category of natural numbers ordered by divisibility)
- Introduced some notation in an attempt to simplify proofwriting

#### `Attempt_2.lean`

This file is an **unfinished** attempt to show that the category of categories is cartesian closed.

This file, a fork of `Attempt_1.lean`, slightly modifies the definition of a `Category` to disentangle itself from issues of proof-irrelevance (by switching from `Sort` to `Type`).

While we have progressed much on the path to showing that the category of `Category.{u, u}` categories is cartesian closed, we had perhaps chosen a stronger goal than necessary. The unfinished part of our proof attempts to show that two functors are _equal_, where the more suitable notion might have been showing them to be _isomorphic_. Our attempts at proving functorial equality immediately led us into [dependent type theory hell](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/EqToHom.html), and we have barely returned unscathed.

Yet, our work demonstrates that while showing existence of "strict" exponential objects might be tricky in the dependent type-theoretic framework, slightly relaxing the conditions might just work (and would better satisfy the [principle of equivalence](https://ncatlab.org/nlab/show/principle+of+equivalence)).

### Conclusion

During the development of this project, we saw strange Lean quirks, spoke with a lot of people on the Lean Zulip chat, started hating heterogeneous equality, and meddled with category theory.

Overall, we did have a lot of fun, and learnt a lot too.
