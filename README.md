This project attempts to implement a formal framework for doing category theory in Lean from scratch (i.e., without using any `import`s). 

#### `Attempt_1.lean`

This is the base code that we came up with, and in this file, we have
- Definition of a category
- Certain basic category theoretical definitions (initial and terminal objects, functors, natural transformations, exponential objects, Cartesian closed categories, etc.)
- Some basic theorems to get started working with them
- An example implementation of a category (the posetal category of natural numbers ordered by divisibility)

#### `Attempt_2.lean`

This file is an **unfinished** attempt to show that the category of categories is cartesian closed.

This file, a fork of `Attempt_1.lean`, slightly modifies the definition of a `Category` to disentangle itself from issues of proof-irrelevance (by switching from `Sort` to `Type`).

While we have progressed much on the path to showing that the category of `Category.{u, u}` categories is cartesian closed, we had perhaps chosen a stronger goal than necessary. The unfinished part of our proof attempts to show that two functors are _equal_, where the more suitable notion might have been showing them to be _isomorphic_. As expected, our attempts at proving functorial equality immediately led us into [dependent type theory hell](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/EqToHom.html), and we have not returned unscathed.