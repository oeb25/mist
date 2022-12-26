# 🍃 Mint

> Mint is the inprogress codename for my master thesis: A language and editor experience for working with formal program verification, with high focus on usability, user-friendliness, error reporting, and quality-of-life feature.

## Project summary

Mint is a language that builds on the work done by previous formal verifications stacks such as [Viper](https://viper.ethz.ch/). The intent of the language is to offer the same level of control as Viper, but to ease the experience of working with the language and toolchain as a whole. The primary focus will be to guide the user towards correct specifications, by providing tools to avoid strange situations and errors, and help the user when such situations inevitably occur.

## Project goals

The idea of the project stems from my own experience learning about formal verification and the ecosystem as a whole, and from the issues I've observed from my fellow students when working with the tools as well.

The following is a list of ideas for areas of improvements and alterations, which have the objective of bringing the project closer to its goals:

- Totality checking
  - Total correctness for while loops and methods.
  - When possible, find variants automatically and show without user intervention.
- Auto infer bounds in loop invariants
  - In programs such as `while (i < n) { i := i + 1 }`, finding the bounds of the loop variable and adding them as invariants automatically, such as `while (i < n) invariant i <= n { i := i + 1 }`, provides stronger guarantees after the loop body.
- Function injectivity by annotation or inferred
- Explicit ghost code
    - Variable, methods, arguments, fields, should all be able to have an added `ghost` annotation and then have this guarantee checked statically.
    - It remains to show whether annotating types, statements, both, or something different will be the best approach.
- Execution of code
    - Not only should the language be a specification language, it should also have rudimentary execution of the code.
    - Whether the code is interpreted or translated into some other language remains to be shown.
    - The implications of the are quite large, and could possibly allow for features that are not possible to plain Viper.
- Fuzzing/quickchecking the code for fast feedback
    - Formal verification is great for proving the absence of bugs, but in some cases the bugs are plainly obvious but still hard for the verifier to communicate to the user, and the time needed to find these errors are sometimes less than ideal.
    - Fuzzing provides an alternative to this, by quickly trying a vast number of inputs to you methods, and might quickly uncover some edge case. Here it will use the execution provided in the last point.
    - Additionally, as the errors occur from a concrete instantiation of the variables, they constitute counter-examples as well as stacktraces, which are perfect for debugging!
- Abstract data types
    - ... might be over kill, but some variant of `struct` and `enum` would be great for usability.
    - These would have ghost fields and invariants.
- Quantifier pattern/trigger hints
    - Finding a good pattern for quantifiers is an art form, or at least so I've been told as I've yet to successfully specify anything non-trivial with them.
    - There might be cases where recognizable structures in the case that hints towards some pattern, which the language then can either implicitly add, or suggest a quick-fix for adding it.
    - Also in cases where the SMT solver might discover some pattern for a quantifier, adding an inlay hint or providing a quick-fix for adding it explicitly to the code has benefits:
        - Explicitly convey to the user what patter solves the problem. This can aid in the users learning experience, and they might be able to infer some patters when they encounter issues with patters at a later stage. (The word "pattern" is overloaded...)
        - Speedup the searching by the SMT solver/direct it towards the correct solutions. This could reduce some non-determinism during verification.
- Type inference
    - Letting the user do `var x := 12` instead of `var x: Int := 12` is just a small nicety.
- Loosen the constraints on expression/instantiation/declaration/definition cases
    - Allow expressions such as `var x := new(*)` and `var x := my_method()`.
- Provide sugar for common permission patterns
    - This could include having references, where the exact given permission is automatically given back at the end of the scope (like RAII).
    - In some cases, where a method might be called recursively, this might require halving the permission at each recursive call, sort of like an implicitly added ghost argument.
