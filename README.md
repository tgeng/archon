# Archon

An experimental language that tries to combine dependent type, lexical algebraic effects & handlers,
and quantitative types.

## Design

Overall the core type theory is a mixture of

* [EMLTT of Danel Ahman](https://dl.acm.org/doi/10.1145/3371126)
* [Effect instance of Dariusz Biernacki et al.](https://dl.acm.org/doi/10.1145/3371116)
* A
  specialized [graded modal dependent type theory of Andras et al.](https://dl.acm.org/doi/10.1145/3607862)

The type checker supports meta variable and unification is implemented based on the [Agda
paper](https://www.cse.chalmers.se/~ulfn/papers/thesis.pdf) by Norell.

On top of that, inductive type and co-pattern matching is implemented based
on [Elaborating dependent
(co)pattern matching](https://dl.acm.org/doi/10.1145/3236770) from Jesper Cockx et al.

For detailed design, one can check
out [term.scala](src/main/scala/com/github/tgeng/archon/core/ir/term.scala) for core type theory IR
and [typing.scala](src/main/scala/com/github/tgeng/archon/core/ir/typing.scala) for the type
checker.

## Progress

✅ completed | 🚧 under construction | 💡 planned

* [🚧] Core type theory
    * [✅] IR
    * [🚧] Type checker
        * [✅] Normalization and conversion
        * [✅] Subtyping
        * [✅] Meta variable unification
        * [✅] Escape analysis to detect effect instance leak
        * [💡] Totality checker
        * [💡] Proof searcher
        * [💡] Nominal subtyping of records and effects
    * [✅] Function elaboration
* [🚧] Low-level IR
    * [🚧] LIR ([Archon VM](https://github.com/tgeng/archon-vm)) - need to adopt lexical effects
    * [💡] IR -> LIR lowering
    * [💡] Primitives
* [💡] Frontend IR (User language)
    * [💡] [Mix-fix parser](https://www.cse.chalmers.se/~nad/publications/danielsson-norell-mixfix.pdf)
    * [💡] FIR -> IR lowering
        * [💡] Type class via record and proof search
        * [💡] Type-driven resolution? (likely limited to only certain heuristics)
* [💡] Standard library