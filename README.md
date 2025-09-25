# Closed normal form (CNF)

Idea:
* Define constrained beta reduction: Only applies if the subexpression it operates on (must be an application) is closed.
* Induces normal form (CNF): Fully reduced as per constrained beta reduction.
* Constrained beta reduction mirrors reduction of corresponding SKI terms (example that this is not the case for unconstrained beta reduction: `λx.(λy.y) (x x)` which translates to something like `S (K I) (S I I)`)
* CNF analogous to (full) NF of corresponding SKI term

Benefits:
* TLDR: CNF more useful than BNF and HNF
* Recursive functions can be in CNF (impossible for BNF)
* Recursive functions can also be in HNF, but HNF is terrible to define equality (not modular, counterexample: Let `id1 := \x.x`, `id2 := id1 id1`, `foo := \f.\g.g f` then `id1 == id2` but not `foo id1 == foo id2`). CNF on the other hand may induce an equality relationship as useful/strong as BNF, but able to reason about recursive functions.
* Should pave the way for an "intensional" LC where triaging on an expression forces it into CNF. (Wouldn't be confluent without forcing into some NF. BNF would diverge on introspection of recursive functions. HNF would also diverge on recursive introspection of recursive function because recursively applied HNF is BNF.)

Theorems:
* (cl1 --> cl2) => ([cl1] -->* [cl2])
* TODO: (lc1 --> lc2) => ([lc1] -->* [lc2])
* TODO: CNF > BNF (trivial), but is there also some relationship between (W)HNF and CNF?

Visualization ideas:
* Side-by-side reduction of CL and LC, translation arrows