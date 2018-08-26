- check epr graph
- switch to POD representation of expressions -- i hate oop
- inductive generalization
- model minimization?
- phase automata
- support functions
- somehow use heuristic "first frame that contains no initial condition"
- implement smarter unsat core minimization using binary search
- generalization heuristic: eliminate mutable conjuncts first
- refactor remaining AST methods to pattern-matching style
    - resolve
    - pretty printer
- restore alpha-equivalence in __eq__ and __hash__ by introducing auxilliary
  method uses a scope to track binding of local variables only, and treats free
  symbols as compare-by-name
- implement modules, which we really want for functors, which we use as a kind of macro
    - proposed module declaration syntax:
        module total_order(t: sort, r: relation (t, t))
          axiom r(X,X)                        # Reflexivity
          axiom r(X, Y) & r(Y, Z) -> r(X, Z)  # Transitivity
          axiom r(X, Y) & r(Y, X) -> X = Y    # Anti-symmetry
          axiom r(X, Y) | r(Y, X)             # Totality
        end
      which declares a module parametrized by a sort t and a binary relation r over t.
      Note that type checking the parameters to a module is a sort of telescope,
      and that when type checking the body of a module, the parameters are in scope.
      So the Scope class will have to have a notion of stack for more than just
      local variables.
    - proposed instantiation syntax:
        sort node
        relation le(node, node)
        instantiate total_order(node, le)
    - things to think about:
      - nested modules?
      - logical ordering of declarations in a file
          - right now the order is: sorts, relations/functions/constants, everything else
          - modules don't fit nicely anywhere, since we might want to instantiate a module
            that declares a sort that we then use in a later relation's arity,
            but on the other hand we might want to pass a relation into an instantiation.
      - can module bodies refer to things in scope from outer modules?
          - this makes the ordering problem even harder
      - when module body includes named declarations, how are those names used via
        instantiation?
      - can we bring the functor-argument type ascription syntax closer in line with
        the top-level declaration syntax? right now its
            r: relation (t, t)
        versus
            relation r(t, t)

        Would there be anything wrong with
            module total_order(sort t, relation r(t, t))
        ? In other words, syntax is identical, and we just separate with commas to emphasize
        that declarations are ordered for both telescoping and instantiation-argument purposes.

    - maybe a first pass at modules is:
      - are always functors (ie, even those that take zero parameters must be instantiated
      - only allowed to declare things without names, like axioms.
      - heck, for now, just axioms


- implement derived relations (aka definitions) as z3-translation-time macros
- collect several counterexamples before blocking
    - ask hypothetical questions "if I blocked this diagram, would the conjunct push?"
    - but this is hard, because diagrams are generalized only near the end of blocking them
    - so before we block (and thus generalize) we only have a very specific diagram
      that won't be that helpful in ruling out states.
    - still, might be useful to collect several such diagrams

- can we generalize diagrams *before* we try to block?
    - given a two-state countermodel showing how to violate a conjecture
      by stepping from the previous frame, can we generalize the (prestate of the) model
      such that it is still a valid counter model, but contains fewer conjuncts?
    - what exactly is the condition that we maintain during generalization?
      well, for soundness, we need to know that the prestate remains definitely unsafe.
      so if we have a generalized ("partial") prestate model thing, we want to say
      that in *every* completion of the model, there is a transition that violates safety.

- think about hierarchical logging, so that diffs will be more accurate
    - find good tree diff algorithm (json?)