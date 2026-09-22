# HasKLogiX: a Haskell-embedded DSL for Prolog programming

Summary of the two academic works in this directory, both by Ari Vitor da Silva Lazzarotto, advised by Prof. Dr. André Rauber Du Bois (Universidade Federal de Pelotas, Centro de Desenvolvimento Tecnológico):

- `TCC_Ari_Vitor_Lazzarotto_final.pdf`: undergraduate thesis (Trabalho de Conclusão de Curso), "Uma DSL embutida em Haskell para programação Prolog", defended 2023-05-15.
- `Artigo_WEIT_02_09_23.pdf`: condensed paper, "HasKLogiX: Uma DSL embutida em Haskell para programação Prolog", dated 2023-10-02.

Both describe the original version of this repository. The summary below reflects what they claimed *at the time they were written*; see the top-level `ROADMAP.md` for the project's current state.

## Motivation

Functional and logic languages are both declarative, but emphasize different strengths: functional languages (Haskell) offer clear semantics, lazy evaluation, and higher-order functions; logic languages (Prolog) offer non-determinism and multi-directional predicates, which favor code reuse. The work combines both paradigms in a single Haskell program: a Prolog interpreter written as a Domain-Specific Language embedded in Haskell, so a programmer writes Prolog-style facts and rules as Haskell data and queries them with a Haskell function.

## Theoretical background (thesis, chapter 2)

The thesis covers, in more depth than the paper:

- Declarative programming: contrasts imperative (C) and functional (Haskell) implementations of the same algorithm to motivate why functional/logic styles were chosen.
- Unification: presents the Martelli-Montanari algorithm (six-rule term-rewriting system over equation sets) for computing a most general unifier (MGU), including the occurs-check case.
- SLD resolution: explains Prolog's operational semantics as Selective (leftmost literal), Linear (each step uses the previous resolvent), Definite-clause resolution, illustrated with an SLD tree for a `likes/based` example program, plus a case showing SLD resolution is refutation-complete but Prolog's specific leftmost-depth-first search strategy is not (clause order can turn a solvable query into an infinite branch).

## Design

Two core Haskell types drive the whole interpreter:

```haskell
data Term = Var String | Atom String | Func String [Term]
data Clause = Term :- [Term] | Simple Term
type Prolog = [Clause]
```

A `Term` is a variable, an atom, or a function/compound term. A `Clause` is either a fact (`Simple`) or a rule (head `:-` body). A `Prolog` program is just a list of clauses. Substitutions are represented as association lists (`[(String, Term)]`) rather than a `Map`, a deliberate simplicity/performance tradeoff the thesis flags explicitly as a place a `HashMap` would help for large queries.

The core functions, as originally specified:

- `unify :: Term -> Term -> Subst` (returning `Nothing` on failure, i.e. effectively `Maybe Subst`)
- `substituteAll :: [(String, Term)] -> Term -> Term`
- `interpret :: Prolog -> Term -> Subst` (also effectively `Maybe Subst`): walks the program, unifying clause heads with the query, recursing into rule bodies (`interpretBody`), and backtracking to the next clause on failure
- `queryResult :: Prolog -> Term -> [(String, String)]`: renames query variables via alpha-conversion first (avoiding capture with the program's own variables), calls `interpret`, then filters the resulting substitution down to just the query's own variables, pretty-printed

An example from the paper: given a `parent/2` fact database, `queryResult myExample1 (Func "parent" [Var "X", Atom "james"])` returns `[("X","arne")]`.

## Related work (paper, section 2)

The paper cites Prolog-interpreter-in-Haskell projects found on GitHub (`hspl`, `propella/prolog`, monadic implementations `Erdwolf/prolog`, `cimbul/hasklog`) and the paper "Embedding Prolog in Haskell" (Spivey and Seres, 1999 Haskell Workshop), which takes a different approach: translating each Prolog predicate into a Haskell function over lazy lists, rather than interpreting a Prolog AST.

## Stated limitations (as of 2023)

Both works explicitly scope out, as future work:

- Cuts (`!`)
- Negation as failure (`\+`)
- More advanced control structures (if-then-else, while-style loops)
- No syntax validation: a malformed clause or query term raises a runtime error rather than a parse error
- A translator from concrete Prolog syntax into the DSL's Haskell AST (i.e., no parser at all yet at this stage; programs are written directly as Haskell values)

All of these, plus arithmetic, list notation, `findall`/`bagof`, and dynamic `assert`/`retract`, have since been implemented in this repository; see `ROADMAP.md` for the up-to-date checklist.

## References

The bibliography (shared substantially between both works) draws on: Antoy (2005, evaluation strategies for functional logic programming), Antoy and Hanus (2010, *Commun. ACM*, functional logic programming), Fernández (2004, *Programming Languages and Operational Semantics*, the source of the unification and SLD-resolution algorithms used), Martelli and Montanari (1982, *TOPLAS*, the unification algorithm), Roussel (1975, the original Prolog reference manual), Spivey and Seres (1999, embedding Prolog in Haskell), and Wielemaker et al. (2012, *TPLP*, SWI-Prolog).
