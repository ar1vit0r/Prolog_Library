# Prolog_Library

A minimal Prolog interpreter written in Haskell. Implements unification, clause interpretation with backtracking, fresh variable generation, cuts, negation as failure, arithmetic, list notation, `findall`/`bagof`, and dynamic `assert`/`retract` (facts only).

## Build

```bash
cabal build
```

## Run

```bash
cabal run prolog-library
```

Or with GHCi:

```bash
ghci src/Term.hs src/Unify.hs src/Interpret.hs src/Examples.hs
```

## Modules

| Module | Purpose |
|--------|---------|
| `Term` | Core types: `Term`, `Clause`, `Prolog`, `Subst` |
| `Unify` | Robinson unification and substitution |
| `FreshVars` | Fresh-variable generation and alpha-conversion |
| `Parse` | Parsec-based parser for terms and clause databases |
| `Interpret` | Interpreter with backtracking, cuts, negation, and built-ins |
| `ListOps` | List predicates (`member`, `append`, `reverse`, `select`, `perm`) |
| `Graph` | Graph reachability example (`edge`/`path`/`connected`) |
| `Examples` | Genealogical tree database and sample queries |
| `Tests` | Unit tests covering every module above |

## Features

- **Unification**: standard Robinson unification with substitution
- **Backtracking**: depth-first search over the clause database
- **Cuts (`Cut`)**: commits to the current clause, prevents backtracking
- **Negation as failure (`\+`)**
- **Arithmetic**: `is`, comparisons, `+ - * / mod`
- **`findall`/`bagof`**: collect all solutions into a list
- **Dynamic `assert`/`assertz`/`asserta`/`retract`**: facts only
- **Fresh variables**: state-based alpha-conversion (no name collisions)
- **Failure reporting**: no matching clause is an empty solution list, not an error

## Example

```haskell
queryResult myExample (Func "pai" [Var "X", Atom "janeti"])
-- [("X","olicio")]
```

The `myExample` database models a family tree with `progenitor`, `sexo`, `mae`, and `pai` predicates.
