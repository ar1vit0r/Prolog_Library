# Prolog_Library

A minimal Prolog interpreter written in Haskell. Implements unification, clause interpretation with backtracking, fresh variable generation, cuts, and error reporting.

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
| `Interpret` | Interpreter with backtracking and cuts |
| `Examples` | Genealogical tree database and sample queries |
| `Tests` | Unit tests for unification, substitution, and queries |

## Features

- **Unification**: standard Robinson unification with substitution
- **Backtracking**: depth-first search over the clause database
- **Cuts (`Cut`)**: commits to the current clause, prevents backtracking
- **Fresh variables**: state-based alpha-conversion (no name collisions)
- **Error reporting**: `Either String` results with failure messages

## Example

```haskell
queryResult myExample (Func "pai" [Var "X", Atom "janeti"])
-- [("X","olicio")]
```

The `myExample` database models a family tree with `progenitor`, `sexo`, `mae`, and `pai` predicates.
