# Prolog_Library

A minimal Prolog interpreter written in Haskell. Implements unification, clause interpretation with backtracking, and variable renaming (alpha-conversion).

## Usage

```bash
ghci Prolog_Library.hs
```

Then call `main` to run the built-in genealogical tree examples, or use `queryResult` directly:

```haskell
queryResult myExample (Func "mae" [Var "Y", Atom "ari_vitor"])
```

## How it works

- **Terms**: `Var` (variable), `Atom` (constant), `Func` (compound term with arguments)
- **Clauses**: facts (`Simple t`) or rules (`t :- [body]`)
- **Unification**: standard Robinson unification (`unify`)
- **Interpretation**: depth-first search with backtracking over the clause database
- **Alpha-conversion**: renames variables with `øVAR` suffix to avoid capture

## Example queries

The included `myExample` database models a family tree with `progenitor`, `sexo`, `mae`, and `pai` predicates.
