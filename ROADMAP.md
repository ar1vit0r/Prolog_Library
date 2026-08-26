# Roadmap

## Phase 1: Core Improvements
- [x] List notation `[H|T]` via `.` functor
- [x] Negation as failure (`\+`)
- [x] Built-in arithmetic (`is`, `+`, `-`, `*`, `/`)
- [x] Comparison operators (`=:=`, `<`, `>`, `=\\=`)
- [x] `=` unification built-in

## Phase 2: Example Library
- [x] List operations — `member`, `append`, `reverse`, `select`, `perm`
- [x] Graph reachability — `edge`, `path`, `connected` (recursive rules + backtracking)
- [x] Map coloring — constraint satisfaction via backtracking + negation
- [x] Fibonacci & factorial — recursive arithmetic
- [x] List length & sum — recursive list processing
- [ ] Symbolic differentiation — `deriv` with term manipulation
- [ ] Natural language mini-grammar — `sentence`, `noun_phrase`, `verb_phrase`

## Phase 3: Advanced Features
- [x] Cuts (`Cut` term in rule bodies)
- [x] Findall/bagof (collect all solutions into a list)
- [ ] Dynamic assert/retract (modify the database at runtime)
- [ ] Meta-interpreter (Prolog interpreter in Prolog)
- [ ] DCG (Definite Clause Grammar) notation

## Phase 4: Expand Tests
- [x] Parser tests — roundtrip `parseProg` → prettyPrint, syntax error cases
- [x] Edge cases — empty lists, nested lists, deep recursion, single-clause programs
- [x] Builtins — division by zero, `mod` by zero, `is` type mismatch, comparison on non-numeric atoms
- [x] `bagof` — test failure when no solutions (unlike `findall`)
- [x] Negation — `\+` on bound vars, nested `\+`, `\+` in rule bodies with cuts
- [x] `perm` — enumerate permutations, verify count
- [x] Error paths — `Left` results from `interpret`, malformed programs in `parseProg`
- [ ] Use `parseProg` for inline programs in tests instead of hand-built ASTs

## Phase 5: Legibility
- [x] Deduplicate `resolve` helper (3 identical copies in Interpret.hs → one shared)
- [ ] Remove `collectVars`, reuse `varsInTerm` from Unify
- [ ] Extract `evalBinop` to collapse 7 near-identical comparison builtins
- [ ] Add docstrings to key functions (`interpret`, `mergeSubst`, `eval`, `queryResult`)
- [ ] Add module-level doc comments to all modules
- [ ] Consolidate `Examples.myExample` / `Tests.familyProg` into single source of truth
- [ ] Extract fresh variable logic (`freshVarIO`, `freshenClauseIO`, `renameIO`) into `FreshVars` module
- [ ] Extract built-in handlers (`evalBuiltin`) from `interpret` into own section/module
- [ ] Comment `mergeSubst` and `unsafePerformIO` usage explaining the semantics
