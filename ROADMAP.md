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
