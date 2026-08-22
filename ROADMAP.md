# Roadmap

## Phase 1: Core Improvements
- [ ] List notation `[H|T]` via `.` functor
- [ ] Negation as failure (`\+`)
- [ ] Built-in arithmetic (`is`, `+`, `-`, `*`, `/`)
- [ ] Comparison operators (`=:=`, `<`, `>`, `=\\=`)

## Phase 2: Example Library
- [ ] List operations — `member`, `append`, `reverse`, `flatten`, `length`
- [ ] Graph reachability — `edge`, `path`, `reachable` (recursive rules + backtracking)
- [ ] Symbolic differentiation — `deriv` with term manipulation
- [ ] Natural language mini-grammar — `sentence`, `noun_phrase`, `verb_phrase`
- [ ] Map coloring — constraint satisfaction via backtracking
- [ ] Permutation — `perm`, `remove` (elegant backtracking showcase)

## Phase 3: Advanced Features
- [ ] Cuts in rule bodies (`!` as a goal, not just `Cut` term)
- [ ] Findall/bagof (collect all solutions into a list)
- [ ] Dynamic assert/retract (modify the database at runtime)
- [ ] Meta-interpreter (Prolog interpreter in Prolog)
- [ ] DCG (Definite Clause Grammar) notation
