# constraint microKanren

This repository contains the Racket reference implementation of constraint microKanren. It is the implementation repository cited by both versions of *A Framework for Extending microKanren with Constraints*; it is not a manuscript-source repository.

## Papers

Jason Hemann and Daniel P. Friedman:

- [Scheme and Functional Programming Workshop version (2015)](https://www.schemeworkshop.org/2015/sfpw3-2015-hemann-friedman.pdf)
- [Expanded WFLP 2016 version, published in EPTCS 234 (2017)](https://doi.org/10.4204/EPTCS.234.10)

Both papers direct readers to `github.com/jasonhemann/constraint-microKanren` for the implementation. The manuscript sources are maintained separately as private archival repositories with independent Git histories:

- [Scheme Workshop 2015 manuscript source](https://github.com/jasonhemann/constraint-microkanren-scheme-2015) (private)
- [WFLP 2016 manuscript source](https://github.com/jasonhemann/constraint-microkanren-wflp-2016) (private)

## Files

- [`paper-code.rkt`](paper-code.rkt) — the core framework and example constraint system, originally added from the paper and subsequently corrected.
- [`usage.rkt`](usage.rkt) — miniKanren syntax wrappers, example relations, and RackUnit checks.
- [`single-file-system.rkt`](single-file-system.rkt) — a later, self-contained version of the system with additional miniKanren forms and utilities.
- [`LICENSE`](LICENSE) — the MIT License.

## Running the examples

With [Racket](https://racket-lang.org/) installed:

```sh
raco test usage.rkt
```

`usage.rkt` loads `paper-code.rkt` and runs the included `membero` and relational type-inference examples with their RackUnit checks.

## Provenance

Commit [`b772935`](https://github.com/jasonhemann/constraint-microKanren/commit/b772935990b014c600bd506409e3fe0e4d39355d) added `paper-code.rkt` and `usage.rkt` as code from the paper and accompanying examples. Later commits added the single-file version and corrections. Consequently, the current `master` branch is not a frozen snapshot of either paper.

## License

Copyright © 2015 Jason Hemann. Released under the [MIT License](LICENSE).
