# hodgefermat

A small Lean 4 program that counts **Hodge classes on Fermat varieties** using
**Shioda's criterion**, and separates those that come from linear subspaces
("decomposable") from those that do not ("indecomposable").

It is a port of a Python reference implementation (`hodge_fermat_ht.py`) and uses only
the Lean core library and `Std` (no Mathlib).

> **What this is not.** The program does not prove or test the Hodge conjecture.
> It is a combinatorial calculator for the eigenspace decomposition described below.

## Background

Let

```
X = X_m^n :  x_0^m + x_1^m + ... + x_{n+1}^m = 0   in  P^{n+1},     n even,
```

be the Fermat variety of degree `m` and dimension `n`.

* The primitive middle cohomology `H^n_prim(X, C)` splits into one-dimensional
  eigenspaces `V(α)` under the action of `μ_m^{n+2} / μ_m` (Pham). They are indexed by
  tuples `α = (a_0, …, a_{n+1})` with `a_i ∈ {1, …, m-1}` and `Σ a_i ≡ 0 (mod m)`.
* Put `⟨α⟩ = Σ a_i / m` (an integer). `V(α)` has Hodge type `(p, q)` with
  `q = ⟨α⟩ − 1` and `p = n − q`.
* **Shioda's criterion.** `V(α)` consists of Hodge classes (type `(n/2, n/2)`, stable
  under Galois) if and only if
  `⟨tα⟩ = n/2 + 1` for every `t ∈ (Z/m)^*`,
  i.e. `Σ_i (t·a_i mod m) = (n/2 + 1)·m` for every unit `t`.
* `α` is **decomposable** if it can be split into pairs `{a, m − a}`. These classes come
  from linear subspaces contained in `X`.
* Everything else that satisfies Shioda's criterion is **indecomposable**: not explained
  by linear subspaces directly. This does **not** mean the class is non-algebraic.
  For example, the Hodge conjecture is known for `X_m^n` for all `n` when `m` is prime,
  `m = 4`, or `m ≤ 20` (Ran, Shioda), so such classes are algebraic there too; they
  just require other constructions.
* For `n = 2` the Picard number is `ρ = (number of Hodge classes) + 1`, the extra
  class being the hyperplane class.

## Requirements

Lean 4 (a recent release, ≥ 4.15 recommended; the code uses `List.flatMap` and
`Std.HashMap`).

## Build and run

Run directly with the interpreter:

```
lean --run HodgeFermat.lean selftest
lean --run HodgeFermat.lean hodge 4 2
lean --run HodgeFermat.lean list 6 4 --limit 3
lean --run HodgeFermat.lean table 2 30 --n 2
```

For large parameters, compile it instead (much faster than interpreting). Create a Lake
package and use `HodgeFermat.lean` as its `Main.lean`:

```
lake new hodgefermat
cp HodgeFermat.lean hodgefermat/Main.lean
cd hodgefermat
lake build
.lake/build/bin/hodgefermat table 2 30 --n 2
```

## Commands

| Command | Description |
|---|---|
| `selftest` | Runs built-in checks (K3 Hodge numbers, known Picard numbers, consistency checks). |
| `hodge m n` | Primitive Hodge numbers `h^{p,q}_prim` of `X_m^n`. |
| `list m n [--limit L]` | Counts, plus Galois-orbit representatives of indecomposable Hodge classes (default `L = 40`). |
| `table mlo mhi [--n N]` | Table for `m = mlo … mhi` (default `N = 2`). For `n = 2` it also prints the Picard number `rho`. |

Columns of `table`: `prim` = dimension of the primitive middle cohomology, `Hodge` =
number of Hodge classes in it, `decomp.` = decomposable ones, `indecomp.` = the rest.
All counts are numbers of *ordered* tuples `α`.

## Example output

The numbers below come from the Python reference implementation; the Lean version is
meant to reproduce them exactly.

`hodge 4 2` (Fermat quartic surface, a K3 surface):

```
X_4^2: primitive Hodge numbers
  h^(0,2)_prim = 1
  h^(1,1)_prim = 19
  h^(2,0)_prim = 1
  total primitive dimension = 21
```

`list 6 4 --limit 3`:

```
X_6^4: primitive dim=2605, Hodge classes=1751, decomposable (linear subspace)=1001, indecomposable=750
Indecomposable Galois-orbit representatives (4 total, first 3):
  alpha=(1, 1, 3, 4, 4, 5)  (this orbit family: 360 ordered alphas)
  alpha=(1, 1, 4, 4, 4, 4)  (this orbit family: 30 ordered alphas)
  alpha=(1, 2, 3, 4, 4, 4)  (this orbit family: 240 ordered alphas)
  ...
```

`table 2 12 --n 2`:

| m | prim | Hodge | decomp. | indecomp. | rho |
|--:|-----:|------:|--------:|----------:|----:|
| 2 | 1 | 1 | 1 | 0 | 2 |
| 3 | 6 | 6 | 6 | 0 | 7 |
| 4 | 21 | 19 | 19 | 0 | 20 |
| 5 | 52 | 36 | 36 | 0 | 37 |
| 6 | 105 | 85 | 61 | 24 | 86 |
| 7 | 186 | 90 | 90 | 0 | 91 |
| 8 | 301 | 175 | 127 | 48 | 176 |
| 9 | 456 | 216 | 168 | 48 | 217 |
| 10 | 657 | 361 | 217 | 144 | 362 |
| 11 | 910 | 270 | 270 | 0 | 271 |
| 12 | 1221 | 643 | 331 | 312 | 644 |

`selftest` checks, among other things, that `m = 4, n = 2` gives the K3 Hodge numbers
above, that the Picard numbers for `m = 3, 4, 5, 7` are `7, 20, 37, 91`, that every
decomposable `α` satisfies Shioda's criterion, and that no indecomposable Hodge class
appears for prime `m` when `n = 2`.

## Limitations

* The number of multisets grows quickly with `m` and `n` (roughly `C(m + n, n + 2)`),
  so large parameters are slow, especially with the interpreter.
* Arguments are natural numbers; invalid parameters (`m < 2`, odd `n`, `n < 2`) are
  rejected with an error. Extra command-line arguments are ignored.
* "Indecomposable" is a statement about linear subspaces only; see the note above.

## References

* T. Shioda, *The Hodge conjecture for Fermat varieties*, Math. Ann. **245** (1979), 175–198.
* Z. Ran, *Cycles on Fermat hypersurfaces*, Compositio Math. **42** (1980), no. 1, 121–142.
* G. da Silva Jr., *Notes on the Hodge conjecture for Fermat varieties*,
  arXiv:2101.04739.

## License

MIT; see [LICENSE](LICENSE).
