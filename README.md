# Complexity Theory in Lean

This repository defines and proves lemmas about the class of polynomial time functions.
It also introduces a tactic in `polytime_tac.lean` which tries to automatically prove that
functions run in polynomial time.

## Implementation

The basic implementation is based of the structure of `to_partrec.code` [in mathlib]( https://github.com/leanprover-community/mathlib/blob/master/src/computability/tm_to_partrec.lean) and
the start of [BoltonBailey's PR](https://github.com/leanprover-community/mathlib/pull/11046).

However, one key difference is that rather than using `list ℕ` as the main data structure, we use `ptree` ("plain tree"), which is a binary tree with no data
attached to the leaves (defined in `plain_tree.lean`):

```lean
inductive ptree
| nil
| node (left : ptree) (right : ptree)
```

The main reason for this is that otherwise, we would need a pairing function $\mathbb{N} \times \mathbb{N} \rightarrow \mathbb{N}$ with logarithmic overhead
(I worked on this for a bit [here](https://github.com/leanprover-community/mathlib/pull/13213), but I eventually got fed up with it, and `ptree` is much easier to use).

## Structure

There are a few files containing essentially dead code that need to be cleaned up. The files of interest are:
  - `code.lean` -- Defines the code model
  - `plain_tree.lean` -- Defines `ptree`, a plain binary tree with no data
  - `time_bound.lean` -- Defines what it means for a code `c` to run in time $T(n)$
  - `polytime.lean` -- Very short file that specializes the lemmas from `time_bound` to the case of polynomial bounds.
  - `polycodable_init.lean` -- Defines `polycodable` and `polytime_fun`.
      In general, functions on other types $f : \alpha \rightarrow \beta$ are said to run in polynomial time
      if they have an encoding to `ptree` (many encodings e.g. unit, bool, pair, list, are defined in `plain_tree.lean`), and
      there is a code which runs in polynomial time and equals the function under this encoding. The encoding being a `polycodable`
      is the stronger property that `encode (decode x)` runs in polynomial time .This file sets up some basic
      definitions that the tactic depends on.
  - `polytime_tac.lean` -- A tactic, `polyfun`, to automatically discharge goals of the form `polytime_fun f`.
  - `polycodable.lean` -- Proves many more encodings are `polycodable` using `polyfun`
  - `polysize.lean` -- Defines predicates `polysize_fun`, `polysize_fun_safe`, and `polysize_fun_uniform` which are each some variant
    of the fact that some function's growth is bounded by a polynomial in the input (possibly uniformly with respect to another input).
  - `polyfix.lean` -- Proves that repeatedly evaluating a polynomial time function $f : \sigma \rightarrow \sigma$ polynomially many times such that the
    state $\sigma$ doesn't grow to fast results in a polynomial time function.
  - `lists.lean` -- Shows that many functions about lists run in polynomial time.
  - `nat.lean` -- Shows that addition and multiplication of numbers encoded as bits run in polynomial time.
  
## Example of the tactic




