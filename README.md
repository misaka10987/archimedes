# Archimedes

> Don't disturb my circle!

![GitHub License](https://img.shields.io/github/license/misaka10987/archimedes)
![GitHub Actions Workflow Status](https://img.shields.io/github/actions/workflow/status/misaka10987/archimedes/lean_action_ci.yml)
![GitHub commit activity](https://img.shields.io/github/commit-activity/m/misaka10987/archimedes)

*Archimedes* is a mathematics library specifically for Euclidean geometry in a 3-dimensional Euclidean space. It provides intuitive, non-abstract definitions of geometrical concepts while trying to maximize interoperability with [Mathlib](https://github.com/leanprover-community/mathlib4).

## Install

In `lakefile.toml`:

```toml
[[require]]
scope = "misaka10987"
name = "archimedes"
rev = "main"
```

Use in your code:

```lean4
import Archimedes
```

## Why Archimedes

Mathlib is a great project with generalized support for various types of geometries. However, a considerable proportion of geometrical topics appear to be within 2 or 3 dimensional Euclidean space. While mathlib guarantees generality, it takes a bit extra work to deal with those common geometric objects.

```lean4
variable
  {V : Type*} {P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
```

Moreover, there exists enormous geometric results that is developed within the Euclidean space which describes our macroscopic slow-speed universe, and, mathlib, either because such properties does not hold, becomes trivial, in other spaces, or they are irrelevant with modern geometry studies, does not include these theories.

Archimedes tries to offer a solution for that. By limiting its range of application, it is able to include more geometric theorems, as well as providing more domain-specific definitions for writing proofs that is easy to use. If you prefer these features:

- batteries-included definitions

- based on vector space $\mathbb R^n$ instead of Euclid's postulates

- interoperable with Mathlib via `EuclideanSpace ℝ (Fin 3)` 

- use purely geometric method and vector method at the same time

then Archimedes would probably be suitable for you.
