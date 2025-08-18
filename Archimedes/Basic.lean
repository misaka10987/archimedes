import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct


namespace A

/--
A point (vector) in a 3-dimensional Euclidean space.
For declaring a point, simply use `p : Point`.

This is an alias for Mathlib's `EuclideanSpace ℝ (Fin 3)`,
and thus has exactly the same behaviour.

# Component Convention

Traditionally,
$x$, $y$ and $z$ is usually used to name the components of a 3-dimensional vector.
Since `EuclideanSpace ℝ (Fin 3)` is in fact a function from `Fin 3` to `ℝ`,
and components are accessed with function call,
for consistency, it is specified here that for `p : Point`:
- `p 0` is the $x$ component;
- `p 1` is the $y$ component;
- `p 2` is the $z$ component.
-/
abbrev Point := EuclideanSpace ℝ (Fin 3)


infix:69 "⬝" => inner ℝ

/--
Naive definition of dot product of 3-dimensional vectors,
i.e. sum of product of corresponding components.
-/
theorem dot (v w : Point) : v ⬝ w = v 0 • w 0 + v 1 • w 1 + v 2 • w 2 := by
  simp [Inner.inner, Fin.sum_univ_succ]
  ring


infix:69 "⨯" => crossProduct


/--
Naive definition of cross product of 3-dimensional vectors.
-/
theorem cross (v w : Point)
: v ⨯ w = ![v 1 • w 2 - v 2 • w 1, v 2 • w 0 - v 0 • w 2, v 0 • w 1 - v 1 • w 0 ]
:= by
  simp [crossProduct]


/--
Naive definition of normal of 3-dimensional vector,
i.e. square root of sum of components squared.
-/
theorem norm (v : Point) : ‖v‖ = √ (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
  simp [Norm.norm, Fin.sum_univ_succ, Real.sqrt_eq_rpow]
  ring_nf

/--
Square of normal of a vector, or sum of square of components, is non-negative.
-/
theorem sq_norm_nn (v : Point) : 0 ≤ v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  repeat first | apply add_nonneg | apply sq_nonneg

/--
Square of normal of a vector equals to the sum of square of components.
-/
theorem sq_norm (v : Point) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  simp [norm, Real.sq_sqrt (sq_norm_nn v)]

/--
A vector dot products itself equals square of its normal.
-/
theorem sq_norm_eq_dot_self (v : Point) : ‖v‖ ^ 2 = v ⬝ v := by
  simp [dot, norm, pow_two]
  rw [←Real.sqrt_mul, Real.sqrt_mul_self]
  repeat first | apply add_nonneg | apply mul_self_nonneg


/--
The origin point, or $(0,0,0)$.
-/
abbrev o : Point := 0

/--
The origin is zero vector.
-/
@[simp]
lemma zeros_eq_origin : ![0, 0, 0] = o := by simp


/--
The unit vector on $x$ axis.
-/
abbrev x : Point := ![1, 0, 0]

/--
The unit vector on $y$ axis.
-/
abbrev y : Point := ![0, 1, 0]

/--
The unit vector on $z$ axis.
-/
abbrev z : Point := ![0, 0, 1]


/--
Unit vector of a specific vector.
Defined as `x`, or $(1, 0, 0)$ for zero vector.
-/
noncomputable def unit (v : Point) : Point :=
  if ‖v‖ = 0 then x else (1 / ‖v‖) • v


/--
The normal of a unit vector always equals to $1$.
-/
@[simp]
lemma norm_unit_is_one (v : Point) : ‖unit v‖ = 1 := by
  simp [unit]
  by_cases h: v = 0
  · simp [h, norm]
  · simp [h, norm_smul]

/--
A vector dot products its unit vector equals its normal.
-/
theorem dot_unit_eq_norm (v : Point) : v ⬝ unit v = ‖v‖ := by
  simp [unit, dot]
  by_cases h : v = 0
  · simp [h]
  · simp [h]
    have : ‖v‖ ≠ 0 := fun hh ↦ h (norm_eq_zero.mp hh)
    field_simp
    simp [norm]
    ring_nf
    simp [Real.sq_sqrt (sq_norm_nn v)]

end A
