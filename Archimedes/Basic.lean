import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct


namespace A

/--
A point (vector) in a 3-dimensional Euclidean space.
For declaring a point, simply use `p : Point`.

This is an alias for Mathlib's `EuclideanSpace ℝ (Fin 3)`,
and thus has exactly the same behaviour.
-/
abbrev Point := EuclideanSpace ℝ (Fin 3)

namespace Point

/--
The x-component of the vector, defined as `self 0` .
-/
@[simp]
abbrev x (self : Point) : ℝ := self 0

/--
The y-component of the vector, defined as `self 1` .
-/
@[simp]
abbrev y (self : Point) : ℝ := self 1

/--
The z-component of the vector, defined as `self 2` .
-/
@[simp]
abbrev z (self : Point) : ℝ := self 2

/--
The dot product.
-/
@[simp]
noncomputable abbrev dot (self : Point) (v : Point) : ℝ :=
  Inner.inner ℝ self v

/--
The dot product.
-/
infix:69 "∘" => dot

/--
The cross product.
-/
@[simp]
abbrev cross (self : Point) (v : Point) : Point :=
  crossProduct self v

/--
The cross product.
-/
infix:69 "⨯" => cross

/--
Naive definition of dot product of 3-dimensional vectors,
i.e. sum of product of corresponding components.
-/
theorem inner_product (v w : Point) : v ∘ w = v.x • w.x + v.y • w.y + v.z • w.z := by
  simp [Inner.inner, Fin.sum_univ_succ]
  ring

/--
Naive definition of cross product of 3-dimensional vectors.
-/
theorem vector_product (v w : Point)
: v ⨯ w = ![ v.y • w.z - v.z • w.y, v.z • w.x - v.x • w.z, v.x • w.y - v.y • w.x ]
:= by
  simp [crossProduct]

/--
A vector's inner product with itself $\left< \mathbf v, \mathbf v \right>$ is non-negative.
-/
theorem dot_self_nn (v : Point) : 0 ≤ v ∘ v := by
  simp [inner_product]
  repeat first | apply add_nonneg | apply mul_self_nonneg

end Point

/--
Naive definition of normal of 3-dimensional vector,
i.e. square root of sum of components squared.
-/
theorem norm (v : Point) : ‖v‖ = √ (v.x ^ 2 + v.y ^ 2 + v.z ^ 2) := by
  simp [Norm.norm, Fin.sum_univ_succ, Real.sqrt_eq_rpow]
  ring_nf

/--
Square of normal of a vector, or sum of square of components, is non-negative.
-/
theorem sq_norm_nn (v : Point) : 0 ≤ v.x ^ 2 + v.y ^ 2 + v.z ^ 2 := by
  repeat first | apply add_nonneg | apply sq_nonneg

/--
Square of normal of a vector equals to the sum of square of components.
-/
theorem sq_norm (v : Point) : ‖v‖ ^ 2 = v.x ^ 2 + v.y ^ 2 + v.z ^ 2 := by
  simp [norm, Real.sq_sqrt (sq_norm_nn v)]

/--
A vector dot products itself equals square of its normal.
-/
theorem sq_norm_eq_dot_self (v : Point) : ‖v‖ ^ 2 = v ∘ v := by
  simp [Point.inner_product, norm, pow_two]
  rw [←Real.sqrt_mul, Real.sqrt_mul_self]
  repeat first | apply add_nonneg | apply mul_self_nonneg


/--
The origin point, or $(0, 0, 0)$.
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
theorem dot_unit_eq_norm (v : Point) : v ∘ unit v = ‖v‖ := by
  simp [unit, Point.inner_product]
  by_cases h : v = 0
  · simp [h]
  · simp [h]
    have : ‖v‖ ≠ 0 := fun hh ↦ h (norm_eq_zero.mp hh)
    field_simp
    simp [norm]
    ring_nf
    simp [Real.sq_sqrt (sq_norm_nn v)]

end A
