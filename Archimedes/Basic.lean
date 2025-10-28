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
abbrev x (self : Point) : ℝ := self 0

/--
The y-component of the vector, defined as `self 1` .
-/
abbrev y (self : Point) : ℝ := self 1

/--
The z-component of the vector, defined as `self 2` .
-/
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
  nlinarith

/--
The length, or norm of the vector.
-/
noncomputable abbrev len (v : Point) : ℝ := ‖v‖

/--
Naive definition of norm of 3-dimensional vector,
i.e. square root of sum of components squared.
-/
theorem norm (v : Point) : ‖v‖ = √ (v.x ^ 2 + v.y ^ 2 + v.z ^ 2) := by
  simp [Norm.norm, Fin.sum_univ_succ, Real.sqrt_eq_rpow]
  ring_nf

/--
The length, or norm of the vector is non-negative.
-/
theorem len_nn (v : Point) : 0 ≤ ‖v‖ := by
  simp [norm]

/--
A vector dot products itself equals square of its normal.
-/
theorem sq_norm_eq_dot_self (v : Point) : ‖v‖ ^ 2 = v ∘ v := by
  simp [norm, inner_product, ←pow_two]
  rw [Real.sq_sqrt]
  positivity

/--
The unit vector of a specific vector.
Note that this is undefined for zero vector.
-/
noncomputable def unit (self : Point) : Point :=
  (1 / ‖self‖) • self

/--
The norm of a unit vector, if defined, is $1$ .
-/
@[simp]
theorem unit_norm_one (v : Point) (nonzero : v ≠ 0) : ‖v.unit‖ = 1 := by
  simp [unit, norm_smul]
  field_simp

/--
A vector's length equals dot product with its unit vector.
-/
theorem len_dot_unit (v : Point) (nonzero : v ≠ 0) : ‖v‖ = v ∘ v.unit := by
  simp [unit, norm, inner_product]
  have : ‖v‖ ≠ 0 := fun h ↦ nonzero (norm_eq_zero.mp h)
  rw [norm] at this
  field_simp
  rw [Real.sq_sqrt]
  positivity

end Point

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

end A
