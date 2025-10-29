import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional


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

/--
The parallel relation.
-/
def parallel (self : Point) (v : Point) : Prop :=
  Collinear ℝ {0, self, v}

/--
The parallel relation.
-/
infix:49 "∥" => parallel

/--
Naive definition for parallel vectors, i.e. one is a multiple of another.
-/
theorem collinear (v w : Point) : v ∥ w ↔ v = 0 ∨ ∃ k : ℝ, w = k • v := by
  by_cases h : v = 0
  · exact ⟨ fun _ ↦ Or.inl h, by simp [parallel, h]; apply collinear_pair ⟩
  · simp [parallel, h, collinear_iff_exists_forall_eq_smul_vadd]
    constructor
    · intro ⟨ p₀, x, ⟨ r_0, h_0 ⟩, ⟨ r_v, h_v ⟩, ⟨ r_w, h_w ⟩ ⟩
      let k := (r_w - r_0) / (r_v - r_0)
      have : w = k • v := by
        simp [k, h_v, h_w]
        have h_nz : r_v - r_0 ≠ 0 := by
          by_contra
          have : r_v = r_0 := by linarith
          rw [this, ←h_0] at h_v
          contradiction
        rw [←smul_add, ←smul_right_inj h_nz, smul_smul, ←mul_div_assoc]
        field_simp [h_nz]
        have : p₀ = - (r_0 • x) := (neg_eq_of_add_eq_zero_right h_0.symm).symm
        simp [this, ←smul_assoc, ←neg_smul, ←sub_eq_zero, sub_eq_add_neg]
        simp only [←add_smul]
        simp
        ring_nf
        tauto
      exact ⟨ k, this ⟩
    · intro ⟨ k, h_k ⟩
      use 0, v
      exact ⟨ ⟨ 0, by simp ⟩, ⟨ 1, by simp ⟩, ⟨ k, by simp [h_k] ⟩ ⟩

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
