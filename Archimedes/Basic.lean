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
infix:69 " ∘ " => dot

/--
The cross product.
-/
@[simp]
abbrev cross (self : Point) (v : Point) : Point :=
  crossProduct self v

/--
The cross product.
-/
infix:69 " ⨯ " => cross

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

Note that the zero vector is defined to be not parallel with any vectors other than the zero vector.
This is for parallel to be an equivalence relation.
-/
def parallel (v w : Point) : Prop :=
  ∃ k : ℝ , w = k • v ∧ ∃ k : ℝ , v = k • w

/--
The parallel relation.
-/
infix:49 " ∥ " => parallel

/--
The non-parallel relation.
-/
infix:49 " ∦ " => ¬parallel

/--
Parallel relation is reflective.
-/
theorem parallel.refl (v : Point) : v ∥ v := by
  simp [parallel]
  use 1
  simp

/--
Parallel relation is symmetric.
-/
theorem parallel.symm (v w : Point) : v ∥ w → w ∥ v := by
  simp [parallel]
  intro k_w _ k_v _
  constructor
  · use k_v
  · use k_w

/--
Parallel relation is transitive.
-/
theorem parallel.trans (v w u : Point) : v ∥ w → w ∥ u → v ∥ u := by
  simp [parallel]
  intro k_wv h_wv k_vw h_vw k_uw h_uw k_wu h_wu
  constructor
  · use k_uw • k_wv
    simp [h_uw, h_wv, mul_smul]
  · use k_vw • k_wu
    simp [h_vw, h_wu, mul_smul]

instance parallel_eq : Equivalence parallel where
  refl := parallel.refl
  symm := @parallel.symm
  trans := @parallel.trans

/--
Parallel relation is commutive.
-/
theorem parallel_comm (v w : Point) : v ∥ w ↔ w ∥ v :=
  ⟨ parallel.symm v w, parallel.symm w v ⟩

/--
The zero vector is the only one parallel to zero vector.
-/
theorem zero_parallel_zero (v : Point) : v ∥ 0 ↔ v = 0 := by
  simp [parallel]
  intro
  use 0
  simp

/--
Linear independence.
-/
abbrev lnindep (v w : Point) := LinearIndependent ℝ ![v, w]

/--
Linear independence is symmetric.
-/
theorem lnindep.symm (v w : Point) : lnindep v w → lnindep w v := by
  simp [lnindep]
  rw [LinearIndependent.pair_symm_iff]
  simp

/--
Linear independence is commutative.
-/
theorem lnindep_comm (v w : Point) : lnindep v w ↔ lnindep w v :=
  ⟨ lnindep.symm v w, lnindep.symm w v ⟩

/--
Linear dependence.
-/
abbrev lndep (v w : Point) := ¬LinearIndependent ℝ ![v, w]

/--
Linear dependence is reflective.
-/
theorem lndep.refl (v : Point) : lndep v v := by
  simp [not_linearIndependent_iff]
  use Finset.univ, ![1, -1]
  simp

/--
Linear dependence is symmetric.
-/
theorem lndep.symm (v w : Point) : lndep v w → lndep w v := by
  simp [lndep, lnindep_comm]

/--
Linear dependence is commutative.
-/
theorem lndep_comm (v w : Point) : lndep v w ↔ lndep w v :=
  ⟨ lndep.symm v w, lndep.symm w v ⟩

/--
Parallel vectors are linear dependent.
-/
theorem parallel.lndep (v w : Point) : v ∥ w → lndep v w := by
  simp [parallel, Point.lndep, not_linearIndependent_iff]
  intro x h _ _
  use Finset.univ, ![-x, 1]
  simp [h]

/--
A vector with all-zero components is a zero vector.
-/
@[simp]
lemma zero_components : ![0, 0, 0] = 0 := by simp

end Point

end A
