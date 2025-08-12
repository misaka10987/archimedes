import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct


namespace A


abbrev Point := EuclideanSpace ℝ (Fin 3)


infix:69 "⬝" => inner ℝ

theorem inner (v w : Point) : v ⬝ w = v 0 • w 0 + v 1 • w 1 + v 2 • w 2 := by
  simp [Inner.inner, Fin.sum_univ_succ]
  ring


infix:69 "⨯" => crossProduct

theorem cross (v w : Point)
: v ⨯ w = ![v 1 • w 2 - v 2 • w 1, v 2 • w 0 - v 0 • w 2, v 0 • w 1 - v 1 • w 0 ]
:= by
  simp [crossProduct]


theorem norm (v : Point) : ‖v‖ = √ (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
  simp [Norm.norm, Fin.sum_univ_succ, Real.sqrt_eq_rpow]
  ring_nf

theorem sq_norm_eq_dot_self (v : Point) : ‖v‖ ^ 2 = v ⬝ v := by
  simp [inner, norm, pow_two]
  rw [←Real.sqrt_mul, Real.sqrt_mul_self]
  repeat first | apply add_nonneg | apply mul_self_nonneg


abbrev o : Point := 0

@[simp]
lemma zeros_eq_origin : ![0, 0, 0] = o := by simp


abbrev x : Point := ![1, 0, 0]
abbrev y : Point := ![0, 1, 0]
abbrev z : Point := ![0, 0, 1]

end A
