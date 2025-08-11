import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

def hello := "world"

abbrev APoint := EuclideanSpace ℝ (Fin 3)

infix:69 "⬝" => inner ℝ

theorem a_inner (v w : APoint) : v ⬝ w = v 0 • w 0 + v 1 • w 1 + v 2 • w 2 := by
  simp [inner, Fin.sum_univ_succ]
  ring

infix:69 "⨯" => crossProduct

theorem a_cross (v w : APoint)
: v ⨯ w = ![v 1 • w 2 - v 2 • w 1, v 2 • w 0 - v 0 • w 2, v 0 • w 1 - v 1 • w 0 ]
:= by
  simp [crossProduct]

-- theorem a_norm (v : APoint) : ‖v‖₊  = (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) ^ (1/2 : ℝ) := by
--   simp [norm, Fin.sum_univ_succ]
--   ring_nf

abbrev a_0 : APoint := 0

@[simp]
lemma zeros_eq_origin : ![0, 0, 0] = a_0 := by simp

example
: let o : APoint := ![0, 0, 0]
  ∀ v : APoint, v + o = v
:= by
  simp

abbrev a_x : APoint := ![1, 0, 0]
abbrev a_y : APoint := ![0, 1, 0]
abbrev a_z : APoint := ![0, 0, 1]
