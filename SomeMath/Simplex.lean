import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic


def elwileq {n : Nat} (v1 v2 : Fin n → Real) : Prop :=
  ∀ i : Fin n, v1 i ≤ v2 i


def polyhedron {n m : Nat}
  (A : Matrix (Fin m) (Fin n) Real)
  (b : Fin m → Real)
  (x : Fin n → Real)
  : Prop :=
  elwileq (Matrix.mulVec A x) b
