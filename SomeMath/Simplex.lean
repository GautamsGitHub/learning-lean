import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic


def elwiL {n : Nat} (v1 v2 : Fin n → Real) : Prop :=
  ∀ i : Fin n, v1 i < v2 i

def elwiG {n : Nat} (v1 v2 : Fin n → Real) : Prop :=
  ∀ i : Fin n, v1 i > v2 i

def elwiEq {n : Nat} (v1 v2 : Fin n → Real) : Prop :=
  ∀ i : Fin n, v1 i = v2 i

def polyhedron {n m : Nat}
  (A : Matrix (Fin m) (Fin n) Real)
  (b : Fin m → Real)
  (x : Fin n → Real)
  : Prop :=
  ¬ elwiL (Matrix.mulVec A x) b

def dual_polyhedron {n m : Nat}
  (A : Matrix (Fin m) (Fin n) Real)
  (c : Fin n → Real)
  (u : Fin m → Real)
  : Prop :=
  (elwiEq (Matrix.mulVec (A.transpose) u) c) ∧ (¬ elwiL u 0)


structure Prebasis {n : Nat} {m : Fin n} where
  set : Finset (Fin n)
  hsize : set.card = m


#check @Prebasis.mk 3 1 (Finset.cons
    (@Fin.mk 8 6 (by simp))
    (@Finset.empty (Fin 3))
    (Finset.not_mem_empty _))
  (by
    simp
    rfl)
