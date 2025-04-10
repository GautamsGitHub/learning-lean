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


structure Prebasis {m : Nat} where
  n : Fin m
  f : (Fin n) → (Fin m)

structure Prebasis' {m : Nat} {n : Fin m} where
  set : Finset (Fin m)
  hsize : set.card = n


#check @Prebasis'.mk 3 1 (Finset.cons
    (@Fin.mk 8 6 (by simp))
    (@Finset.empty (Fin 3))
    (Finset.not_mem_empty _))
  (by
    simp
    rfl)

noncomputable def row_submx' {m : Nat}
  (p : Nat)
  (Q : Matrix (Fin m) (Fin p) Real)
  (I : Finset (Fin m))
  : (Matrix (Fin I.card) (Fin p) Real) :=
  Matrix.of (fun (i : Fin I.card) (j : Fin p) =>
    Q (I.toList.get (Fin.cast (Eq.symm I.length_toList) i)) j
  )

def row_submx {m p s : Nat}
  (Q : Matrix (Fin m) (Fin p) Real)
  (I : (Fin s) → (Fin m))
  : (Matrix (Fin s) (Fin p) Real) :=
  Matrix.of (fun (i : Fin s) (j : Fin p) =>
    Q (I i) j
  )

def matrix_of_prebasis {m p : Nat}
  (Q : Matrix (Fin m) (Fin p) Real)
  (I : @Prebasis m)
  : (Matrix (Fin I.n) (Fin p) Real)
  := row_submx Q I.f
