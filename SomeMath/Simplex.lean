import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin


def elwiL {n : Nat} (v1 v2 : Fin n → Real) : Prop :=
  ∀ i : Fin n, v1 i < v2 i

def elwiG {n : Nat} (v1 v2 : Fin n → Real) : Prop :=
  ∀ i : Fin n, v1 i > v2 i

def elwiEq {n : Nat} (v1 v2 : Fin n → Real) : Prop :=
  ∀ i : Fin n, v1 i = v2 i

def polyhedron {m n : Nat}
  (A : Matrix (Fin m) (Fin n) Real)
  (b : Fin m → Real)
  (x : Fin n → Real)
  : Prop :=
  ¬ elwiL (Matrix.mulVec A x) b

def dual_polyhedron {m n : Nat}
  (A : Matrix (Fin m) (Fin n) Real)
  (c : Fin n → Real)
  (u : Fin m → Real)
  : Prop :=
  (elwiEq (Matrix.mulVec (A.transpose) u) c) ∧ (¬ elwiL u 0)


structure Prebasis {m : Nat} (n : Fin m) where
  f : (Fin n) → (Fin m)
  inj : Function.Injective f

structure Prebasis' {m : Nat} {n : Fin m} where
  set : Finset (Fin m)
  hsize : set.card = n

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

def matrix_of_prebasis {m p : Nat} {n : Fin m}
  (Q : Matrix (Fin m) (Fin p) Real)
  (I : @Prebasis m n)
  : (Matrix (Fin n) (Fin p) Real)
  := row_submx Q I.f

structure MyBasis {m : Nat} {n : Fin m}
  (A : Matrix (Fin m) (Fin n) Real) where
  I : @Prebasis m n
  bas : (matrix_of_prebasis A I).det = 0

noncomputable def my_basis_point {m : Nat} {n : Fin m}
  (A : Matrix (Fin m) (Fin n) Real)
  (b : Fin m → Real)
  (Ib : MyBasis A)
  : (Fin n → Real)
  := Matrix.mulVec
    (Ring.inverse (matrix_of_prebasis A Ib.I))
    (b ∘ Ib.I.f)

structure PrebasisWithBasis {m : Nat} {n : Fin m}
  (A : Matrix (Fin m) (Fin n) Real)
  (b : Fin m → Real) where
  I : @Prebasis m n
  basis : Basis (Fin n) Real (Fin n → Real)
  -- h : the basis is made of the I vectors from A

def basis_point {m : Nat} {n : Fin m}
  (A : Matrix (Fin m) (Fin n) Real)
  (b : Fin m → Real)
  (Ib : PrebasisWithBasis A b)
  : (Fin n → Real)
  := (Ib.basis).repr (b ∘ Ib.I.f)

structure FeasibleBasisMy {m : Nat} {n : Fin m}
  (A : Matrix (Fin m) (Fin n) Real)
  (b : Fin m → Real) where
  Ib : @MyBasis m n A
  inph : polyhedron A b (my_basis_point A b Ib)

structure FeasibleBasis {m : Nat} {n : Fin m}
  (A : Matrix (Fin m) (Fin n) Real)
  (b : Fin m → Real) where
  Ib : PrebasisWithBasis A b
  inph : polyhedron A b (basis_point A b Ib)

#check Basis.ofEquivFun
#check LinearEquiv.ofBijective
