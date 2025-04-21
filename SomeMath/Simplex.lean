import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Invertible
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


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
  (Matrix.mulVec A x) ≥ b

def dual_polyhedron {m n : Nat}
  (A : Matrix (Fin m) (Fin n) Real)
  (c : Fin n → Real)
  (u : Fin m → Real)
  : Prop :=
  ((Matrix.mulVec (A.transpose) u) = c) ∧ (u ≥ 0)


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

structure IBasis {m : Nat} {n : Fin m}
  (A : Matrix (Fin m) (Fin n) Real) where
  I : @Prebasis m n
  bas : Invertible (matrix_of_prebasis A I)
  -- or something meaning matrix is invertible

noncomputable def i_basis_point {m : Nat} {n : Fin m}
  (A : Matrix (Fin m) (Fin n) Real)
  (b : Fin m → Real)
  (Ib : IBasis A)
  : (Fin n → Real)
  := Matrix.mulVec Ib.bas.invOf (b ∘ Ib.I.f)


structure FeasibleBasisI {m : Nat} {n : Fin m}
  (A : Matrix (Fin m) (Fin n) Real)
  (b : Fin m → Real) where
  Ib : @IBasis m n A
  inph : polyhedron A b (i_basis_point A b Ib)

noncomputable def point_of_basis {m : Nat} {n : Fin m}
  (A : Matrix (Fin m) (Fin n) Real)
  (b : Fin m → Real)
  (Ib : IBasis A)
  : (Fin n → Real) :=
  Matrix.mulVec
    Ib.bas.invOf
    (b ∘ Ib.I.f)
  -- maybe could use Ring.inverse instead



noncomputable def reduced_cost_of_basis {m : Nat} {n : Fin m}
  (A : Matrix (Fin m) (Fin n) Real)
  (c : Fin n → Real)
  (Ib : @IBasis m n A)
  : (Fin n → Real) :=
  Matrix.mulVec Ib.bas.invOf.transpose c


theorem weak_duality {m : Nat} {n : Fin m}
  {x : Fin n → Real} {u : Fin m → Real}
  (A : Matrix (Fin m) (Fin n) Real)
  (b : Fin m → Real)
  (c : Fin n → Real)
  : (polyhedron A b x) ∧ (dual_polyhedron A c u) →
    (dotProduct c x) ≥ (dotProduct b u)
  := by
    intro h1
    rcases h1 with ⟨ph, dph⟩
    rcases dph with ⟨h2, h3⟩
    rw [
      ← h2,
      Matrix.mulVec_transpose,
      ← Matrix.dotProduct_mulVec,
      dotProduct_comm]
    apply LE.le.ge
    apply dotProduct_le_dotProduct_of_nonneg_right
      ph (LE.le.ge h3)


def extend_indexed
  (m : Nat) (n : Fin m) (I : @Prebasis m n) (u : Fin n → Real)
  : Fin m → Real := fun ei =>
    match Fin.find (fun i : Fin n => I.f i = ei) with
    | some i => u i
    | none => 0

theorem ei_I_f
  (m : Nat)
  (n : Fin m)
  (I : @Prebasis m n)
  (v : Fin n → Real)
  (i : Fin n)
  : extend_indexed m n I v (I.f i) = v i := by
    rw [extend_indexed, Fin.find_eq_some_iff.mpr]
    apply And.intro
    rfl
    intros j hsame
    apply le_of_eq
    apply Eq.symm
    exact I.inj hsame

theorem ei_nn {m : Nat} {n : Fin m} {u : Fin n → Real}
  (I : @Prebasis m n)
  : extend_indexed m n I u ≥ 0 ↔  u ≥ 0 := by
  apply Iff.intro
  · intro hei i
    rw [← ei_I_f  m n I u i]
    apply GE.ge.le
    exact hei (I.f i)
  · intro hu fi
    rw [Pi.zero_apply, extend_indexed]
    cases Fin.find fun i ↦ I.f i = fi with
    | some i => exact (GE.ge.le (hu i))
    | none => rfl


theorem ei_dot {m : Nat} {n : Fin m}
  (I : @Prebasis m n)
  (v1 : Fin m → Real)
  (v2 : Fin n → Real)
  : dotProduct (extend_indexed m n I v2) v1
    = dotProduct v2 (v1 ∘ I.f) := by
    rw [
      dotProduct,
      ← Finset.sum_filter_add_sum_filter_not
        (Finset.univ)
        (fun i => i ∈ Finset.image I.f (Finset.univ))
    ]
    have h1 : ∑ x ∈ Finset.filter
      (fun x ↦ x ∉ Finset.image I.f Finset.univ)
      Finset.univ,
      (extend_indexed m n I v2 x) * v1 x = 0 := by
      apply Finset.sum_eq_zero
      intros x hx
      simp [
        Finset.mem_filter,
        Finset.mem_univ,
        true_and
        ] at hx
      rw [extend_indexed, Fin.find_eq_none_iff.mpr]
      simp
      exact hx
    rw [h1, add_zero]
    have h2 : Finset.filter
      (fun x ↦ x ∈ Finset.image I.f Finset.univ)
      Finset.univ = Finset.image I.f Finset.univ := by
      ext x
      simp
    rw [h2]
    rw [Finset.sum_image (by
      intros x _ y _ h
      exact I.inj h
      )]
    simp_rw [ei_I_f]
    rw [dotProduct]
    rfl

theorem ext_reduced_cost_dual_feasible {m : Nat} {n : Fin m}
  (A : Matrix (Fin m) (Fin n) Real)
  (c : Fin n → Real)
  (Ib : @IBasis m n A)
  : let u := (reduced_cost_of_basis A c Ib)
    u ≥ 0 ↔ dual_polyhedron A c (extend_indexed m n Ib.I u) := by
  have hswapij : (Matrix.of fun i j ↦ A (Ib.I.f i) j).transpose
    = (Matrix.of fun j i ↦ A (Ib.I.f i) j) := by
    apply funext
    intros
    apply funext
    intros
    rw [Matrix.transpose_apply]
    rfl
  have hMPB : (Matrix.of fun i j ↦ A (Ib.I.f i) j)
    = matrix_of_prebasis A Ib.I := by
    unfold matrix_of_prebasis
    unfold row_submx
    rfl
  apply Iff.intro
  · intro h1
    apply And.intro
    · rw [
      Matrix.mulVec_eq_sum,
      Matrix.transpose_transpose,
      ← Finset.sum_filter_add_sum_filter_not
        (Finset.univ)
        (fun i => i ∈ Finset.image Ib.I.f (Finset.univ))]
      have h2 : ∑ x ∈ Finset.filter
        (fun x ↦ x ∉ Finset.image Ib.I.f Finset.univ)
        Finset.univ,
        MulOpposite.op
          (extend_indexed
            m n Ib.I (reduced_cost_of_basis A c Ib) x
          ) • A x = 0 := by
        apply Finset.sum_eq_zero
        intros x hx
        simp [
          Finset.mem_filter,
          Finset.mem_univ,
          true_and
          ] at hx
        rw [extend_indexed, Fin.find_eq_none_iff.mpr]
        simp
        exact hx
      have h3 : ∑ x ∈ Finset.filter
        (fun x ↦ x ∈ Finset.image Ib.I.f Finset.univ)
        Finset.univ,
        MulOpposite.op
          (extend_indexed
            m n Ib.I (reduced_cost_of_basis A c Ib) x
          ) • A x = c := by
        have : Finset.filter
          (fun x ↦ x ∈ Finset.image Ib.I.f Finset.univ)
          Finset.univ = Finset.image Ib.I.f Finset.univ := by
          ext x
          simp
        rw [this]
        rw [Finset.sum_image (by
          intros x _ y _ h
          exact Ib.I.inj h
          )]
        rw [
          reduced_cost_of_basis,
        ]
        simp_rw [ei_I_f]
        have hsubmt : (x : Fin n) → A (Ib.I.f x)
          = (Matrix.of fun j i ↦ A (Ib.I.f i) j).transpose
            x := by
          intro x
          apply funext
          simp
        rw [Finset.sum_congr rfl (fun x _ ↦ by rw [hsubmt x])]
        conv =>
          lhs
          rw [← Matrix.mulVec_eq_sum, Matrix.mulVec_mulVec]

        have : Invertible (matrix_of_prebasis A Ib.I) := Ib.bas
        rw [
          ← hswapij,
          hMPB,
          Matrix.transpose_invOf,
          mul_invOf_self
        ]
        rw [Matrix.one_mulVec]

      rw [h2, h3, add_zero]
    · intro x
      rw [Pi.zero_apply, extend_indexed]
      cases Fin.find fun i ↦ Ib.I.f i = x with
      | some i => exact h1 i
      | none => rfl
  · intro hdp
    have : (i : Fin n) → reduced_cost_of_basis A c Ib i
      = extend_indexed m n Ib.I
        (reduced_cost_of_basis A c Ib) (Ib.I.f i) := by
      intro i
      rw [extend_indexed, Fin.find_eq_some_iff.mpr]
      apply And.intro
      rfl
      intros j hsame
      apply le_of_eq
      apply Eq.symm
      exact Ib.I.inj hsame
    intro i
    rw [Pi.zero_apply, this]
    rcases hdp with ⟨_, hnonneg⟩
    exact hnonneg (Ib.I.f i)

theorem optimal_cert_on_basis {m : Nat} {n : Fin m}
  (A : Matrix (Fin m) (Fin n) Real)
  (b : Fin m → Real)
  (c : Fin n → Real)
  (FBI : @FeasibleBasisI m n A b)
  : (y : Fin n → Real) → polyhedron A b y →
    reduced_cost_of_basis A c FBI.Ib ≥ 0 →
    dotProduct c (i_basis_point A b FBI.Ib)
    ≤ dotProduct c y := by
  intros y hphy hrcnn
  have hdp := (ext_reduced_cost_dual_feasible A c FBI.Ib).mp hrcnn
  have h1 := weak_duality A b c (And.intro hphy hdp)
  have hinv : Invertible (matrix_of_prebasis A FBI.Ib.I) := FBI.Ib.bas
  rw [
    i_basis_point,
    Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose]
  unfold reduced_cost_of_basis at h1
  apply GE.ge.le at h1
  rw [dotProduct_comm, ei_dot] at h1
  exact h1
