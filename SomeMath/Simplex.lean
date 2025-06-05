import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Invertible
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

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


def row_submx {m p s : Nat}
  (Q : Matrix (Fin m) (Fin p) Real)
  (f : (Fin s) → (Fin m))
  : (Matrix (Fin s) (Fin p) Real) :=
  -- Matrix.of (fun (i : Fin s) (j : Fin p) =>
  --   Q (I i) j
  -- )
  Matrix.of Q ∘ f

def matrix_of_prebasis {m p : Nat} {n : Fin m}
  (Q : Matrix (Fin m) (Fin p) Real)
  (I : @Prebasis m n)
  : (Matrix (Fin n) (Fin p) Real)
  := row_submx Q I.f

structure IBasis {m : Nat} {n : Fin m}
  (A : Matrix (Fin m) (Fin n) Real)
  (I : @Prebasis m n) where
  bas : Invertible (matrix_of_prebasis A I)
  -- or something meaning matrix is invertible

noncomputable def i_basis_point {m : Nat} {n : Fin m}
  {A : Matrix (Fin m) (Fin n) Real}
  {I : @Prebasis m n}
  (b : Fin m → Real)
  (Ib : IBasis A I)
  : (Fin n → Real)
  := Matrix.mulVec Ib.bas.invOf (b ∘ I.f)


structure FeasibleBasisI {m : Nat} {n : Fin m}
  {A : Matrix (Fin m) (Fin n) Real}
  {I : @Prebasis m n}
  (b : Fin m → Real)
  (Ib : @IBasis m n A I) where
  inph : polyhedron A b (i_basis_point b Ib)


noncomputable def reduced_cost_of_basis {m : Nat} {n : Fin m}
  {A : Matrix (Fin m) (Fin n) Real}
  {I : @Prebasis m n}
  (c : Fin n → Real)
  (Ib : @IBasis m n A I)
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
  {A : Matrix (Fin m) (Fin n) Real}
  {I : @Prebasis m n}
  (c : Fin n → Real)
  (Ib : @IBasis m n A I)
  : let u := (reduced_cost_of_basis c Ib)
    u ≥ 0 ↔ dual_polyhedron A c (extend_indexed m n I u) := by
  have hswapij : (Matrix.of fun i j ↦ A (I.f i) j).transpose
    = (Matrix.of fun j i ↦ A (I.f i) j) := by
    apply funext
    intros
    apply funext
    intros
    rw [Matrix.transpose_apply]
    rfl
  have hMPB : (Matrix.of fun i j ↦ A (I.f i) j)
    = matrix_of_prebasis A I := by
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
        (fun i => i ∈ Finset.image I.f (Finset.univ))]
      have h2 : ∑ x ∈ Finset.filter
        (fun x ↦ x ∉ Finset.image I.f Finset.univ)
        Finset.univ,
        MulOpposite.op
          (extend_indexed
            m n I (reduced_cost_of_basis c Ib) x
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
        (fun x ↦ x ∈ Finset.image I.f Finset.univ)
        Finset.univ,
        MulOpposite.op
          (extend_indexed
            m n I (reduced_cost_of_basis c Ib) x
          ) • A x = c := by
        have : Finset.filter
          (fun x ↦ x ∈ Finset.image I.f Finset.univ)
          Finset.univ = Finset.image I.f Finset.univ := by
          ext x
          simp
        rw [this]
        rw [Finset.sum_image (by
          intros x _ y _ h
          exact I.inj h
          )]
        rw [
          reduced_cost_of_basis,
        ]
        simp_rw [ei_I_f]
        have hsubmt : (x : Fin n) → A (I.f x)
          = (Matrix.of fun j i ↦ A (I.f i) j).transpose
            x := by
          intro x
          apply funext
          simp
        rw [Finset.sum_congr rfl (fun x _ ↦ by rw [hsubmt x])]
        conv =>
          lhs
          rw [← Matrix.mulVec_eq_sum, Matrix.mulVec_mulVec]

        have : Invertible (matrix_of_prebasis A I) := Ib.bas
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
      cases Fin.find fun i ↦ I.f i = x with
      | some i => exact h1 i
      | none => rfl
  · intro hdp
    have : (i : Fin n) → reduced_cost_of_basis c Ib i
      = extend_indexed m n I
        (reduced_cost_of_basis c Ib) (I.f i) := by
      intro i
      rw [extend_indexed, Fin.find_eq_some_iff.mpr]
      apply And.intro
      rfl
      intros j hsame
      apply le_of_eq
      apply Eq.symm
      exact I.inj hsame
    intro i
    rw [Pi.zero_apply, this]
    rcases hdp with ⟨_, hnonneg⟩
    exact hnonneg (I.f i)

theorem optimal_cert_on_basis {m : Nat} {n : Fin m}
  {A : Matrix (Fin m) (Fin n) Real}
  {I : @Prebasis m n}
  (b : Fin m → Real)
  (c : Fin n → Real)
  (Ib : IBasis A I)
  (_ : @FeasibleBasisI m n A I b Ib)
  : (y : Fin n → Real) → polyhedron A b y →
    reduced_cost_of_basis c Ib ≥ 0 →
    dotProduct c (i_basis_point b Ib)
    ≤ dotProduct c y := by
  intros y hphy hrcnn
  have hdp := (ext_reduced_cost_dual_feasible c Ib).mp hrcnn
  have h1 := weak_duality A b c (And.intro hphy hdp)
  have hinv : Invertible (matrix_of_prebasis A I) := Ib.bas
  rw [
    i_basis_point,
    Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose]
  unfold reduced_cost_of_basis at h1
  apply GE.ge.le at h1
  rw [dotProduct_comm, ei_dot] at h1
  exact h1


def direction
  {m : Nat}
  {n : Fin m}
  {A : Matrix (Fin m) (Fin n) Real}
  {I : @Prebasis m n}
  (Ib : IBasis A I)
  (i : Fin n)
  : (Fin n → Real) :=
  Ib.bas.invOf.transpose i

theorem direction_improvement
  {m : Nat}
  {n : Fin m}
  {A : Matrix (Fin m) (Fin n) Real}
  {I : @Prebasis m n}
  (c : Fin n → Real)
  (Ib : IBasis A I)
  (i : Fin n)
  : (reduced_cost_of_basis c Ib) i < 0 →
    dotProduct c (direction Ib i) < 0 := by
  intro h
  unfold reduced_cost_of_basis at h
  unfold Matrix.mulVec at h
  unfold direction
  rw [dotProduct_comm]
  exact h

def feasible_dir
  {m : Nat}
  {n : Fin m}
  (A : Matrix (Fin m) (Fin n) Real)
  (d : Fin n → Real)
  : Prop :=
  Matrix.mulVec A d ≥ 0

theorem unbounded_cert_on_basis
  {m : Nat}
  {n : Fin m}
  {I : Prebasis n}
  {A : Matrix (Fin m) (Fin n) Real}
  {Ib : IBasis A I}
  (b : Fin m → Real)
  (c : Fin n → Real)
  (FBI : FeasibleBasisI b Ib)
  (i : Fin n)
  : feasible_dir A (direction Ib i) →
    reduced_cost_of_basis c Ib i < 0 →
    ∀ M : Real, ∃ x : Fin n → Real,
      polyhedron A b x ∧ dotProduct c x < M := by
  intros hfeasd hnegrc M
  let p1 : Fin n → Real := i_basis_point b Ib
  let d : Fin n → Real := direction Ib i
  let p2 : Fin n → Real :=
    p1 + (max 1 ((M - 1 - dotProduct c p1) / dotProduct c d)) • d
  have hdlsc := direction_improvement c Ib i hnegrc
  use p2
  apply And.intro
  · unfold polyhedron
    rw [Matrix.mulVec_add]
    apply LE.le.ge
    rw [← sub_nonneg, add_comm, add_sub_assoc]
    apply add_nonneg
    · rw [Matrix.mulVec_smul]
      apply smul_nonneg'
      · apply (le_trans zero_le_one)
        exact le_max_left 1 ((M - 1 - c ⬝ᵥ p1) / c ⬝ᵥ d)
      · exact LE.le.ge hfeasd
    · rw [sub_nonneg]
      exact GE.ge.le FBI.inph
  · rw [dotProduct_add]
    by_cases h : (M - 1 - c ⬝ᵥ p1) / c ⬝ᵥ d < 1
    · rw [max_eq_left_of_lt h, one_smul]
      apply lt_tsub_iff_left.mp
      apply (div_lt_one_of_neg hdlsc).mp at h
      linarith
    · have h2 := le_of_not_lt h
      rw [max_eq_right h2, dotProduct_smul]
      apply lt_tsub_iff_left.mp
      rw [
        smul_eq_mul,
        mul_comm_div,
        (div_eq_one_iff_eq (ne_of_lt hdlsc)).mpr (by rfl)]
      linarith

def b_pert {m : Nat} (b : Fin m → Real)
  : Matrix (Fin m) (Fin (m + 1)) Real :=
  Matrix.of (
    fun i j ↦
      if j = 0 then b i
      else if j = i + 1 then -1
      else 0
  )

noncomputable def i_basis_point_pert {m : Nat} {n : Fin m}
  {I : Prebasis n}
  {A : Matrix (Fin m) (Fin n) Real}
  (b : Fin m → Real)
  (Ib : IBasis A I)
  : Matrix (Fin n) (Fin (m + 1)) Real :=
  let bp := b_pert b
  -- Ib.bas.invOf * Matrix.of (bp ∘ I.f)
  Ib.bas.invOf * row_submx bp I.f

theorem rel_basis_point {m : Nat} {n : Fin m}
  {I : Prebasis n}
  {A : Matrix (Fin m) (Fin n) Real}
  (b : Fin m → Real)
  (Ib : IBasis A I)
  : i_basis_point b Ib =
    fun i => (i_basis_point_pert b Ib) i 0 := by
  funext i
  have h
    : (Matrix.of (b_pert b ∘ I.f)).transpose 0 =
      b ∘ I.f := by
    funext i
    rw [
      Matrix.transpose_apply,
      b_pert
    ]
    simp
  rw [
    i_basis_point_pert,
    i_basis_point,
    ← Matrix.transpose_apply
      (Ib.bas.invOf * Matrix.of (b_pert b ∘ I.f)),
    Matrix.transpose_mul,
    Matrix.mul_apply_eq_vecMul,
    Matrix.vecMul_transpose,
    h
  ]

def row_lex {l : Nat} (r1 r2: Fin l → Real) : Prop :=
  row_lex_counter r1 r2 0
where
  row_lex_counter
    {l : Nat}
    (r1 r2: Fin l → Real)
    (c : Fin (l + 1))
    : Prop :=
    if h : c.val < l then
      r1 ⟨c.val, h⟩ < r2 ⟨c.val, h⟩
      ∨ (r1 ⟨c.val, h⟩ = r2 ⟨c.val, h⟩ ∧ row_lex_counter r1 r2
        ⟨c.val + 1, Nat.add_one_lt_add_one_iff.mpr h⟩)
    else True

theorem row_lex_implies_leq
  {l : Nat} {r1 r2: Fin l → Real} (hl: l > 0)
  : row_lex r1 r2 → r1 ⟨0, hl⟩ ≤ r2 ⟨0, hl⟩ := by
  have hlr := GT.gt.lt hl
  unfold row_lex
  unfold row_lex.row_lex_counter
  intro h2
  have h00 := @Fin.val_zero
    (l + 1)
    (NeZero.of_pos
      (lt_trans hlr (Nat.lt_succ_self l)))
  split at h2
  · next h => cases h2 with
    | inl h3 =>
      apply le_of_lt
      rw [Fin.mk_eq_mk.mpr (h00)] at h3
      exact h3
    | inr h4 =>
      apply le_of_eq
      rw [Fin.mk_eq_mk.mpr (h00)] at h4
      exact h4.left
  · exfalso
    next h =>
      apply h
      exact GT.gt.lt hl


def is_lex_feasible {m : Nat} {n : Fin m}
  {I : Prebasis n}
  {A : Matrix (Fin m) (Fin n) Real}
  (b : Fin m → Real)
  (Ib : IBasis A I)
  : Prop :=
  ∀ i : Fin m,
  row_lex
    (b_pert b i)
    (Matrix.vecMul (A i) (i_basis_point_pert b Ib))

structure LexFeasibleBasis {m : Nat} {n : Fin m}
  {I : Prebasis n}
  {A : Matrix (Fin m) (Fin n) Real}
  (b : Fin m → Real)
  (Ib : IBasis A I) where
  pert_feas : is_lex_feasible b Ib

theorem lex_feasible_basis_is_feasible {m : Nat} {n : Fin m}
  {I : Prebasis n}
  {A : Matrix (Fin m) (Fin n) Real}
  {b : Fin m → Real}
  {Ib : IBasis A I}
  -- (hl : m > 0)
  (LFBI : LexFeasibleBasis b Ib)
  : FeasibleBasisI b Ib := by
  have := LFBI.pert_feas
  unfold is_lex_feasible at this
  apply FeasibleBasisI.mk
  unfold polyhedron
  intro i
  have := this i
  have := @row_lex_implies_leq (m + 1) _ _ (by simp) this
  unfold b_pert at this
  rw [Matrix.of_apply, if_pos] at this
  · have h1 : Matrix.vecMul (A i) (i_basis_point_pert b Ib) 0
      = A.mulVec (i_basis_point b Ib) i := by
      rw [rel_basis_point]
      unfold Matrix.vecMul
      unfold Matrix.mulVec
      simp
    rw [← h1]
    exact this
  · rfl


theorem col_b_pert  {m : Nat} {n : Fin m}
  (I : Prebasis n)
  (j : Fin m)
  (b : Fin m → Real)
  : (matrix_of_prebasis (b_pert b) I).transpose
      ⟨j + 1, by simp⟩ != 0 ↔
    j ∈ Finset.image I.f Finset.univ := by
  apply Iff.comm.mp
  apply Iff.intro
  · intro h1
    have h2 := Finset.mem_image.mp h1
    obtain ⟨i, hi⟩ := h2
    simp
    intro h3
    have h4 : (matrix_of_prebasis (b_pert b) I).transpose
      ⟨j + 1, by simp⟩ i = -1 := by
      unfold matrix_of_prebasis b_pert
        Matrix.transpose row_submx
      simp [hi.right]
      rfl
    have := congrFun h3 i
    rw [h4] at this
    simp at this
  · intro h1
    simp at h1
    by_contra h2
    apply h1
    unfold matrix_of_prebasis b_pert
      Matrix.transpose row_submx
    simp at h2
    funext x
    have h3 := h2 x
    simp
    intro h4
    apply h3
    apply Fin.succ_inj.mp
    rw [←h4]
    rfl

theorem col_point_of_basis_pert  {m : Nat} {n : Fin m}
  {A : Matrix (Fin m) (Fin n) Real}
  {I : @Prebasis m n}
  (j : Fin m)
  (b : Fin m → Real)
  (Ib : IBasis A I)
  : (i_basis_point_pert b Ib).transpose
      ⟨j + 1, by simp⟩ != 0 ↔
    j ∈ Finset.image I.f Finset.univ := by
    rw [(Iff.comm.mp (col_b_pert I j b))]
    unfold i_basis_point_pert
    simp
    apply not_iff_not.mpr
    rw [Matrix.mul_apply_eq_vecMul]
    apply Iff.intro
    · rw [Matrix.vecMul_transpose]
      intro h1
      rw [matrix_of_prebasis]
      let M := matrix_of_prebasis A I
      have hminv := Ib.bas
      let x := ((row_submx (b_pert b) I.f).transpose
        ⟨(j + 1), by simp⟩)
      show x = 0
      rw [
        ← Matrix.one_mulVec x,
        ← Matrix.mul_inv_of_invertible M,
        ← Matrix.mulVec_mulVec,
        h1,
        Matrix.mulVec_zero]
    · intro h1
      unfold matrix_of_prebasis at h1
      rw [h1, Matrix.zero_vecMul]

theorem eq_pert_point_imp_eq_bas {m : Nat} {n : Fin m}
  {A : Matrix (Fin m) (Fin n) Real}
  {I1 I2 : @Prebasis m n}
  (b : Fin m → Real)
  (Ib1 : IBasis A I1)
  (Ib2 : IBasis A I2)
  : i_basis_point_pert b Ib1 = i_basis_point_pert b Ib2
    → Finset.image I1.f (Finset.univ)
      = Finset.image I2.f (Finset.univ) := by
    intro hbps
    ext j
    rw [
      ← col_point_of_basis_pert j b Ib1,
      hbps,
      col_point_of_basis_pert j b Ib2]
