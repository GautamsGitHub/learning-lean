namespace Hidden

open Nat

universe u

inductive List (α : Type u) where
  | empty : List α
  | cons : α → List α → List α


open List

def reverse {α : Type u} (as : List α) : List α :=
  loop as empty
where
  loop : List α → List α → List α
  | empty, ras => ras
  | cons a ast, ras => loop ast (cons a ras)

def len {α : Type u} : List α → Nat
  | empty => 0
  | cons _ as => 1 + (len as)


theorem rloop_maintains_length {α : Type u} (xs ys : List α)
  : len (reverse.loop xs ys) = len (xs) + len (ys) := by
  match xs, ys with
  | empty, _ => rw [reverse.loop, len]; simp
  | cons x xs, empty =>
    rw [reverse.loop, rloop_maintains_length xs _]
    repeat (rw [len])
    simp +arith
  | cons x xs, cons y ys =>
    rw [reverse.loop, rloop_maintains_length xs _]
    repeat (rw [len])
    simp +arith


theorem reverse_maintains_length {α : Type u} (as : List α)
  : len as = len (reverse as) := by
  rw [reverse, rloop_maintains_length as empty, len]
  simp

theorem reverse_loop_swap {α : Type u} (xs ys : List α)
  : reverse.loop (reverse.loop xs ys) empty
    = reverse.loop (reverse.loop empty ys) xs := by
  match xs, ys with
  | empty, ys => simp [reverse.loop]
  | cons x xs, ys =>
    rw [
      reverse.loop,
      reverse.loop,
      reverse_loop_swap,
      reverse.loop,
      reverse.loop]

theorem reverse_reverse {α : Type u} (xs : List α)
  : xs = reverse (reverse xs) := by
  rw [
    reverse,
    reverse,
    reverse_loop_swap,
    reverse.loop,
    reverse.loop]

end Hidden

universe u v


def myrec {motive : Nat → Type u}
  (hz : motive Nat.zero)
  (hs : (x : Nat) → motive x → motive (x + 1))
  : (∀ n : Nat, motive n) := by
  intro n
  match n with
  | Nat.zero => exact hz
  | Nat.succ prev =>
    have hp : motive prev := myrec hz hs prev
    exact hs prev hp

-- def mybrec {motive : Nat → Type u}
--   (hb : ((b : Nat) → Nat.below (motive := motive) b → motive b))
--   : (∀ n : Nat, motive n) := by
--   intro n
--   have h1 : Nat.below (motive := motive) n := sorry
--   exact hb n h1


-- noncomputable def myFix {α : Type u} {r : α → α → Prop} {C : α → Type v}
--   (hWF : WellFounded r)
--   (recipe : (x : α) → ((y : α) → r y x → C y) → C x)
--   : (x : α) → C x :=
--   fun whl => recipe whl (fun (prt : α) (h : r prt whl) => myFix hWF recipe prt)
-- termination_by t => t
-- decreasing_by
--   have hrprt := WellFounded.apply hWF prt
--   have hrx := WellFounded.apply hWF x
--   simp
--   admit




inductive MyVector (α : Type u) : Nat → Type u
  | nil  : MyVector α 0
  | cons : α → {n : Nat} → MyVector α n → MyVector α (n+1)

open MyVector

def rev_append {α : Type u}
  : {n : Nat} → {m : Nat} → MyVector α n → MyVector α m → MyVector α (n + m)
  | _, 0, v, _ => v
  | 0, _, _, v => Eq.mp (by simp) v
  | n+1, m, cons a v1p, v2 => Eq.mp (by
    rw [Nat.add_assoc n 1 m, Nat.add_comm 1 m])
    (@rev_append α n (m+1) v1p (cons a v2))

def reverse {α : Type u} {n : Nat} (v : MyVector α n) : MyVector α n :=
  loop v nil
where
  loop : {n : Nat} → {m : Nat} → MyVector α n → MyVector α m → MyVector α (n + m)
    | 0, _, _, res => Eq.mp (by simp) res
    | n+1, m, cons a v1p, v2 => Eq.mp (by
      rw [Nat.add_assoc n 1 m, Nat.add_comm 1 m])
      (@loop n (m+1) v1p (cons a v2))

mutual
  def append {α : Type u} {n : Nat} {m : Nat} (v1 : MyVector α n) (v2 : MyVector α m)
    : MyVector α (n + m) :=
    rev_append (@reverse' α n v1) v2

  def reverse' {α : Type u} : {n : Nat} → MyVector α n → MyVector α n
    | 0, nil => nil
    | 1, v => v
    | np+1, cons a vp =>
      (@append α np 1 (@reverse' α np vp) (cons a nil))
end

#check Eq.mp
