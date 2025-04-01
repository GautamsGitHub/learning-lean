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

theorem reverse_reverse_loop {α : Type u} (xs rts : List α)
  : reverse.loop xs rts = reverse.loop (reverse.loop rts xs) empty := by
  match xs, rts with
  |

theorem reverse_reverse {α : Type u} (as : List α)
  : as = reverse (reverse as) := by
  have loopstarter (as : List α)
    : as = reverse.loop empty as := rfl
  have rrloop (as ras : List α)
    : reverse.loop as ras = reverse (reverse.loop ras as) :=
    List.recOn as
    (List.recOn ras (by simp [reverse.loop, reverse]) (by
      intros a as1 ih
      admit
    ))
    (by admit)
  calc as
    _ = reverse.loop empty as := loopstarter as
    _ = reverse (reverse.loop as empty) := rrloop empty as
    _ = reverse (reverse as) := by
      rw [rrloop as empty, ← loopstarter as]

theorem reverse_reverse' {α : Type u} (as : List α)
  : as = reverse (reverse as) := by
  have loopstarter (as : List α)
    : reverse.loop empty as = as := rfl
  have rrloop (as : List α)
    : reverse (reverse.loop as empty) = as :=
    List.recOn as
    (by simp [reverse.loop, reverse])
    (by
      intros a as h1
      rw [reverse.loop]
      admit
    )
  calc as
    _ = reverse (reverse.loop as empty) := by simp [rrloop]
    _ = reverse (reverse as) := by rw [← reverse]


variable (C : Nat → Type u)
variable (α : Type)
variable (r : Prop)

#check List.below
#reduce List.below (α := Nat) (motive := fun l => len l = len l) (cons 3 empty)
