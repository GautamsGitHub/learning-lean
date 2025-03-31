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

theorem reverse_maintains_length {α : Type u} (as : List α)
  : len as = len (reverse as) :=
  List.recOn (motive := fun as => len as = len (reverse as))
    as
    (show len empty = len (reverse empty) from rfl)
    (fun (a : α) (as : List α) (ih : len as = len (reverse as)) =>
     show len (cons a as) = len (reverse (cons a as)) from
     calc len (cons a as)
      _ = 1 + len as := rfl
      _ = 1 + len (reverse as) := by rw [ih]
      _ = len (reverse (cons a as)) := by
        rw [reverse]
        sorry -- would need auxiliary lemma about reverse.loop
        )

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
