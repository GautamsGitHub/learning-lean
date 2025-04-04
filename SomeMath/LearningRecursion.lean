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

#check Acc

-- instance mywf {α : Type u} : WellFoundedRelation α :=
--   ⟨InvImage _ r sizeOf⟩


noncomputable def myFix {α : Type u} {r : α → α → Prop} {C : α → Type v}
  (hWF : WellFounded r)
  (recipe : (x : α) → ((y : α) → r y x → C y) → C x)
  : (x : α) → C x :=
  fun whl => recipe whl (fun (prt : α) (h : r prt whl) => myFix hWF recipe prt)
termination_by t => t
decreasing_by
  have hrprt := WellFounded.apply hWF prt
  have hrx := WellFounded.apply hWF x
  simp
  admit
