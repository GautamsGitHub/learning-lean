namespace Hidden

open Nat

universe u

inductive List (α : Type u) where
  | empty : List α
  | cons : α → List α → List α

def l : List Nat := List.empty

inductive Listless where
  | empty : Listless
  | cons (α : Type u): α → Listless → Listless

def ll : Listless := Listless.empty
def ll1 := ll.cons Nat 3
def ll11 := Listless.cons Nat 3 ll
def ll2 := ll.cons (List Nat) l
def ll12 := ll1.cons (List Nat) l

def myfun : Listless → Nat
  | Listless.empty => 5
  | Listless.cons t _ _ => match t with
    | Nat => 54
    -- | _ => 24

#eval myfun ll2
