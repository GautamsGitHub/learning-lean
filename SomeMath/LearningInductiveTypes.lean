inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

def myAdd (n1 : MyNat) (n2 : MyNat) : MyNat :=
  match n1 with
  | MyNat.zero => n2
  | (MyNat.succ pn1) => MyNat.succ (myAdd pn1 n2)

def myTimes (n1 : MyNat) (n2 : MyNat) : MyNat :=
  match n1 with
  | MyNat.zero => MyNat.zero
  | (MyNat.succ pn1) => myAdd n2 (myTimes pn1 n2)


def myPred (n : MyNat) : MyNat :=
  match n with
  | MyNat.zero => MyNat.zero
  | MyNat.succ pn => pn

def myMinus (n1 : MyNat) (n2 : MyNat) : MyNat :=
  match n2 with
  | MyNat.zero => n1
  | (MyNat.succ pn2) => myPred (myMinus n1 pn2)


def myGreaterThan (n1 : MyNat) (n2 : MyNat) : Bool :=
  match myMinus n1 n2 with
  | MyNat.zero => false
  | MyNat.succ _ => true

example (n1 : MyNat) (n2 : MyNat) : ((n1 = MyNat.zero) ∧ (n2 = MyNat.zero)) → n1 = n2 := by
  intro h1
  cases h1 with
  | intro hl hr =>
    rw [hl, hr]


theorem add_zero (n : MyNat) : myAdd n MyNat.zero = n := by
  match n with
  | MyNat.zero => rw [myAdd]
  | MyNat.succ pn =>
    rw [myAdd, add_zero]


theorem succ_succ_minus (n : MyNat)
  : myMinus n.succ.succ n = (myMinus n.succ n).succ := by

theorem succ_minus (n : MyNat) : myMinus n.succ n = MyNat.zero.succ := by
  match n with
  | MyNat.zero => rw [myMinus]
  | MyNat.succ pn =>
    rw [myMinus]
    sorry

theorem minus_cancels_add (n1 : MyNat) (n2 : MyNat) :
  myMinus (myAdd n2 n1) n2 = n1 := by
  match n2 with
  | MyNat.zero =>
    rw [myAdd, myMinus]
  | MyNat.succ pn2 =>
    rw [myAdd, myMinus]
    match n1 with
    | MyNat.zero =>
      sorry
    | MyNat.succ pn1 =>
      sorry
