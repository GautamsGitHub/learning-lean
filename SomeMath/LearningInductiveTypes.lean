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

theorem add_zero (n : MyNat) : myAdd n MyNat.zero = n := by
  match n with
  | MyNat.zero => rw [myAdd]
  | MyNat.succ pn =>
    rw [myAdd, add_zero]


theorem pred_minus (n1 : MyNat) (n2 : MyNat)
  : myPred (myMinus n1.succ n2) = myMinus n1 n2 := by
  match n2 with
  | MyNat.zero =>
    rw [myMinus, myMinus, myPred]
  | MyNat.succ pn2 =>
    rw [myMinus, myMinus, pred_minus]


theorem minus_self (n : MyNat) : myMinus n n = MyNat.zero := by
  match n with
  | MyNat.zero => rfl
  | MyNat.succ pn => rw [myMinus, pred_minus, minus_self]


theorem add_suc (n1 : MyNat) (n2 : MyNat) :
  myAdd n1 n2.succ = (myAdd n1 n2).succ := by
  match n1 with
  | MyNat.zero => rw [myAdd, myAdd]
  | MyNat.succ pn1 => rw [myAdd, add_suc, myAdd]

theorem comm_add (n1 : MyNat) (n2 : MyNat)
  : myAdd n1 n2 = myAdd n2 n1 := by
  match n2 with
  | MyNat.zero => rw [myAdd, add_zero]
  | MyNat.succ pn2 =>
    rw [add_suc, myAdd, comm_add]

theorem minus_cancels_add (n1 : MyNat) (n2 : MyNat) :
  myMinus (myAdd n2 n1) n2 = n1 := by
  match n2 with
  | MyNat.zero =>
    rw [myAdd, myMinus]
  | MyNat.succ pn2 =>
    rw [myAdd, myMinus, pred_minus, minus_cancels_add]
