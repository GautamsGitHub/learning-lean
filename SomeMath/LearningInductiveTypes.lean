inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

def myPlus (n1 : MyNat) (n2 : MyNat) : MyNat :=
  match n1 with
  | MyNat.zero => n2
  | (MyNat.succ pn1) => MyNat.succ (myPlus pn1 n2)

def myTimes (n1 : MyNat) (n2 : MyNat) : MyNat :=
  match n1 with
  | MyNat.zero => MyNat.zero
  | (MyNat.succ pn1) => myPlus n2 (myTimes pn1 n2)


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

theorem plus_zero (n : MyNat) : myPlus n MyNat.zero = n := by
  match n with
  | MyNat.zero => rw [myPlus]
  | MyNat.succ pn =>
    rw [myPlus, plus_zero]


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


theorem plus_succ (n1 : MyNat) (n2 : MyNat) :
  myPlus n1 n2.succ = (myPlus n1 n2).succ := by
  match n1 with
  | MyNat.zero => rw [myPlus, myPlus]
  | MyNat.succ pn1 => rw [myPlus, plus_succ, myPlus]

theorem comm_plus (n1 : MyNat) (n2 : MyNat)
  : myPlus n1 n2 = myPlus n2 n1 := by
  match n2 with
  | MyNat.zero => rw [myPlus, plus_zero]
  | MyNat.succ pn2 =>
    rw [plus_succ, myPlus, comm_plus]

theorem minus_cancels_plus (n1 : MyNat) (n2 : MyNat) :
  myMinus (myPlus n2 n1) n2 = n1 := by
  match n2 with
  | MyNat.zero =>
    rw [myPlus, myMinus]
  | MyNat.succ pn2 =>
    rw [myPlus, myMinus, pred_minus, minus_cancels_plus]

def myExponent (b : MyNat) (e : MyNat) : MyNat :=
  match e with
  | MyNat.zero => MyNat.zero.succ
  | MyNat.succ pe => myTimes b (myExponent b pe)


theorem times_zero (n : MyNat)
  : myTimes n MyNat.zero = MyNat.zero := by
  match n with
  | MyNat.zero => rw [myTimes]
  | MyNat.succ pn => rw [myTimes, myPlus, times_zero]

theorem assoc_plus (n1 n2 n3 : MyNat)
  : myPlus n1 (myPlus n2 n3) = myPlus (myPlus n1 n2) n3 := by
  match n2 with
  | MyNat.zero => rw [myPlus, plus_zero]
  | MyNat.succ pn2 => rw [myPlus, plus_succ, plus_succ, myPlus, assoc_plus]

theorem times_succ (n1 : MyNat) (n2 : MyNat)
  : myTimes n1 n2.succ = myPlus n1 (myTimes n1 n2) := by
  match n1 with
  | MyNat.zero => rw [myTimes, myPlus, myTimes]
  | MyNat.succ pn1 =>
    rw [
      myTimes,
      myPlus,
      myTimes,
      myPlus,
      times_succ,
      assoc_plus,
      assoc_plus,
      comm_plus n2 pn1
      ]

theorem comm_times (n1 : MyNat) (n2 : MyNat)
  : myTimes n1 n2 = myTimes n2 n1 := by
  match n1 with
  | MyNat.zero => rw [times_zero, myTimes]
  | MyNat.succ pn1 => rw [myTimes, times_succ, comm_times]

theorem dist_times_plus (m n1 n2 : MyNat)
  : myTimes m (myPlus n1 n2) = myPlus (myTimes m n1) (myTimes m n2) := by
  match m with
  | MyNat.zero => simp [myTimes, myPlus]
  | MyNat.succ pm =>
    have h1 (a b c d : MyNat)
      : myPlus (myPlus a b) (myPlus c d) = myPlus (myPlus a c) (myPlus b d) := by
      rw [
        ←assoc_plus,
        assoc_plus b c d,
        comm_plus b c,
        ← assoc_plus c b d,
        assoc_plus]
    rw [
      myTimes,
      myTimes,
      myTimes,
      h1,
      dist_times_plus]

theorem assoc_times (n1 n2 n3 : MyNat)
  : myTimes n1 (myTimes n2 n3) = myTimes (myTimes n1 n2) n3 := by
  match n2 with
  | MyNat.zero => rw [myTimes, times_zero, myTimes]
  | MyNat.succ pn2 =>
    rw [
      myTimes,
      times_succ,
      dist_times_plus,
      comm_times (myPlus _ _) _,
      dist_times_plus,
      comm_times n3 _,
      comm_times n3 _,
      assoc_times
      ]

theorem multiplying_exponents (b : MyNat) (e1 : MyNat) (e2 : MyNat)
  : myTimes (myExponent b e1) (myExponent b e2) = (myExponent b (myPlus e1 e2)) := by
  match e1 with
  | MyNat.zero => rw [myExponent, myTimes, myTimes, plus_zero, myPlus]
  | MyNat.succ pe1 =>
    rw [myExponent, myPlus, myExponent, ← assoc_times, multiplying_exponents];
