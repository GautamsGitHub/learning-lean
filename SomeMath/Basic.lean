def hello := "world"

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r :=
  fun h1 =>
    Exists.elim h1 (fun _ => (fun r => r))

example (a : α) : r → (∃ _ : α, r) :=
  fun p1 => (Exists.intro a p1)

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun h1 => Exists.elim h1 (fun w1 => fun p1 =>
      And.intro (Exists.intro w1 (And.left p1)) (And.right p1)))
    (fun h1 => Exists.elim h1.left (fun w1 => fun p1 =>
      Exists.intro w1 (And.intro p1 h1.right)))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun h1 => Exists.elim h1 (fun w1 => fun p1 =>
      Or.elim p1
        (fun pl => Or.inl (Exists.intro w1 pl))
        (fun pr => Or.inr (Exists.intro w1 pr))))
    (fun h1 => Or.elim h1
      (fun pl => Exists.elim pl (fun wl => fun pl1 =>
        Exists.intro wl (Or.inl pl1)))
      (fun pr => Exists.elim pr (fun wr => fun pr1 =>
        Exists.intro wr (Or.inr pr1))))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h1 => (fun p1 => Exists.elim p1 (fun w => fun p2 => p2 (h1 w))))
    (fun h1 x1 => byContradiction (fun h2 => h1 (Exists.intro x1 h2)))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (fun h1 => (fun p1 => Exists.elim h1 (fun w => fun p2 => (p1 w) p2)))
    (fun h1 => byContradiction (fun h2 =>
      h1 (fun h3 => fun h4 => h2 (Exists.intro h3 h4))))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (fun h1 => fun x1 => fun p1 => h1 (Exists.intro x1 p1))
    (fun h1 => fun h2 => Exists.elim h2 (fun p1 => h1 p1))

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h1 => byContradiction (fun h2 =>
      h1 (fun h3 => byContradiction (fun h4 => h2 ⟨ h3, h4 ⟩ ))))
    (fun h1 => Exists.elim h1 (fun w1 p1 => fun p2 => p1 (p2 w1)))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (fun h1 => fun h2 => Exists.elim h2 (fun w1 p1 => (h1 w1) p1))
    (fun h1 => fun h2 => fun p1 => h1 (Exists.intro h2 p1))

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun h1 => fun h2 => Exists.elim h1 (fun w1 p1 => p1 (h2 w1)))
    (fun h1 => byCases
      (fun r1 : r => ⟨ a, fun _ => r1 ⟩ )
      (fun nr1 => byContradiction (fun h2 =>
        nr1 (h1 (fun x1 => byContradiction (fun h3 =>
          h2 (Exists.intro x1 (fun h4 => False.elim (h3 h4)))))))))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun h1 => fun r1 => Exists.elim h1 (fun w1 p1 => Exists.intro w1 (p1 r1)))
    (fun h1 => byCases
      (fun r1 : r => Exists.elim (h1 r1) (fun w1 p1 => ⟨ w1 , fun _ => p1 ⟩ ))
      (fun nr1 => Exists.intro a (fun p1 => False.elim (nr1 p1))))


example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun h1 => byCases
      (fun r1 : r => Or.inr r1)
      (fun nr1 => Or.inl (fun x1 => Or.elim (h1 x1) (id) (fun r1 => False.elim (nr1 r1)))))
    (fun h1 => fun x1 => Or.elim h1 (fun p1 => Or.inl (p1 x1)) (fun r1 => Or.inr r1))


variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  Iff.elim
    (fun h1 h2 => byCases
      (fun p1 : shaves barber barber => (h1 p1) p1)
      (fun np1 => np1 (h2 np1)))
    (h barber)
