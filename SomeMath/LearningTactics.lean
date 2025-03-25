open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r := by
  intro h
  cases h with
  | intro _ r => exact r

example (a : α) : r → (∃ _ : α, r) := by
  intro
  exists a

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  · intro h
    constructor
    · cases h with
      | intro x1 p1 => exists x1; exact And.left p1
    · cases h with
      | intro _ p1 => exact And.right p1
  · intro h
    cases And.left h with
    | intro x1 p1 => exists x1; apply And.intro p1; exact And.right h


example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  · intro h
    cases h with
    | intro x1 p1 =>
      cases p1 with
      | inl => apply Or.inl; exists x1
      | inr => apply Or.inr; exists x1
  · intro h
    cases h with
    | inl hl =>
      cases hl with
      | intro x1 p1 => exists x1; apply Or.inl; exact p1
    | inr hr =>
      cases hr with
      | intro x1 p1 => exists x1; apply Or.inr; exact p1

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  apply Iff.intro
  · intro h1 h2
    cases h2 with
    | intro x1 np1 => exact np1 (h1 x1)
  · intro h1 x1
    false_or_by_contra;
    have h2 : ∃ x, ¬ p x := by
      exists x1
    contradiction


example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  apply Iff.intro
  · intro h1
    false_or_by_contra
    have h2 : ∀ x , p x := by
      intro h2
      false_or_by_contra
      have h3 : ∃ x , ¬ p x := by
        exists h2
      contradiction
    contradiction
  · intro h1
    cases h1 with
    | intro w1 p1 =>
      intro h2
      exact p1 (h2 w1)


example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  apply Iff.intro
  · intro h1 h2
    cases h1 with
    | intro w1 p1 =>
      exact p1 (h2 w1)
  · intro h1
    by_cases h2 : r
    · exists a
      intro
      exact h2
    · by_cases h3 : ∃ x, ¬ p x
      · cases h3 with
        | intro w1 np1 => exists w1; intro; contradiction
      · have h4 : ∀ x, p x := by
          intro x1
          by_cases h5 : p x1
          · assumption
          · have h6 : ∃ x, ¬ p x := by exists x1
            contradiction
        have _ : r := h1 h4
        contradiction


example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  apply Iff.intro
  · intro h1 h2
    cases h1 with
    | intro x1 p1 => exists x1; exact p1 h2
  · intro h1
    by_cases h2 : r
    · cases h1 h2 with
      | intro x1 p1 => exists x1; intro; exact p1
    · exists a
      intro
      contradiction

example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (apply And.intro; repeat (first | assumption | apply Or.inl; assumption | apply Or.inr))
