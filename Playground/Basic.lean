def NonTail.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs

def Tail.sum (xs : List Nat) : Nat :=
  Tail.sumHelper 0 xs

theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  intro n
  induction xs generalizing n with
  | nil =>
    unfold NonTail.sum
    unfold Tail.sumHelper
    rfl
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sumHelper]
    rw [← Nat.add_assoc]
    rw [Nat.add_comm y]
    apply ih (n+y)

theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [NonTail.sum, Tail.sum]
  have h := non_tail_sum_eq_helper_accum xs 0
  simp at h
  trivial
