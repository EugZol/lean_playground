import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

theorem left_cut : a * b < b ∧ b ≠ 0 → a = 0 := by
  intro i
  rcases i with ⟨l, _⟩
  have h : a < 1 := by exact lt_one_of_mul_lt_left l
  linarith

def prime_list (n : Nat) : List Nat :=
  List.filter Nat.Prime (List.range (n + 1))

theorem prime_list_member_le_n : ∀k ∈ prime_list n, k ≤ n := by
  intro k
  intro k_in_prime_list
  simp [prime_list] at k_in_prime_list
  linarith

def list_product (xs : List Nat) : Nat :=
  List.foldl (fun acc x => acc * x) 1 xs

theorem list_product_recursion (x : Nat) (xs : List Nat) : list_product (x :: xs) = x * list_product xs := by
  induction x generalizing xs with
  | zero =>
    simp [list_product]
    induction xs with
    | nil =>
      simp [list_product]
    | cons head tail ih_2 =>
      simp [list_product] at *
      trivial
  | succ y =>
    induction xs with
    | nil =>
      simp [list_product]
    | cons head tail =>
      simp [list_product] at *
      exact List.foldl_assoc

theorem list_product_ge_1 : list_product xs ≥ 1 ↔ ∀x ∈ xs, x ≠ 0 := by
  constructor
  . intro there
    intro x
    intro x_in_xs
    induction xs generalizing x with
    | nil =>
      contradiction
    | cons y ys ih =>
      rw [list_product_recursion] at there
      have y_ge_1 : y ≠ 0 := by
        by_contra y_eq_0
        rw [y_eq_0] at there
        ring_nf at there
        contradiction
      have h : y * list_product ys ≠ 0 := by exact Nat.not_eq_zero_of_lt there
      have h1 : list_product ys ≠ 0 := by exact Nat.ne_zero_of_mul_ne_zero_right h
      have ih_mp : list_product ys ≥ 1 := by
        exact Nat.one_le_iff_ne_zero.mpr h1
      by_cases x_is_head : x = y
      . rw [← x_is_head] at y_ge_1
        trivial
      . have x_in_ys : x ∈ ys := by exact List.mem_of_ne_of_mem x_is_head x_in_xs
        apply ih at ih_mp
        tauto
  . intro there
    induction xs with
    | nil =>
      decide
    | cons y ys ih =>
      rw [list_product_recursion]
      have y_ne_0 : y ≠ 0 := by exact Ne.symm (List.ne_of_not_mem_cons fun a ↦ there 0 a rfl)
      contrapose ih
      simp at *
      tauto

theorem product_list_member_le_product : (∀x, x ∈ xs → x ≠ 0) → (∀x, x ∈ xs → x ≤ list_product xs) := by
  intro there
  intro x
  intro x_in_xs
  have h := list_product_ge_1.mpr there
  induction xs generalizing x with
  | nil =>
    contradiction
  | cons y ys ih =>
    rw [list_product_recursion]
    rw [list_product_recursion] at h
    by_cases x_is_head : x = y
    . rw [x_is_head]
      refine Nat.le_mul_of_pos_right y ?_
      exact Nat.pos_of_mul_pos_left h
    . have x_is_tail : x ∈ ys := by exact List.mem_of_ne_of_mem x_is_head x_in_xs
      have there_r : ∀ x ∈ ys, x ≠ 0 := by
        by_contra contra
        simp at contra
        have c : 0 ∈ y::ys := by exact List.mem_cons_of_mem y contra
        tauto
      have y_ne_0 : y ≠ 0 := by exact Ne.symm (List.ne_of_not_mem_cons fun a ↦ there 0 a rfl)
      have g3 : list_product ys ≥ 1 := by
        exact list_product_ge_1.mpr there_r
      by_contra contra
      simp at contra
      have g4 : y * list_product ys < list_product ys := by exact Nat.lt_of_lt_of_le contra (ih there_r x x_is_tail g3)
      have g5 : list_product ys ≠ 0 := by exact Nat.not_eq_zero_of_lt g3
      have g6 := left_cut ⟨g4, g5⟩
      contradiction

theorem member_div_list_product (xs : List Nat) : x ∈ xs → x ∣ list_product xs := by
  intro x_in_xs
  induction xs generalizing x with
  | nil =>
    contradiction
  | cons y ys ih =>
    by_cases this_or_that : x = y
    . rw [this_or_that]
      rw [list_product_recursion]
      exact Nat.dvd_mul_right y (list_product ys)
    . have x_in_ys : x ∈ ys := by
        exact List.mem_of_ne_of_mem this_or_that x_in_xs
      apply ih at x_in_ys
      rw [list_product_recursion]
      exact Dvd.dvd.mul_left x_in_ys y

theorem in_range_x_then_in_range_x_add_one : ∀x ∈ List.range n, x ∈ List.range (n + 1) := by
  intro x
  intro x_in_range_n
  refine List.mem_range.mpr ?_
  induction x generalizing n with
  | zero =>
    simp at x_in_range_n
    linarith
  | succ y ih =>
    induction y with
    | zero =>
      simp at *
      linarith
    | succ z ih_z =>
      simp at *
      linarith

theorem prime_list_element_is_prime : ∀n, ∀x ∈ prime_list n, Nat.Prime x := by
  intro n
  intro x
  intro x_in_list
  apply List.mem_filter.mp at x_in_list
  simp at x_in_list
  exact x_in_list.right

theorem prime_is_element_of_prime_list : ∀k ≥ 2, ∀n ≥ k, Nat.Prime k → k ∈ prime_list n := by
  intro k
  intro k_ge_2
  intro n
  unfold prime_list
  induction k generalizing n with
  | zero =>
    linarith
  | succ x ih =>
    by_cases c : x = 1
    . rw [c]
      simp
      intro
      intro
      constructor
      . linarith
      . trivial
    . have x_ge_2 : x ≥ 2 := by
        simp at k_ge_2
        refine (Nat.two_le_iff x).mpr ?_
        constructor
        . linarith
        . trivial
      intro x_le_n
      simp at *
      intro x_add_one_prime
      constructor
      . exact x_le_n
      . exact x_add_one_prime

theorem only_primes_in_prime_list : ∀n, ∀p ≤ n, p ≥ 2 → (p ∈ prime_list n ↔ Nat.Prime p) := by
  intro n
  intro p
  intro p_le_n
  intro p_ge_2
  constructor
  . exact fun a ↦ prime_list_element_is_prime n p a
  . exact fun a ↦ prime_is_element_of_prime_list p p_ge_2 n p_le_n a

def primes_product n := list_product (prime_list n)

theorem prime_div_primes_product : ∀k ≤ n, k ≠ 0 → Nat.Prime k → k ∣ primes_product n := by
  unfold primes_product
  intro k
  intro k_le_n
  intro k_ne_0
  by_cases k_is_1 : k = 1
  . intro k_is_prime
    rw [k_is_1] at k_is_prime
    contradiction
  . have k_ge_2 : k ≥ 2 := by
      refine (Nat.two_le_iff k).mpr ?_
      tauto
    intro k_is_prime
    have k_in_list : k ∈ prime_list n := by exact
      (only_primes_in_prime_list n k k_le_n k_ge_2).mpr k_is_prime
    exact member_div_list_product (prime_list n) k_in_list

theorem infinite_primes : ∀n, ∃ k, Nat.Prime k ∧ k > n := by
  intro n
  by_cases n_eq_0 : n < 2
  . use 3
    constructor
    . trivial
    . tauto
  . simp at n_eq_0
    have n_gt_0 : n > 0 := by exact Nat.zero_lt_of_lt n_eq_0
    by_contra op
    simp at op
    let all_primes := prime_list n
    have all_primes_indeed : ∀x, Nat.Prime x → x ∈ all_primes := by
      intro x
      intro x_is_prime
      by_cases x_ge_2 : x >= 2
      . exact (only_primes_in_prime_list n x (op x x_is_prime) x_ge_2).mpr x_is_prime
      . simp at x_ge_2
        by_cases x_eq_0 : x = 0
        . rw [x_eq_0] at x_is_prime
          contradiction
        . have x_le_1 : x ≤ 1 := by
            exact Nat.le_of_lt_succ x_ge_2
          have x_eq_1 : x = 1 := by
            have x_gt_0 : x > 0 := by exact Nat.zero_lt_of_ne_zero x_eq_0
            linarith
          simp [all_primes]
          simp [prime_list]
          rw [x_eq_1]
          simp
          have t := op x x_is_prime
          rw [x_eq_1] at x_is_prime
          contradiction
    have all_primes_are_primes : ∀x, x ∈ all_primes → Nat.Prime x := by
      exact fun x a ↦ prime_list_element_is_prime n x a
    let next_prime := primes_product n + 1
    have next_prime_ge_2 : next_prime ≥ 2 := by
      have h : next_prime ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one (primes_product n))
      have h2 : next_prime ≠ 1 := by
        unfold_let next_prime at *
        unfold primes_product at *
        have h3 : list_product (prime_list n) ≥ 1 := by
          refine list_product_ge_1.mpr ?_
          intro x
          intro x_in_prime_list
          exact
            Nat.Prime.ne_zero
              (all_primes_are_primes x
                (all_primes_indeed x (all_primes_are_primes x x_in_prime_list)))
        linarith
      refine (Nat.two_le_iff next_prime).mpr ?_
      constructor
      . trivial
      . trivial
    by_cases c : Nat.Prime next_prime
    . have not_in_list : next_prime ∉ all_primes := by
        refine List.forall_mem_ne.mp ?_
        intro a'
        intro a'_in_all_primes
        refine Nat.ne_of_lt' ?_
        unfold_let next_prime
        unfold_let all_primes at a'_in_all_primes
        unfold primes_product
        have h : a' ≤ list_product (prime_list n) := by
          refine
            product_list_member_le_product ?_ a'
              (all_primes_indeed a'
                (all_primes_are_primes a'
                  (all_primes_indeed a' (all_primes_are_primes a' a'_in_all_primes))))
          intro x
          intro x_in_prime_list
          have h : Nat.Prime x := by exact all_primes_are_primes x (all_primes_indeed x (all_primes_are_primes x x_in_prime_list))
          exact
            Nat.Prime.ne_zero
              (all_primes_are_primes x
                (all_primes_indeed x (all_primes_are_primes x (all_primes_indeed x h))))
        linarith
      tauto
    . let min_fac := Nat.minFac next_prime
      have min_fac_is_prime : Nat.Prime min_fac := by
        refine Nat.minFac_prime ?n1
        exact Ne.symm (Nat.ne_of_lt next_prime_ge_2)
      have min_fac_ne_next_prime : min_fac < next_prime := by
        by_contra h
        unfold_let min_fac at h
        have h := (Nat.not_prime_iff_minFac_lt next_prime_ge_2).mp c
        linarith
      have min_fac_div_next_prime : min_fac ∣ next_prime := by
        exact Nat.minFac_dvd next_prime
      unfold_let next_prime at min_fac_div_next_prime
      rw [add_comm] at min_fac_div_next_prime
      have min_fac_not_div_prime_product : ¬ min_fac ∣ primes_product n := by
        by_contra h
        unfold_let next_prime at min_fac_ne_next_prime
        have h1 : min_fac ∣ 1 := by
          have h2 := (Nat.dvd_add_iff_left h).mpr min_fac_div_next_prime
          trivial
        have h2 : min_fac = 1 := by exact Nat.eq_one_of_dvd_one h1
        unfold_let min_fac at h2
        have h3 := Nat.minFac_eq_one_iff.mp h2
        linarith
      have h : min_fac ∣ primes_product n := by
        have h1 : min_fac ∈ all_primes := all_primes_indeed min_fac min_fac_is_prime
        refine
          prime_div_primes_product min_fac
            (op min_fac
              (all_primes_are_primes min_fac
                (all_primes_indeed min_fac (all_primes_are_primes min_fac h1))))
            ?_
            (all_primes_are_primes min_fac
              (all_primes_indeed min_fac
                (all_primes_are_primes min_fac (all_primes_indeed min_fac min_fac_is_prime))))
        exact
          Nat.Prime.ne_zero
            (all_primes_are_primes min_fac
              (all_primes_indeed min_fac
                (all_primes_are_primes min_fac (all_primes_indeed min_fac min_fac_is_prime))))
      contradiction

#check infinite_primes
