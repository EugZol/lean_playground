-- https://en.wikipedia.org/wiki/Lattice_(order)

import Mathlib.Tactic
set_option pp.proofs true

namespace Playground

-- A partially ordered set (poset) (L,≤) is called a lattice if it is both
-- a join- and a meet-semilattice, i.e. each two-element subset {a,b} ⊆ L has
-- a join (i.e. least upper bound) and dually a meet (i.e. greatest lower bound).

structure PartialOrderMagma :=
  (carrier : Type)
  (lte : carrier → carrier → Prop)

class PartialOrder (m : PartialOrderMagma) :=
  (rfl : ∀ a, m.lte a a)
  (asymm : ∀ a b, m.lte a b → m.lte b a → a = b)
  (trans : ∀ a b c, m.lte a b → m.lte b c → m.lte a c)

def isLeastUpperBound (m : PartialOrderMagma) (a b c : m.carrier) :=
  m.lte a c ∧ m.lte b c ∧ (
    ∀ another_c, m.lte a another_c ∧ m.lte b another_c → m.lte c another_c
  )

def isGreatestLowerBound (m : PartialOrderMagma) (a b c : m.carrier) :=
  m.lte c a ∧ m.lte c b ∧ (
    ∀ another_c, m.lte another_c a ∧ m.lte another_c b → m.lte another_c c
  )

class SetLattice (po : PartialOrder m) :=
  (two_join : ∀ a b, ∃ c, isLeastUpperBound m a b c)
  (two_meet : ∀ a b, ∃ c, isGreatestLowerBound m a b c)

section SetLatticeProperties

variable {m : PartialOrderMagma} [po : PartialOrder m]

-- Each semilattice is the dual of the other.

def dual_partial_order_magma (m : PartialOrderMagma) : PartialOrderMagma :=
  {
    carrier := m.carrier,
    lte := fun a b => m.lte b a
  }

def dual_partial_order (po : PartialOrder m) : PartialOrder (dual_partial_order_magma m) :=
  {
    rfl := po.rfl,
    asymm := fun a b hab hba => symm (po.asymm b a hab hba),
    trans := fun a b c hab hbc => po.trans c b a hbc hab
  }

def dual_set_lattice (sl : SetLattice po) : SetLattice (dual_partial_order po) :=
  {
    two_join := fun a b => by
      have h := sl.two_meet b a
      unfold isLeastUpperBound
      unfold isGreatestLowerBound at h
      tauto
    two_meet := fun a b => by
      have h := sl.two_join b a
      unfold isLeastUpperBound at h
      unfold isGreatestLowerBound
      tauto
  }

-- It follows by an induction argument that every non-empty finite subset of a lattice
-- has a least upper bound and a greatest lower bound.

theorem all_join (sl : SetLattice po) (S : Finset m.carrier) (ne : S ≠ ∅) : ∃ c, ((∀ x ∈ S, m.lte x c) ∧ (
  ∀ another_c, (∀ x ∈ S, m.lte x another_c) → m.lte c another_c
)) := by
  induction S using Finset.induction_on
  case inst =>
    exact Classical.typeDecidableEq m.carrier
  case empty =>
    trivial
  case insert a S2 _ IH =>
    by_cases h : S2 = ∅
    . use a
      rw [h]
      constructor
      . simp
        exact PartialOrder.rfl a
      . simp
    . apply IH at h
      obtain ⟨c, ⟨hc1, hc2⟩⟩ := h
      simp
      have h := sl.two_join a c
      obtain ⟨a', ⟨ha1', ⟨ha2', ha3'⟩⟩⟩ := h
      use a'
      constructor
      . constructor
        . trivial
        . intro a''
          intro a''_in_s
          exact PartialOrder.trans a'' c a' (hc1 a'' a''_in_s) ha2'
      . intro x'
        intro a_lte_x'
        intro x''
        specialize ha3' x'
        apply ha3'
        tauto

theorem all_meet (sl : SetLattice po) (S : Finset m.carrier) (ne : S ≠ ∅) : ∃ c, ((∀ x ∈ S, m.lte c x) ∧ (
  ∀ another_c, (∀ x ∈ S, m.lte another_c x) → m.lte another_c c
)) := by
  exact @all_join (dual_partial_order_magma m) (dual_partial_order po)
    (dual_set_lattice sl) S ne

end SetLatticeProperties

structure LatticeDoubleMagma :=
  (carrier : Type)
  (join : carrier → carrier → carrier)
  (meet : carrier → carrier → carrier)

class Lattice (m : LatticeDoubleMagma) :=
  (join_assoc : ∀ a b c, m.join (m.join a b) c = m.join a (m.join b c))
  (meet_assoc : ∀ a b c, m.meet (m.meet a b) c = m.meet a (m.meet b c))
  (join_comm : ∀ a b, m.join a b = m.join b a)
  (meet_comm : ∀ a b, m.meet a b = m.meet b a)
  (join_meet_absorb : ∀ a b, m.join a (m.meet a b) = a)
  (meet_join_absorb: ∀ a b, m.meet a (m.join a b) = a)

section LatticeProperties

variable {m : LatticeDoubleMagma}

-- Each semilattice is the dual of the other.

def dual_lattice_double_magma (lm : LatticeDoubleMagma) : LatticeDoubleMagma :=
  {
    carrier := lm.carrier,
    join := fun a b => lm.meet a b,
    meet := fun a b => lm.join a b
  }

def dual_lattice (l : Lattice m) : Lattice (dual_lattice_double_magma m) :=
  {
    join_assoc := l.meet_assoc,
    meet_assoc := l.join_assoc,
    join_comm := l.meet_comm,
    meet_comm := l.join_comm,
    join_meet_absorb := l.meet_join_absorb,
    meet_join_absorb := l.join_meet_absorb
  }

theorem join_idempotency (l : Lattice m) : ∀ a, m.join a a = a := by
  intro  a
  nth_rw 2 [← l.meet_join_absorb a a]
  rw [l.join_meet_absorb]

theorem meet_idempotency (l : Lattice m) : ∀ a, m.meet a a = a := by
  intro a
  nth_rw 2 [← l.join_meet_absorb a a]
  rw [l.meet_join_absorb]

end LatticeProperties

section SetAlgebraEquivalence

noncomputable def set_lattice_to_lattice_double_magma
  {pom : PartialOrderMagma}
  {po : PartialOrder pom}
  (sl : SetLattice po) :
  LatticeDoubleMagma :=
  {
    carrier := pom.carrier,
    join := λ a b => Classical.choose (sl.two_join a b),
    meet := λ a b => Classical.choose (sl.two_meet a b)
  }

lemma join_assoc_eq
  {pom : PartialOrderMagma}
  {po : PartialOrder pom}
  (sl : SetLattice po) :
  let m := set_lattice_to_lattice_double_magma sl; ∀ a b c, m.join (m.join a b) c = m.join a (m.join b c) := by
  intro m
  intro a b c
  have hm : m.join = λ a b => Classical.choose (sl.two_join a b) := rfl
  rw [hm]
  simp
  congr
  -- Goal: isLeastUpperBound pom (Classical.choose (SetLattice.two_join po a b)) c =
  --   isLeastUpperBound pom a (Classical.choose (SetLattice.two_join po b c))
  -- Replacing encompassing expressions for "two_join a b" and "two_join b c"
  --   with join_ab and join_bc (and judgements about them h_join_ab, h_join_bc)
  --   respectively
  have h_join_ab := Classical.choose_spec (SetLattice.two_join po a b)
  have h_join_bc := Classical.choose_spec (SetLattice.two_join po b c)
  set join_ab := Classical.choose (SetLattice.two_join po a b)
  set join_bc := Classical.choose (SetLattice.two_join po b c)
  unfold isLeastUpperBound at *
  ext x
  -- Goal: x is least upper bound for join_ab and c ↔
  --   x is least upper bound for a and join_bc
  constructor
  . intro h' -- ->
    -- We are given:
    --
    --    ┌─────► x ◄──────┐
    --    │(h'.1)          │
    -- join_ab   join_bc   │(h'.2)
    --  ▲   ▲     ▲   ▲    │
    --  │   │     │   │    │
    --  a   └─ b ─┘   c ───┘
    --
    -- Goal:
    --
    -- ┌─► x ◄─┐
    -- │       │
    -- a    join_bc
    --
    -- By definition of least upper bound, we are to prove three facts:
    --
    -- 1. lte a x
    -- 2. lte join_bc x
    -- 3. if there is another such (1. and 2.) element x', then lte x x'
    --
    have h1 : pom.lte a x :=
      -- Proved by transitivity: a -> join_ab -> x
      PartialOrder.trans a join_ab x h_join_ab.1 h'.1
    refine ⟨h1, ?_⟩
    have h2 : pom.lte join_bc x :=
      -- Proved by: x is upper bound for b and c;
      --   but join_bc is LEAST upper bound for b and c
      h_join_bc.2.2 x ⟨PartialOrder.trans b join_ab x h_join_ab.2.1 h'.1, h'.2.1⟩
    refine ⟨h2, ?_⟩
    -- Remaining goal: ∀ x', lte a x' ∧ lte join_bc x' → lte x x'
    intro x' ⟨a_lte_x', join_bc_lte_x'⟩
    -- Proved by:
    -- 1. x' is upper bound for a, b => lte join_ab x' (least upper bound property of join_ab)
    -- 2. x' is upper bound for join_ab, c => lte x x' (least upper bound property of x)
    have b_lte_x' : pom.lte b x' := PartialOrder.trans b join_bc x' h_join_bc.1 join_bc_lte_x'
    have join_ab_lte_x' : pom.lte join_ab x' :=
      h_join_ab.2.2 x' ⟨a_lte_x', b_lte_x'⟩
    have c_lte_x' : pom.lte c x' := PartialOrder.trans c join_bc x' h_join_bc.2.1 join_bc_lte_x'
    exact h'.2.2 x' ⟨join_ab_lte_x', c_lte_x'⟩
  . intro h' -- <-
    -- We are given:
    --
    --  ┌──────► x ◄─────┐
    --  │(h'.1)          │(h'.2)
    --  │   join_ab   join_bc
    --  │    ▲   ▲     ▲   ▲
    --  │    │   │     │   │
    --  └─── a   └─ b ─┘   c
    --
    -- Goal:
    --
    --    ┌─► x ◄─┐
    --    │       │
    -- join_ab    c
    --
    -- By definition of least upper bound, we are to prove three facts:
    --
    -- 1. lte join_ab x
    -- 2. lte c x
    -- 3. if there is another such (1. and 2.) element x', then lte x x'
    --
    have h1 : pom.lte join_ab x :=
      -- Proved by: x is upper bound for a and b;
      --   but join_ab is LEAST upper bound for a and b
      h_join_ab.2.2 x ⟨h'.1, PartialOrder.trans b join_bc x h_join_bc.1 h'.2.1⟩
    refine ⟨h1, ?_⟩
    have h2 : pom.lte c x :=
      -- Proved by transitivity: с -> join_bc -> x
      PartialOrder.trans c join_bc x h_join_bc.2.1 h'.2.1
    refine ⟨h2, ?_⟩
    -- Remaining goal: ∀ x', lte join_ab x' ∧ lte c x' → lte x x'
    intro x' ⟨join_ab_lte_x', c_lte_x'⟩
    -- Proved by:
    -- 1. x' is upper bound for b, c => lte join_bc x' (least upper bound property of join_bc)
    -- 2. x' is upper bound for a, join_bc => lte x x' (least upper bound property of x)
    have b_lte_x' : pom.lte b x' := PartialOrder.trans b join_ab x' h_join_ab.2.1 join_ab_lte_x'
    have join_bc_lte_x' : pom.lte join_bc x' :=
      h_join_bc.2.2 x' ⟨b_lte_x', c_lte_x'⟩
    have a_lte_x' : pom.lte a x' := PartialOrder.trans a join_ab x' h_join_ab.1 join_ab_lte_x'
    exact h'.2.2 x' ⟨a_lte_x', join_bc_lte_x'⟩

lemma meet_assoc_eq
  {pom : PartialOrderMagma}
  {po : PartialOrder pom}
  (sl : SetLattice po) :
  let m := set_lattice_to_lattice_double_magma sl; ∀ a b c, m.meet (m.meet a b) c = m.meet a (m.meet b c) := by
  exact join_assoc_eq (dual_set_lattice sl)

-- this vs separate instance Lattice (SetLattice.toLattice ...)?
noncomputable def SetLattice.toLattice {m : PartialOrderMagma} {po : PartialOrder m} (sl : SetLattice po) :
  Lattice {
    carrier := m.carrier,
    join := λ a b => Classical.choose (sl.two_join a b),
    meet := λ a b => Classical.choose (sl.two_meet a b)
  } :=
  {
    join_assoc := join_assoc_eq sl,
    meet_assoc := meet_assoc_eq sl,
    join_comm := sorry,
    meet_comm := sorry,
    join_meet_absorb := sorry,
    meet_join_absorb := sorry
  }

end SetAlgebraEquivalence

end Playground
