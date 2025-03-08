-- https://en.wikipedia.org/wiki/Lattice_(order)

import Mathlib.Tactic

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
  have h := @all_join (dual_partial_order_magma m) (dual_partial_order po)
    (dual_set_lattice sl) S ne
  tauto

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

-- this vs separate instance Lattice (SetLattice.toLattice ...)?
set_option pp.proofs true
noncomputable def SetLattice.toLattice {m : PartialOrderMagma} {po : PartialOrder m} (sl : SetLattice po) :
  Lattice {
    carrier := m.carrier,
    join := λ a b => Classical.choose (sl.two_join a b),
    meet := λ a b => Classical.choose (sl.two_meet a b)
  } :=
  {
    join_assoc := by
      simp
      intro a b c
      congr
      have ⟨h11, h12, h13⟩ := Classical.choose_spec (two_join po a b)
      set c1 := Classical.choose (two_join po a b)
      have ⟨h21, h22, h23⟩ := Classical.choose_spec (two_join po b c)
      set c2 := Classical.choose (two_join po b c)
      unfold isLeastUpperBound at *
      ext x
      simp at *
      constructor
      . intro ⟨h31, h32, h33⟩
        constructor
        . exact PartialOrder.trans a c1 x h11 h31
        . constructor
          . specialize h23 x
            have h : m.lte b x := PartialOrder.trans b c1 x h12 h31
            apply h23
            trivial
            trivial
          . intro y y1 y2
            specialize h33 y
            have h : m.lte c y := PartialOrder.trans c c2 y h22 y2
            specialize h13 y
            apply h13 at y1
            have h' : m.lte b y := PartialOrder.trans b c2 y h21 y2
            apply y1 at h'
            apply h33
            trivial
            trivial
      . intro ⟨h31, h32, h33⟩
        constructor
        . have h : m.lte b x := PartialOrder.trans b c2 x h21 h32
          specialize h13 x h31 h
          exact h13
        . constructor
          . exact PartialOrder.trans c c2 x h22 h32
          . intro y y1 y2
            have h : m.lte a y := PartialOrder.trans a c1 y h11 y1
            have h' : m.lte b y := PartialOrder.trans b c1 y h12 y1
            specialize h23 y h' y2
            exact h33 y h h23

    meet_assoc := by
      intro a b c
      have dl := dual_lattice sl.toLattice
      have h := dl.join_assoc a b c
      tauto

    join_comm := sorry,
    meet_comm := sorry,
    join_meet_absorb := sorry,
    meet_join_absorb := sorry
  }

end SetAlgebraEquivalence

end Playground
