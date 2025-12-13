import Mathlib.Order.Defs.Unbundled
import Bisimulations.LTS
import Bisimulations.Relation

variable {α} {lts : LTS α}

structure StrongBisimulation (R : Rel lts) : Prop where
  symmetric : Symmetric R
  transfer : ∀ a, Transfers (lts.transition a) R

def bisimilar : Rel lts := Biggest StrongBisimulation

lemma strong_bisimulation_reverse {R : Rel lts}
    : StrongBisimulation R → StrongBisimulation (flip R) := by
  rintro ⟨hsymm, htransf⟩
  constructor
  · intro p q
    apply hsymm
  · intro a
    exact (transfers_of_symmetric hsymm (htransf a))

@[simp] lemma symmetric_bisimilar : Symmetric (@bisimilar (lts := lts)) := by
  rintro p q ⟨R, h_sb, hr⟩
  refine ⟨R, h_sb, h_sb.symmetric hr⟩

theorem strong_bisimulation_of_bisimilar : StrongBisimulation (@bisimilar (lts := lts)) := by
  refine ⟨symmetric_bisimilar, ?_⟩
  rintro a p p' q ht ⟨R, h_sb, hr⟩
  rcases (h_sb.transfer a ht hr) with ⟨q', ht', hr'⟩
  exact ⟨q', ht', ⟨R, h_sb, hr'⟩⟩

structure DirectedStrongBisimulation (R : Rel lts) : Prop where
  transfer : ∀ a, DirectedTransfers (lts.transition a) R

def directed_bisimilar : Rel lts := Biggest DirectedStrongBisimulation

theorem directed_strong_bisimulation_of_directed_bisimilar
    : DirectedStrongBisimulation (@directed_bisimilar (lts := lts)) := by
  constructor
  rintro a p p' q ht ⟨R, h_sb, hr⟩
  rcases (h_sb.transfer a ht hr) with ⟨q', ht', ⟨hrl', hrr'⟩⟩
  refine ⟨q', ht', ?_⟩
  constructor <;> refine ⟨R, h_sb, ?_⟩ <;> assumption

lemma directed_strong_bisimulation_of_strong_bisimulation {R : Rel lts}
    : StrongBisimulation R → DirectedStrongBisimulation R := by
  intro ⟨hsymm, htransf⟩
  constructor
  intro a
  apply_rules [directed_transfers_of_transfers_of_symmetric]

lemma directed_bisimilar_of_bisimilar {p q : lts.Node}
    : bisimilar p q → directed_bisimilar p q := by
  intro ⟨R, h_sb, hr⟩
  refine ⟨R, ?_, hr⟩
  exact directed_strong_bisimulation_of_strong_bisimulation h_sb

lemma strong_bisimulation_of_symm_interior_of_directed_strong_bisimulation {R : Rel lts}
    : DirectedStrongBisimulation R → StrongBisimulation (SymmInterior R) := by
  intro h_dsb
  refine ⟨symmetric_of_symm_interior, ?_⟩
  intro a p p' q ht ⟨hrl, hrr⟩
  exact h_dsb.transfer a ht hrl

lemma strong_bisimulation_of_directed_bisimilar
    : StrongBisimulation (SymmInterior (@directed_bisimilar (lts := lts))) :=
  strong_bisimulation_of_symm_interior_of_directed_strong_bisimulation
    directed_strong_bisimulation_of_directed_bisimilar

theorem bisimilar_iff_symm_interior_of_directed_bisimilar {p q : lts.Node}
    : bisimilar p q ↔ SymmInterior directed_bisimilar p q := by
  constructor
  · intro hb
    constructor <;> apply directed_bisimilar_of_bisimilar
    · assumption
    · apply symmetric_bisimilar; assumption
  · rintro ⟨h_db, h_db'⟩
    refine ⟨SymmInterior directed_bisimilar, strong_bisimulation_of_directed_bisimilar, ?_⟩
    constructor <;> assumption

structure StrongApartness (R : Rel lts) : Prop where
  symmetry : Symmetric R
  cotransfer : ∀ a, CoTransfers (lts.transition a) R

def apart : Rel lts := Smallest StrongApartness

lemma strong_apartness_of_compl_strong_bisimulation {R : Rel lts}
    : StrongBisimulation R → StrongApartness (Compl R) := by
  intro ⟨hsymm, htransf⟩
  refine ⟨symmetric_of_compl hsymm, ?_⟩
  intro a
  apply cotransfers_of_compl_transfers
  apply htransf

lemma strong_bisimulation_of_compl_strong_apartness {R : Rel lts}
    : StrongApartness R → StrongBisimulation (Compl R) := by
  intro ⟨hsymm, hcotransf⟩
  refine ⟨symmetric_of_compl hsymm, ?_⟩
  intro a
  apply transfers_of_compl_cotransfers
  apply hcotransf

theorem not_bisimilar_and_apart {p q : lts.Node}
    : bisimilar p q → apart p q → False := by
  rintro ⟨R, hsb, hr⟩ ha
  have := strong_apartness_of_compl_strong_bisimulation hsb
  exact ha (Compl R) this hr

open Classical in
theorem apart_of_not_bisimilar {p q : lts.Node}
    : ¬bisimilar p q → apart p q := by
  intro hnb Q hsa
  apply byContradiction
  intro hnq
  apply hnb
  exact ⟨Compl Q, strong_bisimulation_of_compl_strong_apartness hsa, hnq⟩

open Classical in
theorem bisimilar_or_apart {p q : lts.Node}
    : bisimilar p q ∨ apart p q := by
  cases em (bisimilar p q)
  · left; assumption
  · right; apply apart_of_not_bisimilar; assumption
