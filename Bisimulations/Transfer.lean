import Mathlib.Logic.Relation
import Bisimulations.Relation

variable {β : Type l}

def Transfers {Obs : β → Sort k} (RT : RelT Obs) (R : Rel β) (p q : β) :=
  R p q → ∀ op : Obs p, ∃ oq : Obs q, RT R op oq

variable {Obs : β → Sort k} {RT : RelT Obs} {R Q : Rel β}

variable (RT) in
class LawfulPosRelT extends LawfulRelT RT where
  preserves_reflexivity : ∀ R, Reflexive R → DepReflexive (RT R)
  preserves_transitivity : ∀ R, Transitive R → DepTransitive (RT R)

lemma transfers_closed_under_union [laws : LawfulRelT RT]
    : Transfers RT R p q → Transfers RT Q p q → Transfers RT (RelCup R Q) p q := by
  rintro htransfr htransfq (hr | hq) op
  · rcases htransfr hr op with ⟨oq, hr'⟩
    exists oq
    apply laws.monotone _ _ left_subrel_rel_cup
    assumption
  · rcases htransfq hq op with ⟨oq, hq'⟩
    exists oq
    apply laws.monotone _ _ right_subrel_rel_cup
    assumption

lemma transfers_closed_under_reflexivity [laws : LawfulPosRelT RT]
    : Transfers RT R p q → Transfers RT (Relation.ReflGen R) p q := by
  rintro htransf (_ | hr) op
  · exists op
    apply laws.preserves_reflexivity
    exact Relation.reflexive_reflGen
  · rcases htransf hr op with ⟨oq, hr'⟩
    exists oq
    apply laws.monotone _ _ subrel_reflgen
    assumption

structure TransferRel (RT : RelT Obs) (R : Rel β) where
  transfer : ∀ ⦃p q : β⦄, Transfers RT R p q

lemma transfer_rel_closed_under_transitivity [laws : LawfulPosRelT RT]
    : TransferRel RT R → TransferRel RT (Relation.TransGen R) := by
  intro ⟨htfs⟩
  constructor
  intro p _ hr
  induction hr
  case single q hr =>
    intro op
    rcases htfs hr op with ⟨oq, hr'⟩
    exists oq
    apply laws.monotone _ _ subrel_transgen
    assumption
  case tail q s hpq hqs ih =>
    intro op
    rcases ih op with ⟨oq, hpq'⟩
    rcases htfs hqs oq with ⟨or, hqs'⟩
    exists or
    apply laws.preserves_transitivity
    · exact Relation.transitive_transGen
    · assumption
    · apply laws.monotone _ _ subrel_transgen
      assumption

def transferRel (RT : RelT Obs) := Biggest (TransferRel RT)

lemma transfer_rel_closed_under_union [laws : LawfulRelT RT]
    : TransferRel RT R → TransferRel RT Q → TransferRel RT (RelCup R Q) := by
  intro ⟨htransfr⟩ ⟨htransfq⟩
  constructor
  intro p q
  apply transfers_closed_under_union
  · apply htransfr
  · apply htransfq

lemma subdeprel_of_transfer_rel
    : TransferRel RT R → SubRel R (transferRel RT) := biggest_is_maximal

lemma transfer_rel_of_transfer_rel [laws : LawfulRelT RT]
    : TransferRel RT (transferRel RT) := by
  constructor
  intro p q ⟨R, hstr, hr⟩ op
  rcases hstr.transfer hr op with ⟨oq, hr'⟩
  refine ⟨oq, ?_⟩
  apply laws.monotone R _ (subdeprel_of_transfer_rel hstr) hr'
