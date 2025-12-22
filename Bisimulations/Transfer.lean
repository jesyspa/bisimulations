import Bisimulations.Relation

variable {β : Sort l}

def Transfers {Obs : β → Sort k} (RT : RelT Obs) (R : Rel β) (p q : β) :=
  R p q → ∀ op : Obs p, ∃ oq : Obs q, RT R op oq

variable {Obs : β → Sort k} {RT : RelT Obs} {R Q : Rel β}

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

structure TransferRel (RT : RelT Obs) (R : Rel β) where
  transfer : ∀ ⦃p q : β⦄, Transfers RT R p q

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
