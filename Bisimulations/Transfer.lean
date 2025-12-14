import Bisimulations.Relation

variable {β : Sort l}

def Transfers {Obs : β → Sort k} (RT : RelT Obs) (R : Rel β) (p q : β) :=
  R p q → ∀ op : Obs p, ∃ oq : Obs q, RT R op oq

variable {Obs : β → Sort k} {RT : RelT Obs} {R : Rel β}

structure TransferRel (RT : RelT Obs) (R : Rel β) where
  transfer : ∀ ⦃p q : β⦄, Transfers RT R p q

def transferRel (RT : RelT Obs) := Biggest (TransferRel RT)

lemma subdeprel_of_transfer_rel
    : TransferRel RT R → SubRel R (transferRel RT) := biggest_is_maximal

lemma transfer_rel_of_transfer_rel [laws : LawfulRelT RT]
    : TransferRel RT (transferRel RT) := by
  constructor
  intro p q ⟨R, hstr, hr⟩ op
  rcases hstr.transfer hr op with ⟨oq, hr'⟩
  refine ⟨oq, ?_⟩
  apply laws.monotone R _ (subdeprel_of_transfer_rel hstr) hr'
