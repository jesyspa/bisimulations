import Bisimulations.Relation

variable {β : Type l}

def Cotransfers {Obs : β → Sort k} (RT : RelT Obs) (R : Rel β) (p q : β) :=
  ∀ op : Obs p, (∀ oq : Obs q, RT R op oq) → R p q

variable {Obs : β → Sort k} {RT : RelT Obs} {R : Rel β}

structure CotransferRel (RT : RelT Obs) (R : Rel β) where
  cotransfer : ∀ ⦃p q : β⦄, Cotransfers RT R p q

def cotransferRel (RT : RelT Obs) := Smallest (CotransferRel RT)

lemma superdeprel_of_cotransfer_rel
    : CotransferRel RT R → SubRel (cotransferRel RT) R := smallest_is_minimal

lemma cotransfer_rel_of_cotransfer_rel [laws : LawfulRelT RT]
    : CotransferRel RT (cotransferRel RT) := by
  constructor
  intro p q op hcont R hctr
  apply hctr.cotransfer
  · intro oq
    apply laws.monotone _ _ (superdeprel_of_cotransfer_rel hctr)
    apply hcont
