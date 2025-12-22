import Bisimulations.Relation
import Bisimulations.Transfer
import Bisimulations.Cotransfer

variable {β : Type l} {Obs : β → Sort k}

class DualRelTPair (RT QT : RelT Obs) where
  compl_left : ∀ R {p q : β} (op : Obs p) (oq : Obs q), ¬ RT R op oq ↔ QT (Compl R) op oq
  compl_right : ∀ R {p q : β} (op : Obs p) (oq : Obs q), RT (Compl R) op oq ↔ ¬ QT R op oq

variable {RT QT : RelT Obs} {R : Rel β}

lemma cotransfers_of_compl_transfers [pair : DualRelTPair RT QT]
    : Transfers RT R p q → Cotransfers QT (Compl R) p q := by
  intro htransf op hcont hrp
  rcases htransf hrp op with ⟨oq, hrq⟩
  specialize hcont oq
  rewrite [←pair.compl_left] at hcont
  contradiction

open Classical in
lemma transfers_of_compl_cotransfers [pair : DualRelTPair RT QT]
    : Cotransfers QT R p q → Transfers RT (Compl R) p q := by
  intro hcotransf hnr op
  apply byContradiction
  intro hnex
  apply hnr
  apply hcotransf op
  intro oq
  apply byContradiction
  intro hnr'
  apply hnex
  exists oq
  rewrite [pair.compl_right]
  assumption

lemma cotransfer_rel_of_compl_transfer_rel [pair : DualRelTPair RT QT]
    : TransferRel RT R → CotransferRel QT (Compl R) := by
  intro ⟨htransf⟩
  constructor
  intro p q
  apply @cotransfers_of_compl_transfers (pair := pair)
  apply htransf

lemma transfer_rel_of_compl_cotransfer_rel [pair : DualRelTPair RT QT]
    : CotransferRel QT R → TransferRel RT (Compl R) := by
  intro ⟨hcotransf⟩
  constructor
  intro p q
  apply @transfers_of_compl_cotransfers (pair := pair)
  apply hcotransf

lemma not_cotransfer_and_transfer_rel [pair : DualRelTPair RT QT]
    : cotransferRel QT p q → transferRel RT p q → False := by
  intro hcotransf ⟨R, htransf, hr⟩
  apply hcotransf (Compl R) ?_ hr
  apply @cotransfer_rel_of_compl_transfer_rel (pair := pair)
  assumption

open Classical in
lemma cotransfer_rel_of_not_transfer_rel [pair : DualRelTPair RT QT]
    : ¬ transferRel RT p q → cotransferRel QT p q := by
  intro hntransf R hctr
  apply byContradiction
  intro hnr
  apply hntransf
  refine ⟨Compl R, ?_, hnr⟩
  apply @transfer_rel_of_compl_cotransfer_rel (pair := pair)
  assumption

theorem cotransfer_rel_iff_not_transfer_rel [pair : DualRelTPair RT QT]
    : cotransferRel QT p q ↔ ¬ transferRel RT p q := by
  constructor
  · apply not_cotransfer_and_transfer_rel
  · apply cotransfer_rel_of_not_transfer_rel

theorem transfer_or_cotransfer_rel [pair : DualRelTPair RT QT]
    : transferRel RT p q ∨ cotransferRel QT p q := by
  cases em (transferRel RT p q)
  · left; assumption
  · right; apply @cotransfer_rel_of_not_transfer_rel (pair := pair); assumption
