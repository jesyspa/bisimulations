import Bisimulations.Relation
import Bisimulations.Transfer
import Bisimulations.Cotransfer

variable {β : Sort l} {Obs : β → Sort k} {RT : RelT Obs} {R : Rel β}

-- The converse does not generally seem to hold.
lemma cotransfers_of_compl_transfers [laws : LawfulRelT RT]
    : Transfers RT R p q → Cotransfers RT (Compl R) p q := by
  intro htransf op hcont hrp
  rcases htransf hrp op with ⟨oq, hrq⟩
  apply laws.not_both_direct_and_compl
  · assumption
  · apply hcont

open Classical in
lemma transfers_of_compl_cotransfers [laws : LawfulRelT RT]
    : Cotransfers RT R p q → Transfers RT (Compl R) p q := by
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
  sorry -- Meow :( Not sure whether I can prove this



lemma cotransfer_rel_of_compl_transfer_rel [laws : LawfulRelT RT]
    : TransferRel RT R → CotransferRel RT (Compl R) := by
  intro ⟨htransf⟩
  constructor
  intro p q
  apply cotransfers_of_compl_transfers
  apply htransf

lemma transfer_rel_of_compl_cotransfer_rel [laws : LawfulRelT RT]
    : CotransferRel RT R → TransferRel RT (Compl R) := by
  intro ⟨hcotransf⟩
  constructor
  intro p q
  apply transfers_of_compl_cotransfers
  apply hcotransf

lemma not_transfer_and_cotransfer_rel [laws : LawfulRelT RT]
    : transferRel RT p q → cotransferRel RT p q → False := by
  intro ⟨R, htransf, hr⟩ hcotransf
  exact hcotransf _ (cotransfer_rel_of_compl_transfer_rel htransf) hr

open Classical in
lemma cotransfer_rel_of_not_transfer_rel [laws : LawfulRelT RT]
    : ¬ transferRel RT p q → cotransferRel RT p q := by
  intro hntransf R hctr
  apply byContradiction
  intro hnr
  apply hntransf
  refine ⟨Compl R, ?_, hnr⟩


  sorry

open Classical in
lemma transfer_or_cotransfer_rel [laws : LawfulRelT RT]
    : transferRel RT p q ∨ cotransferRel RT p q := by
  cases em (transferRel RT p q)
  · left; assumption
  · right; apply cotransfer_rel_of_not_transfer_rel; assumption
