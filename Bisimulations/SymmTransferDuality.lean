import Bisimulations.Relation
import Bisimulations.SymmTransfer
import Bisimulations.SymmCotransfer
import Bisimulations.TransferDuality

-- These theorems are very close to their original proofs; likely we can
-- extend TransferRel with any property that is preserved by intersection,
-- union, and complement, and prove all of them that way.
variable {β : Sort l} {Obs : β → Sort k} {RT QT : RelT Obs} {R : Rel β}

lemma symm_cotransfer_rel_of_compl_symm_transfer_rel [pair : DualRelTPair RT QT]
    : SymmTransferRel RT R → SymmCotransferRel QT (Compl R) := by
  intro ⟨htransf, hsymm⟩
  apply SymmCotransferRel.mk ?_ (symmetric_of_compl hsymm)
  apply @cotransfer_rel_of_compl_transfer_rel (pair := pair)
  assumption

lemma symm_transfer_rel_of_compl_symm_cotransfer_rel [pair : DualRelTPair RT QT]
    : SymmCotransferRel QT R → SymmTransferRel RT (Compl R) := by
  intro ⟨hcotransf, hsymm⟩
  apply SymmTransferRel.mk ?_ (symmetric_of_compl hsymm)
  apply @transfer_rel_of_compl_cotransfer_rel (pair := pair)
  assumption

lemma not_symm_cotransfer_and_symm_transfer_rel [pair : DualRelTPair RT QT]
    : symmCotransferRel QT p q → symmTransferRel RT p q → False := by
  intro hcotransf ⟨R, htransf, hr⟩
  apply hcotransf (Compl R) ?_ hr
  apply @symm_cotransfer_rel_of_compl_symm_transfer_rel (pair := pair)
  assumption

open Classical in
lemma symm_cotransfer_rel_of_not_symm_transfer_rel [pair : DualRelTPair RT QT]
    : ¬ symmTransferRel RT p q → symmCotransferRel QT p q := by
  intro hntransf R hctr
  apply byContradiction
  intro hnr
  apply hntransf
  refine ⟨Compl R, ?_, hnr⟩
  apply @symm_transfer_rel_of_compl_symm_cotransfer_rel (pair := pair)
  assumption

theorem symm_cotransfer_rel_iff_not_symm_transfer_rel [pair : DualRelTPair RT QT]
    : symmCotransferRel QT p q ↔ ¬ symmTransferRel RT p q := by
  constructor
  · apply not_symm_cotransfer_and_symm_transfer_rel
  · apply symm_cotransfer_rel_of_not_symm_transfer_rel

open Classical in
theorem symm_transfer_or_symm_cotransfer_rel [pair : DualRelTPair RT QT]
    : symmTransferRel RT p q ∨ symmCotransferRel QT p q := by
  cases em (symmTransferRel RT p q)
  · left; assumption
  · right; apply @symm_cotransfer_rel_of_not_symm_transfer_rel (pair := pair); assumption
