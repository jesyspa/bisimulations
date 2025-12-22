import Bisimulations.Relation
import Bisimulations.Transfer

variable {β : Type l}
variable {Obs : β → Sort k} {RT : RelT Obs} {R : Rel β}

lemma transfers_of_symmetric
    : Symmetric R → Transfers RT R p q → Transfers RT (flip R) p q := by
  intro hsymm htransf hr op
  rcases htransf (hsymm hr) op with ⟨oq, hr'⟩
  exists oq
  rw [eq_flip_of_symmetric hsymm]
  assumption

structure SymmTransferRel (RT : RelT Obs) (R : Rel β) extends TransferRel RT R where
  symmetric : Symmetric R

lemma symm_transfer_rel_reverse
    : SymmTransferRel RT R → SymmTransferRel RT (flip R) := by
  intro ⟨htransf, hsymm⟩
  rw [eq_flip_of_symmetric hsymm]
  constructor <;> assumption

lemma symm_transfer_rel_of_symm_closure_transfer_rel [laws : LawfulRelT RT]
    : TransferRel RT R → TransferRel RT (flip R) → SymmTransferRel RT (SymmClosure R) := by
  intros
  apply SymmTransferRel.mk ?_ symmetric_of_symm_closure
  apply transfer_rel_closed_under_union <;> assumption

def symmTransferRel (RT : RelT Obs) := Biggest (SymmTransferRel RT)

lemma subdeprel_of_symm_transfer_rel
    : SymmTransferRel RT R → SubRel R (symmTransferRel RT) := biggest_is_maximal

lemma symm_of_symm_transfer_rel : Symmetric (symmTransferRel RT) := by
  intro p q ⟨R, hstr, hr⟩
  refine ⟨R, hstr, hstr.symmetric hr⟩

@[symm]
lemma symm_lemma_symm_transfer_rel : symmTransferRel RT p q → symmTransferRel RT q p := by
  apply symm_of_symm_transfer_rel

-- TODO: can this be derived from the non-symmetric case?
lemma symm_transfer_rel_of_symm_transfer_rel [laws : LawfulRelT RT]
    : SymmTransferRel RT (symmTransferRel RT) := by
  refine ⟨⟨?_⟩, symm_of_symm_transfer_rel⟩
  intro p q ⟨R, hstr, hr⟩ op
  rcases hstr.transfer hr op with ⟨oq, hr'⟩
  refine ⟨oq, ?_⟩
  apply laws.monotone R _ (subdeprel_of_symm_transfer_rel hstr) hr'

lemma transfer_of_symm_transfer
    : symmTransferRel RT p q → transferRel RT p q :=
  fun ⟨R, hsymmtransf, hr⟩ => ⟨R, hsymmtransf.toTransferRel, hr⟩

lemma symm_interior_transfer_of_symm_transfer
    : symmTransferRel RT p q → SymmInterior (transferRel RT) p q := by
  intro h
  constructor <;> apply transfer_of_symm_transfer
  · assumption
  · symm; assumption
