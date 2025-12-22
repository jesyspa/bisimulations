import Mathlib.Order.Defs.Unbundled
import Bisimulations.LTS
import Bisimulations.Relation
import Bisimulations.SymmTransfer
import Bisimulations.SymmCotransfer
import Bisimulations.Transfer
import Bisimulations.Cotransfer
import Bisimulations.TransferDuality
import Bisimulations.SymmTransferDuality

variable {α} {lts : LTS α}

structure StrongObs (lts : LTS α) (p : lts.Node) where
  action :  α
  target : lts.Node
  transition : lts.transition action p target

structure StrongObsPosDepRel
  (lts : LTS α) (R : Rel lts.Node)
  ⦃p q : lts.Node⦄ (op : StrongObs lts p) (oq : StrongObs lts q) : Prop
where
  action_eq : op.action = oq.action
  target_rel : SymmInterior R op.target oq.target

inductive StrongObsNegDepRel
  (lts : LTS α) (R : Rel lts.Node)
  ⦃p q : lts.Node⦄ (op : StrongObs lts p) (oq : StrongObs lts q) : Prop
where
  | action_neq : op.action ≠ oq.action → StrongObsNegDepRel lts R op oq
  | target_rel : SymmClosure R op.target oq.target → StrongObsNegDepRel lts R op oq

def StrongPosT (lts : LTS α) : RelT (StrongObs lts) := StrongObsPosDepRel lts
def StrongNegT (lts : LTS α) : RelT (StrongObs lts) := StrongObsNegDepRel lts

instance strongPairInst (lts : LTS α) : DualRelTPair (StrongPosT lts) (StrongNegT lts) where
  compl_left := by
    intro R p q op oq
    constructor
    · intro hnpos
      cases em (op.action = oq.action)
      · cases em (SymmInterior R op.target oq.target)
        · exfalso
          apply hnpos
          constructor <;> assumption
        · apply StrongObsNegDepRel.target_rel
          rewrite [symm_closure_compl_eq_compl_symm_interior]
          assumption
      · apply StrongObsNegDepRel.action_neq
        assumption
    · rintro (hnact | hrel) hpos
      · apply hnact
        exact hpos.action_eq
      · rewrite [symm_closure_compl_eq_compl_symm_interior] at hrel
        exact hrel hpos.target_rel
  compl_right := by
    intro R p q op oq
    constructor
    · rintro hpos (hnact | hrel)
      · apply hnact
        exact hpos.action_eq
      · have := hpos.target_rel
        rewrite [symm_interior_compl_eq_compl_symm_closure] at this
        contradiction
    · intro hnneg
      cases em (op.action = oq.action)
      · cases em (SymmClosure R op.target oq.target)
        · exfalso
          apply hnneg
          apply StrongObsNegDepRel.target_rel
          assumption
        · constructor
          · assumption
          · rewrite [symm_interior_compl_eq_compl_symm_closure]
            assumption
      · exfalso
        apply hnneg
        apply StrongObsNegDepRel.action_neq
        assumption

namespace Strong

def directed_bisimilar : Rel lts.Node := transferRel (StrongPosT lts)
def bisimilar : Rel lts.Node := symmTransferRel (StrongPosT lts)
def directed_apart : Rel lts.Node := cotransferRel (StrongNegT lts)
def apart : Rel lts.Node := symmCotransferRel (StrongNegT lts)

theorem directed_apart_iff_not_directed_bisimilar {p q : lts.Node} :
    directed_apart p q ↔ ¬ directed_bisimilar p q := by
  apply cotransfer_rel_iff_not_transfer_rel

theorem symm_closure_directed_apart_iff_apart {p q : lts.Node} :
    SymmClosure directed_apart p q ↔ apart p q := by
  sorry

theorem symm_interior_directed_bisimilar_iff_bisimilar {p q : lts.Node} :
    SymmInterior directed_bisimilar p q ↔ bisimilar p q := by
  sorry

theorem apart_iff_not_bisimilar {p q : lts.Node} :
    apart p q ↔ ¬ bisimilar p q := by
  apply symm_cotransfer_rel_iff_not_symm_transfer_rel

end Strong
