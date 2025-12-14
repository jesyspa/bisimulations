import Mathlib.Order.Defs.Unbundled
import Bisimulations.LTS
import Bisimulations.Relation
import Bisimulations.SymmTransfer
import Bisimulations.SymmCotransfer
import Bisimulations.Transfer
import Bisimulations.Cotransfer

variable {α} {lts : LTS α}

structure StrongObs (lts : LTS α) (p : lts.Node) where
  action :  α
  target : lts.Node
  transition : lts.transition action p target

structure StrongObsDepRel
  (lts : LTS α) (R : Rel lts.Node)
  ⦃p q : lts.Node⦄ (op : StrongObs lts p) (oq : StrongObs lts q)
where
  action_eq : op.action = oq.action
  target_rel : R op.target oq.target

def StrongT (lts : LTS α) : RelT (StrongObs lts) := StrongObsDepRel lts

instance strongt_lawful : LawfulRelT (StrongT lts) where
  preserves_symm := by
    intro R hsymm p q op oq hsr
    constructor
    · symm; exact hsr.action_eq
    · apply hsymm; exact hsr.target_rel
  not_both_direct_and_compl := by
    intro R p q op oq hsr hsrc
    exact hsrc.target_rel hsr.target_rel
  monotone := by
    intro R R' hsub p q op oq hsr
    constructor
    · exact hsr.action_eq
    · apply hsub; exact hsr.target_rel

namespace Strong

def directed_bisimilar : Rel lts.Node := transferRel (StrongT lts)
def bisimilar : Rel lts.Node := symmTransferRel (StrongT lts)
def directed_apart : Rel lts.Node := cotransferRel (StrongT lts)
def apart : Rel lts.Node := symmCotransferRel (StrongT lts)

end Strong
