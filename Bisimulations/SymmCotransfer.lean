import Bisimulations.Relation
import Bisimulations.Cotransfer

variable {β : Sort l}
variable {Obs : β → Sort k} {RT : RelT Obs} {R : Rel β}

structure SymmCotransferRel (RT : RelT Obs) (R : Rel β) extends CotransferRel RT R where
  symmetric : Symmetric R

lemma symm_cotransfer_rel_reverse
    : SymmCotransferRel RT R → SymmCotransferRel RT (flip R) := by
  intro ⟨htransf, hsymm⟩
  rw [eq_flip_of_symmetric hsymm]
  constructor <;> assumption

def symmCotransferRel (RT : RelT Obs) := Smallest (SymmCotransferRel RT)

lemma superdeprel_of_symm_cotransfer_rel
    : SymmCotransferRel RT R → SubRel (symmCotransferRel RT) R := smallest_is_minimal

lemma symm_of_symm_cotransfer_rel : Symmetric (symmCotransferRel RT) := by
  intro p q hctr R hsctr
  apply hsctr.symmetric
  apply hctr
  assumption

-- TODO: can this be derived from the non-symmetric case?
lemma symm_cotransfer_rel_of_symm_cotransfer_rel [laws : LawfulRelT RT]
    : SymmCotransferRel RT (symmCotransferRel RT) := by
  refine ⟨⟨?_⟩, symm_of_symm_cotransfer_rel⟩
  intro p q op hcont R hsctr
  apply hsctr.cotransfer
  · intro oq
    apply laws.monotone _ _ (superdeprel_of_symm_cotransfer_rel hsctr)
    apply hcont
