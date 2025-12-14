import Mathlib.Tactic.Lemma
import Mathlib.Order.Defs.Unbundled

variable {β : Sort l}

abbrev Rel β := β → β → Prop
abbrev DepRel (F : β → Sort k) := ⦃p q : β⦄ → F p → F q → Prop
abbrev RelT (F : β → Sort k) := Rel β → DepRel F

def Compl (P : Rel β) (p q : β) : Prop := ¬ P p q

def DepSymmetric {F : β → Sort k} (R : DepRel F) :=
  ∀ ⦃p q : β⦄ ⦃op : F p⦄ ⦃oq : F q⦄, R op oq → R oq op

class LawfulRelT {Obs : β → Sort k} (RT : RelT Obs) where
  preserves_symm : ∀ R, Symmetric R → DepSymmetric (RT R)
  not_both_direct_and_compl :
    ∀ R, ∀ ⦃p q : β⦄ ⦃op : Obs p⦄ ⦃oq : Obs q⦄, RT R op oq → RT (Compl R) op oq → False

def Biggest (P : Rel β → Prop) (p q : β) : Prop := ∃ R, P R ∧ R p q
def Smallest (P : Rel β → Prop) (p q : β) : Prop := ∀ R, P R → R p q
def SymmInterior (R : Rel β) (p q : β) := R p q ∧ R q p

def Transfers {Obs : β → Sort k} (RT : RelT Obs) (R : Rel β) (p q : β) :=
  R p q → ∀ op : Obs p, ∃ oq : Obs q, RT R op oq
def CoTransfers {Obs : β → Sort k} (RT : RelT Obs) (R : Rel β) (p q : β) :=
  ∀ op : Obs p, (∀ oq : Obs q, RT R op oq) → R p q

variable {Obs : β → Sort k} {RT : RelT Obs} {R : Rel β}

lemma symmetric_of_compl
    : Symmetric R → Symmetric (Compl R) := by
  intro hsymm p q hcr hr
  exact hr |> hsymm |> hcr

@[simp] lemma eq_flip_of_symmetric : Symmetric R → flip R = R := by
  intro hsymm
  funext
  rename_i p q
  unfold flip
  suffices R p q ↔ R q p by rw [this]
  constructor <;> apply hsymm

lemma transfers_of_symmetric
    : Symmetric R → Transfers RT R p q → Transfers RT (flip R) p q := by
  intro hsymm htransf hr op
  rcases htransf (hsymm hr) op with ⟨oq, hr'⟩
  exists oq
  rw [eq_flip_of_symmetric hsymm]
  assumption

-- The converse does not generally seem to hold.
lemma cotransfers_of_compl_transfers [laws : LawfulRelT RT]
    : Transfers RT R p q → CoTransfers RT (Compl R) p q := by
  intro htransf op hcont hrp
  rcases htransf hrp op with ⟨oq, hrq⟩
  apply laws.not_both_direct_and_compl
  · assumption
  · apply hcont

@[simp] lemma symmetric_of_symm_interior : Symmetric (SymmInterior R) := by
  intro p q ⟨hr, hr'⟩
  constructor <;> assumption

structure TransferRel (RT : RelT Obs) (R : Rel β) where
  transfer : ∀ ⦃p q : β⦄, Transfers RT R p q

structure SymmTransferRel (RT : RelT Obs) (R : Rel β) extends TransferRel RT R where
  symmetric : Symmetric R
