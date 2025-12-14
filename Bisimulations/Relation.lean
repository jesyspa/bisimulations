import Mathlib.Tactic.Lemma
import Mathlib.Order.Defs.Unbundled

variable {β : Sort l}

abbrev Rel β := β → β → Prop
abbrev DepRel (F : β → Sort k) := ⦃p q : β⦄ → F p → F q → Prop
abbrev RelT (F : β → Sort k) := Rel β → DepRel F

def Compl (P : Rel β) (p q : β) : Prop := ¬ P p q

def DepSymmetric {F : β → Sort k} (R : DepRel F) :=
  ∀ ⦃p q : β⦄ ⦃op : F p⦄ ⦃oq : F q⦄, R op oq → R oq op

def SubRel (R R' : Rel β) := ∀ ⦃p q⦄, R p q → R' p q
def SubDepRel {F : β → Sort k} (R R' : DepRel F) :=
  ∀ ⦃p q : β⦄ ⦃op : F p⦄ ⦃oq : F q⦄, R op oq → R' op oq

class LawfulRelT {Obs : β → Sort k} (RT : RelT Obs) where
  preserves_symm : ∀ R, Symmetric R → DepSymmetric (RT R)
  not_both_direct_and_compl :
    ∀ R, ∀ ⦃p q : β⦄ ⦃op : Obs p⦄ ⦃oq : Obs q⦄, RT R op oq → RT (Compl R) op oq → False
  monotone : ∀ R R', SubRel R R' → SubDepRel (RT R) (RT R')

def Biggest (P : Rel β → Prop) (p q : β) : Prop := ∃ R, P R ∧ R p q
def Smallest (P : Rel β → Prop) (p q : β) : Prop := ∀ R, P R → R p q
def SymmInterior (R : Rel β) (p q : β) := R p q ∧ R q p

lemma biggest_is_maximal {P : Rel β → Prop}
    : P R → SubRel R (Biggest P) := fun hp _ _ hr => ⟨R, hp, hr⟩

lemma smallest_is_minimal {P : Rel β → Prop}
    : P R → SubRel (Smallest P) R := fun hp _ _ hr => hr R hp

variable {R : Rel β}

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

@[simp] lemma symmetric_of_symm_interior : Symmetric (SymmInterior R) := by
  intro p q ⟨hr, hr'⟩
  constructor <;> assumption
