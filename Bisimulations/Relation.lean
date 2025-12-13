import Mathlib.Tactic.Lemma
import Mathlib.Order.Defs.Unbundled

variable {β : Sort l}

def Compl (P : β → β → Prop) (p q : β) : Prop := ¬ P p q

def Biggest (P : (β → β → Prop) → Prop) (p q : β) : Prop := ∃ R, P R ∧ R p q
def Smallest (P : (β → β → Prop) → Prop) (p q : β) : Prop := ∀ R, P R → R p q
def SymmInterior (R : β → β → Prop) (p q : β) := R p q ∧ R q p

def Transfers (T R : β → β → Prop) := ∀ {p p' q : β}, T p p' → R p q → ∃ q', T q q' ∧ R p' q'
def DirectedTransfers (T R : β → β → Prop) :=
  ∀ {p p' q}, T p p' → R p q → ∃ q', T q q' ∧ SymmInterior R p' q'

def CoTransfers (T R : β → β → Prop) := ∀ {p p' q : β}, T p p' → (∀ q', T q q' → R p' q') → R p q
def DirectedCoTransfers (T R : β → β → Prop) :=
  ∀ {p p' q : β}, T p p' → (∀ q', T q q' → SymmInterior R p' q') → R p q

variable {T R : β → β → Prop}

lemma symmetric_of_compl
    : Symmetric R → Symmetric (Compl R) := by
  intro hsymm p q hcr hr
  exact hr |> hsymm |> hcr

lemma transfers_of_directed_transfers
    : DirectedTransfers T R → Transfers T R := by
  intro htransf p p' q ht hr
  rcases htransf ht hr with ⟨q', ht', ⟨hrl', hrr⟩⟩
  refine ⟨q', ht', hrl'⟩

lemma directed_transfers_of_transfers_of_symmetric
    : Symmetric R → Transfers T R → DirectedTransfers T R := by
  intros hsymm htransf p p' q ht hr
  rcases htransf ht hr with ⟨q', ht', hr'⟩
  refine ⟨q', ht', ?_⟩
  constructor
  · assumption
  · apply hsymm; assumption

lemma transfers_of_symmetric
    : Symmetric R → Transfers T R → Transfers T (flip R) := by
  intro hsymm htransf p p' q ht hr
  unfold flip at *
  rcases (htransf ht (hsymm hr)) with ⟨q', ht', hr'⟩
  exact ⟨q', ht', hsymm hr'⟩

lemma cotransfers_of_compl_transfers
    : Transfers T R → CoTransfers T (Compl R) := by
  intro htransf p p' q ht hnr hr
  rcases htransf ht hr with ⟨q', ht', hr'⟩
  exact hnr q' ht' hr'

open Classical in
lemma transfers_of_compl_cotransfers
    : CoTransfers T R → Transfers T (Compl R) := by
  intro hcotransf p p' q ht hnr
  apply byContradiction
  intro hnstep
  apply hnr
  apply hcotransf ht
  intro q' ht'
  apply byContradiction
  intro hnr'
  apply hnstep
  exists q'

@[simp] lemma symmetric_of_symm_interior : Symmetric (SymmInterior R) := by
  intro p q ⟨hr, hr'⟩
  constructor <;> assumption
