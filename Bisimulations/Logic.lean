import Bisimulations.LTS

inductive HML (α : Type) where
  | top
  | and (φ ψ : HML α)
  | not (φ : HML α)
  | diamond (a : α) (φ : HML α)

variable {α} {lts : LTS α}

mutual
  inductive Satisfies : lts.Node → HML α → Prop where
    | sat_top : Satisfies p .top
    | sat_and : Satisfies p φ → Satisfies p ψ → Satisfies p (φ.and ψ)
    | sat_not : Refutes p φ → Satisfies p (.not φ)
    | sat_diamond : lts.transition a p p' → Satisfies p' φ → Satisfies p (φ.diamond a)

  inductive Refutes : lts.Node → HML α → Prop where
    | rft_and_left {φ ψ : HML α} : Refutes p φ → Refutes p (φ.and ψ)
    | rft_and_right {φ ψ : HML α} : Refutes p ψ → Refutes p (φ.and ψ)
    | rft_not : Satisfies p φ → Refutes p (.not φ)
    | rft_diamond : (∀ {p'}, lts.transition a p p' → Refutes p' φ) → Refutes p (φ.diamond a)
end

theorem not_satisfies_and_refutes
    : Satisfies p φ → Refutes p φ → False
  | .sat_and hsl _, .rft_and_left hrl => not_satisfies_and_refutes hsl hrl
  | .sat_and _ hsr, .rft_and_right hrr => not_satisfies_and_refutes hsr hrr
  | .sat_not hr, .rft_not hs => not_satisfies_and_refutes hs hr
  | .sat_diamond ht hs, .rft_diamond hr => not_satisfies_and_refutes hs (hr ht)

open Classical in
theorem satisfies_or_refutes {p : lts.Node} {φ : HML α}
    : Satisfies p φ ∨ Refutes p φ := by
  induction φ generalizing p with
  | top => left; constructor
  | and φ ψ hφ hψ =>
    cases hφ
    · cases hψ
      · left; constructor <;> assumption
      · right; apply Refutes.rft_and_right; assumption
    · right; apply Refutes.rft_and_left; assumption
  | not φ hφ =>
    cases hφ
    · right; constructor; assumption
    · left; constructor; assumption
  | diamond a φ hφ =>
      rcases em (∃ p', lts.transition a p p' ∧ Satisfies p' φ)
        with ⟨p', ht, hs⟩ | hn
      · left; constructor <;> assumption
      · right; constructor
        intro p' ht
        cases hφ
        · exfalso
          apply hn
          refine ⟨p', ht, ?_⟩
          assumption
        · assumption
