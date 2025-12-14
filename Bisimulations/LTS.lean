import Mathlib.Tactic.Lemma

structure LTS (α : Type) where
  Node : Type
  transition : α → Node → Node → Prop
