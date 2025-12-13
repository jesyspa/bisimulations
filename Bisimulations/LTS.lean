import Mathlib.Tactic.Lemma

structure LTS (α : Type) where
  Node : Type
  transition : α → Node → Node → Prop

def Rel (lts : LTS α) := lts.Node → lts.Node → Prop
