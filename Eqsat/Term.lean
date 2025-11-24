import Mathlib.Order.SetNotation

-- NOTE: According to Section 2.1 a signature needs to be finite, but in Section 2.2 we construct
-- the signature Σ ∪ Q which is infinite. Thus, we drop the requirement of finiteness here.
class Signature (S : Type _) where
  arity : S → Nat

@[simp]
def Signature.extend (S E) [Signature S] : Signature (S ⊕ E) where
  arity
    | .inl s => arity s
    | .inr _ => 0

@[simp]
instance Signature.instExtend [Signature S] : Signature (S ⊕ E) :=
  Signature.extend S E

open Signature

abbrev Args [Signature S] (s : S) (α : Type _) :=
  Fin (arity s) → α

inductive Pattern (S V) [Signature S] where
  | var (v : V)
  | app (fn : S) (args : Fin (arity fn) → Pattern S V)

@[simp]
def Pattern.vars [Signature S] : Pattern S V → Set V
  | var v      => {v}
  | app _ args => ⋃ i, vars (args i)

abbrev Term (S) [Signature S] :=
  Pattern S Empty

nonrec abbrev Term.Args [Signature S] (s : S) :=
  Args s (Term S)

abbrev Term.app [Signature S] (fn : S) (args : Args fn) :=
  Pattern.app fn args

def Term.toExtended [Signature S] : Term S → @Term (S ⊕ E) Signature.instExtend
  | .app fn args => .app (.inl fn) fun i => toExtended (args i)

instance [Signature S] : Coe (Term S) (@Term (S ⊕ E) Signature.instExtend) where
  coe := Term.toExtended

instance [Signature S] : Coe E (@Term (S ⊕ E) Signature.instExtend) where
  coe e := .app (.inr e) nofun
