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

def Args.set [Signature S] {s : S} (as : Args s α) (i : Fin <| arity s) (a : α) : Args s α :=
  fun j => if i = j then a else as j

inductive Pattern (S V) [Signature S] where
  | var (v : V)
  | app (fn : S) (args : Fin (arity fn) → Pattern S V)

instance [Signature S] : Coe V (Pattern S V) where
  coe := .var

infixl:100 " ° " => Pattern.app

@[simp]
def Pattern.vars [Signature S] : Pattern S V → Set V
  | (v : V)  => {v}
  | _ ° args => ⋃ i, vars (args i)

abbrev Term (S) [Signature S] :=
  Pattern S Empty

namespace Term

nonrec abbrev Args [Signature S] (s : S) :=
  Args s (Term S)

def toExtended [Signature S] : Term S → @Term (S ⊕ E) Signature.instExtend
  | fn ° args => (.inl fn) ° fun i => toExtended (args i)

instance [Signature S] : Coe (Term S) (@Term (S ⊕ E) Signature.instExtend) where
  coe := Term.toExtended

instance [Signature S] : Coe E (@Term (S ⊕ E) Signature.instExtend) where
  coe e := (.inr e) ° nofun
