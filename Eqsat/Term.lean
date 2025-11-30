import Mathlib.Order.SetNotation

-- NOTE: According to Section 2.1 a signature needs to be finite, but in Section 2.2 we construct
-- the signature Σ ∪ Q which is infinite. Thus, we drop the requirement of finiteness here.
class Signature (S : Type _) where
  arity : S → Nat

inductive Signature.Extended (S E : Type _) [Signature S] where
  | sig (s : S)
  | ext (e : E)

infixl:100 " ⨄ " => Signature.Extended

instance [Signature S] : Coe S (S ⨄ E) where
  coe := .sig

instance [Signature S] : Coe E (S ⨄ E) where
  coe := .ext

@[simp]
nonrec def Signature.Extended.arity {S E} [Signature S] : S ⨄ E → Nat
  | .sig s => arity s
  | .ext _ => 0

@[simp]
instance [Signature S] : Signature (S ⨄ E) where
  arity := Signature.Extended.arity

open Signature

abbrev Args [Signature S] (s : S) (α : Type _) :=
  Fin (arity s) → α

def Args.set [Signature S] {s : S} (as : Args s α) (i : Fin <| arity s) (a : α) : Args s α :=
  fun j => if i = j then a else as j

notation:(arg + 1) as "[" i " := " a "]" => Args.set as i a

inductive Pattern (S V) [Signature S] where
  | var (v : V)
  | app (fn : S) (args : Fin (arity fn) → Pattern S V)

instance [Signature S] : Coe V (Pattern S V) where
  coe := .var

infixl:arg " ° " => Pattern.app

@[simp]
def Pattern.vars [Signature S] : Pattern S V → Set V
  | (v : V)  => {v}
  | _ ° args => ⋃ i, vars (args i)

abbrev Term (S) [Signature S] :=
  Pattern S Empty

namespace Term

nonrec abbrev Args [Signature S] (s : S) :=
  Args s (Term S)

abbrev extend [Signature S] : Term S → Term (S ⨄ E)
  | fn ° args => fn ° (extend <| args ·)

prefix:100 "⇈" => extend

instance [Signature S] : Coe (Term S) (Term <| S ⨄ E) where
  coe := extend

instance [Signature S] : Coe E (Term <| S ⨄ E) where
  coe e := e ° nofun
