import Mathlib.Order.SetNotation
import Lean

-- NOTE: According to Section 2.1 a signature needs to be finite, but in Section 2.2 we construct
-- the signature Σ ∪ Q which is infinite. Thus, we drop the requirement of finiteness here.
class Signature (S : Type _) where
  arity : S → Nat

namespace Signature

inductive Extended (S E : Type _) [Signature S] where
  | sig (s : S)
  | ext (e : E)

infixl:100 " ⨄ " => Extended

instance [Signature S] : Coe S (S ⨄ E) where
  coe := .sig

instance [Signature S] : Coe E (S ⨄ E) where
  coe := .ext

namespace Extended

@[app_unexpander Extended.sig]
def sigUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $s) => `(↑$s)
  | s        => return s

@[app_unexpander Extended.ext]
def extUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $s) => `(↑$s)
  | s        => return s

@[simp]
nonrec def arity {S E} [Signature S] : S ⨄ E → Nat
  | .sig s => arity s
  | .ext _ => 0

@[simp]
instance [Signature S] : Signature (S ⨄ E) where
  arity := Signature.Extended.arity

end Signature.Extended

open Signature

abbrev Args [Signature S] (s : S) (α : Type _) :=
  Fin (arity s) → α

@[simp]
def Args.set [Signature S] {s : S} (as : Args s α) (i : Nat) (a : α) : Args s α :=
  fun j => if i = j then a else as j

notation:(arg + 1) as "[" i " := " a "]" => Args.set as i a

@[simp]
theorem Args.set_self [Signature S] {s : S} (as : Args s α) (i : Fin <| arity s) :
    as[i := as i] = as := by
  grind [Args.set]

instance [Signature S] {s : S} : Coe (Args s E) (Args s <| S ⨄ E) where
  coe as := (as ·)

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

variable [Signature S]

nonrec abbrev Args (s : S) :=
  Args s (Term S)

abbrev extend : Term S → Term (S ⨄ E)
  | fn ° args => fn ° (extend <| args ·)

instance : Coe (Term S) (Term <| S ⨄ E) where
  coe := extend

@[app_unexpander Term.extend]
def extendUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $t) => `(↑$t)
  | e        => return e

instance : Coe E (Term <| S ⨄ E) where
  coe e := e ° nofun

@[cases_eliminator]
def casesOn
    {motive : Term S → Sort _} (t : Term S)
    (app : (fn : S) → (args : Fin (arity fn) → Term S) → motive fn ° args) : motive t :=
  match t with
  | .var v     => v.elim
  | .app fn as => app fn as
