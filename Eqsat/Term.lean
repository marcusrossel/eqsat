import Mathlib.Order.SetNotation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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

namespace Args

variable [Signature S] {s : S}

@[simp]
def set (as : Args s α) (i : Nat) (a : α) : Args s α :=
  fun j => if i = j then a else as j

notation:(arg + 1) as "[" i " := " a "]" => Args.set as i a

@[simp]
theorem set_self (as : Args s α) (i : Fin <| arity s) : as[i := as i] = as := by
  grind [Args.set]

@[simp]
theorem set_get (as : Args s α) (i : Fin <| arity s) (a) : as[i := a] i = a := by
  grind [Args.set]

@[simp]
theorem set_twice (as : Args s α) (i : Fin <| arity s) (a₁ a₂) :
    as[i := a₁][i := a₂] = as[i := a₂] := by
  grind [Args.set]

@[simp]
theorem set_ne_comm (as : Args s α) (a₁ a₂) {i₁ i₂ : Fin <| arity s} (h : i₁ ≠ i₂) :
    as[i₁ := a₁][i₂ := a₂] = as[i₂ := a₂][i₁ := a₁] := by
  grind [Args.set]

@[simp]
theorem set_get_ne (as : Args s α) (a) {i₁ i₂ : Fin <| arity s} (h : i₁ ≠ i₂) :
    as[i₁ := a] i₂ = as i₂ := by
  grind [Args.set]

instance [Signature S] {s : S} : Coe (Args s E) (Args s <| S ⨄ E) where
  coe as := (as ·)

end Args

inductive Pattern (S : Type u) (V : Type v) [Signature S] : Type (max u v) where
  | var (v : V)
  | app (fn : S) (args : Args fn <| Pattern S V)

namespace Pattern

variable [Signature S]

instance : Coe V (Pattern S V) where
  coe := .var

infixl:arg " ° " => Pattern.app

def size [SizeOf S] [SizeOf V] : Pattern S V → Nat
  | .var v     => sizeOf v
  | .app fn as => 1 + sizeOf fn + ∑ i, size (as i)

instance [SizeOf S] [SizeOf V] : SizeOf (Pattern S V) where
  sizeOf := Pattern.size

@[simp]
def vars : Pattern S V → Set V
  | (v : V)  => {v}
  | _ ° args => ⋃ i, vars (args i)

end Pattern

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

@[induction_eliminator]
def recOn
    {motive : Term S → Sort _} (t : Term S)
    (app : ∀ fn args, (∀ i, motive <| args i) → motive fn ° args) : motive t :=
  match t with
  | .var v => v.elim
  | .app fn as =>
    app fn as fun i =>
      match _ : as i with
      | .app fnᵢ asᵢ => recOn (fnᵢ ° asᵢ) app
decreasing_by
  have := Finset.single_le_sum_of_canonicallyOrdered (f := Pattern.size ∘ as) (Finset.mem_univ i)
  simp only [sizeOf]
  grind [Pattern.size]

end Term
