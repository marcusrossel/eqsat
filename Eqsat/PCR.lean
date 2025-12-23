import Eqsat.Term
import Mathlib.Order.Defs.Unbundled

@[ext]
structure PER (α : Type _) where
  rel   : α → α → Prop
  symm  : Symmetric rel
  trans : Transitive rel

instance : CoeFun (PER α) (fun _ => α → α → Prop) where
  coe := PER.rel

namespace PER

def support (per : PER α) : Set α :=
  { a | per a a }

instance supportSetoid (per : PER α) : Setoid (support per) where
  r a₁ a₂ := per.rel a₁ a₂
  iseqv   := by grind [Equivalence, support, PER.symm, PER.trans, Symmetric, Transitive]

variable [Signature S]

def Congruent (per : PER <| Term S) : Prop :=
  ∀ {fn : S} {as bs : Term.Args fn},
    (∀ i, per (as i) (bs i)) → fn ° as ∈ per.support → per (fn ° as) (fn ° bs)

def Reachable (per : PER <| Term S) : Prop :=
  ∀ {fn : S} {as : Term.Args fn}, fn ° as ∈ per.support → ∀ i, as i ∈ per.support

end PER

@[ext]
structure PCR (S) [Signature S] extends per : PER (Term S) where
  congr : per.Congruent
  reach : per.Reachable

def PCR.Classes [Signature S] (pcr : PCR S) : Type :=
  Quotient <| PER.supportSetoid pcr.per
