import Eqsat.Term
import Mathlib.Order.Defs.Unbundled

structure PER (α : Type _) where
  rel   : α → α → Prop
  symm  : Symmetric rel
  trans : Transitive rel

instance : CoeFun (PER α) (fun _ => α → α → Prop) where
  coe := PER.rel

namespace PER

def support (per : PER α) : Set α :=
  { a | per a a }

variable [Signature S]

open Signature Term

def Congruent (per : PER <| Term S) : Prop :=
  ∀ {fn : S} {as bs : Args fn}, as = bs → app fn as ∈ per.support → per (app fn as) (app fn bs)

def Reachable (per : PER <| Term S) : Prop :=
  ∀ {fn : S} {as : Args fn}, app fn as ∈ per.support → ∀ i, as i ∈ per.support

end PER

structure PCR (S) [Signature S] extends per : PER (Term S) where
  congr : per.Congruent
  reach : per.Reachable
