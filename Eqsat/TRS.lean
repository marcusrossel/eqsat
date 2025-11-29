import Mathlib.Logic.Relation
import Eqsat.Term

variable (S V : Type _) [Signature S]

def Subst := V → Term S

def Subst.apply {S V} [Signature S] (σ : Subst S V) : Pattern S V → Term S
  | (v : V)   => σ v
  | fn ° args => fn ° (apply σ <| args ·)

@[simp]
theorem Subst.apply_no_vars {S} [Signature S] (σ : Subst S Empty) (p : Pattern S Empty) :
    σ.apply p = p := by
  induction p
  case var => contradiction
  case app => simp [apply, *]

structure Rewrite where
  lhs : Pattern S V
  rhs : Pattern S V
  sub : rhs.vars ⊆ lhs.vars := by simp

abbrev TRS :=
  Set (Rewrite S V)

namespace TRS

inductive Step {S V} [Signature S] (θ : TRS S V) : Term S → Term S → Prop where
  | subst (σ : Subst S V) (mem : rw ∈ θ) : Step θ (σ.apply rw.lhs) (σ.apply rw.rhs)
  | child (fn : S) (as : Term.Args fn) {i} (step : Step θ (as i) a) : Step θ (fn ° as) (fn ° as.set i a)

notation t₁ " →[" θ "] " t₂ => TRS.Step θ t₁ t₂

abbrev Steps {S V} [Signature S] (θ : TRS S V) :=
  Relation.ReflTransGen (Step θ)

notation t₁ " →*[" θ "] " t₂ => Steps θ t₁ t₂
