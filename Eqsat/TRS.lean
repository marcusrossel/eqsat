import Mathlib.Logic.Relation
import Eqsat.Term

variable (S V : Type _) [Signature S]

def Subst := V → Term S

def Subst.apply {S V} [Signature S] (σ : Subst S V) : Pattern S V → Term S
  | .var v       => σ v
  | .app fn args => .app fn (apply σ <| args ·)

structure Rewrite where
  lhs : Pattern S V
  rhs : Pattern S V
  sub : rhs.vars ⊆ lhs.vars := by simp

abbrev TRS :=
  Set (Rewrite S V)

inductive TRS.Step {S V} [Signature S] (θ : TRS S V) : Term S → Term S → Prop where
  | subst (σ : Subst S V) (mem : rw ∈ θ) : Step θ (σ.apply rw.lhs) (σ.apply rw.rhs)
  | child (fn : S) (as bs : Term.Args fn) {i} (step : Step θ (as i) (bs i)) : Step θ (.app fn as) (.app fn bs)

notation t₁ " →[" θ "] " t₂ => TRS.Step θ t₁ t₂

abbrev TRS.Steps {S V} [Signature S] (θ : TRS S V) :=
  Relation.ReflTransGen (TRS.Step θ)

notation t₁ " →*[" θ "] " t₂ => TRS.Steps θ t₁ t₂
