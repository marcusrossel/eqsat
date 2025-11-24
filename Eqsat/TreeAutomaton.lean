import Mathlib.Data.Set.Lattice
import Eqsat.TRS

namespace TreeAutomaton

structure Transition (S Q) [Signature S] where
  fn   : S
  args : Args fn Q
  dst  : Q

-- TODO: Is this definition correct? We interpret all state vars as constants, so there are no
--       variables. Thus, the only rewrite steps which can occur are subterm replacements.
def Transition.toRewrite [Signature S] (trans : Transition S Q) :
    Rewrite (S ⊕ Q) Empty where
  lhs := .app (.inl trans.fn) fun i => ↑(trans.args i)
  rhs := ↑trans.dst

structure _root_.TreeAutomaton (S Q) [Signature S] where
  trans : Set (TreeAutomaton.Transition S Q)
  final : Set Q

variable [Signature S]

def trs (auto : TreeAutomaton S Q) : TRS (S ⊕ Q) Empty :=
  Transition.toRewrite '' auto.trans

notation t₁ " →*[" auto "] " t₂ => t₁ →*[TreeAutomaton.trs auto] t₂

def Accepts (auto : TreeAutomaton S Q) (q : Q) (t : Term S) : Prop :=
  t →*[auto] q

def Deterministic (auto : TreeAutomaton S Q) : Prop :=
  ∀ {t : Term S} {q₁ q₂ : Q}, (t →*[auto] q₁) → (t →*[auto] q₂) → q₁ = q₂

def Reachable (auto : TreeAutomaton S Q) : Prop :=
  ∀ q : Q, ∃ t : Term S, t →*[auto] q
