import Mathlib.Data.Set.Lattice
import Eqsat.TRS

namespace TreeAutomaton

structure Transition (S Q) [Signature S] where
  fn   : S
  args : Args fn Q
  dst  : Q

def Transition.toRewrite [Signature S] (trans : Transition S Q) : Rewrite (S ⨄ Q) Empty where
  lhs := trans.fn ° (trans.args ·)
  rhs := ↑trans.dst

structure _root_.TreeAutomaton (S Q) [Signature S] where
  trans : Set (Transition S Q)
  final : Set Q

variable [Signature S]

def trs (auto : TreeAutomaton S Q) : TRS (S ⨄ Q) Empty :=
  Transition.toRewrite '' auto.trans

notation t₁ " →*[" auto "] " t₂ => t₁ →*[TreeAutomaton.trs auto] t₂

def Accepts (auto : TreeAutomaton S Q) (q : Q) (t : Term S) : Prop :=
  t →*[auto] q

-- TODO: Perhaps we should just generalize this to the final accepting thing being a term, not just a state.
--       Then this also speicalizes to the state case.
theorem accepts_child {auto : TreeAutomaton S Q} (acc : (fn ° as : Term S) →*[auto] q) (i) :
    ∃ qᵢ : Q, as i →*[auto] qᵢ := by
  sorry

def Deterministic (auto : TreeAutomaton S Q) : Prop :=
  ∀ {t : Term S} {q₁ q₂ : Q}, (t →*[auto] q₁) → (t →*[auto] q₂) → q₁ = q₂

def Reachable (auto : TreeAutomaton S Q) : Prop :=
  ∀ q : Q, ∃ t : Term S, t →*[auto] q
