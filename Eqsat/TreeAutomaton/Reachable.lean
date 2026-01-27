import Eqsat.TreeAutomaton.Basic

namespace TreeAutomaton

variable [Signature S] {auto : TreeAutomaton S Q}

-- A given state is reachable (from a ground term) if it is the destination of a transition where
-- all source states are reachable. Note that this condition is vacuously satisfied for constants.
inductive IsReachableState (auto : TreeAutomaton S Q) : Q → Prop where
  | intro : tr ∈ auto.trans → (∀ i, IsReachableState auto <| tr.srcs i) → IsReachableState auto tr.dst

-- The set of reachable states.
abbrev ReachableState (auto : TreeAutomaton S Q) : Type :=
  { q // auto.IsReachableState q }

def IsReachableTransition (auto : TreeAutomaton S Q) (tr : Transition S Q) : Prop :=
  ∀ i, auto.IsReachableState <| tr.srcs i

def Transition.liftReachable {auto : TreeAutomaton S Q} (tr : Transition S auto.ReachableState) :
    Transition S Q where
  sym  := tr.sym
  srcs := (tr.srcs ·)
  dst  := tr.dst

def reachableTrans (auto : TreeAutomaton S Q) : Set (Transition S auto.ReachableState) :=
  { tr | auto.IsReachableTransition tr.liftReachable }

def reachableFinal (auto : TreeAutomaton S Q) : Set auto.ReachableState :=
  { q | ↑q ∈ auto.final ∧ auto.IsReachableState q }

-- The reachable sub-automaton prunes all unreachable states and transitions.
def reachable (auto : TreeAutomaton S Q) : TreeAutomaton S auto.ReachableState where
  trans := auto.reachableTrans
  final := auto.reachableFinal

def reachable_preserves_confluence {auto : TreeAutomaton S Q} (con : auto.trs.Confluent) :
    auto.reachable.trs.Confluent := by
  intro t t₁ t₂ s₁ s₂
  sorry
