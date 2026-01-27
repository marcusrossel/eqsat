import Eqsat.TreeAutomaton.Reachable
import Eqsat.PCR

/- **Definition 3** -/
structure EGraph (S Q) [Signature S] extends auto : TreeAutomaton S Q where
  det      : auto.Deterministic
  reach    : auto.Reachable
  no_final : auto.final = ∅

namespace EGraph

variable [Signature S] {graph : EGraph S Q}

abbrev EClass (_ : EGraph S Q) := Q

abbrev ENode (_ : EGraph S Q) := TreeAutomaton.Transition S Q

abbrev EClass.Represents (c : EClass graph) (t : Term S) : Prop :=
  graph.Accepts c t

end EGraph
