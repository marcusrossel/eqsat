import Eqsat.TreeAutomaton
import Eqsat.PCR

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

def pcr (graph : EGraph S Q) : PCR S where
  rel t₁ t₂ :=
    ∃ c : EClass graph, c.Represents t₁ ∧ c.Represents t₂
  symm := by
    grind [Symmetric]
  trans _ _ _ := by
    simp only [forall_exists_index, and_imp]
    intro c _ h₁ _ h₂ _
    exists c
    have := graph.det h₁ h₂
    simp_all
  congr h mem := by
    simp_all [PER.support]
  reach h i := by
    simp only [PER.support, and_self, Set.mem_setOf_eq] at *
    obtain ⟨_, h⟩ := h
    exact TreeAutomaton.accepts_child h i
