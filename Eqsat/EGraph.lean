import Eqsat.TreeAutomaton
import Eqsat.PCR

/-- Definition 3 -/
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

/-- Definition 5 -/
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
    rename_i fn as bs
    simp_all [PER.support]
    obtain ⟨c, hc⟩ := mem
    refine ⟨c, hc, ?_⟩
    have ⟨qs, hq₁, hq₂⟩ := hc.final
    apply Relation.ReflTransGen.tail ?_ (TreeAutomaton.step_of_transition hq₁)
    · refine TRS.Steps.children (fun i => ?_)
      have ⟨_, hc₁, hc₂⟩ := h i
      obtain ⟨rfl⟩ := graph.det hc₁ <| TreeAutomaton.steps_child hq₂ i
      exact hc₂
  reach h i := by
    simp only [PER.support, and_self, Set.mem_setOf_eq] at *
    obtain ⟨_, h⟩ := h
    apply h.child

end EGraph

/- Theorem 6 -/
namespace PCR

variable [Signature S] {graph : EGraph S Q}

def egraph (pcr : PCR S) : EGraph S pcr.classes where
  trans :=
    { ⟨fn, qs, dst⟩ |
      ∃ (as : Term.Args fn) (mem₁ : fn ° as ∈ pcr.support) (mem₂ : ∀ i, as i ∈ pcr.support),
      dst = Quotient.mk' ⟨fn ° as, mem₁⟩ ∧
      qs = fun i => Quotient.mk' ⟨as i, mem₂ i⟩
    }
  final    := ∅
  no_final := rfl
  det      := sorry
  reach    := sorry

theorem egraph_correct (pcr : PCR S) : pcr.egraph.pcr = pcr := by
  ext t₁ t₂
  induction t₁ generalizing t₂ <;> cases t₂ <;> try contradiction
  case app.app fn₁ as₁ ih fn₂ as₂ =>
    simp only [egraph, EGraph.pcr] at ih ⊢
    apply Iff.intro (fun h => ?mp) (fun h => ?mpr)
    case mp =>
      obtain ⟨c, hc₁, hc₂⟩ := h
      if hf : fn₁ = fn₂ then
        subst hf
        apply pcr.congr fun i => ih i (as₂ i) |>.mp ?_
        -- TODO: There should be a lemma stating that (∃ c, Represents c t) coincides with
        --       membership in the PCR's support.
        · sorry
        · sorry
      else
        sorry
    case mpr h => sorry

theorem egraph_unique {pcr : PCR S} (h : pcr = graph.pcr) : graph ≍ pcr.egraph := by
  sorry
  -- TODO: We might not be able to prove this up to HEq, but only some weaker notion of
  --       isomorphism.

end PCR
