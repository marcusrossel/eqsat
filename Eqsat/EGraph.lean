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
    simp only [PER.support, and_self] at mem
    obtain ⟨c, hc⟩ := mem
    refine ⟨c, hc, ?_⟩
    have ⟨qs, hq₁, hq₂⟩ := hc.final
    apply TRS.Steps.tail (TRS.Steps.children fun i => ?_) (TreeAutomaton.step_of_transition hq₁)
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

inductive transitions (pcr : PCR S) : Set (TreeAutomaton.Transition S pcr.Classes)
  | intro (mem₁ : fn ° as ∈ pcr.support) (mem₂ : ∀ i, as i ∈ pcr.support) :
    transitions pcr ⟨fn, fun i => ⟦⟨as i, mem₂ i⟩⟧, ⟦⟨fn ° as, mem₁⟩⟧⟩

def automaton (pcr : PCR S) : TreeAutomaton S pcr.Classes where
  trans := pcr.transitions
  final := ∅

theorem automaton_single_deterministic {pcr : PCR S} {t : Term _} {q₁ q₂ : pcr.Classes}
    (h₁ : t -[pcr.automaton]→ q₁) (h₂ : t -[pcr.automaton]→ q₂) : q₁ = q₂ := by
  sorry

theorem automaton_deterministic (pcr : PCR S) : pcr.automaton.Deterministic := by
  rw [TreeAutomaton.Deterministic]
  intro t q₁ q₂ hq₁ hq₂
  rw [TreeAutomaton.Accepts] at hq₁ hq₂
  generalize hl : t.extend = lhs at hq₁ hq₂
  generalize hr₁ : (q₁ : Term <| S ⨄ pcr.Classes) = rhs₁ at hq₁
  generalize hr₂ : (q₂ : Term <| S ⨄ pcr.Classes) = rhs₂ at hq₂
  suffices rhs₁ = rhs₂ by simp_all [← hr₂]
  induction hq₁ generalizing rhs₂ <;> cases hq₂
  case refl.refl => rfl
  case refl.tail =>
    sorry -- contra as hl and hr₁ equate a term with a state
  case tail.refl =>
    sorry -- contra as hl and hr₂ equate a term with a state
  case tail.tail b₁ c₁ hd₁ tl₁ ih b₂ hd₂ tl₂ =>
    -- by children lemma we get transitions from each child of lhs
    -- (aka t, which has to be of the form fn ° as) to a state
    --
    -- then apply IH for each child
    --
    -- then we get we only have to show that the final steps
    -- are deterministic (perhaps factor that out into a lemma).
    -- first of all, establish that it has to be a subst-step, as a children step can't have a
    -- state as dst.
    -- then use automaton_single_deterministic
    sorry

theorem automaton_reachable (pcr : PCR S) : pcr.automaton.Reachable := by
  sorry

def egraph (pcr : PCR S) : EGraph S pcr.Classes where
  auto     := pcr.automaton
  no_final := rfl
  det      := pcr.automaton_deterministic
  reach    := pcr.automaton_reachable

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
