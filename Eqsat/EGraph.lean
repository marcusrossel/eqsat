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
  congr h mem := open TreeAutomaton TRS.Steps in by
    rename_i fn as bs
    simp only [PER.support, and_self] at mem
    obtain ⟨c, hc⟩ := mem
    refine ⟨c, hc, ?_⟩
    have ⟨qs, hq₁, hq₂⟩ := hc.final
    apply tail (children fun i => ?_) (step_of_transition hq₁)
    have ⟨_, hc₁, hc₂⟩ := h i
    obtain ⟨rfl⟩ := graph.det hc₁ <| steps_child hq₂ i
    exact hc₂
  reach h i := by
    simp only [PER.support, and_self, Set.mem_setOf_eq] at *
    obtain ⟨_, h⟩ := h
    apply h.child

end EGraph

/- Theorem 6 -/
namespace PCR

variable [Signature S] {graph : EGraph S Q}

inductive IsAutomatonTransition (pcr : PCR S) : (TreeAutomaton.Transition S pcr.Classes) → Prop
  | intro (mem₁ : fn ° as ∈ pcr.support) (mem₂ : ∀ i, as i ∈ pcr.support) :
    IsAutomatonTransition pcr ⟨fn, fun i => ⟦⟨as i, mem₂ i⟩⟧, ⟦⟨fn ° as, mem₁⟩⟧⟩

def automaton (pcr : PCR S) : TreeAutomaton S pcr.Classes where
  trans := { tr | pcr.IsAutomatonTransition tr }
  final := ∅

open TreeAutomaton Signature.Extended in section

theorem automaton_step_deterministic {pcr : PCR S} {t : Term _} {q₁ q₂ : pcr.Classes}
    (h₁ : t -[pcr.automaton]→ q₁) (h₂ : t -[pcr.automaton]→ q₂) : q₁ = q₂ := by
  let fn ° as := t
  obtain ⟨_, ⟨mem₁₁, mem₁₂⟩, h₁⟩ := mem_trs_to_trans h₁.rw_of_ext.choose_spec
  obtain ⟨_, ⟨mem₂₁, mem₂₂⟩, h₂⟩ := mem_trs_to_trans h₂.rw_of_ext.choose_spec
  simp only [Transition.toRewrite, Rewrite.mk.injEq, Pattern.app.injEq, ext.injEq] at h₁ h₂
  obtain ⟨⟨rfl, rfl⟩, rfl, _⟩ := h₁
  obtain ⟨⟨⟨rfl, rfl⟩, h⟩, rfl, _⟩ := h₂
  rename_i fn as₁ _ as₂ _
  have h i : (⟦⟨as₁ i, mem₁₂ _⟩⟧ : Quotient pcr.supportSetoid) = ⟦⟨as₂ i, mem₂₂ _⟩⟧ := by
    have := congrFun (eq_of_heq h) i
    simp_all
  exact Quotient.sound <| @pcr.congr fn as₁ as₂ (Quotient.eq.mp <| h ·) mem₁₁

theorem automaton_deterministic (pcr : PCR S) : pcr.automaton.Deterministic := by
  intro t q₁ q₂ hq₁ hq₂
  let fn ° as := t
  have ⟨qs₁, mem₁, h₁⟩ := hq₁.final
  have ⟨qs₂, mem₂, h₂⟩ := hq₂.final
  have h := funext fun i => automaton_deterministic pcr (steps_child h₁ i) (steps_child h₂ i)
  exact automaton_step_deterministic (step_of_transition mem₁) (step_of_transition <| h ▸ mem₂)

theorem automaton_reachable (pcr : PCR S) : pcr.automaton.Reachable := by
  refine Quotient.ind fun ⟨t, h⟩ => ⟨t, ?_⟩
  induction t
  case app ih =>
    exact .tail (.children fun i => ih i <| pcr.reach h i) (step_of_transition <| .intro ..)

end

def egraph (pcr : PCR S) : EGraph S pcr.Classes where
  auto     := pcr.automaton
  no_final := rfl
  det      := pcr.automaton_deterministic
  reach    := pcr.automaton_reachable

theorem egraph_correct (pcr : PCR S) : pcr.egraph.pcr = pcr := by
  ext t₁ t₂
  induction t₁ generalizing t₂
  let fn₂ ° as₂ := t₂
  case app fn₁ as₁ ih =>
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
