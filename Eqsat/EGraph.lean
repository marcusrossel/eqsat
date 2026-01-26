import Eqsat.TreeAutomaton
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

-- Intuition: The rewrites induce two steps lhs → rhs₁ and lhs → rhs₂. We would like to apply
--            determinism to this, but can't as lhs is not a ground term. However, lhs must have the
--            form fn(q₁, ..., qₙ) where each qᵢ is a state variable (member of `Q`). Thus, by
--            reachability for each qᵢ we can obtain a term tᵢ with tᵢ →* qᵢ. Thus, the *ground*
--            term fn(t₁, ..., tₙ) rewrites to lhs, which then rewrites to rhs₁ and rhs₂
--            respectively. On these two rewrite sequences we can apply determinism.
open TreeAutomaton TRS in
theorem rw_lhs_unique (mem₁ : ⟨lhs, rhs₁, h₁⟩ ∈ graph.trs) (mem₂ : ⟨lhs, rhs₂, h₂⟩ ∈ graph.trs) :
    rhs₁ = rhs₂ := by
  have ⟨⟨sym₁, srcs₁, dst₁⟩, _, h₁⟩ := mem_trs_to_trans mem₁
  have ⟨⟨sym₂, srcs₂, dst₂⟩, _, h₂⟩ := mem_trs_to_trans mem₂
  rw [Transition.toRewrite] at h₁ h₂
  injections; subst_vars; injections; simp_all only [Pattern.app.injEq, heq_eq_eq]
  refine ⟨?_, funext (·.elim0)⟩
  have sᵢ := (graph.reach <| srcs₁ ·)
  have s  := Steps.children (S := S ⨄ Q) (fn := sym₁) (sᵢ · |>.choose_spec)
  have s₁ := Steps.trans s <| .single <| .subst' mem₁
  have s₂ := Steps.trans s <| .single <| .subst' mem₂
  rw [graph.det (t := sym₁ ° (sᵢ · |>.choose)) s₁ s₂]

-- Intuition: If we take single steps t → t₁ and t → t₂, we can always join t₁ and t₂ my mimicking
--            the step of the other side respectively.
theorem trs_locallyConfluent (graph : EGraph S Q) : graph.trs.LocallyConfluent := by
  intro t t₁ t₂ s₁ s₂
  cases TreeAutomaton.Bistep.of_steps s₁ s₂
  -- If both steps directly apply a rewrite, then by determinism (by `rw_lhs_unique`) the rewrite
  -- must have been the same one, so we have t₁ = t₂ and choose t₃ to be the same.
  case subst _ mem₁ _ mem₂ =>
    exact ⟨t₁, by simp [graph.rw_lhs_unique mem₁ mem₂]⟩
  -- If both steps rewrite a child, there are two possible cases.
  case child fn i₁ a₁ i₂ a₂ as h₁ h₂ =>
    -- Case 1: Both steps rewrite the same child. In that case, by induction, those child terms are
    --         joinable, so t₁ and t₂ are joinable.
    if hi : i₁ = i₂ then
      subst hi
      have ⟨_, ha₁, ha₂⟩ := trs_locallyConfluent graph h₁ h₂
      have s₁ := Args.set_twice as .. ▸ TRS.Steps.child (Args.set_get as i₁ a₁ ▸ ha₁)
      have s₂ := Args.set_twice as .. ▸ TRS.Steps.child (Args.set_get as i₁ a₂ ▸ ha₂)
      exact ⟨_, s₁, s₂⟩
    -- Case 2: Both steps rewrite different children. That is:
    --         * Step 1 rewrites fn ° as → fn ° as[i₁ := a₁], and
    --         * Step 2 rewrites fn ° as → fn ° as[i₂ := a₂], with i₁ ≠ i₂.
    --         In that case, we show that the rewrite of Step 1 can still be applied to the result
    --         of Step 2, and vice versa. Thus both sides can be rewritten to:
    --         * fn ° as[i₁ := a₁][i₂ := a₂], and
    --         * fn ° as[i₂ := a₂][i₁ := a₁], respectively.
    --         These terms are obviously equal.
    else
      have s₁ := TRS.Step.child fn _ <| Args.set_get_ne as a₂ (Ne.symm hi) ▸ h₁
      have s₂ := TRS.Step.child fn _ <| Args.set_get_ne as a₁ hi ▸ h₂
      replace s₂ := Args.set_ne_comm as _ _ hi ▸ s₂
      exact ⟨_, .single s₂, .single s₁⟩

-- TODO: Can we also prove the opposite direction: any tree automaton with a confluent TRS is an
--       e-graph?
--       Perhaps we can use a connection between confluence and PCRs for this? Could this also help
--       to prove `trs_confluent` in the first place?
--       What is the overall relationship between the following:
--
--       E-Graph ←induces→ PCR
--          |               ↑
--        induces           |
--          ↓               |
--       confluent trs ←----? [TRaaT]
--
theorem trs_confluent (graph : EGraph S Q) : graph.trs.Confluent :=
  TRS.LocallyConfluent.confluent_of_rev_wf graph.trs_locallyConfluent graph.rev_step_wf

/- **Definition 5** -/
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

/- **Theorem 6** -/
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

open EGraph

theorem egraph_correct (pcr : PCR S) : pcr.egraph.pcr = pcr := by
  ext t₁ t₂
  have acc₁ : pcr.egraph.Accepts ⟦⟨t₁, sorry⟩⟧ t₁ := sorry
  have acc₂ : pcr.egraph.Accepts ⟦⟨t₂, sorry⟩⟧ t₂ := sorry
  apply Iff.intro (fun h => ?mp) (fun h => ?mpr)
  case mp =>
    obtain ⟨c, hc₁, hc₂⟩ := h
    exact Quotient.eq.mp <| pcr.egraph.det acc₂ hc₂ ▸ pcr.egraph.det acc₁ hc₁
  case mpr h =>
    replace h : (⟦⟨t₁, sorry⟩⟧ : pcr.Classes) = ⟦⟨t₂, sorry⟩⟧ := sorry
    exact ⟨_, acc₁, h ▸ acc₂⟩

theorem egraph_unique {pcr : PCR S} (h : pcr = graph.pcr) : graph ≍ pcr.egraph := by
  sorry
  -- TODO: We might not be able to prove this up to HEq, but only some weaker notion of
  --       isomorphism.

end PCR
