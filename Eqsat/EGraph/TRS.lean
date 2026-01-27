import Eqsat.EGraph.Basic

namespace EGraph

variable [Signature S] {graph : EGraph S Q}

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

theorem trs_confluent (graph : EGraph S Q) : graph.trs.Confluent :=
  TRS.LocallyConfluent.confluent_of_terminating graph.trs_locallyConfluent graph.trs_terminating

theorem trs_convergent (graph : EGraph S Q) : graph.trs.Convergent where
  confluent   := graph.trs_confluent
  terminating := graph.trs_terminating

-- Every tree automaton with a convergent TRS (and no final states) has an "equivalent" e-graph.
-- By "equivalent" we mean ...
-- TODO: which we prove in theorem ...
open TreeAutomaton in
def ofConvergent (auto : TreeAutomaton S Q) (con : auto.trs.Convergent) (fin : auto.final = ∅) :
    EGraph S auto.ReachableState where
  auto := auto.reachable
  no_final := by simp [reachable, reachableFinal, fin]
  det h₁ h₂ := by
    have con : auto.reachable.trs.Confluent := reachable_preserves_confluence con.confluent
    have := TRS.Confluent.unique_nfs con (state_isNF _) (state_isNF _) h₁ h₂
    simp_all
  reach q := by
    let ⟨q, hq⟩ := q
    induction hq
    case const tr mem h =>
      exists tr.sym ° (h ▸ · |>.elim0)
      have s := TreeAutomaton.step_of_transition mem
      sorry -- TODO: Follows from s
    case trans tr mem h ih =>
      -- TODO: do you need to use termination here?
      sorry
