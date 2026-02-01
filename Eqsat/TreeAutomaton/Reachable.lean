import Eqsat.TreeAutomaton.Basic

variable [Signature S] {auto : TreeAutomaton S Q}

namespace TreeAutomaton

-- A given state is reachable (from a ground term) if it is the destination of a transition where
-- all source states are reachable. Note that this condition is vacuously satisfied for constants.
inductive IsReachableState (auto : TreeAutomaton S Q) : Q → Prop where
  | intro : tr ∈ auto.trans → (∀ i, IsReachableState auto <| tr.srcs i) → IsReachableState auto tr.dst

-- The set of reachable states.
abbrev ReachableState (auto : TreeAutomaton S Q) : Type :=
  { q // auto.IsReachableState q }

def Transition.expand {auto : TreeAutomaton S Q} (tr : Transition S auto.ReachableState) :
    Transition S Q where
  sym  := tr.sym
  srcs := (tr.srcs ·)
  dst  := tr.dst

def IsReachableTransition (auto : TreeAutomaton S Q) (tr : Transition S Q) : Prop :=
  ∀ i, auto.IsReachableState <| tr.srcs i

def reachableTrans (auto : TreeAutomaton S Q) : Set (Transition S auto.ReachableState) :=
  { tr | tr.expand ∈ auto.trans ∧ auto.IsReachableTransition tr.expand }

def reachableFinal (auto : TreeAutomaton S Q) : Set auto.ReachableState :=
  { q | ↑q ∈ auto.final ∧ auto.IsReachableState q }

-- The reachable sub-automaton prunes all unreachable states and transitions.
def reachable (auto : TreeAutomaton S Q) : TreeAutomaton S auto.ReachableState where
  trans := auto.reachableTrans
  final := auto.reachableFinal

end TreeAutomaton

section Expand

@[simp]
def Pattern.expand : Pattern (S ⨄ auto.ReachableState) V → Pattern (S ⨄ Q) V
  | (v : V)        => v
  | (.sig fn) ° as => fn ° (expand <| as ·)
  | (.ext fn) ° as => fn ° (expand <| as ·)

theorem Pattern.expand_inj {p₁ p₂ : Pattern (S ⨄ auto.ReachableState) V}
    (h : p₁.expand = p₂.expand) : p₁ = p₂ := by
  induction p₁ generalizing p₂ <;> cases p₂
  case var.var => simp_all [expand]
  case var.app fn _ => cases fn <;> contradiction
  case app.var fn₁ _ _ _ => cases fn₁ <;> contradiction
  case app.app fn₁ _ ih fn₂ _ =>
    cases fn₁ <;> cases fn₂
    case sig.ext => injections
    case ext.sig => injections
    case sig.sig =>
      injections; subst_vars
      congr
      ext i
      have h := congr (eq_of_heq ‹_›) (rfl : i = i)
      exact ih _ h
    case ext.ext =>
      injections
      congr
      next h => exact Subtype.val_inj.mp h
      next h _ =>
        ext i
        have h := congr h (rfl : i = i)
        exact ih _ h

@[simp]
def Pattern.expand_vars (p : Pattern (S ⨄ auto.ReachableState) V) : p.expand.vars = p.vars := by
  induction p
  case var => rfl
  case app fn _ ih => cases fn <;> simp [ih]

@[simp]
def Rewrite.expand (rw : Rewrite (S ⨄ auto.ReachableState) V) : Rewrite (S ⨄ Q) V where
  lhs := rw.lhs.expand
  rhs := rw.rhs.expand
  sub := by simp [rw.sub]

def Subst.expand (σ : Subst (S ⨄ auto.ReachableState) V) : Subst (S ⨄ Q) V :=
  fun i => (σ i).expand

theorem TreeAutomaton.mem_reachable_trans (mem : tr ∈ auto.reachable.trans) :
    tr.expand ∈ auto.trans := by
  simp_all [reachable, reachableTrans]

theorem TreeAutomaton.mem_reachable_trs (mem : rw ∈ auto.reachable.trs) : rw.expand ∈ auto.trs := by
  have ⟨tr, h₁, h₂⟩ := mem_trs_to_trans mem
  rw [Transition.toRewrite] at h₂
  simp only [trs, Rewrite.expand, Set.mem_image, ← h₂, Pattern.expand]
  exists tr.expand, mem_reachable_trans h₁
  simp [Transition.toRewrite]
  refine ⟨⟨rfl, ?_⟩, rfl, funext (·.elim0)⟩
  ext i; congr; ext i; exact i.elim0

theorem Args.set_expand (as : Term.Args fn) (a : Term <| S ⨄ auto.ReachableState) :
    (as[↑i := a] · |>.expand) = (as · |>.expand)[i := a.expand] := by
  ext i; cases fn
  all_goals simp only [set]; split <;> rfl

theorem TRS.Step.expand (s : t₁ -[auto.reachable]→ t₂) : t₁.expand -[auto]→ t₂.expand := by
  induction s
  case subst σ mem =>
    have := Step.subst σ.expand <| TreeAutomaton.mem_reachable_trs mem
    simp_all
  case child a fn as i s ih =>
    cases fn
    all_goals
      rename_i fn
      simp only [Pattern.expand]
      erw [Args.set_expand as a]
      exact Step.child (a := a.expand) fn (as · |>.expand) ih

open TreeAutomaton in
theorem TRS.Step.restrict {t₁ : Term (S ⨄ auto.ReachableState)} (s : t₁.expand -[auto]→ t₂) :
    ∃ r : Term (S ⨄ auto.ReachableState), (t₂ = r.expand) ∧ t₁ -[auto.reachable]→ r := by
  generalize hl : t₁.expand = lhs at s
  induction s generalizing t₁
  case subst mem =>
    simp at *
    have ⟨tr, _, ht⟩ := mem_trs_to_trans mem
    rw [Transition.toRewrite] at ht
    have hd : auto.IsReachableState tr.dst := sorry
    exists (⟨tr.dst, hd⟩ : auto.ReachableState)
    simp only [← ht] at ⊢ hl
    constructor
    · congr; ext i; exact i.elim0
    · have ⟨trr, ht₁, ht₂⟩ : ∃ trr : Transition S auto.ReachableState, trr.expand = tr ∧ trr ∈ auto.reachable.trans :=
        sorry -- It might suffice to prove just ht₁ and then deduce ht₂ from left✝
      subst ht₁
      have := step_of_transition ht₂
      -- bubble up the expand throught hl, then rewrite in the goal, the rest should follow
      sorry
  case child a fn as i s ih =>
    let fn₁ ° as₁ := t₁
    cases fn₁
    all_goals
      rw [Pattern.expand] at hl
      injection hl with hl₁ hl₂
      subst hl₁ hl₂
      have ⟨r, hr, s'⟩ := ih rfl
      subst hr
      erw [← Args.set_expand as₁ r, ← Pattern.expand]
      exact ⟨_, rfl, .child _ _ s'⟩

theorem TRS.Steps.expand (s : t₁ -[auto.reachable]→* t₂) : t₁.expand -[auto]→* t₂.expand := by
  induction s
  case refl => rfl
  case tail tl ih => exact tail ih tl.expand

theorem TRS.Steps.restrict {t₁ : Term (S ⨄ auto.ReachableState)} (s : t₁.expand -[auto]→* t₂) :
    ∃ r : Term (S ⨄ auto.ReachableState), (t₂ = r.expand) ∧ (t₁ -[auto.reachable]→* r) := by
  induction s
  case refl => exact ⟨_, rfl, .refl⟩
  case tail tl ih =>
    obtain ⟨_, hr, hd⟩ := ih
    have ⟨_, hr, tl⟩ := (hr ▸ tl).restrict
    exact ⟨_, hr, .tail hd tl⟩

end Expand

def TreeAutomaton.reachable_preserves_confluence (con : auto.trs.Confluent) :
    auto.reachable.trs.Confluent := by
  intro t t₁ t₂ s₁ s₂
  have ⟨_, s₁, s₂⟩ := con s₁.expand s₂.expand
  have ⟨r, hr₁, s₁⟩ := s₁.restrict
  have ⟨_, hr₂, s₂⟩ := s₂.restrict
  have hr := Pattern.expand_inj (hr₁ ▸ hr₂)
  exact ⟨r, s₁, hr ▸ s₂⟩
