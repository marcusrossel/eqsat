import Eqsat.TreeAutomaton.Basic

variable [Signature S] {auto : TreeAutomaton S Q}

namespace TreeAutomaton

-- A given state is applicable (from a ground term) if it is the destination of a transition where
-- all source states are applicable. Note that this condition is vacuously satisfied for constants.
inductive IsApplicableState (auto : TreeAutomaton S Q) : Q → Prop where
  | intro : tr ∈ auto.trans → (∀ i, IsApplicableState auto <| tr.srcs i) → IsApplicableState auto tr.dst

-- The set of applicable states.
abbrev ApplicableState (auto : TreeAutomaton S Q) : Type :=
  { q // auto.IsApplicableState q }

def Transition.expand {auto : TreeAutomaton S Q} (tr : Transition S auto.ApplicableState) :
    Transition S Q where
  sym  := tr.sym
  srcs := (tr.srcs ·)
  dst  := tr.dst

def IsApplicableTransition (auto : TreeAutomaton S Q) (tr : Transition S Q) : Prop :=
  ∀ i, auto.IsApplicableState <| tr.srcs i

def applicableTrans (auto : TreeAutomaton S Q) : Set (Transition S auto.ApplicableState) :=
  { τ | τ.expand ∈ auto.trans ∧ auto.IsApplicableTransition τ.expand }

def applicableFinal (auto : TreeAutomaton S Q) : Set auto.ApplicableState :=
  { q | ↑q ∈ auto.final ∧ auto.IsApplicableState q }

-- The applicable sub-automaton prunes all "unreachable" states and transitions.
def applicable (auto : TreeAutomaton S Q) : TreeAutomaton S auto.ApplicableState where
  trans := auto.applicableTrans
  final := auto.applicableFinal

end TreeAutomaton

section Expand

@[simp]
def Signature.Extended.expand : (S ⨄ auto.ApplicableState) → S ⨄ Q
  | .sig s => s
  | .ext s => s

theorem Signature.Extended.expand_arity :
    (s : S ⨄ auto.ApplicableState) → Signature.arity s.expand = Signature.arity s
  | .sig _ => rfl
  | .ext _ => rfl

@[simp]
def Pattern.expand : Pattern (S ⨄ auto.ApplicableState) V → Pattern (S ⨄ Q) V
  | (v : V) => v
  | fn ° as => fn.expand ° (expand <| as <| fn.expand_arity ▸ ·)

theorem Pattern.expand_inj {p₁ p₂ : Pattern (S ⨄ auto.ApplicableState) V}
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
def Pattern.expand_vars (p : Pattern (S ⨄ auto.ApplicableState) V) : p.expand.vars = p.vars := by
  induction p
  case var => rfl
  case app fn _ ih => cases fn <;> simp [ih]

@[simp]
def Rewrite.expand (rw : Rewrite (S ⨄ auto.ApplicableState) V) : Rewrite (S ⨄ Q) V where
  lhs := rw.lhs.expand
  rhs := rw.rhs.expand
  sub := by simp [rw.sub]

def Subst.expand (σ : Subst (S ⨄ auto.ApplicableState) V) : Subst (S ⨄ Q) V :=
  fun i => (σ i).expand

theorem TreeAutomaton.mem_applicable_trans (mem : tr ∈ auto.applicable.trans) :
    tr.expand ∈ auto.trans := by
  simp_all [applicable, applicableTrans]

theorem TreeAutomaton.mem_applicable_trs (mem : rw ∈ auto.applicable.trs) : rw.expand ∈ auto.trs := by
  have ⟨tr, h₁, h₂⟩ := mem_trs_to_trans mem
  rw [Transition.toRewrite] at h₂
  simp only [trs, Rewrite.expand, Set.mem_image, ← h₂, Pattern.expand]
  exists tr.expand, mem_applicable_trans h₁
  simp [Transition.toRewrite]
  refine ⟨⟨rfl, ?_⟩, rfl, funext (·.elim0)⟩
  ext i; congr; ext i; exact i.elim0

theorem TreeAutomaton.restrict_mem_trans
    (mem : τ ∈ auto.trans) (h : ∀ i, auto.IsApplicableState <| τ.srcs i) :
    ⟨τ.sym, fun i => ⟨τ.srcs i, h i⟩, ⟨τ.dst, ⟨mem, h⟩⟩⟩ ∈ auto.applicable.trans :=
  ⟨mem, h⟩

theorem Args.set_expand (as : Term.Args fn) (a : Term <| S ⨄ auto.ApplicableState) :
    (as[↑i := a] · |>.expand) = (as · |>.expand)[i := a.expand] := by
  ext i; simp only [set]; split <;> rfl

theorem TRS.Step.expand (s : t₁ -[auto.applicable]→ t₂) : t₁.expand -[auto]→ t₂.expand := by
  induction s
  case subst σ mem =>
    have := Step.subst σ.expand <| TreeAutomaton.mem_applicable_trs mem
    simp_all
  case child a fn as i s ih =>
    cases fn
    all_goals
      rename_i fn
      simp only [Pattern.expand]
      erw [Args.set_expand as a]
      exact Step.child (a := a.expand) fn (as · |>.expand) ih

open TreeAutomaton in
theorem TRS.Step.restrict {t₁ : Term (S ⨄ auto.ApplicableState)} (s : t₁.expand -[auto]→ t₂) :
    ∃ r : Term (S ⨄ auto.ApplicableState), (t₂ = r.expand) ∧ t₁ -[auto.applicable]→ r := by
  generalize hl : t₁.expand = lhs at s
  induction s generalizing t₁
  case subst mem =>
    simp only [Subst.apply_no_vars] at ⊢ hl
    have ⟨tr, mem, ht⟩ := mem_trs_to_trans mem
    rw [Transition.toRewrite] at ht
    have hd : auto.IsApplicableState tr.dst := by
      -- TODO: Factor this out into a lemma.
      refine .intro mem fun i => ?_
      simp only [← ht] at hl
      let fn₁ ° as₁ := t₁
      rw [Pattern.expand] at hl
      injection hl with hl₁ hl₂
      cases fn₁
      case sig =>
        injection hl₁; subst_vars
        have := congr (eq_of_heq hl₂) (rfl : i = i)
        simp at this
        let (eq := h) a₁ ° a₂ := as₁ i
        rw [h, Pattern.expand] at this
        injection this with h
        cases a₁
        case sig => contradiction
        case ext =>
          rw [Signature.Extended.expand] at h
          injection h with h
          rw [← h]
          sorry -- refine .intro ?_ ?_
      case ext => sorry
    exists (⟨tr.dst, hd⟩ : auto.ApplicableState)
    simp only [← ht] at ⊢ hl
    constructor
    · congr; ext i; exact i.elim0
    · have ⟨trr, ht₁, ht₂⟩ : ∃ trr : Transition S auto.ApplicableState, trr.expand = tr ∧ trr ∈ auto.applicable.trans :=
        sorry -- It might suffice to prove just ht₁ and then deduce ht₂ from mem
      subst ht₁
      have h : t₁.expand = (↑trr.sym ° (trr.srcs ·)).expand (auto := auto) := by
        simp only [Transition.expand] at hl
        sorry
      exact Pattern.expand_inj h ▸ step_of_transition ht₂
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

theorem TRS.Steps.expand (s : t₁ -[auto.applicable]→* t₂) : t₁.expand -[auto]→* t₂.expand := by
  induction s
  case refl => rfl
  case tail tl ih => exact tail ih tl.expand

theorem TRS.Steps.restrict {t₁ : Term (S ⨄ auto.ApplicableState)} (s : t₁.expand -[auto]→* t₂) :
    ∃ r : Term (S ⨄ auto.ApplicableState), (t₂ = r.expand) ∧ (t₁ -[auto.applicable]→* r) := by
  induction s
  case refl => exact ⟨_, rfl, .refl⟩
  case tail tl ih =>
    obtain ⟨_, hr, hd⟩ := ih
    have ⟨_, hr, tl⟩ := (hr ▸ tl).restrict
    exact ⟨_, hr, .tail hd tl⟩

end Expand

def TreeAutomaton.applicable_preserves_confluence (con : auto.trs.Confluent) :
    auto.applicable.trs.Confluent := by
  intro t t₁ t₂ s₁ s₂
  have ⟨_, s₁, s₂⟩ := con s₁.expand s₂.expand
  have ⟨r, hr₁, s₁⟩ := s₁.restrict
  have ⟨_, hr₂, s₂⟩ := s₂.restrict
  have hr := Pattern.expand_inj (hr₁ ▸ hr₂)
  exact ⟨r, s₁, hr ▸ s₂⟩

def TreeAutomaton.applicable_preserves_termination (con : auto.trs.Terminating) :
    auto.applicable.trs.Terminating := by
  sorry -- TODO: Currently this is not needed.

def TreeAutomaton.applicable_trs_reachable : auto.applicable.Reachable := by
  intro ⟨q, hq⟩
  induction hq
  case intro τ mem h ih =>
    exists τ.sym ° (ih · |>.choose)
    refine TRS.Steps.tail ?_ (step_of_transition <| restrict_mem_trans mem h)
    exact TRS.Steps.children (ih · |>.choose_spec)

-- TODO: Useful lemma? Ground terms can only be accepted by applicable states.
--       This should pretty much follow from the definition of applicable states.
