import Mathlib.Data.Set.Lattice
import Eqsat.TRS

namespace TreeAutomaton

structure Transition (S Q) [Signature S] where
  fn   : S
  args : Args fn Q
  dst  : Q

-- TODO: Is this definition correct? We interpret all state vars as constants, so there are no
--       variables. Thus, the only rewrite steps which can occur are subterm replacements.
def Transition.toRewrite [Signature S] (trans : Transition S Q) :
    Rewrite (S ⊕ Q) Empty where
  lhs := (.inl trans.fn) ° fun i => ↑(trans.args i)
  rhs := ↑trans.dst

structure _root_.TreeAutomaton (S Q) [Signature S] where
  trans : Set (TreeAutomaton.Transition S Q)
  final : Set Q

variable [Signature S]

def trs (auto : TreeAutomaton S Q) : TRS (S ⊕ Q) Empty :=
  Transition.toRewrite '' auto.trans

notation t₁ " →*[" auto "] " t₂ => t₁ →*[TreeAutomaton.trs auto] t₂

def Accepts (auto : TreeAutomaton S Q) (q : Q) (t : Term S) : Prop :=
  t →*[auto] q

-- TODO: Perhaps we should just generalize this to the final accepting thing being a term, not just a state.
--       Then this also speicalizes to the state case.
theorem Accepts.child {auto : TreeAutomaton S Q} (acc : Accepts auto q <| fn ° as) (i) :
    ∃ qᵢ : Q, Accepts auto qᵢ (as i) := by
  sorry
  /-cases acc
  case refl =>
    sorry
  case tail t hd tl =>
    obtain ⟨qs, rfl⟩ : ∃ qs, t = .app (.inl fn) qs := sorry -- should follow from tl
    replace hd : (Term.toExtended <| .app fn as) →*[auto] (Term.app (.inl fn) qs) := hd

    -- simp [Term.toExtended] at hd
  -/
  /-
  cases acc.cases_head
  case inl h => simp [Term.toExtended] at h
  case inr h =>
    obtain ⟨_, h, _⟩ := h
    generalize ht : Term.toExtended (.app fn as) = t at h
    cases h
    case subst rw _ mem _ =>
      rw [Subst.apply_no_vars] at ht
      obtain ⟨tr, mem, rfl⟩ := mem
      simp only [Term.toExtended, Transition.toRewrite, Pattern.app.injEq, Sum.inl.injEq] at ht
      obtain ⟨rfl, ht⟩ := ht
      replace ht := eq_of_heq ht
      replace ht : (as i).toExtended = .app (.inr (tr.args i)) nofun := sorry -- specialize ht to i

      -- by ht and mem?
      -- apply Relation.ReflTransGen.tail .refl
      rw [ht]
      sorry -- construct a Step.child?
    case child => sorry
  -/
  /-
  cases acc
  case tail t hd tl =>

    obtain ⟨qs, rfl⟩ : ∃ qs, t = .app (.inl fn) qs := sorry -- should follow from tl
    replace hd : (Term.toExtended <| .app fn as) →*[auto] (Term.app (.inl fn) qs) := hd
    simp [Term.toExtended] at hd
    cases hd
    case refl => sorry -- should follow from tl
    case tail => sorry
  -/
  /-
  case inl => simp [Term.toExtended] at *
  case inr h =>

    obtain ⟨c, h, _⟩ := h
    generalize hl : Term.toExtended (.app fn as) = lhs at h
    generalize hr : c = rhs at h
    cases h
    case subst rw _ _ mem =>
      rw [Subst.apply_no_vars] at hl hr
      obtain ⟨tr, mem, htr⟩ := mem
      subst htr
      simp only [Term.toExtended, Transition.toRewrite, Pattern.app.injEq, Sum.inl.injEq] at hl hr
      obtain ⟨rfl, hl⟩ := hl
      replace hl := eq_of_heq hl
      exists tr.args -- IS THIS IS INCORRECT?
      intro i
      apply Relation.ReflTransGen.tail .refl
      replace hl : (as i).toExtended = .app (.inr (tr.args i)) nofun := sorry -- specialize hl to i
      rw [hl]
      sorry -- construct a Step.child?
    case child => sorry -- might require induction instead of cases
    -/

def Deterministic (auto : TreeAutomaton S Q) : Prop :=
  ∀ {t : Term S} {q₁ q₂ : Q}, (t →*[auto] q₁) → (t →*[auto] q₂) → q₁ = q₂

def Reachable (auto : TreeAutomaton S Q) : Prop :=
  ∀ q : Q, ∃ t : Term S, t →*[auto] q
