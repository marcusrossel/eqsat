import Mathlib.Data.Set.Lattice
import Eqsat.TRS

namespace TreeAutomaton

structure Transition (S Q) [Signature S] where
  fn   : S
  args : Args fn Q
  dst  : Q

def Transition.toRewrite [Signature S] (trans : Transition S Q) : Rewrite (S ⨄ Q) Empty where
  lhs := trans.fn ° (trans.args ·)
  rhs := ↑trans.dst

structure _root_.TreeAutomaton (S Q) [Signature S] where
  trans : Set (Transition S Q)
  final : Set Q

variable [Signature S]

def trs (auto : TreeAutomaton S Q) : TRS (S ⨄ Q) Empty :=
  Transition.toRewrite '' auto.trans

notation t₁ " -[" auto "]→ " t₂ => t₁ -[TreeAutomaton.trs auto]→ t₂
notation t₁ " -[" auto "]→* " t₂ => t₁ -[TreeAutomaton.trs auto]→* t₂

variable {auto : TreeAutomaton S Q} in section

theorem step_extLT : (t₁ -[auto]→ t₂) → t₁.ExtLT t₂
  | .child (.sig _) _ h =>
    Term.ExtLT.child (step_extLT h)
  | .subst _ mem => by
    obtain ⟨_, _, rfl⟩ := Set.mem_image _ _ _ |>.mp mem
    simp only [Transition.toRewrite]
    constructor

theorem step_preserves_fn (h : fn₁ ° as -[auto]→ fn₂ ° bs) : fn₁ = fn₂ := by
  generalize hl : fn₁ ° as = lhs at h
  generalize hr : fn₂ ° bs = rhs at h
  induction h
  case subst => sorry
  case child => sorry

theorem steps_preserve_fn (h : fn₁ ° as -[auto]→* fn₂ ° bs) : fn₁ = fn₂ := by
  cases h
  case refl => rfl
  case tail t hd tl =>
    cases t
    case var => contradiction
    case app =>
      obtain ⟨rfl⟩ := step_preserves_fn tl
      exact steps_preserve_fn hd
termination_by fn₂ ° bs
decreasing_by exact step_extLT tl

end

def Accepts (auto : TreeAutomaton S Q) (q : Q) (t : Term S) : Prop :=
  t -[auto]→* q

-- If a state `q` accepts a term `fn ° as`, then the final step of that acceptance must have been
-- based on a transition `⟨fn, qs, q⟩ ∈ auto.trans` where `qs` are states which accept `as`.
theorem Accepts.final {auto : TreeAutomaton S Q} (acc : Accepts auto q (fn ° as)) :
    ∃ qs : Args fn Q, ⟨fn, qs, q⟩ ∈ auto.trans ∧ ↑(fn ° as) -[auto]→* fn ° (qs ·) := by
  cases acc
  case tail lhs has h =>
    generalize hr : (q : Term <| S ⨄ Q) = rhs at h
    cases h
    case subst mem =>
      obtain ⟨t, ht, rfl⟩ := Set.mem_image _ _ _ |>.mp mem
      simp only [Transition.toRewrite, Subst.apply_no_vars] at *
      obtain ⟨rfl⟩ := steps_preserve_fn has
      exists t.args
      simp_all
    case child =>
      obtain ⟨rfl⟩ := steps_preserve_fn has
      simp at hr

theorem accepts_child {auto : TreeAutomaton S Q} (acc : (fn ° as : Term S) -[auto]→* t) (i) :
    ∃ qᵢ : Q, as i -[auto]→* qᵢ := by
  sorry

def Deterministic (auto : TreeAutomaton S Q) : Prop :=
  ∀ {t : Term S} {q₁ q₂ : Q}, (t -[auto]→* q₁) → (t -[auto]→* q₂) → q₁ = q₂

def Reachable (auto : TreeAutomaton S Q) : Prop :=
  ∀ q : Q, ∃ t : Term S, t -[auto]→* q
