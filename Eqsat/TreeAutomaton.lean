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

def Transition.map [Signature S] (trans : Transition S Q₁) (f : Q₁ → Q₂) : Transition S Q₂ where
  fn   := trans.fn
  args := (f <| trans.args ·)
  dst  := f trans.dst

structure _root_.TreeAutomaton (S Q) [Signature S] where
  trans : Set (Transition S Q)
  final : Set Q

variable [Signature S]

def trs (auto : TreeAutomaton S Q) : TRS (S ⨄ Q) Empty :=
  Transition.toRewrite '' auto.trans

notation t₁ " -[" auto "]→ " t₂ => t₁ -[TreeAutomaton.trs auto]→ t₂
notation t₁ " -[" auto "]→* " t₂ => t₁ -[TreeAutomaton.trs auto]→* t₂

variable {auto : TreeAutomaton S Q} {fn₁ : S ⨄ Q} {fn₂ : S} in section

theorem step_preserves_fn (h : fn₁ ° as -[auto]→ fn₂ ° bs) : fn₁ = fn₂ := by
  generalize hl : fn₁ ° as = lhs at h
  generalize hr : (Signature.Extended.sig fn₂) ° bs = rhs at h
  cases h
  case subst mem =>
    obtain ⟨_, _, rfl⟩ := Set.mem_image _ _ _ |>.mp mem
    simp [Transition.toRewrite] at hr
  case child => grind

theorem step_child (h : fn ° as -[auto]→ fn ° bs) (i) : (as i -[auto]→ bs i) ∨ (as i = bs i) := by
  generalize hl : fn ° as = lhs at h
  generalize hr : fn ° bs = rhs at h
  cases h
  case subst mem =>
    cases fn
    case ext => exact i.elim0
    case sig =>
      obtain ⟨_, _, rfl⟩ := Set.mem_image _ _ _ |>.mp mem
      simp [Transition.toRewrite] at hr
  case child j _ =>
    injection hl with hl
    subst hl
    by_cases j = i <;> simp_all

theorem steps_preserve_fn (h : fn₁ ° as -[auto]→* fn₂ ° bs) : fn₁ = fn₂ := by
  generalize hl : fn₁ ° as = lhs at h
  generalize hr : (Signature.Extended.sig fn₂) ° bs = rhs at h
  induction h generalizing bs
  case refl =>
    injection hl ▸ hr with h _
    exact h.symm
  case tail b _ hd tl ih =>
    subst hl hr
    cases b
    case var => contradiction
    case app =>
      obtain ⟨rfl⟩ := step_preserves_fn tl
      exact ih rfl

theorem steps_child {as bs} (h : fn ° as -[auto]→* fn ° bs) (i) : as i -[auto]→* bs i := by
  cases fn
  case ext => exact i.elim0
  case sig fn =>
    generalize hl : (Signature.Extended.sig fn) ° as = lhs at h
    generalize hr : (Signature.Extended.sig fn) ° bs = rhs at h
    induction h generalizing bs
    case refl =>
      injection hl ▸ hr with _ h
      exact h ▸ .refl
    case tail b _ hd tl ih  =>
      subst hl hr
      cases b
      case var => contradiction
      case app =>
        obtain ⟨rfl⟩ := step_preserves_fn tl
        cases step_child tl i
        case inl h => exact .tail (ih rfl) h
        case inr h => exact h ▸ (ih rfl)

end

def Accepts (auto : TreeAutomaton S Q) (q : Q) (t : Term S) : Prop :=
  t -[auto]→* q

-- If a state `q` accepts a term `fn ° as`, then the final step of that acceptance must have been
-- based on a transition `⟨fn, qs, q⟩ ∈ auto.trans` where `qs` are states which accept `as`.
theorem Accepts.final {auto : TreeAutomaton S Q} (acc : Accepts auto q <| fn ° as) :
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
    case child fn' _ _ _ =>
      cases fn'
      case sig =>
        obtain ⟨rfl⟩ := steps_preserve_fn has
        simp at hr
      case ext i _ =>
        exact i.elim0

theorem Accepts.child {auto : TreeAutomaton S Q} (acc : Accepts auto q <| fn ° as) (i) :
    ∃ qᵢ : Q, as i -[auto]→* qᵢ :=
  have ⟨_, _, h⟩ := acc.final
  ⟨_, steps_child h i⟩

def Deterministic (auto : TreeAutomaton S Q) : Prop :=
  ∀ {t : Term S} {q₁ q₂ : Q}, (t -[auto]→* q₁) → (t -[auto]→* q₂) → q₁ = q₂

def Reachable (auto : TreeAutomaton S Q) : Prop :=
  ∀ q : Q, ∃ t : Term S, t -[auto]→* q

structure Hom (auto₁ : TreeAutomaton S Q₁) (auto₂ : TreeAutomaton S Q₂) where
  hom   : Q₁ → Q₂
  final : ∀ q ∈ auto₁.final, hom q ∈ auto₂.final
  trans : ∀ t ∈ auto₁.trans, t.map hom ∈ auto₂.trans

variable {auto₁ : TreeAutomaton S Q₁} {auto₂ : TreeAutomaton S Q₂}

instance : CoeFun (Hom auto₁ auto₂) (fun _ => Q₁ → Q₂) where
  coe := Hom.hom

theorem Accepts.hom (acc : Accepts auto₁ q t) (hom : Hom auto₁ auto₂) :
    Accepts auto₂ (hom q) t := by
  induction t generalizing q
  case var =>
    contradiction
  case app ih =>
    have ⟨_, t₁, h⟩ := acc.final
    have ht₂ := hom.trans _ t₁
    have hrw₂ := Set.mem_image Transition.toRewrite _ _ |>.mpr ⟨_, ht₂, rfl⟩
    have tl := TRS.Step.subst nofun hrw₂
    simp only [Subst.apply_no_vars] at tl
    apply Relation.ReflTransGen.tail ?_ tl
    exact TRS.Steps.all_children (ih · <| steps_child h _)
