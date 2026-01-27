import Mathlib.Data.Set.Lattice
import Eqsat.TRS

namespace TreeAutomaton

structure Transition (S Q) [Signature S] where
  sym  : S
  srcs : Args sym Q
  dst  : Q

def Transition.toRewrite [Signature S] (trans : Transition S Q) : Rewrite (S ⨄ Q) Empty where
  lhs := trans.sym ° (trans.srcs ·)
  rhs := ↑trans.dst

def Transition.map [Signature S] (trans : Transition S Q₁) (f : Q₁ → Q₂) : Transition S Q₂ where
  sym  := trans.sym
  srcs := (f <| trans.srcs ·)
  dst  := f trans.dst

structure _root_.TreeAutomaton (S Q) [Signature S] where
  trans : Set (Transition S Q)
  final : Set Q

variable [Signature S]

def trs (auto : TreeAutomaton S Q) : TRS (S ⨄ Q) Empty :=
  Transition.toRewrite '' auto.trans

notation t₁ " -[" auto "]→ " t₂ => t₁ -[TreeAutomaton.trs auto]→ t₂
notation t₂ " ←[" auto "]- " t₁ => t₁ -[TreeAutomaton.trs auto]→ t₂
notation t₁ " -[" auto "]→* " t₂ => t₁ -[TreeAutomaton.trs auto]→* t₂

variable {auto : TreeAutomaton S Q} {fn₁ : S ⨄ Q} {fn₂ : S} in section

theorem trans_to_mem_trs (h : t ∈ auto.trans) : t.toRewrite ∈ auto.trs :=
  Set.mem_image Transition.toRewrite _ _ |>.mpr ⟨_, h, rfl⟩

theorem mem_trs_to_trans (h : rw ∈ auto.trs) : ∃ t ∈ auto.trans, t.toRewrite = rw :=
  Set.mem_image _ _ _ |>.mp h

theorem step_lhs_is_proper_app (h : t₁ -[auto]→ t₂) : ∃ (fn : S) (as : _), t₁ = ↑fn ° as := by
  cases h
  case subst mem =>
    have ⟨_, _, h⟩ := mem_trs_to_trans mem
    simp_all [Transition.toRewrite, ← h]
  case child fn as _ _ =>
    cases fn
    case sig fn _ _ => exists fn, as
    case ext i _    => exact i.elim0

theorem step_of_transition {fn : S} {qs : Args fn Q} {q : Q} (mem : ⟨fn, qs, q⟩ ∈ auto.trans) :
    fn ° (qs ·) -[auto]→ q :=
  TRS.Step.subst' <| trans_to_mem_trs mem

theorem step_preserves_fn (h : fn₁ ° as -[auto]→ fn₂ ° bs) : fn₁ = fn₂ := by
  generalize hl : fn₁ ° as = lhs at h
  generalize hr : (Signature.Extended.sig fn₂) ° bs = rhs at h
  cases h
  case subst mem =>
    obtain ⟨_, _, rfl⟩ := mem_trs_to_trans mem
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
      obtain ⟨_, _, rfl⟩ := mem_trs_to_trans mem
      simp [Transition.toRewrite] at hr
  case child j _ =>
    injection hr with hr hr'
    subst hr hr'
    grind [Args.set]

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

theorem rev_step_subrelation_ELT : Subrelation (· ←[auto]- ·) Term.ELT := by
  intro t₁ t₂ s
  -- TODO: You should maybe have a custom cases eliminator for steps on tree automata, as we often
  --       immediately want to access the underlying transition of the rewrite rule in the `subst`
  --       case, and use the fact that `fn : S` in the `child` case.
  induction s
  case subst mem =>
    have ⟨_, _, h⟩ := mem_trs_to_trans mem
    simp [← h, Transition.toRewrite, Subst.apply_no_vars, Term.ELT, Term.esize]
  case child aᵢ fn as i s ih =>
    cases fn
    case ext => exact i.elim0
    case sig =>
      simp only [Term.ELT, Term.esize, Args.set, add_lt_add_iff_left] at ih ⊢
      apply Finset.sum_lt_sum <;> grind

theorem trs_terminating : auto.trs.Terminating :=
  rev_step_subrelation_ELT.wf Term.ELT.wf

theorem state_isNF (q : Q) : auto.trs.IsNF q := by
  intro t h
  generalize hl : (q : Term <| S ⨄ Q) = lhs at h
  cases h
  case subst mem =>
    have ⟨_, _, ht⟩ := mem_trs_to_trans mem
    simp_all [Transition.toRewrite, ← ht]
  case child i _ =>
    injections; subst_vars
    exact i.elim0

end

def Accepts (auto : TreeAutomaton S Q) (q : Q) (t : Term S) : Prop :=
  t -[auto]→* q

namespace Accepts

variable {auto : TreeAutomaton S Q}

-- If a state `q` accepts a term `fn ° as`, then the final step of that acceptance must have been
-- based on a transition `⟨fn, qs, q⟩ ∈ auto.trans` where `qs` are states which accept `as`.
theorem final (acc : Accepts auto q <| fn ° as) :
    ∃ qs : Args fn Q, ⟨fn, qs, q⟩ ∈ auto.trans ∧ ↑(fn ° as) -[auto]→* fn ° (qs ·) := by
  cases acc
  case tail lhs has h =>
    generalize hr : (q : Term <| S ⨄ Q) = rhs at h
    cases h
    case subst mem =>
      obtain ⟨t, ht, rfl⟩ := mem_trs_to_trans mem
      simp only [Transition.toRewrite, Subst.apply_no_vars] at *
      obtain ⟨rfl⟩ := steps_preserve_fn has
      exists t.srcs
      simp_all
    case child fn' _ _ _ =>
      cases fn'
      case sig =>
        obtain ⟨rfl⟩ := steps_preserve_fn has
        simp at hr
      case ext i _ =>
        exact i.elim0

theorem child (acc : Accepts auto q <| fn ° as) (i) : ∃ qᵢ : Q, as i -[auto]→* qᵢ :=
  have ⟨_, _, h⟩ := acc.final
  ⟨_, steps_child h i⟩

end Accepts

def Deterministic (auto : TreeAutomaton S Q) : Prop :=
  ∀ {t : Term S} {q₁ q₂ : Q}, (Accepts auto q₁ t) → (Accepts auto q₂ t) → q₁ = q₂

def Reachable (auto : TreeAutomaton S Q) : Prop :=
  ∀ q : Q, ∃ t : Term S, Accepts auto q t

structure Hom (auto₁ : TreeAutomaton S Q₁) (auto₂ : TreeAutomaton S Q₂) where
  hom   : Q₁ → Q₂
  final : ∀ q ∈ auto₁.final, hom q ∈ auto₂.final
  trans : ∀ t ∈ auto₁.trans, t.map hom ∈ auto₂.trans

variable {auto : TreeAutomaton S Q} {auto₁ : TreeAutomaton S Q₁} {auto₂ : TreeAutomaton S Q₂}

instance : CoeFun (Hom auto₁ auto₂) (fun _ => Q₁ → Q₂) where
  coe := Hom.hom

/- **Lemma 2** -/
theorem Accepts.hom (acc : Accepts auto₁ q t) (hom : Hom auto₁ auto₂) :
    Accepts auto₂ (hom q) t := by
  induction t generalizing q
  case app ih =>
    have ⟨_, t₁, h⟩ := acc.final
    apply TRS.Steps.tail ?_ <| step_of_transition (hom.trans _ t₁)
    exact TRS.Steps.children (ih · <| steps_child h _)

-- Terms t₁ and t₂ are in a bistep relation with respect to t if both t₁ and t₂ can be reached from
-- t with the same kind of single step (`subst` or `child`). We prove below that for any two steps
-- t → t₁ and t → t₂, the respective terms are in a bistep relation.
inductive Bistep (auto : TreeAutomaton S Q) : Term (S ⨄ Q) → Term (S ⨄ Q) → Term (S ⨄ Q) → Prop
  | subst (mem₁ : ⟨lhs, rhs₁, sub₁⟩ ∈ auto.trs) (mem₂ : ⟨lhs, rhs₂, sub₂⟩ ∈ auto.trs) :
    Bistep auto lhs rhs₁ rhs₂
  | child {as : Args fn <| Term (S ⨄ Q)} (step₁ : as i₁ -[auto]→ a₁) (step₁ : as i₂ -[auto]→ a₂) :
    Bistep auto (fn ° as) (fn ° as[i₁ := a₁]) (fn ° as[i₂ := a₂])

-- TODO: Turn `Bistep.of_steps` into a `cases_eliminator`.

-- It can't be that a step t → t₁ applies a rewrite rule directly, while another step t → t₂
-- rewrites a subterm, as a rewrite rule can only apply when all of t's children are state
-- variables, and state variables cannot themselves be rewritten, thus making t → t₂ impossible.
theorem Bistep.of_steps (s₁ : t -[auto]→ t₁) (s₂ : t -[auto]→ t₂) : Bistep auto t t₁ t₂ := by
  cases s₁ <;> simp only [Subst.apply_no_vars] at *
  case' subst rw₁ _ mem₁ =>
    generalize hl : rw₁.lhs = lhs at s₂ ⊢
    cases s₂
    -- Case 1: Both are `subst`s.
    case subst => grind [cases Rewrite, Bistep.subst]
    -- Case 2: Both are different: contradiction.
    case' child s₂ =>
      have ⟨_, _, hi⟩ := step_lhs_is_proper_app s₂
      have ⟨_, _, htr⟩ := mem_trs_to_trans mem₁
      injection htr ▸ hl with hl₁ hl₂
      subst hl₁
      have := eq_of_heq hl₂ ▸ hi
      injections
  case child fn₁ as₁ _ s₁ =>
    generalize hl : fn₁ ° as₁ = lhs at s₂
    cases s₂
    -- Case 3: Both are `child`s.
    case child s₂ =>
      injection hl with h₁ h₂
      subst h₁ h₂
      exact .child s₁ s₂
    -- Case 4: Both are different: contradiction.
    case subst mem₂ =>
      have ⟨_, _, hi⟩ := step_lhs_is_proper_app s₁
      have ⟨_, _, htr⟩ := mem_trs_to_trans mem₂
      injection htr ▸ hl with hl₁ hl₂
      subst hl₁
      have := eq_of_heq hl₂ ▸ hi
      injections
