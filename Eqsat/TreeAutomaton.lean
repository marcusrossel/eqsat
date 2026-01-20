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
notation t₁ " -[" auto "]→* " t₂ => t₁ -[TreeAutomaton.trs auto]→* t₂

variable {auto : TreeAutomaton S Q} {fn₁ : S ⨄ Q} {fn₂ : S} in section

theorem trans_to_mem_trs (h : t ∈ auto.trans) : t.toRewrite ∈ auto.trs :=
  Set.mem_image Transition.toRewrite _ _ |>.mpr ⟨_, h, rfl⟩

theorem mem_trs_to_trans (h : rw ∈ auto.trs) : ∃ t ∈ auto.trans, t.toRewrite = rw :=
  Set.mem_image _ _ _ |>.mp h

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

namespace Deterministic

variable {auto : TreeAutomaton S Q}

-- Terms t, t₁ and t₂ are in a bistep relation if it is possible that t → t₁ and t → t₂ in a
-- deterministic automaton. This is only the case if both are substitutions or both rewrite a child
-- term of t. We prove below that any two steps in a deterministic tree automaton are bisteps.
inductive Bistep (auto : TreeAutomaton S Q) : Term (S ⨄ Q) → Term (S ⨄ Q) → Term (S ⨄ Q) → Prop
  | subst (mem₁ : ⟨lhs, rhs₁, sub₁⟩ ∈ auto.trs) (mem₂ : ⟨lhs, rhs₂, sub₂⟩ ∈ auto.trs) :
    Bistep auto lhs rhs₁ rhs₂
  | child {as : Args fn <| Term (S ⨄ Q)} (step₁ : as i₁ -[auto]→ a₁) (step₁ : as i₂ -[auto]→ a₂) :
    Bistep auto (fn ° as) (fn ° as[i₁ := a₁]) (fn ° as[i₂ := a₂])

-- It can't be that t → t₁ applies a rewrite rule while t → t₂ rewrites a subterm, as a rewrite rule
-- can only apply when all of t's children are state variables, and state variables cannot
-- themselves be rewritten, thus making t → t₂ impossible.
theorem bistep (s₁ : t -[auto]→ t₁) (s₂ : t -[auto]→ t₂) (det : auto.Deterministic) :
    Bistep auto t t₁ t₂ :=
  sorry

-- Note: This theorem is immediately for applicable to any `Bistep.subst`.
theorem rw_lhs_unique
    (mem₁ : ⟨lhs, rhs₁, sub₁⟩ ∈ auto.trs) (mem₂ : ⟨lhs, rhs₂, sub₂⟩ ∈ auto.trs)
    (det : auto.Deterministic) : rhs₁ = rhs₂ :=
  sorry

-- Intuition: If we take single steps t → t₁ and t → t₂, we can always join t₁ and t₂ my mimicking
--            the step of the other side respectively.
theorem trs_semiConfluent (det : auto.Deterministic) : auto.trs.SemiConfluent := by
  intro t t₁ t₂ s₁ s₂
  cases bistep s₁ s₂ det
  -- If both steps directly apply a rewrite, then by determinism (by `rw_lhs_unique`) the rewrite
  -- must have been the same one, so we have t₁ = t₂ and choose t₃ to be the same.
  case subst _ mem₁ _ mem₂ => exact ⟨t₁, by simp [det.rw_lhs_unique mem₁ mem₂]⟩
  -- If both steps rewrite a child, there are two possible cases.
  case child fn i₁ a₁ i₂ a₂ as h₁ h₂ =>
    -- Case 1: Both steps rewrite the same child. In that case, by induction, those child terms are
    --         joinable, so t₁ and t₂ are joinable.
    if hi : i₁ = i₂ then
      subst hi
      have ⟨_, ha₁, ha₂⟩ := det.trs_semiConfluent h₁ h₂
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

theorem trs_confluent (det : auto.Deterministic) : auto.trs.Confluent :=
  TRS.SemiConfluent.confluent det.trs_semiConfluent

-- TODO: This might be a bit pointless as the definition of `TreeAutomaton.Determinism` is already
--       about the TRS.
--
-- *Counterexample*
--
-- Function symbols: `true` (arity 0), `false` (arity 2)
-- State Variables: `unit`
-- Automaton:
--
--  [true]→ (unit) ==[false]
--             ↑__________/
--
-- Induced TRS contains: false(true, unit) ← false(true, true) → false(unit, true)
theorem trs_not_deterministic : ∃ (S Q : Type) (_ : Signature S) (auto : TreeAutomaton S Q),
    auto.Deterministic ∧ ¬auto.trs.Deterministic := by
  let sig  : Signature Bool                     := { arity | true => 0 | false => 2 }
  let tr   : TreeAutomaton.Transition Bool Unit := ⟨true, nofun, .unit⟩
  let auto : TreeAutomaton Bool Unit            := { trans := { tr }, final := ∅ }
  let t    : Term (Bool ⨄ Unit)                 := true ° nofun
  let u    : Term (Bool ⨄ Unit)                 := Unit.unit
  let tu   : Term.Args (false : Bool ⨄ Unit)    := fun | ⟨0, _⟩ => t | ⟨1, _⟩ => u
  let ut   : Term.Args (false : Bool ⨄ Unit)    := fun | ⟨0, _⟩ => u | ⟨1, _⟩ => t
  let tt   : Term.Args (false : Bool ⨄ Unit)    := fun | ⟨0, _⟩ => t | ⟨1, _⟩ => t
  simp only [TRS.Deterministic, not_forall]
  have mem : tr.toRewrite ∈ auto.trs := trans_to_mem_trs rfl
  replace mem : { lhs := true ° nofun, rhs := Unit.unit } ∈ auto.trs := by
    simp only [Transition.toRewrite, tr] at mem
    simp [Signature.arity, sig] at *
    sorry -- `exact mem` -- TODO: What is this nested application in the LHS?
  refine ⟨Bool, Unit, sig, auto, by simp [Deterministic], false ° tt, false ° tu, false ° ut, ?_, ?_, ?_⟩
  · have s := TRS.Step.child (fn := (false : Bool ⨄ Unit)) (as := tt) (i := ⟨1, sorry⟩) <| TRS.Step.subst' mem
    have : tu = tt[1 := u] := sorry
    exact this ▸ s
  · have s := TRS.Step.child (fn := (false : Bool ⨄ Unit)) (as := tt) (i := ⟨0, sorry⟩) <| TRS.Step.subst' mem
    have : ut = tt[0 := u] := sorry
    exact this ▸ s
  · intro h
    injection h with _ h
    have : tu ⟨0, sorry⟩ = ut ⟨0, sorry⟩ := by rw [h]
    simp +zetaDelta at this

end Deterministic

variable {auto₁ : TreeAutomaton S Q₁} {auto₂ : TreeAutomaton S Q₂}

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
