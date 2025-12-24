import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic
import Eqsat.Term

def Subst (S V : Type _) [Signature S] :=
  V → Term S

def Subst.apply {S V} [Signature S] (σ : Subst S V) : Pattern S V → Term S
  | (v : V)   => σ v
  | fn ° args => fn ° (apply σ <| args ·)

@[simp]
instance [Signature S] : GetElem (Pattern S V) (Subst S V) (Term S) (fun _ _ => True) where
  getElem p σ _ := σ.apply p

@[simp]
theorem Subst.apply_no_vars [Signature S] (σ : Subst S Empty) (p : Pattern S Empty) : p[σ] = p := by
  induction p
  case var => contradiction
  case app => simp_all [apply]

structure Rewrite (S V : Type _) [Signature S] where
  lhs : Pattern S V
  rhs : Pattern S V
  sub : rhs.vars ⊆ lhs.vars := by simp

abbrev TRS (S V : Type _) [Signature S] :=
  Set (Rewrite S V)

namespace TRS

variable {S V} [Signature S]

inductive Step (θ : TRS S V) : Term S → Term S → Prop where
  | subst (σ : Subst S V) (mem : rw ∈ θ) : Step θ rw.lhs[σ] rw.rhs[σ]
  | child (fn : S) (as : Term.Args fn) {i} (step : Step θ (as i) a) : Step θ (fn ° as) (fn ° as[i := a])

notation t₁ " -[" θ "]→ " t₂ => TRS.Step θ t₁ t₂

theorem Step.subst' {θ : TRS S Empty} (mem : rw ∈ θ) : rw.lhs -[θ]→ rw.rhs := by
  have s := Step.subst nofun mem
  simp only [Subst.apply_no_vars] at s
  exact s

-- A step leading to a term `.ext fn₂` (this could be generalized to any application of arity 0)
-- must be a `Step.subst`. Note, we also assume `V := Empty` here, which could be generalized.
theorem Step.rw_of_ext {fn₁ : S ⨄ E} {as} {fn₂ : E} (h : fn₁ ° as -[θ]→ fn₂) :
    ∃ sub, ⟨fn₁ ° as, fn₂, sub⟩ ∈ θ := by
  generalize fn₁ ° as = lhs at h
  generalize hr : (fn₂ : Term <| S ⨄ E) = rhs at h
  cases h
  case subst rw _ _ => simp_all [rw.sub]
  case child i _    => exact Pattern.app.inj hr |>.left ▸ i |>.elim0

abbrev Steps (θ : TRS S V) :=
  Relation.ReflTransGen (· -[θ]→ ·)

namespace Steps

notation t₁ " -[" θ "]→* " t₂ => Steps θ t₁ t₂

theorem refl {θ : TRS S V} : t -[θ]→* t :=
  Relation.ReflTransGen.refl

theorem tail {θ : TRS S V} (head : t₁ -[θ]→* t₂) (tail : t₂ -[θ]→ t₃) : t₁ -[θ]→* t₃ :=
  Relation.ReflTransGen.tail head tail

theorem trans {θ : TRS S V} (head : t₁ -[θ]→* t₂) (tail : t₂ -[θ]→* t₃) : t₁ -[θ]→* t₃ :=
  Relation.ReflTransGen.trans head tail

theorem child {θ : TRS S V} {as} {i : Fin <| Signature.arity fn} (h : as i -[θ]→* b) :
    fn ° as -[θ]→* fn ° as[i := b] := by
  induction h
  case refl => simp [Steps.refl]
  case tail z b _ h ih =>
    have hz : z = as[i := z] i := by simp
    have hb : b = as[i := b] i := by simp
    rw [hb, hz] at h
    have s := Step.child _ _ h
    have : as[i := z][i := b] = as[i := b] := by grind [Args.set]
    grind [.tail]

-- Auxiliary definitions for the proof of `TRS.Steps.children` below.
section Auxiliary

private def ArgSubst (S) [Signature S] (n : Nat) :=
  Fin n → Term S

namespace ArgSubst

private def drop (σ : ArgSubst S <| n + 1) : ArgSubst S n :=
  fun i => σ ⟨i, by simp +arith⟩

private def apply {fn : S} (σ : ArgSubst S n) (as : Term.Args fn) : Term.Args fn :=
  fun i => if h : i < n then σ ⟨i, h⟩ else as i

private theorem apply_all (σ : ArgSubst S <| Signature.arity fn) (as) : σ.apply as = σ :=
  funext <| by simp [apply]

private theorem drop_apply_set {fn : S} (σ : ArgSubst S <| n + 1) (as : Term.Args fn) :
    (σ.drop.apply as)[n := σ ⟨n, Nat.lt_add_one _⟩] = σ.apply as := by
  grind [apply, drop, Args.set]

private theorem drop_apply_get (n : Fin _) (σ : ArgSubst S <| n + 1) (as : Term.Args fn) :
    (σ.drop.apply as) n = as n := by
  simp [apply]

end ArgSubst

private theorem children' {θ : TRS S V} {as} (σ : ArgSubst S n) (hn : n ≤ Signature.arity fn)
    (h : ∀ i : Fin n, as ⟨i, by grind⟩ -[θ]→* σ i) : fn ° as -[θ]→* fn ° (σ.apply as) := by
  induction n
  case zero => exact .refl
  case succ m ih =>
    apply Steps.trans <| ih σ.drop (by grind) (h ⟨·, by grind⟩)
    rw [← ArgSubst.drop_apply_set]
    exact child <| ArgSubst.drop_apply_get ⟨m, by grind⟩ σ as ▸ h ⟨m, by simp⟩

end Auxiliary

theorem children {θ : TRS S V} {as bs} (h : ∀ i, as i -[θ]→* bs i) : fn ° as -[θ]→* fn ° bs :=
  ArgSubst.apply_all bs as ▸ children' bs (Nat.le_refl _) (h ⟨·, by grind⟩)

end TRS.Steps
