import Mathlib.Logic.Relation
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
  have s := TRS.Step.subst (V := Empty) nofun mem
  simp only [Subst.apply_no_vars] at s
  exact s

abbrev Steps (θ : TRS S V) :=
  Relation.ReflTransGen (· -[θ]→ ·)

notation t₁ " -[" θ "]→* " t₂ => Steps θ t₁ t₂

-- TODO: Perhaps the reducing measure is the index.
theorem Steps.children {θ : TRS S V} {as bs} (h : ∀ i, as i -[θ]→* bs i) :
    fn ° as -[θ]→* fn ° bs := by
  cases h : Signature.arity fn
  case zero => sorry
  case succ =>
    if has : as ⟨0, by grind⟩ = bs ⟨0, by grind⟩ then
      sorry
    else
      have ⟨i, hi⟩ : ∃ i, as i ≠ bs i := sorry -- from has
      sorry
