
import data.stream

import unitb.scheduling
import unitb.logic

import util.data.bijection
import util.data.finite
import util.data.countable

namespace det

open predicate

structure program (lbl : Type) (α : Type) : Type :=
  (first : α)
  (step : lbl → α → α)

@[reducible]
def pred (α : Sort*) := pred' α

variables {lbl α : Type}

def program.init (s : program lbl α) (p : pred α) : Prop :=
(s^.first) ⊨ p

def program.take_step (s : program lbl α) : option lbl → α → α
  | none := id
  | (some e) := s^.step e

def program.action_of (s : program lbl α) (e : option lbl) (σ σ' : α) : Prop :=
σ' = s^.take_step e σ

def is_step (s : program lbl α) (σ σ' : α) : Prop :=
∃ ev, s.action_of ev σ σ'

def program.falsify (s : program lbl α) (ev : option lbl) (p q : pred α) : Prop :=
∀ σ, σ ⊨ q → (s^.take_step ev σ) ⊨ - q

def program.transient (s : program lbl α) (p q : pred α) : Prop :=
∃ ev, s.falsify ev p q

def program.falsify_action (s : program lbl α) (p q : pred α) (ev : option lbl)
  (h : s.falsify ev p q)
: •q ⟹ ( ⟦ s.action_of ev ⟧ ⟶ ⊙ - •q ) :=
begin [temporal]
  action {
    intros Hq H₁,
    unfold program.action_of at H₁,
    rw H₁,
    apply (h _ Hq) },
end

lemma program.falsify.negate
   {s : program lbl α} {act : option lbl} {p q : pred' α}
   (H : s.falsify act p q)
:  •q ⋀ ⟦ s^.action_of act ⟧ ⟹ ◇-•q :=
begin [temporal]
  intros H',
  strengthen_to ⊙-• _ ,
  exact program.falsify_action s p q act H Γ H'.left H'.right,
end

lemma program.transient_impl (s : program lbl α) (p : pred' α)
: s.transient p False :=
begin
  unfold program.transient False,
  existsi @none lbl,
  intros σ h,
  cases h
end

lemma program.transient_antimono (s : program lbl α) {p q p' q' : pred α}
  (hp : p' ⟹ p)
  (hq : q' ⟹ q)
  (T₀ : s.transient p q)
: s.transient p' q' :=
begin
  unfold program.transient,
  cases T₀ with ev T₁,
  existsi ev,
  intros σ,
  imp_transitivity [σ ⊨ q,program.take_step s ev σ ⊨ -q], simp,
  intros_mono, apply ew_str hq,
  apply T₁, apply ew_str hq,
end

instance prog_is_system : unitb.system (program lbl α) :=
  { σ := α
  , init := program.init
  , step := is_step
  , transient := program.transient
  , transient_false := λ s p, program.transient_impl s _
  , transient_antimono := program.transient_antimono
  }

open temporal

structure ex (p : program lbl α) (τ : stream α) : Prop :=
    (init : τ 0 = p^.first)
    (safety : τ ⊨ unitb.saf_ex p)
    (liveness : ∀ e, τ ⊨ ◻ ◇ ⟦ p.action_of e ⟧)

open unitb
open nat

section soundness

variables (s : program lbl α)
variables (Γ : cpred α)
variables {p q : pred' α}
variables h : Γ ⊢ ex s

lemma safety : Γ ⊢ ex s ⟶ unitb.saf_ex s :=
by { apply p_imp_ext,
     introv _, apply ex.safety, }
lemma liveness : Γ ⊢ ex s ⟶ ∀∀ e, ◻ ◇ ⟦ s.action_of e ⟧ :=
by { apply p_imp_ext,
     introv _, apply ex.liveness, }

variables {s}
include h

lemma init_sem
  (I₀ : init s p)
: Γ ⊢ •p :=
begin [temporal]
  explicit τ {
    rw h.init,
    apply I₀ }
end

lemma transient.semantics
  (T₀ : s.transient p q)
: Γ ⊢ ◻◇•p ⟶ ◻◇-•q :=
begin [temporal]
  intro,
  simp [program.transient] at T₀,
  cases T₀ with ev T₀,
  assume_negation with hq ,
  simp [p_not_p_not_iff_self] at hq,
  have occ := coincidence hq (liveness s Γ h ev),
  clear h,
  henceforth at occ ⊢,
  eventually occ,
  apply T₀.negate Γ occ
end

end soundness

open scheduling scheduling.unitb

def object (p : program lbl α) : target_mch (option lbl) :=
{ σ := α
, s₀ := p.first
, next := λ l s P, p.take_step l s
, req := ↑λ _ : α, @set.univ (option lbl)
, req_nemp := by { intros _, rw [set.ne_empty_iff_exists_mem], existsi none, trivial, } }

lemma program.witness [sched lbl] (s : program lbl α)
: ∃ (τ : stream (state (program lbl α))), ex s τ :=
begin
  apply exists_imp_exists _ (sched.sched_str (object s)),
  intros τ h,
  have H : ∀ e, •(↑e ∊ (object s).req) ⋀ ⟦target_mch.action (object s) e⟧
              ⟹ ⟦s.action_of e⟧,
  { simp [init_eq_action,action_and_action],
    intro e,
    apply action_entails_action,
    intros σ σ',
    unfold target_mch.action,
    rw [exists_and,exists_imp_iff_forall_imp],
    intro, apply and.left },
  apply ex.mk,
  { rw h.init, refl },
  replace h := h.valid,
  begin [temporal]
    simp [saf_ex],
    henceforth at h ⊢,
    cases h with l h,
    have := (H l Γ h),
    revert this,
    action {
      simp [unitb.step,has_safety.step,is_step],
      intro h, exact ⟨_,h⟩ },
  end,
  intro e, have H' := h.fair e,
  begin [temporal]
    note H'' : •(↑e ∊ (object s).req) = True,
    { simp [temporal.init], congr, },
    simp [H''] at H',
    revert H', monotonicity,
    intros H', apply H e Γ _,
    simp [H''], apply H',
  end
end

instance {α} [sched lbl] : system_sem (program lbl α) :=
  { (_ : system (program lbl α)) with
    ex := λ p, (↑(ex p) : cpred _)
  , safety := safety
  , inhabited := program.witness
  , init_sem := @init_sem _ _
  , transient_sem := @transient.semantics _ _  }

end det
