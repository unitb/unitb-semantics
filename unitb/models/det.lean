
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
def pred α := α → Prop

variables {lbl α : Type}

def program.init (s : program lbl α) (p : pred α) : Prop :=
p (s^.first)

def program.take_step (s : program lbl α) : option lbl → α → α
  | none := id
  | (some e) := s^.step e

def program.action_of (s : program lbl α) (e : option lbl) (σ σ' : α) : Prop :=
σ' = s^.take_step e σ

def is_step (s : program lbl α) (σ σ' : α) : Prop :=
∃ ev, s.action_of ev σ σ'

def program.falsify (s : program lbl α) (ev : option lbl) (p q : pred α) : Prop :=
∀ σ, q σ → ¬ (q (s^.take_step ev σ))

def program.transient (s : program lbl α) (p q : pred α) : Prop :=
∃ ev, s.falsify ev p q

def program.falsify_action (s : program lbl α) (p q : pred α) (ev : option lbl)
  (h : s.falsify ev p q)
: •q ⟹ ( ⟦ s.action_of ev ⟧ ⟶ ⟦ λ _, - q ⟧ ) :=
begin
  intros τ Hq H₁,
  unfold temporal.action program.action_of at H₁,
  unfold temporal.action,
  rw H₁,
  apply (h _ Hq),
end

lemma program.falsify.negate
   {s : program lbl α} {act : option lbl} {p q : pred' α}
:  s.falsify act p q
→  •q && ⟦ s^.action_of act ⟧ ⟹ <>-•q :=
begin
  intros FALSE τ H,
  have GOAL : ⟦ λ _, - q ⟧ τ,
  { cases H with H₀ H₁,
    apply s.falsify_action p q act FALSE _ H₀ H₁, },
  unfold temporal.eventually,
  existsi 1,
  apply GOAL
end

lemma program.transient_impl (s : program lbl α) (p : pred' α)
: s.transient p False :=
begin
  unfold program.transient False,
  existsi @none lbl,
  intros σ h,
  cases h
end

lemma program.transient_antimono (s : program lbl α) {p q p' q' : α → Prop}
  (hp : p' ⟹ p)
  (hq : q' ⟹ q)
  (T₀ : s.transient p q)
: s.transient p' q' :=
begin
  unfold program.transient,
  cases T₀ with ev T₁,
  existsi ev,
  intros σ,
  apply imp_mono (hq _) _ (T₁ σ),
  apply mt (hq _),
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
    (safety : unitb.saf_ex p τ)
    (liveness : ∀ e, ([] <> ⟦ p.action_of e ⟧) τ)

open unitb
open nat

section soundness

variables {s : program lbl α} {p q : pred' α}
variables (τ : stream α)
variables h : ex s τ
include h

lemma init_sem
  (I₀ : init s p)
: (•p) τ :=
begin
  unfold temporal.init,
  rw h.init,
  apply I₀
end

lemma transient.semantics
  (T₀ : s.transient p q)
: ([]<>•p) τ → ([]<>-•q) τ :=
begin
  intro,
  unfold program.transient at T₀,
  cases T₀ with ev T₀,
  cases temporal.em' (• q) τ with hq hnq,
  { have occ := coincidence hq (h.liveness ev),
    rw ← eventually_eventually,
    apply henceforth_entails_henceforth _ _ occ,
    apply eventually_entails_eventually,
    apply T₀.negate },
  { apply hnq }
end

end soundness

open scheduling scheduling.unitb

def object (p : program lbl α) : target_mch (option lbl) :=
{ σ := α
, s₀ := p.first
, next := λ l s P, p.take_step l s
, req := λ _, set.univ
, req_nemp := λ _, @set.ne_empty_of_mem _ set.univ none trivial }

lemma program.witness [sched lbl] (s : program lbl α)
: ∃ (τ : stream (state (program lbl α))), ex s τ :=
begin
  apply exists_imp_exists _ (sched.sched_str (object s)),
  intros τ h,
  have H : ∀ e, •has_mem.mem e ∘ (object s).req && ⟦target_mch.action (object s) e⟧
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
  { unfold saf_ex,
    apply henceforth_entails_henceforth _ _ h.valid,
    rw p_exists_entails_eq_p_forall_entails,
    intro l,
    apply entails_trans _ (H _),
    revert l,
    rw [← p_exists_entails_eq_p_forall_entails,exists_action], refl },
  { intro e,
    apply inf_often_entails_inf_often _ _ (h.fair e _),
    { apply H },
    { have H : has_mem.mem e ∘ (object s).req = True,
      { refl },
      rw [H,init_true,event_true,hence_true],
      apply trivial } },
end

instance {α} [sched lbl] : system_sem (program lbl α) :=
  { (_ : system (program lbl α)) with
    ex := λ p τ, ex p τ
  , safety := @ex.safety _ _
  , inhabited := program.witness
  , init_sem := @init_sem _ _
  , transient_sem := @transient.semantics _ _  }

end det
