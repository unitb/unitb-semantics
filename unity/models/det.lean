
import data.stream

import unity.scheduling
import unity.logic

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

def program.init (s : program lbl α) (p : pred α) : Prop
:= p (s^.first)

def program.take_step (s : program lbl α) : option lbl → α → α
  | none := id
  | (some e) := s^.step e

def program.action_of (s : program lbl α) (e : option lbl) (σ σ' : α) : Prop :=
s^.take_step e σ = σ'

def is_step (s : program lbl α) (σ σ' : α) : Prop :=
∃ ev, s.action_of ev σ σ'

def program.falsify (s : program lbl α) (ev : option lbl) (p q : pred α) : Prop :=
∀ σ, q σ → ¬ (q (s^.take_step ev σ))

def program.transient (s : program lbl α) (p q : pred α) : Prop
:= ∃ ev, s.falsify ev p q

def program.falsify_action (s : program lbl α) (p q : pred α) (ev : option lbl)
  (h : s.falsify ev p q)
: •q ⟹ ( ⟦ s.action_of ev ⟧ ⟶ ⟦ λ _, - q ⟧ ) :=
begin
  unfold program.transient at h,
  intros τ Hq H₁,
  unfold temporal.action program.action_of at H₁,
  unfold temporal.action,
  rw -H₁,
  apply (h _ Hq),
end

lemma program.falsify.negate
   {s : program lbl α} {act : option lbl} {p q : pred' α}
:  s.falsify act p q
→  •q && ⟦ s^.action_of act ⟧ ⟹ <>-•q :=
begin
  intros FALSE τ H,
  assert GOAL : ⟦ λ _, - q ⟧ τ,
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
  apply contrapos (hq _),
end

instance prog_is_system : unity.system (program lbl α) :=
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
    (safety : unity.saf_ex p τ)
    (liveness : ∀ e, ([] <> ⟦ p.action_of e ⟧) τ)

open unity
open nat

def run (s : program lbl α) (τ : stream (option lbl)) : stream α
  | 0 := s.first
  | (succ n) := s.take_step (τ n) (run n)


section soundness

variables {s : program lbl α} {p q : pred' α}
variables (τ : stream α)
variables h : ex s τ
include h

lemma init_sem
  (I₀ : init s p)
: (•p) τ :=
begin
  unfold init system.init program.init at I₀,
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
  { note occ := coincidence hq (h.liveness ev),
    rw -eventually_eventually,
    apply henceforth_entails_henceforth _ _ occ,
    apply eventually_entails_eventually,
    apply T₀.negate },
  { apply hnq }
end

end soundness

open scheduling

lemma program.witness [sched lbl] (s : program lbl α)
: ∃ (τ : stream (state (program lbl α))), ex s τ :=
begin
  apply exists_imp_exists' (run s) _ (sched.sched' (option lbl)),
  intros τ h,
  apply ex.mk,
  { refl },
  { unfold saf_ex,
    intro i,
    simp [action_drop],
    unfold run,
    cases (τ i) with e
    ; unfold program.take_step step has_safety.step is_step,
    { existsi @none lbl, apply rfl },
    { existsi (some e), apply rfl } },
  { apply forall_imp_forall _ h,
    intros e Heq i,
    cases (Heq i) with j Heq,
    rw [stream.drop_drop,init_drop] at Heq,
    unfold eventually, existsi j,
    rw [stream.drop_drop,action_drop,Heq],
    unfold program.action_of,
    refl },
end

instance {α} [sched lbl] : system_sem (program lbl α) :=
  { (_ : system (program lbl α)) with
    ex := λ p τ, ex p τ
  , safety := @ex.safety _ _
  , inhabited := program.witness
  , init_sem := @init_sem _ _
  , transient_sem := @transient.semantics _ _  }

end det
