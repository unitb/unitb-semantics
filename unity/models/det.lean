
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
∃ ev, program.action_of s ev σ σ'

def program.falsify (s : program lbl α) (ev : option lbl) (p : pred α) : Prop
:= ∀ σ, p σ → ¬ (p (s^.take_step ev σ))

def program.transient (s : program lbl α) (p : pred α) : Prop
:= ∃ ev, program.falsify s ev p

def program.falsify_action (s : program lbl α) (p : pred α) (ev : option lbl)
  (h : s.falsify ev p)
: •p ⟹ ( ⟦ program.action_of s ev ⟧ ⟶ ⟦ λ _, - p ⟧ ) :=
begin
  unfold program.transient at h,
  intros τ H₀ H₁,
  unfold temporal.action program.action_of at H₁,
  unfold temporal.action,
  rw -H₁,
  apply h,
  apply H₀
end

lemma program.falsify.negate
   {s : program lbl α} {act : option lbl} {p : pred' α}
:  program.falsify s act p
→  •p && ⟦ s^.action_of act ⟧ ⟹ <>-•p :=
begin
  intros FALSE τ H,
  assert GOAL : ⟦ λ _, - p ⟧ τ,
  { cases H with H₀ H₁,
    apply program.falsify_action s p act FALSE
    ; assumption },
  unfold temporal.eventually,
  existsi 1,
  apply GOAL
end

lemma program.transient_false (s : program lbl α) : program.transient s False :=
begin
  unfold program.transient False,
  existsi @none lbl,
  intros σ h,
  cases h
end

lemma program.transient_str (s : program lbl α) (p q : α → Prop)
  (h : ∀ (i : α), p i → q i)
  (T₀ : program.transient s q)
: program.transient s p :=
begin
  unfold program.transient,
  cases T₀ with ev T₁,
  existsi ev,
  intros σ h',
  note h'' := T₁ σ (h _ h'),
  intro h₂, apply h'',
  apply h _ h₂
end

instance prog_is_system : unity.system (program lbl α) :=
  { σ := α
  , init := program.init
  , step := is_step
  , transient := program.transient
  , transient_false := program.transient_false
  , transient_str := program.transient_str
  }

open temporal

structure ex (p : program lbl α) (τ : stream α) : Prop :=
    (init : τ 0 = p^.first)
    (safety : unity.saf_ex p τ)
    (liveness : ∀ e, ([] <> ⟦ p.action_of e ⟧) τ)

open unity
open nat

def run (s : program lbl α) (τ : stream (option lbl)) : stream α
  | 0 := program.first s
  | (succ n) := program.take_step s (τ n) (run n)


section soundness

variables {s : program lbl α} {p : pred' α}
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
  (T₀ : program.transient s p)
: ([]<>-•p) τ :=
begin
  unfold program.transient at T₀,
  cases T₀ with ev T₀,
  cases temporal.em' (• p) τ with hp hnp,
  { note occ := coincidence hp (h.liveness ev),
    rw -eventually_eventually,
    apply henceforth_entails_henceforth _ _ occ,
    apply eventually_entails_eventually,
    apply T₀.negate },
  { apply hnp }
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
  , transient_sem := @transient.semantics _ _ }

end det
