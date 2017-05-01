
import data.stream

import unity.scheduling
import unity.logic

import util.data.bijection
import util.data.finite
import util.data.countable

namespace det

open predicate

structure prog (lbl : Type) (α : Type) : Type :=
  (first : α)
  (step : lbl → α → α)

@[reducible]
def pred α := α → Prop

variables {lbl α : Type}

def prog.init (s : prog lbl α) (p : pred α) : Prop
:= p (s^.first)

def prog.take_step (s : prog lbl α) : option lbl → α → α
  | none := id
  | (some e) := s^.step e

def prog.action_of (s : prog lbl α) (e : option lbl) (σ σ' : α) : Prop :=
s^.take_step e σ = σ'

def is_step (s : prog lbl α) (σ σ' : α) : Prop :=
∃ ev, prog.action_of s ev σ σ'

def prog.falsify (s : prog lbl α) (ev : option lbl) (p : pred α) : Prop
:= ∀ σ, p σ → ¬ (p (s^.take_step ev σ))

def prog.transient (s : prog lbl α) (p : pred α) : Prop
:= ∃ ev, prog.falsify s ev p

def prog.falsify_action (s : prog lbl α) (p : pred α) (ev : option lbl)
  (h : s.falsify ev p)
: •p ⟹ ( ⟦ prog.action_of s ev ⟧ ⟶ ⟦ λ _, - p ⟧ ) :=
begin
  unfold prog.transient at h,
  intros τ H₀ H₁,
  unfold temporal.action prog.action_of at H₁,
  unfold temporal.action,
  rw -H₁,
  apply h,
  apply H₀
end

lemma prog.falsify.negate
   {s : prog lbl α} {act : option lbl} {p : pred' α}
:  prog.falsify s act p
→  •p && ⟦ s^.action_of act ⟧ ⟹ <>-•p :=
begin
  intros FALSE τ H,
  assert GOAL : ⟦ λ _, - p ⟧ τ,
  { cases H with H₀ H₁,
    apply prog.falsify_action s p act FALSE
    ; assumption },
  unfold temporal.eventually,
  existsi 1,
  apply GOAL
end

lemma prog.transient_false (s : prog lbl α) : prog.transient s False :=
begin
  unfold prog.transient False,
  existsi @none lbl,
  intros σ h,
  cases h
end

lemma prog.transient_str (s : prog lbl α) (p q : α → Prop)
  (h : ∀ (i : α), p i → q i)
  (T₀ : prog.transient s q)
: prog.transient s p :=
begin
  unfold prog.transient,
  cases T₀ with ev T₁,
  existsi ev,
  intros σ h',
  note h'' := T₁ σ (h _ h'),
  intro h₂, apply h'',
  apply h _ h₂
end

instance prog_is_system : unity.system (prog lbl α) :=
  { σ := α
  , init := prog.init
  , step := is_step
  , transient := prog.transient
  , transient_false := prog.transient_false
  , transient_str := prog.transient_str
  }

open temporal

structure ex (p : prog lbl α) (τ : stream α) : Prop :=
    (init : τ 0 = p^.first)
    (safety : unity.saf_ex p τ)
    (liveness : ∀ e, ([] <> ⟦ p.action_of e ⟧) τ)

open unity
open nat

def run (s : prog lbl α) (τ : stream (option lbl)) : stream α
  | 0 := prog.first s
  | (succ n) := prog.take_step s (τ n) (run n)


section soundness

variables {s : prog lbl α} {p : pred' α}
variables (T₀ : prog.transient s p)
include T₀
variables (τ : stream α)

lemma transient.semantics (h : ex s τ)
: ([]<>-•p) τ :=
begin
  unfold prog.transient at T₀,
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

lemma prog.witness [sched lbl] (s : prog lbl α) : ∃ (τ : stream (state (prog lbl α))), ex s τ :=
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
    ; unfold prog.take_step step has_safety.step is_step,
    { existsi @none lbl, apply rfl },
    { existsi (some e), apply rfl } },
  { apply forall_imp_forall _ h,
    intros e Heq i,
    cases (Heq i) with j Heq,
    rw [stream.drop_drop,init_drop] at Heq,
    unfold eventually, existsi j,
    rw [stream.drop_drop,action_drop,Heq],
    unfold prog.action_of,
    refl },
end

instance {α} [sched lbl] : system_sem (prog lbl α) :=
  { (_ : system (prog lbl α)) with
    ex := λ p τ, ex p τ
  , safety := @ex.safety _ _
  , inhabited := prog.witness
  , transient_sem := @transient.semantics _ _ }

end det
