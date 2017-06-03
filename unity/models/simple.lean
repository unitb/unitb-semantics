
import data.stream

import unity.logic

import util.logic

namespace simple

open unity
open predicate

structure program (α : Type) : Type :=
  (first : α)
  (step : α → α)

def pred α := α → Prop

def False {α} : pred α := λ_, false

def program.init {α} (s : program α) (p : pred α) : Prop
:= p (s^.first)

def program.transient {α} (s : program α) (p q : pred α) : Prop
:= ∀ σ, p σ → q σ → ¬ (q (s^.step σ))

def program.unless {α} (s : program α) (p q : pred α) : Prop
:= ∀ σ, p σ ∧ ¬q σ → p (s^.step σ) ∨ q (s^.step σ)

lemma program.transient_impl {α} (s : program α) {p q : α → Prop}
  (H : p ⟹ -q)
: s.transient p q :=
begin
  unfold program.transient,
  intros σ hp hq,
  cases H _ hp hq,
end

lemma program.transient_antimono {α} (s : program α) (p q p' q' : α → Prop)
  (hp : p' ⟹ p)
  (hq : q' ⟹ q)
  (T₀ : s.transient p q)
: s.transient p' q' :=
begin
  unfold program.transient,
  intros σ hp' hq',
  note h'' := T₀ σ (hp _ hp') (hq _ hq'),
  intro h₂, apply h'',
  apply hq _ h₂
end

def is_step {α} (s : program α) (σ σ' : α) : Prop := σ' = s.step σ

instance prog_is_system {α} : system (program α) :=
  { σ := α
  , step := is_step
  , init := program.init
  , transient := program.transient
  , transient_false := λ s p, program.transient_impl s (by simp)
  , transient_antimono := program.transient_antimono
  }

lemma unless_step {α : Type}
  {init : α}
  {step : α → α}
  {p q : α → Prop}
  (h : ∀ σ, p σ → ¬ q σ → p (step σ) ∨ q (step σ))
: unless (program.mk init step) p q :=
begin
  unfold unless,
  intros σ σ' S,
  note h' := h σ, clear h,
  unfold unity.step has_safety.step is_step program.step at S,
  rw S,
  intros h,
  cases h,
  apply h' ; assumption,
end

lemma leads_to_step {α : Type}
  (init : α)
  (step : α → α)
  (p q : α → Prop)
  (h : ∀ σ, p σ → ¬ q σ → q (step σ))
: p ↦ q in program.mk init step :=
begin
  apply leads_to.basis,
  { unfold transient system.transient program.transient program.step,
    intros σ _ h,
    cases h with h₀ h₁,
    note h' := h _ h₀ h₁,
    simp [not_and_iff_not_or_not,not_not_iff_self],
    left, apply h', },
  { apply unless_step,
    intros σ hp hnq,
    right, apply h _ hp hnq, }
end

open nat

open temporal

def ex {α} (s : program α) : cpred α :=
•eq s.first && [] ⟦ is_step s ⟧

lemma ex.safety {α} {s : program α} (τ : stream α)
  (h : ex s τ)
: [] ⟦ is_step s ⟧ $ τ :=
h.right

def ex.witness {α} (s : program α) : stream α
  | 0 := s.first
  | (succ i) := s.step (ex.witness i)

lemma ex.witness_correct  {α} (s : program α)
: ex s (ex.witness s) :=
begin
  unfold ex, simp,
  split,
  { intro i,
    rw action_drop,
    unfold is_step,
    refl },
  { unfold temporal.init,
    refl }
end

section semantics

universe variable u

parameter {α : Type}
variable {s : program α}
variables {p q : pred α}
variable τ : stream α
variable (H : ex s τ)
open temporal

include H

lemma init_sem
  (I₀ : init s p)
: (•p) τ :=
begin
  unfold init system.init program.init at I₀,
  unfold temporal.init,
  note H' := H.left,
  unfold temporal.init at H',
  rw -H', apply I₀,
end

lemma transient.semantics
  (T₀ : transient' s p q)
: ([]<>•p) τ → ([]<>•-q) τ :=
begin
  intros Hp,
  assert Hstep : (<>[]⟦is_step s⟧) τ,
  { apply eventually_weaken,
    apply ex.safety τ H },
  note H' := coincidence Hstep Hp,
  rw -eventually_eventually,
  apply inf_often_entails_inf_often _ _ H',
  { unfold p_entails, rw p_and_p_imp,
    intros τ Hs Hp,
    cases classical.em (•q $ τ) with Hq Hnq,
    { apply eventually_of_next,
      unfold transient' system.transient program.transient at T₀,
      unfold action is_step at Hs,
      rw [next_init,Hs],
      apply T₀ _ Hp Hq, },
    { rw [-p_not_to_fun,not_init] at Hnq,
      apply eventually_weaken _ Hnq }, },
end

end semantics

instance {α} : system_sem (program α) :=
  { (_ : system (program α)) with
    ex := ex
  , safety := @ex.safety _
  , inhabited := λ p, ⟨ex.witness p, ex.witness_correct p⟩
  , init_sem := @init_sem _
  , transient_sem := @transient.semantics _ }

end simple
