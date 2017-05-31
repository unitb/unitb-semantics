
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

def program.transient {α} (s : program α) (p : pred α) : Prop
:= ∀ σ, p σ → ¬ (p (s^.step σ))

def program.unless {α} (s : program α) (p q : pred α) : Prop
:= ∀ σ, p σ ∧ ¬q σ → p (s^.step σ) ∨ q (s^.step σ)

lemma program.transient_false {α} (s : program α)
: s.transient False :=
begin
  unfold program.transient False,
  intros σ h,
  cases h
end

lemma program.transient_str {α} (s : program α) (p q : α → Prop)
  (h : ∀ (i : α), p i → q i)
  (T₀ : s.transient q)
: s.transient p :=
begin
  unfold program.transient,
  intros σ h',
  note h'' := T₀ σ (h _ h'),
  intro h₂, apply h'',
  apply h _ h₂
end

def is_step {α} (s : program α) (σ σ' : α) : Prop := σ' = s.step σ

instance prog_is_system {α} : system (program α) :=
  { σ := α
  , step := is_step
  , init := program.init
  , transient := program.transient
  , transient_false := program.transient_false
  , transient_str := program.transient_str
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
    intros σ h,
    cases h with h₀ h₁,
    note h' := h _ h₀ h₁,
    simp [not_and_iff_not_or_not,not_not_iff_self],
    left, apply h', },
  { apply unless_step,
    intros σ hp hnq,
    right, apply h _ hp hnq, }
end

open nat

def ex {α} (s : program α) : stream α
  | 0 := s^.first
  | (succ n) := s^.step $ ex n

lemma ex.safety {α} {s : program α} (τ : stream α)
  (h : τ = ex s)
: ∀ i, ⟦ is_step s ⟧ (τ.drop i) :=
begin
  intro i,
  subst τ,
  unfold temporal.action is_step stream.drop,
  simp [add_one_eq_succ],
  refl
end

section semantics

universe variable u

parameter {α : Type}
variable {s : program α}
variable {p : pred α}
variable τ : stream α
variable (H : τ = ex s)

include H

lemma init_sem
  (I₀ : init s p)
: (•p) τ :=
begin
  unfold init system.init program.init at I₀,
  unfold temporal.init,
  rw H, apply I₀,
end

lemma transient.semantics
  (T₀ : transient s p)
: ([]<>-•p) τ :=
begin
  intros i,
  cases classical.em ((•p) (stream.drop i τ)) with hp hnp,
  { unfold transient system.transient program.transient at T₀,
    unfold temporal.eventually, existsi 1,
    subst τ,
    simp [temporal.not_init,stream.drop_drop],
    unfold ex p_not temporal.init,
    apply T₀ _ hp, },
  { unfold temporal.eventually p_not, existsi 0,
    simp [stream.drop_drop],
    apply hnp },
end

end semantics

instance {α} : system_sem (program α) :=
  { (_ : system (program α)) with
    ex := λ p τ, τ = ex p
  , safety := @ex.safety _
  , inhabited := λ p, ⟨ex p, rfl⟩
  , init_sem := @init_sem _
  , transient_sem := @transient.semantics _ }

end simple
