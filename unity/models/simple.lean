
import data.stream

import unity.logic

import util.logic

namespace simple

open unity
open predicate

structure prog (α : Type) : Type :=
  (first : α)
  (step : α → α)

def pred α := α → Prop

def False {α} : pred α := λ_, false

def prog.init {α} (s : prog α) (p : pred α) : Prop
:= p (s^.first)

def prog.transient {α} (s : prog α) (p : pred α) : Prop
:= ∀ σ, p σ → ¬ (p (s^.step σ))

def prog.unless {α} (s : prog α) (p q : pred α) : Prop
:= ∀ σ, p σ ∧ ¬q σ → p (s^.step σ) ∨ q (s^.step σ)

lemma prog.transient_false {α} (s : prog α) : prog.transient s False :=
begin
  unfold prog.transient False,
  intros σ h,
  cases h
end

lemma prog.transient_str {α} (s : prog α) (p q : α → Prop)
  (h : ∀ (i : α), p i → q i)
  (T₀ : prog.transient s q)
: prog.transient s p :=
begin
  unfold prog.transient,
  intros σ h',
  note h'' := T₀ σ (h _ h'),
  intro h₂, apply h'',
  apply h _ h₂
end

def is_step {α} (s : prog α) (σ σ' : α) : Prop := σ' = s.step σ

instance prog_is_system {α} : system (prog α) :=
  { σ := α
  , step := is_step
  , init := prog.init
  , transient := prog.transient
  , transient_false := prog.transient_false
  , transient_str := prog.transient_str
  }

open nat

def ex {α} (s : prog α) : stream α
  | 0 := s^.first
  | (succ n) := s^.step $ ex n

lemma ex.safety {α} {s : prog α} (τ : stream α)
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
variable {s : prog α}
variable {p : pred α}
variable T₀ : transient s p
include T₀
variable τ : stream α

lemma transient.semantics (H : τ = ex s) :
([]<>-•p) τ :=
begin
  intros i,
  cases classical.em ((•p) (stream.drop i τ)) with hp hnp,
  { unfold transient system.transient prog.transient at T₀,
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

instance {α} : system_sem (prog α) :=
  { (_ : system (prog α)) with
    ex := λ p τ, τ = ex p
  , safety := @ex.safety _
  , inhabited := λ p, ⟨ex p, rfl⟩
  , transient_sem := @transient.semantics _ }

end simple
