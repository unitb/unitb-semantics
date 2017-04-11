
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

theorem leads_to.semantics {α} {s : prog α} {p q : pred _}
  (P : leads_to s p q)
: ∀ i, p (ex s i) → ∃ j, q (ex s $ i+j) :=
begin
  induction P with
      p' q' t₀ u₀
      p' q' r' P₀ P₁ IH₀ IH₁
      t p' q' P₀ IH₀,
  { intro i,
    intros h',
    cases (classical.em $ q' (ex s i)) with h h,
    { existsi 0, apply h },
    { existsi 1, unfold ex,
      note POST := t₀ (ex s i) ⟨h',h⟩,
      assert STEP : has_safety.step s (ex s i) (s.step (ex s i)),
      { apply rfl },
      note POST' := u₀ (ex s i) _ STEP ⟨h',h⟩,
      apply classical.by_contradiction,
      intros h'', cases POST' with POST' POST',
      { apply POST, exact ⟨POST',h''⟩ },
      { apply h'' POST' } } },
  { intros i h,
    note IH₂ := IH₀ _ h,
    cases IH₂ with j IH₂,
    note IH₃ := IH₁ _ IH₂,
    cases IH₃ with j' IH₃,
    existsi (j + j'),
    rw -add_assoc, apply IH₃ },
  { intro i,
    intros h',
    cases h' with k h',
    apply IH₀ _ _ h' }
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
∀ (i : ℕ), p (τ i) → (∃ (j : ℕ), ¬p (τ (i + j))) :=
begin
  intros i hp,
  unfold transient system.transient prog.transient at T₀,
  existsi 1,
  subst τ,
  unfold ex,
  apply T₀ _ hp,
end

end semantics

instance {α} : system_sem (prog α) :=
  { (_ : system (prog α)) with
    ex := λ p τ, τ = ex p
  , inhabited := λ p, ⟨ex p, rfl⟩
  , transient_sem := @transient.semantics _ }

end simple
