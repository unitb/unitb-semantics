
import data.stream

import unitb.logic

import util.logic

namespace simple

open unitb
open predicate

section

parameter (α : Type)

structure program : Type :=
  (first : α)
  (step : α → α)

def pred := pred' α

parameter {α}

def program.init (s : program) (p : pred) : Prop :=
s.first ⊨ p

def is_step (s : program) (σ σ' : α) : Prop := σ' = s.step σ

def program.transient (s : program) (p q : pred) : Prop :=
⊩ ⟦is_step s⟧ ⟶ •p ⟶ •q ⟶ ⊙-•q

def program.unless (s : program) (p q : pred) : Prop :=
∀ σ, σ ⊨ p ∧ ¬σ ⊨ p → s.step σ ⊨ p ∨ s.step σ ⊨ q

open temporal

lemma program.transient_impl (s : program) {p q : pred}
  (H : p ⟹ -q)
: s.transient p q :=
begin [temporal]
  intros STEP hp hq,
  exfalso,
  revert hq hp,
  simp, rw [not_init],
  clear STEP,
  show _,
  { revert Γ, change _ ⟹ _, monotonicity H, },
end

lemma program.transient_antimono (s : program) (p q p' q' : pred)
  (hp : p' ⟹ p)
  (hq : q' ⟹ q)
  (T₀ : s.transient p q)
: s.transient p' q' :=
begin [temporal]
  replace hp := init_entails_init hp,
  replace hq := init_entails_init hq,
  intros STEP hp' hq',
  replace T₀ := T₀ Γ STEP (hp Γ hp') (hq Γ hq'),
  revert T₀,
  persistent,
  monotonicity,
  apply hq,
end

instance prog_is_system : system program :=
  { σ := α
  , step := is_step
  , init := program.init
  , transient := program.transient
  , transient_false := λ s p, program.transient_impl s (by simp)
  , transient_antimono := program.transient_antimono
  }

lemma unless_step
  {init : α}
  {step : α → α}
  {p q : pred}
  (h : ∀ σ, σ ⊨ p → ¬ σ ⊨ q → step σ ⊨ p ∨ step σ ⊨ q)
: unless (program.mk init step) p q :=
begin
  unfold unless,
  intros σ σ' S,
  have h' := h σ, clear h,
  simp [unitb.step,has_safety.step,is_step] at S,
  rw S,
  intros h,
  cases h,
  apply h' ; assumption,
end

open classical

lemma leads_to_step
  (init : α)
  (step : α → α)
  (p q : pred)
  (h : ∀ σ, σ ⊨ p → ¬ σ ⊨ q → step σ ⊨ q)
: p ↦ q in program.mk init step :=
begin
  apply leads_to.basis,
  { lifted_pred [is_step,temporal.init,not_not_iff_self],
    intros, specialize h _ a_1 a_2,
    simp [a,h], },
  { apply unless_step,
    intros σ hp hnq,
    right, apply h _ hp hnq, }
end

open nat

open temporal

def ex (s : program) : cpred α :=
•eq s.first ⋀ ◻ ⟦ is_step s ⟧

lemma ex.safety (s : program)
: ex s ⟹ ◻ ⟦ is_step s ⟧ :=
begin [temporal]
  intros h, apply h.right
end

def ex.witness (s : program) : stream α
  | 0 := s.first
  | (succ i) := s.step (ex.witness i)

lemma ex.witness_correct (s : program)
: ex.witness s ⊨ ex s :=
begin
  unfold ex, simp,
  split,
  { intro i,
    simp [action,is_step,stream.drop],
    refl },
  { simp [temporal.init],
    exact rfl }
end

section semantics

variable {s : program}
variable Γ : cpred α
variables {p q : pred}
variables H : Γ ⊢ ex s
open temporal
include H

lemma init_sem
  (I₀ : init s p)
: Γ ⊢ •p :=
begin [temporal]
  have H' := H.left,
  revert H',
  lifted_pred,
  show _ ,
  { intros,
    simp [temporal.init] at a ⊢,
    rw ← a,
    assumption },
end

lemma transient.semantics
  (T₀ : transient' s p q)
: Γ ⊢ ◻◇•p ⟶ ◻◇-•q :=
begin [temporal]
  intros Hp,
  replace H := coincidence' (ex.safety s Γ H) Hp,
  rw ← eventually_eventually,
  revert H,
  monotonicity,
  { rw p_and_p_imp,
    intros Hs Hp,
    cases predicate.em (•q) with Hq Hnq,
    { apply T₀ Γ Hs Hp Hnq, },
    { apply Hq } },
end

end semantics

instance : system_sem program :=
  { (_ : system program) with
    ex := ex
  , safety := @ex.safety
  , inhabited := λ p, ⟨ex.witness p, ex.witness_correct p⟩
  , init_sem := @init_sem
  , transient_sem := @transient.semantics }

end

end simple
