
import data.stream

import unity.logic

import util.logic

namespace simple

open unity
open predicate

section

parameter (α : Type)

structure program : Type :=
  (first : α)
  (step : α → α)

def pred := α → Prop

parameter {α}

def program.init (s : program) (p : pred) : Prop
:= p (s^.first)

def is_step (s : program) (σ σ' : α) : Prop := σ' = s.step σ

instance : has_safety program :=
{ σ := α
, init := λ s σ, s.first = σ
, step := is_step }

def program.transient (s : program) (p q : pred) : Prop
:= ∀ σ, reachable s σ → p σ → q σ → ¬ (q (s^.step σ))

def program.unless (s : program) (p q : pred) : Prop
:= ∀ σ, p σ ∧ ¬q σ → p (s^.step σ) ∨ q (s^.step σ)

lemma program.transient_impl (s : program) {p q : pred}
  (H : s ⊢ p ⟶ -q)
: s.transient p q :=
begin
  unfold program.transient,
  intros σ R hp hq,
  cases H _ R hp hq,
end

lemma program.transient_antimono (s : program) (p q p' q' : pred)
  (hp : s ⊢ p' ⟶ p)
  (hq : s ⊢ q' ⟶ q)
  (T₀ : s.transient p q)
: s.transient p' q' :=
begin
  unfold program.transient,
  intros σ R hp' hq',
  note h'' := T₀ σ R (hp _ R hp') (hq _ R hq'),
  intro h₂, apply h'',
  apply hq _ _ h₂,
  apply (reachable.step _ _ R rfl),
end

instance prog_is_system : system program :=
  { σ := α
  , step := is_step
  , init := _
  , transient := program.transient
  , transient_false := λ s p, program.transient_impl s (by simp)
  , transient_antimono := program.transient_antimono
  }

lemma unless_step
  {init : α}
  {step : α → α}
  {p q : α → Prop}
  (h : ∀ σ, p σ → ¬ q σ → p (step σ) ∨ q (step σ))
: unless (program.mk init step) p q :=
begin
  unfold unless,
  intros σ σ' R S,
  note h' := h σ, clear h,
  unfold unity.step has_safety.step is_step program.step at S,
  rw S,
  intros h,
  cases h,
  apply h' ; assumption,
end

lemma leads_to_step
  (init : α)
  (step : α → α)
  (p q : pred)
  (h : ∀ σ, p σ → ¬ q σ → q (step σ))
: p ↦ q in program.mk init step :=
begin
  apply leads_to.basis,
  { unfold transient system.transient program.transient program.step,
    intros σ R _ h,
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

def ex (s : program) : cpred α :=
•eq s.first && [] ⟦ is_step s ⟧

lemma ex.safety {s : program} (τ : stream α)
  (h : ex s τ)
: saf_ex s $ τ :=
h

def ex.witness (s : program) : stream α
  | 0 := s.first
  | (succ i) := s.step (ex.witness i)

lemma ex.witness_correct (s : program)
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

variable {s : program}
variables {p q : pred}
variable τ : stream α
variable (H : ex s τ)
open temporal

include H

lemma init_sem
  (I₀ : init s p)
: (•p) τ :=
begin
  unfold init at I₀,
  apply I₀,
  unfold temporal.init,
  note H' := H.left,
  unfold temporal.init at H',
  rw -H', apply rfl,
end

lemma transient.semantics
  (T₀ : transient' s p q)
: ([]<>•p) τ → ([]<>•-q) τ :=
begin
  intros Hp,
  assert Hstep : (<>[]⟦is_step s⟧) τ,
  { apply eventually_weaken,
    apply (ex.safety τ H).right },
  note H' := coincidence Hstep Hp,
  rw -eventually_eventually,
  apply inf_often_imp_inf_often_of_henceforth _ H',
  apply henceforth_entails_henceforth _ _ (henceforth_reachable (H.safety _)),
  { unfold p_entails, rw p_and_p_imp,
    intros τ Hr Hs Hp,
    cases classical.em (•q $ τ) with Hq Hnq,
    { apply eventually_of_next,
      unfold transient' system.transient program.transient at T₀,
      unfold action is_step at Hs,
      rw [next_init,Hs],
      apply T₀ _ Hr Hp Hq, },
    { rw [-p_not_to_fun,not_init] at Hnq,
      apply eventually_weaken _ Hnq }, },
end

end semantics

instance : system_sem program :=
  { (_ : system program) with
    ex := ex
  , safety := @ex.safety
  , inhabited := λ p, ⟨ex.witness p, ex.witness_correct p⟩
  , transient_sem := @transient.semantics }

end

end simple
