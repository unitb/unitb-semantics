
import data.stream

import unitb.logic

import util.logic

local notation `♯` x := cast (by simp) x

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
∀ v, ⊩ ⟦v | is_step s⟧ ⟶ p!v ⟶ q!v ⟶ ⊙-(q!v)

def program.unless (s : program) (p q : pred) : Prop :=
∀ σ, σ ⊨ p ∧ ¬σ ⊨ p → s.step σ ⊨ p ∨ s.step σ ⊨ q

open temporal

lemma program.transient_impl (s : program) {p q : pred}
  (H : p ⟹ -q)
: s.transient p q :=
begin intro,
begin [temporal]
  intros STEP hp hq,
  exfalso,
  revert hq hp,
  simp,
  clear STEP,
  show _,
  { revert Γ, change _ ⟹ _,
    simp only [p_not_comp],
    monotonicity H, },
end
end

lemma program.transient_antimono (s : program) (p q p' q' : pred)
  (hp : p' ⟹ p)
  (hq : q' ⟹ q)
  (T₀ : s.transient p q)
: s.transient p' q' :=
begin intro,
begin [temporal]
  intros STEP hp' hq',
  replace T₀ := T₀ v Γ STEP _ _,
  apply_mono hq T₀,
  apply_mono hp hp',
  apply_mono hq hq',
end
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
  { intro, lifted_pred [is_step,not_not_iff_self],
    intros, specialize h _ a_1 a_2,
    simp [a,h], },
  { apply unless_step,
    intros σ hp hnq,
    right, apply h _ hp hnq, }
end

open nat

open temporal

variables (s : program) (v : tvar α)

def ex : cpred :=
v ≃ s.first ⋀ ◻ ⟦ v | is_step s ⟧

lemma ex.safety
: ex s v ⟹ ◻ ⟦ v | is_step s ⟧ :=
begin [temporal]
  intros h, apply h.right
end

-- def ex.witness : tvar α :=
-- tvar.mk s.first s.step

lemma ex.witness_correct
: ⊩ ∃∃ w, ex s w :=
begin
  have _inst : inhabited α := ⟨ s.first ⟩,
  have := @witness_construction _ (whole ≃ ↑s.first) True (is_step s) _ _ _ _ _
  ; try { revert this }
  ; simp [is_step,ex],
end

section semantics

variable {s}
variable Γ : cpred
variables {p q : pred}
variable σ : tvar α
variables H : Γ ⊢ ex s σ
open temporal
include H

lemma init_sem
  (I₀ : init s p)
: Γ ⊢ p ! σ :=
begin [temporal]
  dsimp [init,system.init] at I₀,
  replace H := H.left,
  rw H,
  lifted_pred,
  show _ ,
  { exact I₀, },
end

lemma transient.semantics
  (T₀ : transient' s p q)
: Γ ⊢ ◻◇(p!σ) ⟶ ◻◇-(q!σ) :=
begin [temporal]
  intros Hp,
  replace H := coincidence' (ex.safety s σ Γ H) Hp,
  rw ← eventually_eventually,
  revert H,
  monotonicity,
  { rw p_and_p_imp,
    intros Hs Hp,
    cases predicate.em (q!σ) with Hq Hnq,
    { apply T₀ σ Γ Hs Hp Hnq, },
    { apply Hq } },
end

end semantics

instance : system_sem program :=
  { (_ : system program) with
    ex := ex
  , safety := @ex.safety
  , inhabited := ex.witness_correct
  , init_sem := @init_sem
  , transient_sem := @transient.semantics }

end

end simple
