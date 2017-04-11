
import data.stream
import unity.logic
import util.data.bijection
import util.data.finite
import util.data.countable

namespace det

open predicate

structure prog (lbl : Type) (α : Type) : Type :=
  (first : α)
  (step : lbl → α → α)

def pred α := α → Prop

variables {lbl α : Type}

def prog.init (s : prog lbl α) (p : pred α) : Prop
:= p (s^.first)

def prog.take_step (s : prog lbl α) : option lbl → α → α
  | none := id
  | (some e) := s^.step e

def prog.transient (s : prog lbl α) (p : pred α) : Prop
:= ∃ ev, ∀ σ, p σ → ¬ (p (s^.take_step ev σ))

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

def is_step (s : prog lbl α) (σ σ' : α) : Prop :=
∃ e, s^.take_step e σ = σ'

instance prog_is_system : unity.system (prog lbl α) :=
  { σ := α
  , init := prog.init
  , step := is_step
  , transient := prog.transient
  , transient_false := prog.transient_false
  , transient_str := prog.transient_str
  }

open nat

structure ex (p : prog lbl α) (τ : stream α) : Prop :=
    (init : τ 0 = p^.first)
    (safety : ∀ i, ∃ e, p^.take_step e (τ i) = τ (i+1))
    (liveness : ∀ i e, ∃ j, p^.take_step e (τ (i+j)) = τ (i+j+1))

open unity

def run (s : prog lbl α) (τ : stream (option lbl)) : stream α
  | 0 := prog.first s
  | (succ n) := prog.take_step s (τ n) (run n)

@[simp]
lemma run_succ (s : prog lbl α) (τ : stream (option lbl)) (i : ℕ)
: run s τ (succ i) = prog.take_step s (τ i) (run s τ i)
:= rfl

class sched (lbl : Type) :=
  (sched : ∀ α (s : prog lbl α), ∃ τ, ex s τ)

def inf_sched [infinite lbl] : stream (option lbl) :=
stream.map (infinite.to_nat (option lbl))^.g inf_interleave

def fin_sched [finite lbl] : stream (option lbl) :=
stream.map (pos_finite.to_nat (option lbl))^.g (fin_interleave _)

lemma ex_fin_sched [finite lbl] (s : prog lbl α) : ex s (run s fin_sched) :=
  { init := rfl
  , safety := take i, ⟨fin_sched i,rfl⟩
  , liveness :=
    begin
      intros i e,
      cases inf_repeat_fin_inter ((pos_finite.to_nat $ option lbl)^.f e) i with j h,
      existsi j, unfold fin_sched,
      simp [add_one_eq_succ],
      apply congr, rw [stream.map_app,h,bijection.f_inv],
      refl
    end }

lemma ex_inf_sched [infinite lbl] (s : prog lbl α) : ex s (run s inf_sched) :=
  { init := rfl
  , safety := take i, ⟨inf_sched i,rfl⟩
  , liveness :=
    begin
      intros i e,
      cases inf_repeat_inf_inter ((infinite.to_nat $ option lbl)^.f e) i with j h,
      existsi j, unfold fin_sched,
      simp [add_one_eq_succ],
      apply congr, apply congr_arg,
      unfold inf_sched, rw [stream.map_app,h,bijection.f_inv],
      refl
    end }

instance fin_sched_i {lbl} [finite lbl] : sched lbl :=
  { sched := λ _ s, ⟨run s fin_sched, ex_fin_sched s⟩ }

instance inf_sched_i {lbl} [infinite lbl] : sched lbl :=
  { sched := λ _ s, ⟨run s inf_sched, ex_inf_sched s⟩ }

section soundness

variables {s : prog lbl α} {p : pred' α}
variables (T₀ : prog.transient s p)
include T₀
variables (τ : stream α)

lemma transient.semantics (h : ex s τ)
: ∀ (i : ℕ), p (τ i) → (∃ (j : ℕ), ¬p (τ (i + j))) :=
begin
  intros i hp,
  unfold prog.transient at T₀,
  cases T₀ with ev T₀,
  note sch := h.liveness i ev,
  cases sch with j sch,
  cases classical.em (p (τ (i + j))) with h h,
  { existsi j + 1,
    rw [-add_assoc,-sch],
    apply T₀ _ h, },
  { existsi j,
    apply h }
end

end soundness

instance {α} [sched lbl] : system_sem (prog lbl α) :=
  { (_ : system (prog lbl α)) with
    ex := λ p τ, ex p τ
  , inhabited := sched.sched _
  , transient_sem := @transient.semantics _ _ }

end det
