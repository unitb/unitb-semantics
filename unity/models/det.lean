
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

theorem unless.semantics {s : prog lbl α} {τ : stream α} {p q : pred _}
  (P : unless s p q)
  (Hτ : ex s τ)
: ∀ i, p (τ i) → (∀ j, p (τ $ i+j)) ∨ (∃ j, q (τ $ i+j)) :=
begin
  intros i hp,
  rw or_comm,
  cases classical.em (∃ (j : ℕ), q (τ (i + j))) with h h,
  { left, apply h },
  { right, note h' := forall_not_of_not_exists h,
    intro j, induction j with j,
    { apply hp },
    { cases Hτ^.safety (i+j) with e h₁,
      unfold unless at P,
      assert h₁' : has_safety.step s (τ (i + j)) (τ $ i+j+1),
      { unfold has_safety.step system.step is_step,
        existsi e,
        apply h₁ },
      note P' := P _ _ h₁' ⟨ih_1,h' _⟩,
      rw [add_succ,-add_one_eq_succ],
      cases P' with P' P',
      apply P',
      rw [add_assoc] at P',
      cases h' _ (P') } }
end

-- in simple, with transient, q becomes true immediately
-- in this model, we need to rely on fairness
theorem leads_to.semantics {s : prog lbl α} {τ : stream α} {p q : pred _}
  (P : leads_to s p q)
  (Hτ : ex s τ)
: ∀ i, p (τ i) → ∃ j, q (τ $ i+j) :=
begin
  induction P with
      p' q' t₀ u₀
      p' q' r' P₀ P₁ IH₀ IH₁
      t p' q' P₀ IH₀,
  { intro i,
    intros h',
    cases t₀ with e t₀,
    note Hτ' := Hτ^.liveness i e,
    cases Hτ' with j Hτ',
    cases unless.semantics u₀ Hτ i h' with h₁ h₁,
    cases classical.em (q' (τ $ i+j)) with h₀ h₀,
    { existsi j, apply h₀ },
    { existsi j + 1, rw [-add_assoc,-Hτ'],
      note t₁ := not_and_of_not_or_not (t₀ (τ $ i + j) ⟨h₁ _,h₀⟩),
      cases t₁ with t₁ t₁,
      rw [Hτ',add_assoc] at t₁,
      cases t₁ (h₁ _), apply classical.by_contradiction,
      intro h, apply t₁ h },
    { apply h₁ } },
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

class sched (lbl : Type) :=
  (sched : ∀ α (s : prog lbl α), ∃ τ, ex s τ)

def run (s : prog lbl α) (τ : stream (option lbl)) : stream α
  | 0 := prog.first s
  | (succ n) := prog.take_step s (τ n) (run n)

@[simp]
lemma run_succ (s : prog lbl α) (τ : stream (option lbl)) (i : ℕ)
: run s τ (succ i) = prog.take_step s (τ i) (run s τ i)
:= rfl

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

instance {α} [sched lbl] : system_sem (prog lbl α) :=
  { (_ : system (prog lbl α)) with
    ex := λ p τ, ex p τ
  , inhabited := sched.sched _
  , leads_to_sem := λ s p q H τ Hτ i,
      by apply leads_to.semantics H Hτ  }

end det
