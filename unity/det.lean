
import data.stream
import unity.logic
import unity.bijection
import unity.finite
import unity.countable

lemma stream.map_app {α β} (f : α → β) (s : stream α) (i : ℕ)
: stream.map f s i = f (s i) := rfl

namespace det

structure prog (lbl : Type) (α : Type) : Type :=
  (first : α)
  (step : lbl → α → α)

def pred α := α → Prop

variables {lbl α : Type}

def prog.init (s : prog lbl α) (p : pred α) : Prop
:= p (s^.first)

def prog.transient (s : prog lbl α) (p : pred α) : Prop
:= ∃ ev, ∀ σ, p σ → ¬ (p (s^.step ev σ))

def prog.unless (s : prog lbl α) (p q : pred α) : Prop
:= ∀ ev σ, p σ ∧ ¬q σ → p (s^.step ev σ) ∨ q (s^.step ev σ)

lemma prog.transient_false [inhabited lbl] (s : prog lbl α) : prog.transient s False :=
begin
  unfold prog.transient False,
  existsi default lbl,
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

lemma prog.impl_unless (s : prog lbl α) (p q : α → Prop)
   (h : ∀ (i : α), p i → q i)
   : prog.unless s p q :=
begin
  intros ev σ h',
  cases h' with h₀ h₁,
  note h₂ := h _ h₀,
  apply absurd h₂ h₁
end

lemma prog.unless_weak_rhs (s : prog lbl α) (p q r : α → Prop)
   (h : ∀ (i : α), q i → r i)
   (P : prog.unless s p q)
: prog.unless s p r :=
begin
  intros ev σ h',
  apply or.imp_right (h _),
  apply P,
  apply and.imp id _ h',
  cases h',
  intros h₀ h₁,
  apply h₀,
  apply h _ h₁
end

lemma prog.unless_conj (s : prog lbl α) (p₀ q₀ p₁ q₁ : α → Prop)
    (H₀ : prog.unless s p₀ q₀)
    (H₁ : prog.unless s p₁ q₁)
: prog.unless s (λ (i : α), p₀ i ∧ p₁ i) (λ (i : α), q₀ i ∨ q₁ i) :=
begin
  intros ev σ, simp,
  intros h,
  cases h with h₀ h₁,
  cases h₁ with h₁ h₂,
  assert h₃ : ¬ q₀ σ ∧ ¬ q₁ σ,
  { split,
    { intro h,
      apply h₂, apply or.inl h },
    { intro h,
      apply h₂, apply or.inr h } }, -- h₂
  cases h₃ with h₃ h₄,
  note H₀' := H₀ ev σ ⟨h₀,h₃⟩,
  note H₁' := H₁ ev σ ⟨h₁,h₄⟩,
  cases H₀' with H₀' H₀',
  cases H₁' with H₁' H₁',
  { exact or.inr (or.inr ⟨H₀',H₁'⟩) },
  { exact or.inr (or.inl H₁') },
  { exact or.inl H₀' },
end

lemma prog.unless_conj_gen (s : prog lbl α) (p₀ q₀ p₁ q₁ : pred' α)
    (H₀ : prog.unless s p₀ q₀)
    (H₁ : prog.unless s p₁ q₁)
: prog.unless s (p₀ && p₁) (q₀ && p₁ || p₀ && q₁ || q₀ && q₁) :=
begin
  unfold prog.unless, intros ev σ H₂,
  cases H₂ with H₂ H₄,
  cases H₂ with H₂ H₃,
  cases not_or_of_not_and_not H₄ with H₄ H₅,
  cases not_or_of_not_and_not H₄ with H₄ H₆,
  -- cases not_and_of_not_or_not H₅ with H₅ H₅,
  assert H₄ : ¬ q₀ σ,
  { cases not_and_of_not_or_not H₄ with H₄ H₄,
    apply H₄, apply absurd H₃ H₄ },
  assert H₆ : ¬ q₁ σ,
  { cases not_and_of_not_or_not H₆ with H₆ H₆,
    apply absurd H₂ H₆, apply H₆ },
  note H₇ := H₀ ev _ ⟨H₂,H₄⟩,
  note H₈ := H₁ ev _ ⟨H₃,H₆⟩,
  cases H₇ with H₇ H₇,
  all_goals { cases H₈ with H₈ H₈ },
  { apply or.inl, exact ⟨H₇,H₈⟩ },
  { apply or.inr, apply or.inl, apply or.inr, exact ⟨H₇,H₈⟩ },
  { apply or.inr, apply or.inl, apply or.inl, exact ⟨H₇,H₈⟩ },
  { apply or.inr, apply or.inr, exact ⟨H₇,H₈⟩ },
end

instance prog_is_system [inhabited lbl] : system (prog lbl α) :=
  { σ := α
  , init := prog.init
  , transient := prog.transient
  , unless := prog.unless
  , transient_false := prog.transient_false
  , transient_str := prog.transient_str
  , impl_unless := prog.impl_unless
  , unless_weak_rhs := prog.unless_weak_rhs
  , unless_conj_gen := prog.unless_conj_gen
  }

open nat

structure ex (p : prog lbl α) (τ : stream α) : Prop :=
    (init : τ 0 = p^.first)
    (safety : ∀ i, ∃ e, p^.step e (τ i) = τ (i+1))
    (liveness : ∀ i e, ∃ j, p^.step e (τ (i+j)) = τ (i+j+1))

theorem unless.semantics [inhabited lbl] {s : prog lbl α} {τ : stream α} {p q : pred _}
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
      unfold unless system.unless prog.unless at P,
      note P' := P e _ ⟨ih_1,h' _⟩,
      rw [add_succ,-add_one_eq_succ,-h₁],
      cases P' with P' P',
      apply P',
      rw [h₁,add_assoc] at P',
      cases h' _ (P') } }
end

-- in simple, with transient, q becomes true immediately
-- in this model, we need to rely on fairness
theorem leads_to.semantics [inhabited lbl] {s : prog lbl α} {τ : stream α} {p q : pred _}
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

class sched (lbl : Type) extends inhabited lbl :=
  (sched : ∀ α (s : prog lbl α), ∃ τ, ex s τ)

def run (s : prog lbl α) (τ : stream lbl) : stream α
  | 0 := prog.first s
  | (succ n) := prog.step s (τ n) (run n)

@[simp]
lemma run_succ (s : prog lbl α) (τ : stream lbl) (i : ℕ)
: run s τ (succ i) = prog.step s (τ i) (run s τ i)
:= rfl

def inf_sched [infinite lbl] : stream lbl :=
stream.map (infinite.to_nat lbl)^.g inf_interleave

def fin_sched [pos_finite lbl] : stream lbl :=
stream.map (pos_finite.to_nat lbl)^.g (fin_interleave _)

lemma ex_fin_sched [pos_finite lbl] (s : prog lbl α) : ex s (run s fin_sched) :=
  { init := rfl
  , safety := take i, ⟨fin_sched i,rfl⟩
  , liveness :=
    begin
      intros i e,
      cases inf_repeat_fin_inter ((pos_finite.to_nat lbl)^.f e) i with j h,
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
      cases inf_repeat_inf_inter ((infinite.to_nat lbl)^.f e) i with j h,
      existsi j, unfold fin_sched,
      simp [add_one_eq_succ],
      apply congr, apply congr_arg,
      unfold inf_sched, rw [stream.map_app,h,bijection.f_inv],
      refl
    end }

instance fin_sched_i {lbl} [pos_finite lbl] : sched lbl :=
  { default := (pos_finite.to_nat lbl)^.g ⟨pos_finite.pred_count lbl,nat.le_refl _⟩
  , sched := λ _ s, ⟨run s fin_sched, ex_fin_sched s⟩ }

instance inf_sched_i {lbl} [infinite lbl] : sched lbl :=
  { default := (infinite.to_nat lbl)^.g 0
  , sched := λ _ s, ⟨run s inf_sched, ex_inf_sched s⟩ }

instance {α} [sched lbl] : system_sem (prog lbl α) :=
  { (_ : system (prog lbl α)) with
    ex := λ p τ, ex p τ
  , inhabited := sched.sched _
  , leads_to_sem := λ s p q H τ Hτ i,
      by apply leads_to.semantics H Hτ  }

end det
