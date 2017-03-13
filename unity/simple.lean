
import data.stream
import ..unity.logic

namespace simple

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

lemma prog.impl_unless {α} (s : prog α) (p q : α → Prop)
   (h : ∀ (i : α), p i → q i)
   : prog.unless s p q :=
begin
  intros σ h',
  cases h' with h₀ h₁,
  note h₂ := h _ h₀,
  apply absurd h₂ h₁
end

lemma prog.unless_weak_rhs {α} (s : prog α) (p q r : α → Prop)
   (h : ∀ (i : α), q i → r i)
   (P : prog.unless s p q)
: prog.unless s p r :=
begin
  intros σ h',
  apply or.imp_right (h _),
  apply P,
  apply and.imp id _ h',
  cases h',
  intros h₀ h₁,
  apply h₀,
  apply h _ h₁
end

lemma prog.unless_conj {α} (s : prog α) (p₀ q₀ p₁ q₁ : α → Prop)
    (H₀ : prog.unless s p₀ q₀)
    (H₁ : prog.unless s p₁ q₁)
: prog.unless s (λ (i : α), p₀ i ∧ p₁ i) (λ (i : α), q₀ i ∨ q₁ i) :=
begin
  intros σ, simp,
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
  note H₀' := H₀ σ ⟨h₀,h₃⟩,
  note H₁' := H₁ σ ⟨h₁,h₄⟩,
  cases H₀' with H₀' H₀',
  cases H₁' with H₁' H₁',
  { exact or.inr (or.inr ⟨H₀',H₁'⟩) },
  { exact or.inr (or.inl H₁') },
  { exact or.inl H₀' },
end

lemma prog.unless_conj_gen {α} (s : prog α) (p₀ q₀ p₁ q₁ : pred' α)
    (H₀ : prog.unless s p₀ q₀)
    (H₁ : prog.unless s p₁ q₁)
: prog.unless s (p₀ && p₁) (q₀ && p₁ || p₀ && q₁ || q₀ && q₁) :=
begin
  unfold prog.unless, intros σ H₂,
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
  note H₇ := H₀ _ ⟨H₂,H₄⟩,
  note H₈ := H₁ _ ⟨H₃,H₆⟩,
  cases H₇ with H₇ H₇,
  all_goals { cases H₈ with H₈ H₈ },
  { apply or.inl, exact ⟨H₇,H₈⟩ },
  { apply or.inr, apply or.inl, apply or.inr, exact ⟨H₇,H₈⟩ },
  { apply or.inr, apply or.inl, apply or.inl, exact ⟨H₇,H₈⟩ },
  { apply or.inr, apply or.inr, exact ⟨H₇,H₈⟩ },
end

instance prog_is_system {α} : system (prog α) :=
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
      note POST' := u₀ (ex s i) ⟨h',h⟩,
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

instance {α} : system_sem (prog α) :=
  { (_ : system (prog α)) with
    ex := λ p τ, τ = ex p
  , inhabited := λ p, ⟨ex p, rfl⟩
  , leads_to_sem := λ s p q H τ Hτ i,
      begin subst τ, apply leads_to.semantics H end }

end simple
