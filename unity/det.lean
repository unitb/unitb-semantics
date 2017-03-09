
import data.stream
import ..unity.logic

namespace det

record prog (lbl : Type) (α : Type) : Type :=
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

def ex (p : prog lbl α) (τ : stream α) : Prop
  := τ 0 = p^.first ∧ ∀ i, ∃ e, p^.step e (τ i) = τ (i+1)

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
    cases (classical.em $ q' (τ i)) with h h,
    { existsi 0, apply h },
    { existsi 1, unfold ex,
      cases t₀ with e t₀,
      note POST := t₀ (τ i) ⟨h',h⟩,
      note POST' := u₀ (τ i) ⟨h',h⟩,
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
