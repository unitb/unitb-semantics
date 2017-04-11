
import data.stream

import unity.predicate

import util.logic

namespace unity

universe variable u

class has_safety (α : Type u) : Type (u+1) :=
  (σ : Type)
  (step : α → σ → σ → Prop)

def state := has_safety.σ

def step {α} [has_safety α] : α → state α → state α → Prop :=
has_safety.step

def pred α [has_safety α] := state α → Prop

def unless {α} [has_safety α] (s : α) (p q : pred α) : Prop
:= ∀ σ σ', has_safety.step s σ σ' → p σ ∧ ¬ q σ → p σ' ∨ q σ'

def saf_ex {α} [has_safety α] (s : α) (τ : stream (state α)) : Prop :=
∀ i, step s (τ i) (τ $ i+1)

section properties

open predicate

parameter {α : Type u}
variable [has_safety α]
variable s : α
def σ := state α

lemma impl_unless {p q : pred' σ} (h : ∀ i, p i → q i) : unless s p q :=
begin
  intros σ σ' h₀ h₁,
  cases h₁ with h₁ h₂,
  cases h₂ (h _ h₁)
end

lemma unless_weak_rhs {p q r : pred' σ}
         (h : ∀ i, q i → r i)
         (P₀ : unless s p q)
         : unless s p r :=
begin
  apply forall_imp_forall _ P₀,
  intro s,
  apply forall_imp_forall _,
  intro s',
  apply imp_imp_imp_right' _,
  intro step,
  apply imp_mono,
  { apply and.imp id,
    apply imp_imp_imp_left,
    apply h },
  { apply or.imp_right,
    apply h }
end

lemma unless_conj_gen {p₀ q₀ p₁ q₁ : pred' σ}
         (P₀ : unless s p₀ q₀)
         (P₁ : unless s p₁ q₁)
         : unless s (p₀ && p₁) ((q₀ && p₁) || (p₀ && q₁) || (q₀ && q₁)) :=
begin
  intros s s' step H,
  note P₀ := P₀ s s' step,
  note P₁ := P₁ s s' step,
  cases H with H₀ H₂,
  cases H₀ with Hp₀ Hp₁,
  simp [not_or_iff_not_and_not,not_and_iff_not_or_not] at H₂,
  cases H₂ with Hnpnq H₂, cases H₂ with Hnqnp Hnqnq,
  assert Hnq₀ : ¬ q₀ s,
  { cases Hnqnp with h h, assumption,
    cases h Hp₁ },
  assert Hnq₁ : ¬ q₁ s,
  { cases Hnpnq with h h,
    cases h Hp₀,
    apply h },
  note P₀ := P₀ ⟨Hp₀,Hnq₀⟩,
  note P₁ := P₁ ⟨Hp₁,Hnq₁⟩,
  cases P₀ with P₀ P₀
  ; cases P₁ with P₁ P₁,
  { left, exact ⟨P₀,P₁⟩ },
  { apply or.inr (or.inl $ or.inr _),
    exact ⟨P₀,P₁⟩ },
  { apply or.inr (or.inl $ or.inl _),
    exact ⟨P₀,P₁⟩ },
  { apply or.inr (or.inr _),
    exact ⟨P₀,P₁⟩ },
end

open nat

lemma unless_sem {τ : stream σ} {p q : pred' σ}
    (sem : saf_ex s τ)
    (H : unless s p q)
: ∀ i, p (τ i) → (∀ j, p (τ (i+j))) ∨ (∃ j, q (τ (i+j))) :=
begin
  intros i P,
  cases classical.em (∃ (j : ℕ), q (τ (i + j))) with H' H',
  { right, assumption },
  { left, note H' := forall_not_of_not_exists H',
    intro j,
    induction j with j ih,
    { apply P },
    { note ih := H (τ (i+j)) (τ (succ $ i+j)) (sem (i+j)) ⟨ih,H' _⟩,
      cases ih with ih ih,
      apply ih,
      cases H' (succ j) ih } }
end

end properties

end unity
