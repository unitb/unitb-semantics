
import data.stream

import unity.predicate
import unity.temporal

import util.logic

namespace unity

universe variable u

open predicate

class has_safety (α : Type u) : Type (u+1) :=
  (σ : Type)
  (step : α → σ → σ → Prop)

def state := has_safety.σ

def step {α} [has_safety α] : α → state α → state α → Prop :=
has_safety.step


def unless {α} [has_safety α] (s : α) (p q : pred' (state α)) : Prop
:= ∀ σ σ', step s σ σ' → p σ ∧ ¬ q σ → p σ' ∨ q σ'

def saf_ex {α} [has_safety α] (s : α) (τ : stream (state α)) : Prop :=
∀ i, ⟦ step s ⟧ (τ.drop i)

section properties

open predicate

parameter {α : Type u}
variable [has_safety α]
variable s : α
def σ := state α

lemma unless_action {α} [has_safety α] {s : α} {p q : pred' (state α)}
  (h : unless s p q)
: ⟦ λ σ σ', (p σ ∧ ¬ q σ) ⟧ ⟹ ( ⟦ step s ⟧ ⟶  ⟦ λ _, p || q ⟧ ) :=
begin
  intros τ,
  unfold temporal.action,
  intros hpnq act,
  apply h _ _ act hpnq
end

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

lemma unless_refl (p : pred' (state α)) : unless s p p :=
begin
  apply impl_unless,
  apply λ _, id
end

lemma unless_antirefl (p : pred' (state α)) : unless s p (~p) :=
begin
  intros σ σ' X h,
  simp,
  apply classical.em,
end

lemma True_unless (p : pred' (state α)) : unless s True p :=
begin
  intros σ σ' X h,
  left, trivial
end

open nat

open temporal
open stream

lemma unless_sem' {τ : stream σ} {p q : pred' σ} {i : ℕ}
    (sem : saf_ex s τ)
    (H : unless s p q)
: (<>•p) (τ.drop i) → (<>[]•p) (τ.drop i) ∨ (<>•q) (τ.drop i) :=
begin
  intros h,
  cases classical.em ((<> •q) (τ.drop i)) with H' H',
  { right, assumption },
  { left,  simp [p_not_eq_not,not_eventually] at H' ,
    apply ex_map' _ h,
    intros j,
    apply induct,
    intros k hp,
    simp [stream.drop_drop],
    simp [stream.drop_drop] at hp,
    assert GOAL : ⟦λ (_x : σ), p || q⟧ (drop (i + (j + k)) τ),
    { apply unless_action H,
      { unfold action, split,
        unfold init at hp, simp [hp],
        note hnq := henceforth_str' (k+j) H',
        simp [not_init,drop_drop] at hnq, unfold init p_not at hnq,
        simp [hnq], },
      { apply sem } },
    unfold action at GOAL,
    cases GOAL with hp hq,
    { unfold action,
        -- The order of i,j,k changes slightly between
        -- invokations of lean. The next line aims to fix that
      try { simp }, try { simp at hp },
      apply hp },
    { note hnq' := henceforth_str' (k+j+1) H',
      unfold action,
      simp [drop_drop,not_init] at hnq',
      unfold drop init at hq hnq',
      simp at hnq' hq,
      cases hnq' hq } }
end

lemma unless_sem {τ : stream σ} {p q : pred' σ}
    (sem : saf_ex s τ)
    (H : unless s p q)
: (<>•p) τ → (<>[]•p) τ ∨ (<>•q) τ :=
by apply @unless_sem' _ _ _ _ _ _ 0 sem H

end properties

end unity
