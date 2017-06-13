
import data.stream

import unity.predicate
import unity.temporal

import util.logic
import util.data.fin

namespace unity

universe variable u

open predicate
open temporal

class has_safety (α : Type u) : Type (u+1) :=
  (σ : Type)
  (step : α → σ → σ → Prop)

def state := has_safety.σ

def step {α} [has_safety α] : α → state α → state α → Prop :=
has_safety.step

def unless {α} [has_safety α] (s : α) (p q : pred' (state α)) : Prop
:= ∀ σ σ', step s σ σ' → p σ ∧ ¬ q σ → p σ' ∨ q σ'

def co {α} [has_safety α] (s : α) (p q : pred' (state α)) : Prop
:= ∀ σ σ', step s σ σ' → p σ → q σ'

def co' {α} [has_safety α] (s : α) (r : act (state α)) : Prop
:= ∀ σ σ', step s σ σ' → r σ σ'

def unless' {α} [has_safety α] (s : α) (p q : pred' (state α)) (e : act (state α)) : Prop
:= ∀ σ σ', step s σ σ' → ¬ e σ σ' → p σ ∧ ¬ q σ → p σ' ∨ q σ'

lemma unless_eq_unless_except {α} [has_safety α] (s : α) (p q : pred' (state α))
: unless s p q = unless' s p q (λ _, False) :=
begin
  unfold unless unless',
  apply forall_congr_eq, intro σ,
  apply forall_congr_eq, intro σ',
  apply forall_congr_eq, intro P,
  generalize (p σ ∧ ¬q σ → p σ' ∨ q σ') r,
  simp,
  intro,
  rw [-iff_eq_eq],
  split
  ; intro hr ; intros
  ; apply hr,
  trivial,
end

def saf_ex {α} [has_safety α] (s : α) : cpred (state α) :=
 ([] ⟦ step s ⟧)

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

lemma impl_unless {p q : pred' σ} (h : p ⟹ q) : unless s p q :=
begin
  intros σ σ' h₀ h₁,
  cases h₁ with h₁ h₂,
  cases h₂ (h _ h₁)
end

lemma unless_weak_rhs {p q r : pred' σ}
         (h : q ⟹ r)
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

theorem unless_conj {p₀ q₀ p₁ q₁ : pred' (state α)}
  (h₀ : unless s p₀ q₀)
  (h₁ : unless s p₁ q₁)
: unless s (p₀ && p₁) (q₀ || q₁) :=
begin
  apply unless_weak_rhs _ _ (unless_conj_gen _ h₀ h₁),
  apply p_or_entails_of_entails,
  apply p_or_p_imp_p_or',
  { apply p_and_elim_left },
  { apply p_and_elim_right },
  { apply p_and_entails_p_or },
end

lemma unless_disj_gen {p₀ q₀ p₁ q₁ : pred' σ}
         (P₀ : unless s p₀ q₀)
         (P₁ : unless s p₁ q₁)
         : unless s (p₀ || p₁) ((q₀ && - p₁) || (- p₀ && q₁) || (q₀ && q₁)) :=
begin
  intros σ σ' STEP h,
  cases h with h₀ h₁,
  rw [p_not_eq_not,p_not_p_or,p_not_p_or] at h₁,
  repeat { rw p_not_p_and at h₁ },
  simp [p_not_p_not_iff_self] at h₁,
  cases h₁ with h₁ h₂, cases h₂ with h₂ h₃,
  simp at h₀,
  assert h₄ : p₀ σ ∧ ¬q₀ σ ∨ p₁ σ ∧ ¬q₁ σ,
  { note h₄ := and.intro h₀ h₁,
    rw -distrib_right_or at h₄,
    note h₅ := and.intro h₂ h₃,
    rw [or_comm,-distrib_right_or] at h₅,
    rw [distrib_left_or],
    exact ⟨h₄,h₅⟩, },
  note STEP₀ := or.imp (P₀ _ _ STEP) (P₁ _ _ STEP) h₄,
  assert STEP₁ : (p₀ σ' ∨ p₁ σ') ∨ q₀ σ' ∨ q₁ σ',
  { revert STEP₀,
    apply iff.mp, simp, },
  rw [-or_not_and (p₀ σ' ∨ p₁ σ')] at STEP₁,
  revert STEP₁,
  apply or.imp_right,
  rw [not_or_iff_not_and_not,distrib_left_and],
  simp,
  intro h, right, revert h,
  apply or.imp,
  { apply and.imp_right,
    apply and.right },
  { apply and.imp_right,
    apply and.left },
end

lemma unless_disj' {p₀ q₀ p₁ q₁ : pred' σ}
         (P₀ : unless s p₀ q₀)
         (P₁ : unless s p₁ q₁)
         : unless s (p₀ || p₁) (q₀ || q₁) :=
begin
  note h := unless_disj_gen _ P₀ P₁, revert h,
  apply unless_weak_rhs,
  intros i,
  apply or.rec,
  apply or.rec,
  { apply function.comp,
    apply or.intro_left,
    apply and.elim_left },
  { apply function.comp,
    apply or.intro_right,
    apply and.elim_right },
  { apply function.comp,
    apply or.intro_left,
    apply and.elim_left },
end

lemma unless_refl (p : pred' (state α)) : unless s p p :=
begin
  apply impl_unless,
  apply λ _, id
end

lemma unless_antirefl (p : pred' (state α)) : unless s p (-p) :=
begin
  intros σ σ' X h,
  apply classical.em,
end

lemma True_unless (p : pred' (state α)) : unless s True p :=
begin
  intros σ σ' X h,
  left, trivial
end

lemma unless_cancellation {p q r : pred' (state α)}
  (S₀ : unless s p q)
  (S₁ : unless s q r)
: unless s (p || q) r :=
begin
  intros σ σ' h,
  rw and_shunting,
  intros h₀ hr,
  rw [p_or_comm,-p_or_not_and,p_and_comm] at h₀,
  cases h₀ with hq hpnq,
  { apply or.imp_left (or.intro_right _) (S₁ _ _ h _),
    exact ⟨hq,hr⟩ },
  { left,
    apply S₀ _ _ h hpnq, }
end

lemma exists_unless {t} {p : t → pred' (state α)} {q : pred' (state α)}
  (h : ∀ i, unless s (p i) q)
: unless s (∃∃ i, p i) q :=
begin
  intros σ σ' STEP,
  apply and.rec,
  intros h₀ h₁, cases h₀ with x h₀,
  note h₂ := h x _ _ STEP ⟨h₀,h₁⟩,
  apply or.imp_left _ h₂,
  apply Exists.intro x,
end

lemma forall_unless_exists_str {n} {p q : fin n → pred' (state α)}
  (h : ∀ i, unless s (p i) (p i && q i))
: unless s (∀∀ i, p i) ( (∀∀ i, p i) && (∃∃ i, q i) ) :=
begin
  revert p q h,
  induction n with n IH
  ; intros p q h,
  { rw p_forall_fin_zero, apply True_unless, },
  { rw [p_exists_split_one,p_forall_split_one],
    assert h' : ∀ i, unless s (restr p i) (restr p i && restr q i),
    { unfold restr, intro i, apply h },
    note Hconj := unless_conj_gen _ (h fin.max) (IH h'),
    apply unless_weak_rhs _ _ Hconj, clear Hconj,
    { intro, simp, clear h h' IH,
      generalize (∀ (x : fin n), restr p x i) PP, intro,
      generalize (∃ (x : fin n), restr q x i) QQ, intro,
      begin [smt] by_cases (p fin.max i), by_cases PP, by_cases QQ, eblast end, } },
end

lemma forall_unless_exists {n} {p q : fin n → pred' (state α)}
  (h : ∀ i, unless s (p i) (q i))
: unless s (∀∀ i, p i) (∃∃ i, q i) :=
begin
  revert p q h,
  induction n with n IH
  ; intros p q h,
  { rw p_forall_fin_zero, apply True_unless, },
  { rw [p_exists_split_one,p_forall_split_one],
    assert h' : ∀ i, unless s (restr p i) (restr q i),
    { unfold restr, intro i, apply h },
    note Hconj := unless_conj_gen _ (h fin.max) (IH h'),
    apply unless_weak_rhs _ _ Hconj, clear Hconj,
    { intro, simp,
      begin [smt] by_cases (q fin.max i), eblast end, } },
end

lemma forall_unless {n} {p : fin n → pred' (state α)} {b : pred' (state α)}
  (h : ∀ i, unless s (p i) b)
: unless s (∀∀ i, p i) b :=
begin
  note h : unless s (∀∀ i, p i) (∃∃ i : fin n, b) := forall_unless_exists _ h,
  apply unless_weak_rhs _ _ h,
  intro x, simp, apply Exists.rec _,
  intro , apply id,
end

open nat temporal stream

lemma unless_sem' {τ : stream σ} {p q : pred' σ} (i : ℕ)
    (sem : saf_ex s τ)
    (H : unless s p q)
: (<>•p) (τ.drop i) → (<>[]•p) (τ.drop i) ∨ (<>•q) (τ.drop i) :=
begin
  intros h,
  cases classical.em ((<> •q) (τ.drop i)) with H' H',
  { right, assumption },
  { left,  simp [p_not_eq_not,not_eventually] at H' ,
    apply eventually_imp_eventually _ h,
    intros j,
    apply induct,
    intros k hp,
    simp [stream.drop_drop],
    simp [stream.drop_drop] at hp,
    assert GOAL : ⟦λ (_x : σ), p || q⟧ (drop (i + (j + k)) τ),
    { apply unless_action H,
      { simp [action_drop], split,
        simp [init_drop] at hp, simp [init_drop,hp],
        note hnq := henceforth_str' (k+j) H',
        simp [not_init,drop_drop,init_drop] at hnq,
        simp [hnq,init_to_fun], },
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

lemma co_sem'  {τ : stream σ} {A : act σ}
    (sem : saf_ex s τ)
    (H : co' s A)
: []⟦ A ⟧ $ τ :=
begin
  unfold saf_ex at sem,
  apply henceforth_entails_henceforth _ _ sem,
  apply action_entails_action,
  apply H
end

lemma unless_sem {τ : stream σ} {p q : pred' σ}
    (sem : saf_ex s τ)
    (H : unless s p q)
: (<>•p) τ → (<>[]•p) τ ∨ (<>•q) τ :=
by apply @unless_sem' _ _ _ _ _ _ 0 sem H

lemma unless_sem_str {τ : stream σ} {p q : pred' σ}
    (sem : saf_ex s τ)
    (H : unless s p q)
: ([]<>•p ⟶ <>[]•p || []<>•q) τ :=
begin
  rw [shunting,-eventually_eventually ([] _),not_eventually,-henceforth_and],
  apply henceforth_imp_henceforth, intro j,
  rw [-shunting],
  note H' := unless_sem' _ j sem H,
  apply H'
end


lemma unless_sem_exists' {τ : stream σ} {t} {p : t → pred' σ} {q : pred' σ} {evt : act σ}
    (sem : saf_ex s τ)
    (H : ∀ x, unless' s (p x) q evt)
: ( []<>(∃∃ x, •p x) ⟶ (∃∃ x, <>[]•p x) || []<>(•q || ⟦ evt ⟧) ) τ :=
begin
  intro H₀,
  rw [p_or_comm,-p_not_p_imp],
  intro H₁,
  simp [p_not_p_exists,not_henceforth,not_eventually] at H₁,
  unfold eventually at H₁,
  rw eventually_exists at H₀,
  cases H₁ with i H₁,
  note H₂ := H₀ i,
  cases H₂ with x H₂,
  unfold eventually at H₂,
  cases H₂ with j H₂,
  simp,
  existsi x,
  unfold eventually,
  existsi i+j,
  intro k,
  induction k with k
  ; simp [drop_drop] at H₂,
  { apply H₂, },
  { simp [drop_drop] at ih_1,
    rw [drop_succ,-tail_drop],
    simp [drop_drop],
    unfold tail,
    pose σ := (drop (i + (j + k)) τ 0),
    pose σ' := (τ (i + (j + (k + 1)))),
    note H₂ := H₁ (j+k),
    simp [drop_drop] at H₂,
    note H₃ := H₁ (j+k+1),
    simp [drop_drop,init_to_fun] at H₃,
    simp [not_or_iff_not_and_not,init_to_fun] at H₂,
    note IH := H x σ _ (sem _) H₂.right ⟨ih_1,H₂.left⟩,
    cases IH with IH IH,
    { apply IH },
    { unfold drop at H₃ IH,
      simp at H₃ IH,
      simp [not_or_iff_not_and_not] at H₃,
      cases H₃.left IH }, },
end

lemma unless_sem_exists {τ : stream σ} {t} {p : t → pred' σ} {q : pred' σ}
    (sem : saf_ex s τ)
    (H : ∀ x, unless s (p x) q)
: ( []<>(∃∃ x, •p x) ⟶ (∃∃ x, <>[]•p x) || []<>•q ) τ :=
begin
  assert H₀ : ( []<>(∃∃ x, •p x) ⟶ (∃∃ x, <>[]•p x) || []<>(•q || ⟦ λ _, False ⟧) ) τ,
  { apply unless_sem_exists' _ sem,
    simp [unless_eq_unless_except] at H,
    apply H, },
  assert H₁ : action (λ _, False) = (False : cpred σ),
  { apply funext, intro σ,
    refl, },
  rw [H₁,p_or_False] at H₀,
  apply H₀,
end

end properties

end unity
