
import data.stream

import temporal_logic

import util.logic
import util.predicate
import util.data.fin

local notation `♯` x := cast (by simp) x

namespace unitb

universe variable u

open predicate
open temporal

@[reducible]
def pred (σ : Sort u) := pred' σ

-- instance {σ} : has_coe (pred σ) (pred' σ) :=
-- by { unfold pred, apply_instance }

class has_safety (α : Sort u) : Type u :=
  (σ : Sort u)
  (step : α → σ → σ → Prop)

def state := has_safety.σ

def step {α} [has_safety α] : α → act (state α) :=
has_safety.step

def unless {α} [has_safety α] (s : α) (p q : pred' (state α)) : Prop :=
∀ σ σ', step s σ σ' → σ ⊨ p ∧ ¬ σ ⊨ q → σ' ⊨ p ∨ σ' ⊨ q

def co {α} [has_safety α] (s : α) (p q : pred' (state α)) : Prop :=
∀ σ σ', step s σ σ' → σ ⊨ p → σ' ⊨ q

def co' {α} [has_safety α] (s : α) (r : act (state α)) : Prop :=
∀ σ σ', step s σ σ' → r σ σ'

def unless' {α} [has_safety α] (s : α) (p q : pred' (state α)) (e : act (state α)) : Prop :=
∀ σ σ', step s σ σ' → ¬ e σ σ' → σ ⊨ p ∧ ¬ σ ⊨ q → σ' ⊨ p ∨ σ' ⊨ q

lemma unless_eq_unless_except {α} [has_safety α] (s : α) (p q : pred' (state α))
: unless s p q = unless' s p q (λ _ _, false) :=
begin
  unfold unless unless',
  apply forall_congr_eq, intro σ,
  apply forall_congr_eq, intro σ',
  apply forall_congr_eq, intro P,
  generalize : (σ ⊨ p ∧ ¬ σ ⊨ q → σ' ⊨ p ∨ σ' ⊨ q) = r,
  simp,
end

def saf_ex {α : Sort u} [has_safety α] (s : α) (σ : tvar (state α)) : cpred :=
◻ ⟦ σ | step s ⟧

section properties

open predicate

parameter {α : Type u}
variable [has_safety α]
variable s : α
def σ := state α
variables {s}

lemma unless_action' {α} [has_safety α] {s : α} {p q : pred' (state α)} {e : act $ state α}
  (h : unless' s p q e)
  (σ : tvar (state α))
: ⟦ σ | λ σ σ', (σ ⊨ p ∧ ¬ σ ⊨ q) ⟧ ⟹  (⟦ σ | step s ⟧ ⟶ -⟦ σ | e ⟧ ⟶ ⟦ σ | λ _ σ', σ' ⊨ p ∨ σ' ⊨ q ⟧ ) :=
begin [temporal]
  action with σ σ'
  { intros, apply h ; assumption, },
end

lemma unless_action {α} [has_safety α] {s : α} {p q : pred' (state α)}
  (h : unless s p q)
  (σ : tvar (state α))
: ⟦ σ | λ σ σ', (σ ⊨ p ∧ ¬ σ ⊨ q) ⟧ ⟹ ( ⟦ σ | step s ⟧ ⟶  ⟦ σ | λ _ σ', σ' ⊨ p ∨ σ' ⊨ q ⟧ ) :=
begin [temporal]
  action with h₀ h₁
  { apply h _ _ h₁ h₀, }
end

section
open tactic interactive

meta def classical_rules : list simp_arg_type :=
[simp_arg_type.expr ``(not_or_iff_not_and_not)
,simp_arg_type.expr ``(classical.not_and_iff_not_or_not)
,simp_arg_type.expr ``(not_not_iff_self)]

meta def tactic.classical_simp (rules : parse simp_arg_list) : tactic unit :=
tactic.interactive.simp none ff (classical_rules ++ rules) [`predicate] loc.wildcard

meta def tactic.safety_intro (rules : list simp_arg_type) (with_contra : bool := ff) : tactic unit :=
do `(unless _ _ _) ← target,
   σ  ← intro1,
   σ' ← intro1,
   STEP ← intro1,
   hs ← local_context,
   hs.for_each (λ h, try $ do
     `(unless _ _ _) ← infer_type h,
     note h.local_pp_name none (h σ σ' STEP),
     clear h),
   clear STEP,
   when with_contra (() <$ by_contradiction),
   tactic.classical_simp rules


meta def tactic.prove_safety (rs : parse simp_arg_list) : tactic unit :=
do tactic.safety_intro rs,
   try `[begin [smt] intros, break_asms ; by_contradiction ; eblast end]

meta def tactic.prove_safety_with_contra (rs : parse simp_arg_list) : tactic unit :=
do tactic.safety_intro rs tt,
   try `[begin [smt] intros, break_asms ; by_contradiction ; eblast end]

run_cmd add_interactive
   [`tactic.prove_safety
   ,`tactic.safety_intro
   ,`tactic.prove_safety_with_contra
   ,`tactic.classical_simp]

end

lemma unless_imp {p q : pred' σ} (h : p ⟹ q) : unless s p q :=
begin
  intros σ σ' h₀ h₁,
  replace h := entails_to_pointwise h σ,
  cases_matching _ ∧ _, auto,
end

lemma unless_weak_rhs {p q r : pred' σ}
  (h : q ⟹ r)
  (P₀ : unless s p q)
: unless s p r :=
begin
  revert P₀, unfold unless,
  intros_mono s s' step,
  apply imp_mono,
  { apply and.imp id,
    apply imp_imp_imp_left,
    apply ew_str h },
  { apply or.imp_right,
    apply ew_str h }
end

local attribute [instance] classical.prop_decidable

lemma unless_conj_gen {p₀ q₀ p₁ q₁ : pred' σ}
  (P₀ : unless s p₀ q₀)
  (P₁ : unless s p₁ q₁)
: unless s (p₀ ⋀ p₁) ((q₀ ⋀ p₁) ⋁ (p₀ ⋀ q₁) ⋁ (q₀ ⋀ q₁)) :=
by prove_safety [imp_iff_not_or]

theorem unless_conj {p₀ q₀ p₁ q₁ : pred' (state α)}
  (h₀ : unless s p₀ q₀)
  (h₁ : unless s p₁ q₁)
: unless s (p₀ ⋀ p₁) (q₀ ⋁ q₁) :=
by prove_safety

lemma unless_disj_gen {p₀ q₀ p₁ q₁ : pred' σ}
  (P₀ : unless s p₀ q₀)
  (P₁ : unless s p₁ q₁)
: unless s (p₀ ⋁ p₁) ((q₀ ⋀ - p₁) ⋁ (- p₀ ⋀ q₁) ⋁ (q₀ ⋀ q₁)) :=
by prove_safety

lemma unless_disj' {p₀ q₀ p₁ q₁ : pred' σ}
  (P₀ : unless s p₀ q₀)
  (P₁ : unless s p₁ q₁)
: unless s (p₀ ⋁ p₁) (q₀ ⋁ q₁) :=
by prove_safety

@[refl]
lemma unless_refl (p : pred' (state α)) : unless s p p :=
by prove_safety

lemma unless_antirefl (p : pred' (state α)) : unless s p (-p) :=
by prove_safety

@[simp]
lemma True_unless (p : pred' (state α)) : unless s True p :=
by prove_safety

lemma unless_cancellation {p q r : pred' (state α)}
  (S₀ : unless s p q)
  (S₁ : unless s q r)
: unless s (p ⋁ q) r :=
by prove_safety

lemma exists_unless' {t} {p : t → pred' (state α)} {q : pred' (state α)}
  {A : act (state α)}
  (h : ∀ i, unless' s (p i) q A)
: unless' s (∃∃ i, p i) q A :=
begin
  intros σ σ' STEP Hact,
  apply and.rec,
  intros h₀ h₁, cases h₀ with x h₀,
  have h₂ := h x _ _ STEP Hact ⟨h₀,h₁⟩,
  apply or.imp_left _ h₂,
  apply Exists.intro x,
end

lemma exists_unless {t} {p : t → pred' (state α)} {q : pred' (state α)}
  (h : ∀ i, unless s (p i) q)
: unless s (∃∃ i, p i) q :=
begin
  rw unless_eq_unless_except,
  apply exists_unless',
  intro,
  rw [← unless_eq_unless_except],
  apply h
end

lemma forall_unless_exists_str {n} {p q : fin n → pred' (state α)}
  (h : ∀ i, unless s (p i) (p i ⋀ q i))
: unless s (∀∀ i, p i) ( (∀∀ i, p i) ⋀ (∃∃ i, q i) ) :=
begin
  revert p q h,
  induction n with n IH
  ; intros p q h,
  { rw p_forall_fin_zero, apply True_unless, },
  { rw [p_exists_split_one,p_forall_split_one],
    have h' : ∀ i, unless s (restr p i) (restr p i ⋀ restr q i),
    { unfold restr, intro i, apply h },
    have Hconj := unless_conj_gen (h fin.max) (IH h'),
    apply unless_weak_rhs _ Hconj, clear Hconj,
    { lifted_pred,
      begin [smt] intros, break_asms end, } },
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
    have h' : ∀ i, unless s (restr p i) (restr q i),
    { unfold restr, intro i, apply h },
    have Hconj := unless_conj_gen (h fin.max) (IH h'),
    apply unless_weak_rhs _ Hconj, clear Hconj,
    { propositional } },
end
lemma forall_unless {n} {p : fin n → pred' (state α)} {b : pred' (state α)}
  (h : ∀ i, unless s (p i) b)
: unless s (∀∀ i, p i) b :=
begin
  have h : unless s (∀∀ i, p i) (∃∃ i : fin n, b) := forall_unless_exists h,
  apply unless_weak_rhs _ h,
  pointwise with x, simp,
end

open nat temporal stream
variable v : tvar (state α)

instance persistent_saf_ex : persistent (saf_ex s v) :=
by { unfold saf_ex, apply_instance }

variables {Γ : cpred}

lemma unless_sem {p q : pred' σ}
    (sem : Γ ⊢ saf_ex s v)
    (H : unless s p q)
    (h : Γ ⊢ p ! v)
:  Γ ⊢ ◻(p! v) ⋁ ◇(q ! v) :=
begin [temporal]
  focus_left with H',
  { simp [p_not_eq_not,not_eventually] at H' ,
    revert h,
    apply induct (p ! v) _ _,
    henceforth at sem ⊢,
    intros hp,
    have hq  : -q ! v, simp, apply H',
    have hq' : ⊙(-q ! v), simp, apply  H',
    have := unless_action H v Γ _ sem,
    { revert this hq hq',
      clear H,
      action with σ σ'
      { intros,
        cases_matching _ ∨ _ ; auto } },
    revert hp hq hq',
    action with σ σ'
    { intros, clear H,
      split ; auto, } }
end

lemma co_sem' {A : act σ}
    (sem : Γ ⊢ saf_ex s v)
    (H : co' s A)
: Γ ⊢ ◻⟦ v | A ⟧ :=
begin [temporal]
  henceforth at *,
  revert sem,
  action
  { apply H, },
end

lemma unless_sem_str {p q : pred' σ}
    (sem : Γ ⊢ saf_ex s v)
    (H₀ : unless s p q)
    (H₁ : Γ ⊢ ◻◇(p!v))
: Γ ⊢ ◇◻(p!v) ⋁ ◻◇(q!v) :=
begin [temporal]
  rw [← p_not_p_imp,not_eventually],
  intro H₂,
  henceforth at H₁ ⊢,
  eventually H₁,
  henceforth at H₂,
  revert H₂, rw p_not_p_imp,
  apply unless_sem _ sem H₀ H₁,
end

lemma unless_sem_exists' {t} {p : t → pred' σ} {q : pred' σ} {evt : act σ} {v}
    (sem : Γ ⊢ saf_ex s v)
    (H : ∀ x, unless' s (p x) q evt)
: Γ ⊢ ◻◇(∃∃ x, p x!v) ⟶ (∃∃ x, ◇◻(p x!v)) ⋁ ◻◇(q!v ⋁ ⟦ v | evt ⟧) :=
begin [temporal]
  intro H₀,
  rw [p_or_comm,← p_not_p_imp],
  intro H₁,
  simp [p_not_p_exists] at H₁,
  rw ← eventually_exists,
  eventually H₁,
  henceforth at H₀,
  eventually H₀ ⊢,
  revert H₀,
  apply p_exists_p_imp_p_exists,
  introv,
  apply induct,
  henceforth at sem ⊢,
  intro hp,
  simp [p_not_p_or] at H₁,
  have Hnq : -q!v,
  { strengthen_to ◻_, persistent,
    henceforth at H₁ ⊢, simp, apply H₁.left, },
  have Hnnq : ⊙(-q!v),
  { strengthen_to ◻(_!_), persistent,
    henceforth at H₁ ⊢, simp, apply H₁.left, },
  have Hevt : -⟦ v | evt ⟧,
  { strengthen_to ◻_, persistent,
    henceforth at H₁ ⊢, apply H₁.right, },
  clear H₁,
  have := unless_action' (H x) v Γ,
  revert sem hp Hnq Hnnq Hevt this,
  clear H,
  action with h₀ h₁ h₂ h₃ h₄ h₅
  { specialize h₀ ⟨h₄,h₃⟩ h₅ h₁,
    cases_matching _ ∨ _ ; auto },
end

lemma unless_sem_exists {t} {p : t → pred' σ} {q : pred' σ} {v}
    (sem : Γ ⊢ saf_ex s v)
    (H : ∀ x, unless s (p x) q)
: Γ ⊢ ◻◇(∃∃ x, p x!v) ⟶ (∃∃ x, ◇◻(p x!v)) ⋁ ◻◇(q!v)  :=
begin [temporal]
  intros H',
  simp [unless_eq_unless_except] at H,
  have := @unless_sem_exists' _ _ _ _ t p q _ v sem H H',
  revert this,
  monotonicity,
  simp [@action_false (state α)],
end

end properties

end unitb
