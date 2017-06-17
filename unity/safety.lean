
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
  (init : α → pred' σ)
  (step : α → σ → σ → Prop)

section has_safety

parameter (α : Type u)
parameter [has_safety α]
parameter s : α

def state := has_safety.σ α

parameter {α}

def first : pred' state :=
has_safety.init s

def init (p : pred' state) : Prop :=
first ⟹ p

def step : state → state → Prop :=
has_safety.step s

inductive reachable : state → Prop
  | init : ∀ σ, first σ → reachable σ
  | step : ∀ σ σ', reachable σ → step σ σ' → reachable σ'

def holds (p : pred' state) : Prop :=
reachable ⟹ p

local prefix `⊢ `:40 := holds

lemma relative {p : pred' state}
  (h : ⦃ p ⦄)
: ⊢ p :=
by { intros σ h', apply h }

lemma holds_imp_holds {p q : pred' state}
  (h  : ⊢ p ⟶ q)
  (hp : ⊢ p)
: ⊢ q :=
begin
  intros σ hr,
  apply h _ hr,
  apply hp _ hr,
end

lemma holds_imp_and {p q r : pred' state}
  (h  : ⊢ p ⟶ q)
  (hp : ⊢ p ⟶ r)
: ⊢ p ⟶ q && r :=
sorry

@[simp]
lemma holds_True
: ⊢ True :=
entails_True _

@[refl]
lemma holds_impl_refl {p : pred' state}
: ⊢ p ⟶ p :=
relative (entails_refl _)

@[trans]
lemma holds_impl_trans {p : pred' state} (q : pred' state) {r : pred' state}
  (hp : ⊢ p ⟶ q)
  (hq : ⊢ q ⟶ r)
: ⊢ p ⟶ r :=
begin
  apply holds_imp_holds _ _ hq,
  apply holds_imp_holds _ _ hp,
  apply relative s _,
  intro, apply p_imp_p_imp_p_imp_left,
end

def unless (p q : pred' state) : Prop
:= ∀ σ σ', reachable σ → step σ σ' → p σ ∧ ¬ q σ → p σ' ∨ q σ'

def co (p q : pred' state) : Prop
:= ∀ σ σ', reachable σ → step σ σ' → p σ → q σ'

def co'  (r : act state) : Prop
:= ∀ σ σ', reachable σ → step σ σ' → r σ σ'

def invariant (p : pred' state) : Prop :=
init p ∧ co p p

parameter {s}
lemma invariant_holds {p : pred' state}
  (h : invariant p)
: ⊢ p :=
begin
  intros σ hr,
  induction hr with σ h' σ σ' h' IH,
  { apply h.left _ h' },
  { apply h.right _ _ h' IH ih_1, },
end
parameter s

def unless' (p q : pred' state) (e : act state) : Prop
:= ∀ σ σ', reachable σ → step σ σ' → ¬ e σ σ' → p σ ∧ ¬ q σ → p σ' ∨ q σ'

lemma unless_eq_unless_except (p q : pred' state)
: unless p q = unless' p q (λ _, False) :=
begin
  unfold unless unless',
  apply forall_congr_eq, intro σ,
  apply forall_congr_eq, intro σ',
  apply forall_congr_eq, intro P,
  apply forall_congr_eq, intro P,
  generalize (p σ ∧ ¬q σ → p σ' ∨ q σ') r,
  intro,   simp [iff_eq_eq],
  begin [smt] eblast end,
end

def saf_ex: cpred state :=
 •(has_safety.init s) && [] ⟦ step ⟧

section properties

open predicate

def σ := state

parameters {α s}
lemma unless_action {p q : pred' state}
  (h : unless p q)
: •reachable ⟹ ( ⟦ λ σ σ', (p σ ∧ ¬ q σ) ⟧ ⟶ ( ⟦ step ⟧ ⟶  ⟦ λ _, p || q ⟧ ) ) :=
begin
  intros τ,
  unfold temporal.action,
  intros R hpnq act,
  apply h _ _ R act hpnq
end

lemma impl_unless' {p q : pred' σ} (h : ⊢ p ⟶ q) : unless p q :=
begin
  intros σ σ' hr h₀ h₁,
  cases h₁ with h₁ h₂,
  cases h₂ (h _ hr h₁)
end

lemma impl_unless {p q : pred' σ} (h : p ⟹ q) : unless p q :=
by { apply impl_unless', apply relative _ h }

lemma unless_weak_rhs {p q r : pred' σ}
         (h : q ⟹ r)
         (P₀ : unless p q)
         : unless p r :=
begin
  apply forall_imp_forall _ P₀,
  intro s,
  apply forall_imp_forall _,
  intro s',
  apply imp_imp_imp_right' _,
  intro step,
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
  (P₀ : unless p₀ q₀)
  (P₁ : unless p₁ q₁)
: unless (p₀ && p₁) ((q₀ && p₁) || (p₀ && q₁) || (q₀ && q₁)) :=
begin
  intros s s' R step H,
  note P₀ := P₀ s s' R step,
  note P₁ := P₁ s s' R step,
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

theorem unless_conj {p₀ q₀ p₁ q₁ : pred' σ}
  (h₀ : unless p₀ q₀)
  (h₁ : unless p₁ q₁)
: unless (p₀ && p₁) (q₀ || q₁) :=
begin
  apply unless_weak_rhs _ (unless_conj_gen h₀ h₁),
  apply p_or_entails_of_entails,
  apply p_or_p_imp_p_or',
  { apply p_and_elim_left },
  { apply p_and_elim_right },
  { apply p_and_entails_p_or },
end

lemma unless_disj_gen {p₀ q₀ p₁ q₁ : pred' σ}
         (P₀ : unless p₀ q₀)
         (P₁ : unless p₁ q₁)
         : unless (p₀ || p₁) ((q₀ && - p₁) || (- p₀ && q₁) || (q₀ && q₁)) :=
begin
  intros σ σ' R STEP h,
  cases h with h₀ h₁,
  rw [p_not_eq_not,p_not_p_or,p_not_p_or] at h₁,
  repeat { rw p_not_p_and at h₁ },
  simp [p_not_p_not_iff_self] at h₁,
  cases h₁ with h₁ h₂, cases h₂ with h₂ h₃,
  simp at h₀,
  assert h₄ : p₀ σ ∧ ¬q₀ σ ∨ p₁ σ ∧ ¬q₁ σ,
  { clear STEP R P₀ P₁, begin [smt] by_cases p₀ σ, by_cases (q₀ σ) end },
  note STEP₀ := or.imp (P₀ _ _ R STEP) (P₁ _ _ R STEP) h₄,
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
         (P₀ : unless p₀ q₀)
         (P₁ : unless p₁ q₁)
         : unless (p₀ || p₁) (q₀ || q₁) :=
begin
  note h := unless_disj_gen P₀ P₁, revert h,
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

lemma unless_refl (p : pred' σ) : unless p p :=
begin
  apply impl_unless,
  apply λ _, id
end

lemma unless_antirefl (p : pred' σ) : unless p (-p) :=
begin
  intros σ σ' R X h,
  apply classical.em,
end

lemma True_unless (p : pred' σ) : unless True p :=
begin
  intros σ σ' R X h,
  left, trivial
end

lemma unless_cancellation {p q r : pred' σ}
  (S₀ : unless p q)
  (S₁ : unless q r)
: unless (p || q) r :=
begin
  intros σ σ' R h,
  rw and_shunting,
  intros h₀ hr,
  rw [p_or_comm,-p_or_not_and,p_and_comm] at h₀,
  cases h₀ with hq hpnq,
  { apply or.imp_left (or.intro_right _) (S₁ _ _ R h _),
    exact ⟨hq,hr⟩ },
  { left,
    apply S₀ _ _ R h hpnq, }
end

lemma exists_unless {t} {p : t → pred' σ} {q : pred' σ}
  (h : ∀ i, unless (p i) q)
: unless (∃∃ i, p i) q :=
begin
  intros σ σ' R STEP,
  apply and.rec,
  intros h₀ h₁, cases h₀ with x h₀,
  note h₂ := h x _ _ R STEP ⟨h₀,h₁⟩,
  apply or.imp_left _ h₂,
  apply Exists.intro x,
end

lemma forall_unless_exists_str {n} {p q : fin n → pred' σ}
  (h : ∀ i, unless (p i) (p i && q i))
: unless (∀∀ i, p i) ( (∀∀ i, p i) && (∃∃ i, q i) ) :=
begin
  revert p q h,
  induction n with n IH
  ; intros p q h,
  { rw p_forall_fin_zero, apply True_unless, },
  { rw [p_exists_split_one,p_forall_split_one],
    assert h' : ∀ i, unless s (restr p i) (restr p i && restr q i),
    { unfold restr, intro i, apply h },
    note Hconj := unless_conj_gen (h fin.max) (IH h'),
    apply unless_weak_rhs _ Hconj, clear Hconj,
    { intro, simp, clear h h' IH,
      generalize (∀ (x : fin n), restr p x i) PP, intro,
      generalize (∃ (x : fin n), restr q x i) QQ, intro,
      begin [smt] by_cases (p fin.max i), by_cases PP, by_cases QQ end, } },
end

lemma forall_unless_exists {n} {p q : fin n → pred' σ}
  (h : ∀ i, unless (p i) (q i))
: unless (∀∀ i, p i) (∃∃ i, q i) :=
begin
  revert p q h,
  induction n with n IH
  ; intros p q h,
  { rw p_forall_fin_zero, apply True_unless, },
  { rw [p_exists_split_one,p_forall_split_one],
    assert h' : ∀ i, unless s (restr p i) (restr q i),
    { unfold restr, intro i, apply h },
    note Hconj := unless_conj_gen (h fin.max) (IH h'),
    apply unless_weak_rhs _ Hconj, clear Hconj,
    { intro, simp,
      begin [smt] by_cases (q fin.max i), eblast end, } },
end

lemma forall_unless {n} {p : fin n → pred' σ} {b : pred' σ}
  (h : ∀ i, unless (p i) b)
: unless (∀∀ i, p i) b :=
begin
  note h : unless s (∀∀ i, p i) (∃∃ i : fin n, b) := forall_unless_exists h,
  apply unless_weak_rhs _ h,
  intro x, simp, apply Exists.rec _,
  intro , apply id,
end

open nat temporal stream

lemma henceforth_reachable  {τ : stream state}
    (sem : saf_ex τ)
: [] •reachable $ τ :=
begin
  intro i,
  simp [init_drop],
  induction i with i IH,
  { apply reachable.init _ (sem.left), },
  { apply reachable.step _ _ IH,
    note H := sem.right i,
    rw action_drop at H,
    apply H },
end

lemma henceforth_inv {τ : stream state} {p : pred' state}
  (sem : saf_ex τ)
  (h : invariant p)
: []• p $ τ :=
begin
  note H := henceforth_reachable sem,
  revert H,
  apply henceforth_entails_henceforth,
  apply init_entails_init,
  apply invariant_holds h,
end

lemma assume_reach_step {τ : stream σ} {A : act σ}
  (sem : saf_ex τ)
  (h : ∀ s s', reachable s → step s s' → A s s')
: [] ⟦ A ⟧ $ τ :=
begin
  apply henceforth_imp_henceforth _ sem.right,
  apply henceforth_entails_henceforth _ _ (henceforth_reachable sem),
  unfold p_entails,
  rw [-p_and_p_imp,init_eq_action,action_and_action],
  apply action_entails_action,
  simp [and_shunting],
  apply h,
end

lemma assume_reach_step' {τ : stream σ} {A : act σ}
  (sem : saf_ex τ)
  (h : ∀ s s', reachable s → reachable s' → step s s' → A s s')
: [] ⟦ A ⟧ $ τ :=
begin
  apply assume_reach_step sem,
  intros σ σ' Hr Hs,
  apply h _ _ Hr _ Hs,
  apply reachable.step _ _ Hr Hs,
end

lemma unless_sem' {τ : stream σ} {p q : pred' σ} (i : ℕ)
    (sem : saf_ex τ)
    (H : unless p q)
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
    { apply unless_action H _ (henceforth_reachable sem _),
      { simp [action_drop], split,
        simp [init_drop] at hp, simp [init_drop,hp],
        note hnq := henceforth_str' (k+j) H',
        simp [not_init,drop_drop,init_drop] at hnq,
        simp [hnq,init_to_fun], },
      { apply sem.right } },
    unfold action at GOAL,
    cases GOAL with hp hq,
    { unfold action,
        -- The order of i,j,k changes slightly between
        -- invokations of lean. The next line aims to fix that
      try { simp }, try { simp at hp },
      apply hp },
    { note hnq' := henceforth_str' (k+j+1) H',
      unfold action,
      simp [drop_drop,not_init,init_drop] at hnq',
      unfold drop init at hq hnq',
      simp at hq,
      cases hnq' hq } }
end

lemma co_sem'  {τ : stream σ} {A : act σ}
    (sem : saf_ex τ)
    (H : co' A)
: []⟦ A ⟧ $ τ :=
begin
  note H := henceforth_reachable sem,
  note H' := sem.right,
  revert H',
  apply henceforth_imp_henceforth,
  revert H,
  unfold saf_ex at sem,
  apply henceforth_entails_henceforth _ _ ,
  rw [init_eq_action],
  intros τ h,
  apply H _ _ h
end

lemma unless_sem {τ : stream σ} {p q : pred' σ}
    (sem : saf_ex τ)
    (H : unless p q)
: (<>•p) τ → (<>[]•p) τ ∨ (<>•q) τ :=
by apply @unless_sem' _ _ _ _ _ _ 0 sem H

lemma unless_sem_str {τ : stream σ} {p q : pred' σ}
    (sem : saf_ex τ)
    (H : unless p q)
: ([]<>•p ⟶ <>[]•p || []<>•q) τ :=
begin
  rw [shunting,-eventually_eventually ([] _),not_eventually,-henceforth_and],
  apply henceforth_imp_henceforth, intro j,
  rw [-shunting],
  note H' := unless_sem' j sem H,
  apply H'
end


lemma unless_sem_exists' {τ : stream σ} {t} {p : t → pred' σ} {q : pred' σ} {evt : act σ}
    (sem : saf_ex τ)
    (H : ∀ x, unless' (p x) q evt)
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
    note Hr := henceforth_reachable sem,
    note IH := H x σ _ (Hr _) (sem.right _) H₂.right ⟨ih_1,H₂.left⟩,
    cases IH with IH IH,
    { apply IH },
    { unfold drop at H₃ IH,
      simp at H₃ IH,
      simp [not_or_iff_not_and_not] at H₃,
      cases H₃.left IH }, },
end

lemma unless_sem_exists {τ : stream σ} {t} {p : t → pred' σ} {q : pred' σ}
    (sem : saf_ex τ)
    (H : ∀ x, unless (p x) q)
: ( []<>(∃∃ x, •p x) ⟶ (∃∃ x, <>[]•p x) || []<>•q ) τ :=
begin
  assert H₀ : ( []<>(∃∃ x, •p x) ⟶ (∃∃ x, <>[]•p x) || []<>(•q || ⟦ λ _, False ⟧) ) τ,
  { apply unless_sem_exists' sem,
    simp [unless_eq_unless_except] at H,
    apply H, },
  assert H₁ : action (λ _, False) = (False : cpred σ),
  { apply funext, intro σ,
    refl, },
  rw [H₁,p_or_False] at H₀,
  apply H₀,
end

end properties

end has_safety

infix ` ⊢ `:40 := holds

end unity
