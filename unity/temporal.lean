
import data.stream
import unity.predicate

import util.logic

namespace temporal

open predicate

universe variables u u'

variables {β : Type u} {α : Type u'}

@[reducible]
def cpred (β : Type u) := stream β → Prop

def act (β : Type u) := β → β → Prop

def action (a : act β) : cpred β
  | τ := a (τ 0) (τ 1)

def eventually (p : cpred β) : cpred β
  | τ := ∃ i, p (τ.drop i)
def henceforth (p : cpred β) : cpred β
  | τ := Π i, p (τ.drop i)
def next (p : cpred β) : cpred β
  | τ := p τ.tail
def init (p : β → Prop) : cpred β
  | τ := p (τ 0)

prefix `•`:85 := init
prefix `⊙`:90 := next
prefix `<>`:95 := eventually
prefix `[]`:95 := henceforth
notation `⟦`:max act `⟧`:0 := action act
-- notation `⦃` act `⦄`:95 := ew act

@[simp]
lemma init_to_fun (p : pred' β) (τ : stream β) : (•p) τ = p (τ 0) := rfl

def tl_leads_to (p q : pred' β) : cpred β :=
[] (•p ⟶ <>•q)

infix ` ~> `:50 := tl_leads_to

lemma eventually_weaken {p : cpred β} :
  (p ⟹ <> p) :=
begin
  intros τ h,
  unfold eventually,
  existsi 0,
  apply h
end

lemma eventually_weaken' {p : cpred β} {τ} (i) :
  p (stream.drop i τ) → (<> p) τ :=
begin
  intros h,
  unfold eventually,
  existsi i,
  apply h
end

lemma henceforth_str {p : cpred β} :
  ([]p ⟹ p) :=
begin
  intros τ h, apply h 0
end

lemma henceforth_str' {p : cpred β} {τ} (i) :
  ([]p) τ → p (stream.drop i τ) :=
begin
  intros h, apply h i
end

@[simp]
lemma eventually_eventually (p : cpred β) : <><> p = <> p :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  split
  ; unfold eventually
  ; intro h
  ; cases h with i h,
  { cases h with j h,
    existsi (j+i),
    rw stream.drop_drop at h,
    apply h },
  { existsi (0 : ℕ),
    existsi i,
    apply h }
end

@[simp]
lemma henceforth_henceforth (p : cpred β) : [][] p = [] p :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  split
  ; unfold eventually
  ; intro h,
  { intro i,
    note h' := h i 0,
    simp [stream.drop_drop] at h',
    apply h' },
  { intros i j,
    simp [stream.drop_drop],
    apply h }
end

lemma henceforth_drop {p : cpred β} {τ} (i : ℕ) :
([]p) τ → ([]p) (τ.drop i) :=
begin
  intro h,
  rw -henceforth_henceforth at h,
  apply h,
end


lemma ex_map {p q : cpred β} (f : p ⟹ q) : (<>p) ⟹ (<>q) :=
begin
  intro τ,
  apply exists_imp_exists,
  intro i,
  apply f,
end

lemma ex_map' {p q : cpred β} {τ} (f : ([] (p ⟶ q)) τ) : ((<>p) ⟶ (<>q)) τ :=
begin
  apply exists_imp_exists,
  intro i,
  apply f,
end

lemma hence_map {p q : cpred β} (f : p ⟹ q) : ([]p) ⟹ ([]q) :=
begin
  intro τ,
  apply forall_imp_forall,
  intro i,
  apply f,
end

lemma hence_map' {p q : cpred β} {τ} (f : ([] (p ⟶ q)) τ) : (([]p) ⟶ ([]q)) τ :=
begin
  apply forall_imp_forall,
  intro i,
  apply f,
end

lemma init_map {p q : pred' β} (f : p ⟹ q) : (•p) ⟹ (•q) :=
begin
  intro τ,
  apply f,
end

-- lemma leads_to_of_eventually {p q : pred' β} (τ)
--   (h : (<>•p ⟶ <>•q) τ )
-- : (p ~> q) τ :=
-- begin
--   intros i H₀,
--   apply h,
--   apply eventually_weaken _ H₀,
-- end

lemma eventually_of_leads_to' {p q : pred' β} {τ} (i : ℕ)
  (h : (p ~> q) τ)
: (<>•p ⟶ <>•q) (τ.drop i)  :=
begin
  intro hp,
  rw -eventually_eventually,
  apply ex_map' _ hp,
  apply @henceforth_drop _ _ τ i h,
end

lemma eventually_of_leads_to {p q : pred' β} {τ}
  (h : (p ~> q) τ)
: (<>•p ⟶ <>•q) τ  :=
by apply eventually_of_leads_to' 0 h

lemma inf_often_of_leads_to {p q : pred' β} {τ}
  (h : (p ~> q) τ)
: ([]<>•p ⟶ []<>•q) τ :=
begin
  intros P i,
  apply eventually_of_leads_to' _ h (P _)
end

lemma leads_to_trans {p q r : pred' β} (τ)
  (Hp : (p ~> q) τ)
  (Hq : (q ~> r) τ)
: (p ~> r) τ :=
begin
  intros i hp,
  apply eventually_of_leads_to' _ Hq,
  apply Hp _ hp,
end

lemma not_henceforth (p : cpred β) : (~[]p) = (<>~p) :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  apply not_forall_iff_exists_not,
end

lemma not_init (p : pred' β) : (~•p) = •~p := rfl

open nat

lemma induct' {β} (p : pred' β) {τ} (h : ([] (•p ⟶ ⊙•p)) τ)
: [] (•p ⟶ []•p) $ τ :=
begin
  intros j h' i,
  induction i with i ih,
  { apply h' },
  { simp [stream.drop_drop] at ih,
    note h₁ := (h (j+i) ih),
    unfold action stream.drop at h₁,
    simp [stream.drop_drop,add_succ],
    unfold init stream.drop,
    simp, simp at h₁, apply h₁ }
end

lemma induct {β} (p : pred' β) {τ} (h : ([] (•p ⟶ ⊙•p)) τ)
: (•p ⟶ []•p) τ :=
begin
  apply henceforth_str _ _,
  apply induct' _ h
end

lemma not_eventually {β} (p : cpred β) : (~<>p) = ([]~p) :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  apply not_exists_iff_forall_not,
end

theorem em {β} (p : cpred β) : ⦃ <>[]p || []<>(~ p) ⦄ :=
begin
  intro τ,
  assert h : (<>[]p || ~<>[]p) τ,
  { apply classical.em (<>[]p $ τ) },
  simp [not_eventually,not_henceforth] at h,
  apply h
end

theorem em' {β} (p : cpred β) (τ) : (<>[]p) τ ∨ ([]<>(~ p)) τ :=
by apply em

lemma inf_often_of_stable {p : cpred β} : (<>[]p) ⟹ ([]<>p) :=
begin
  intros τ h i,
  cases h with j h,
  unfold eventually,
  existsi j,
  note h' := h i,
  simp [stream.drop_drop],
  simp [stream.drop_drop] at h',
  apply h',
end

@[simp]
lemma hence_false : [](False : cpred β) = False :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  split ; intro h,
  { cases h 0 },
  { cases h }
end

@[simp]
lemma event_false : <>(False : cpred β) = False :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  split ; intro h,
  { cases h with _ h, cases h },
  { cases h }
end

@[simp]
lemma init_false : (•False) = (False : cpred β) :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  split ; intro h,
  { cases h },
  { cases h }
end

@[simp]
lemma hence_true : [](True : cpred β) = True :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  split ; intro h,
  { trivial },
  { intro, trivial }
end

@[simp]
lemma event_true : <>(True : cpred β) = True :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  split ; intro h,
  { trivial },
  { apply exists.intro 0, trivial }
end

@[simp]
lemma init_true : (•True) = (True : cpred β) :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  split ; intro h ; trivial,
end

lemma coincidence {p q : cpred β} {τ}
    (Hp : (<>[]p) τ)
    (Hq : ([]<>q) τ)
: ([]<>(p && q)) τ :=
begin
  intro i,
  cases Hp with j Hp,
  cases (Hq $ i+j) with k Hq,
  note Hp' := Hp (i+k),
  simp [stream.drop_drop] at Hp',
  simp [stream.drop_drop] at Hq,
  unfold eventually,
  existsi (j+k),
  simp [stream.drop_drop],
  exact ⟨Hp',Hq⟩
end

lemma next_imp_next {p q : cpred β} (τ) (h : p ⟹ q)
: (⊙ p ⟶ ⊙ q) τ :=
h _

lemma entail_contrapos {p q : pred' β} : p ⟹ q → (~q) ⟹ ~p :=
begin
  intros h τ hnq hp,
  apply hnq,
  apply h _ hp,
end

lemma eventually_and {p q : cpred β} {τ : stream β}
   (h₀ : ([]p) τ)
   (h₁ : (<>q) τ)
: (<>(p && q) ) τ :=
begin
  unfold eventually at h₀ h₁,
  cases h₁ with j h₁,
  unfold eventually,
  existsi j,
  exact ⟨h₀ _,h₁⟩
end

lemma henceforth_and (p q : cpred β)
: [](p && q) = []p && []q :=
begin
  apply funext, intro τ,
  simp,
  rw [-iff_eq_eq],
  repeat { split ; intros }
  ; intros i ; try { simp, split },
  { apply (a i).left },
  { apply (a i).right },
  { apply a.left },
  { apply a.right },
end

lemma eventually_exists (P : α → cpred β)
: <>(∃∃ x, P x) = ∃∃ x, <>P x :=
begin
  apply funext, intro τ,
  rw -iff_eq_eq,
  unfold eventually p_exists,
  split
  ; intro H
  ; cases H with i H
  ; cases H with j H
  ; exact ⟨_,_,H⟩ ,
end

/- Actions -/

lemma exists_action (t : Type u) (A : t → act β)
: (∃∃ x : t, ⟦ A x ⟧) = ⟦ λ σ σ', ∃ x, A x σ σ' ⟧ :=
begin
  apply funext, intro i,
  simp,
  unfold temporal.action,
  refl
end

lemma or_action (A B : act β)
: ⟦ A ⟧ || ⟦ B ⟧ = ⟦ λ σ σ', A σ σ' ∨ B σ σ' ⟧ :=
begin
  apply funext, intro i,
  simp,
  refl
end
end temporal
