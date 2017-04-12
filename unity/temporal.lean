
import data.stream
import unity.predicate

import util.logic

namespace temporal

open predicate

universe variables u u'

variables {β : Type u}

def cpred (β : Type u) := stream β → Prop

def action (a : β → β → Prop) : cpred β
  | τ := a (τ 0) (τ 1)

def eventually (p : cpred β) : cpred β
  | τ := ∃ i, p (τ.drop i)
def henceforth (p : cpred β) : cpred β
  | τ := Π i, p (τ.drop i)
def init (p : β → Prop) : cpred β
  | τ := p (τ 0)

prefix `<>`:85 := eventually
prefix `[]`:85 := henceforth
prefix `•`:75 := init
notation `⟦`:max act `⟧` := action act
-- notation `⦃` act `⦄`:95 := ew act

def tl_leads_to (p q : pred' β) : cpred β :=
[] (•p ⟶ <>•q)

infix ` ~> `:85 := tl_leads_to

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

lemma eventually_of_leads_to {p q : pred' β} {τ} (i : ℕ)
  (h : (p ~> q) τ)
: (<>•p ⟶ <>•q) (τ.drop i)  :=
begin
  intro hp,
  rw -eventually_eventually,
  apply ex_map' _ hp,
  apply @henceforth_drop _ _ τ i h,
end

lemma inf_often_of_leads_to {p q : pred' β} {τ}
  (h : (p ~> q) τ)
: ([]<>•p ⟶ []<>•q) τ :=
begin
  intros P i,
  apply eventually_of_leads_to _ h (P _)
end

lemma leads_to_trans {p q r : pred' β} (τ)
  (Hp : (p ~> q) τ)
  (Hq : (q ~> r) τ)
: (p ~> r) τ :=
begin
  intros i hp,
  apply eventually_of_leads_to _ Hq,
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

lemma induct {β} (p : pred' β) {τ} (h : ([] (•p ⟶ ⟦ λ _, p ⟧)) τ)
: (•p ⟶ []•p) τ :=
begin
  intros h' i,
  induction i with i ih,
  { apply h' },
  { note h₁ := (h _ ih),
    unfold action stream.drop at h₁,
    unfold init stream.drop,
    simp, simp at h₁, apply h₁ }
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

end temporal
