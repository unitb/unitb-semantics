
import data.stream
import unity.predicate

import util.logic

namespace temporal

open predicate

universe variables u u₀ u₁ u₂

variables {α : Type u₀} {β : Type u₁} {γ : Type u₂}

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

lemma init_to_fun (p : pred' β) (τ : stream β) : (•p) τ = p (τ 0) := rfl

def tl_leads_to (p q : cpred β) : cpred β :=
[] (p ⟶ <>q)

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

lemma init_eq_action {p : pred' β}
: •p = ⟦ λ s s', p s ⟧ :=
rfl

lemma next_init_eq_action {p : pred' β}
: ⊙•p = ⟦ λ s s', p s' ⟧ :=
rfl

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

/- True / False -/

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

lemma init_exists {t} (p : t → pred' β)
: •(∃∃ i, p i) = ∃∃ i, •p i :=
begin
  apply funext, intro,
  simp, unfold init p_exists,
  refl
end

/- monotonicity -/

lemma eventually_entails_eventually {p q : cpred β} (f : p ⟹ q) : (<>p) ⟹ (<>q) :=
begin
  intro τ,
  apply exists_imp_exists,
  intro i,
  apply f,
end

lemma eventually_imp_eventually {p q : cpred β} {τ} (f : ([] (p ⟶ q)) τ)
: ((<>p) ⟶ (<>q)) τ :=
begin
  apply exists_imp_exists,
  intro i,
  apply f,
end

lemma henceforth_entails_henceforth {p q : cpred β} (f : p ⟹ q) : ([]p) ⟹ ([]q) :=
begin
  intro τ,
  apply forall_imp_forall,
  intro i,
  apply f,
end

lemma henceforth_imp_henceforth {p q : cpred β} {τ} (f : ([] (p ⟶ q)) τ) : (([]p) ⟶ ([]q)) τ :=
begin
  apply forall_imp_forall,
  intro i,
  apply f,
end

lemma init_entails_init {p q : pred' β} (f : p ⟹ q) : (•p) ⟹ (•q) :=
begin
  intro τ,
  apply f,
end

/- end monotonicity -/

/- distributivity -/

lemma init_lam (p : Prop)
: •(λ _ : α, p) = (λ _, p) :=
rfl

lemma init_p_or {p q : pred' β}
: •(p || q) = •p || •q :=
rfl

lemma init_p_and {p q : pred' β}
: •(p && q) = •p && •q :=
rfl

lemma action_imp (p q : act β)
: (⟦ λ s s' : β, p s s' → q s s' ⟧ : cpred β) = ⟦ p ⟧ ⟶ ⟦ q ⟧ :=
rfl

/- end distributivity -/

-- lemma leads_to_of_eventually {p q : pred' β} (τ)
--   (h : (<>•p ⟶ <>•q) τ )
-- : (p ~> q) τ :=
-- begin
--   intros i H₀,
--   apply h,
--   apply eventually_weaken _ H₀,
-- end

lemma eventually_of_leads_to' {p q : cpred β} {τ} (i : ℕ)
  (h : [](p ⟶ <>q) $ τ)
: (<>p ⟶ <>q) (τ.drop i)  :=
begin
  intro hp,
  rw -eventually_eventually,
  apply eventually_imp_eventually _ hp,
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

lemma leads_to_trans {p q r : cpred β} (τ)
  (Hp : [](p ⟶ <>q)  $τ)
  (Hq : [](q ⟶ <>r) $ τ)
: [](p ⟶ <>r) $ τ :=
begin
  intros i hp,
  apply eventually_of_leads_to' _ Hq,
  apply Hp _ hp,
end

lemma not_henceforth (p : cpred β) : (- []p) = (<>-p) :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  apply not_forall_iff_exists_not,
end

lemma not_init (p : pred' β) : (-•p) = •-p := rfl

lemma next_or (p q : cpred β)
: ⊙(p || q) = ⊙p || ⊙q :=
rfl

open nat

lemma action_drop (A : act α) (τ : stream α) (i : ℕ)
: ⟦ A ⟧ (τ.drop i) ↔ A (τ i) (τ $ succ i) :=
by { unfold stream.drop action, simp }

lemma init_drop (p : pred' α) (τ : stream α) (i : ℕ)
: (• p) (τ.drop i) ↔ p (τ i)  :=
by { unfold stream.drop action, simp [init_to_fun] }

lemma next_init (p : pred' β) (τ : stream β)
: (⊙•p) τ = p (τ 1) :=
rfl

lemma not_eventually {β} (p : cpred β) : (-<>p) = ([]-p) :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  apply not_exists_iff_forall_not,
end

lemma eventually_p_or {β} (p q : cpred β)
: <>(p || q) = <>p || <>q :=
begin
  apply funext, intro,
  simp,
  unfold eventually,
  simp [exists_or],
end

lemma induct_evt {β} (p q : pred' β) {τ} (h : ([] (•p ⟶ ⊙(•p || •q))) τ)
: [] (•p ⟶ <>• q || []•p) $ τ :=
begin
  intros j h₀,
  rw [p_or_iff_not_imp,not_eventually],
  intros h₁ i,
  induction i with i ih,
  { apply h₀ },
  { simp [stream.drop_drop] at ih,
    note h₂ := (h (j+i) ih),
    unfold action stream.drop at h₂,
    simp [stream.drop_drop,add_succ],
    unfold init stream.drop,
    simp, rw [p_or_comm,next_or,p_or_iff_not_imp] at h₂, simp at h₂,
    apply h₂,
    note h₃ := h₁ (i + 1),
    rw [-p_not_eq_not,stream.drop_drop,init_drop] at h₃,
    simp at h₃,
    simp [next_init,h₃], }
end

lemma induct' {β} (p : pred' β) {τ} (h : ([] (•p ⟶ ⊙•p)) τ)
: [] (•p ⟶ []•p) $ τ :=
begin
  rw [-False_p_or ([]•p),-event_false,-init_false],
  apply induct_evt,
  simp [init_false,p_or_False,h],
end

lemma induct {β} (p : pred' β) {τ} (h : ([] (•p ⟶ ⊙•p)) τ)
: (•p ⟶ []•p) τ :=
begin
  apply henceforth_str _ _,
  apply induct' _ h
end

theorem em {β} (p : cpred β) : ⦃ <>[]p || []<>(- p) ⦄ :=
begin
  intro τ,
  assert h : (<>[]p || -<>[]p) τ,
  { apply classical.em (<>[]p $ τ) },
  simp [not_eventually,not_henceforth] at h,
  apply h
end

theorem em' {β} (p : cpred β) (τ) : (<>[]p) τ ∨ ([]<>(- p)) τ :=
by apply em

-- lemma not_stable (p : pred' β) : (-<>[]•p) = []<>•-p := sorry

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

lemma stable_and_of_stable_of_stable {p q : cpred β} {τ}
    (Hp : (<>[]p) τ)
    (Hq : (<>[]q) τ)
: (<>[](p && q)) τ :=
begin
  unfold eventually henceforth at Hp Hq,
  cases Hp with i Hp,
  cases Hq with j Hq,
  unfold eventually henceforth,
  existsi (i+j), intro k,
  simp [stream.drop_drop],
  note Hq' := Hq (i+k),
  note Hp' := Hp (j+k),
  simp [stream.drop_drop] at Hp' Hq',
  exact ⟨Hp',Hq'⟩
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

lemma entail_contrapos {p q : pred' β} : p ⟹ q → (-q) ⟹ -p :=
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

lemma henceforth_forall (P : α → cpred β)
: [](∀∀ x, P x) = ∀∀ x, []P x :=
begin
  apply funext, intro τ,
  simp,
  unfold henceforth p_forall,
  rw [forall_swap],
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

lemma action_entails_action (A B : act β)
  (h : ∀ σ σ', A σ σ' → B σ σ')
: ⟦ A ⟧ ⟹ ⟦ B ⟧ :=
begin
  unfold p_entails ew,
  intro, simp,
  apply h
end

open function

lemma henceforth_trading (f : α → β) (p : cpred β)
: ([] (p ∘ comp f)) = ([] p) ∘ comp f :=
begin
  apply funext, intro τ,
  rw -iff_eq_eq,
  unfold comp henceforth,
  apply forall_congr, intro i,
  rw iff_eq_eq,
  apply congr_arg,
  apply funext, intro j,
  unfold stream.drop, refl
end

lemma eventually_trading (f : α → β) (p : cpred β)
: (<> (p ∘ comp f)) = (<> p) ∘ comp f :=
begin
  apply funext, intro τ,
  rw -iff_eq_eq,
  unfold comp eventually,
  apply exists_congr, intro i,
  rw iff_eq_eq,
  apply congr_arg,
  apply funext, intro j,
  unfold stream.drop, refl
end

lemma init_trading (f : α → β) (p : pred' β)
: • (p ∘ f) = (• p) ∘ comp f :=
begin
  apply funext, intro x,
  unfold comp init,
  refl
end

lemma comp_comp_app_eq_app_comp (p : cpred β) (f : α → β) (τ : stream α)
: (p ∘ comp f) τ ↔ p (f ∘ τ) :=
by refl

lemma inf_often_trace_init_trading (τ : stream α) (f : α → β) (p : β → Prop)
: ([]<>•(p ∘ f)) τ = ([]<>•p) (f ∘ τ) :=
by rw [init_trading,eventually_trading,henceforth_trading]

lemma inf_often_trace_action_trading (τ : stream α) (f : α → α → β) (p : β → Prop)
: ([]<>⟦ λ σ σ', p (f σ σ') ⟧) τ = ([]<>•p) (λ i, f (τ i) (τ $ succ i)) :=
begin
  unfold henceforth eventually,
  rw -iff_eq_eq,
  apply forall_congr, intro i,
  apply exists_congr, intro j,
  simp [stream.drop_drop,action_drop,init_drop],
end

protected theorem leads_to_strengthen_rhs {α} (q : pred' α) {p r : pred' α} {τ : stream α}
    (H : q ⟹ r)
    (P₀ : p ~> q $ τ)
    : p ~> r $ τ :=
begin
  apply leads_to_trans _ P₀,
  intros i H',
  apply eventually_weaken,
  apply H _ H',
end

protected lemma leads_to_cancellation {α} {p q b r : pred' α} {τ : stream α}
    (P₀ : (p ~> q || b) τ)
    (P₁ : (q ~> r) τ)
    : (p ~> r || b) τ :=
begin
  intros i h,
  rw [init_p_or,eventually_p_or],
  apply p_or_p_imp_p_or_left,
  { apply eventually_of_leads_to' _ P₁ },
  rw [-eventually_p_or,-init_p_or],
  apply P₀ _ h,
end

protected lemma leads_to_disj_rng {α} {t : Type u}
         {p : t → pred' α} {q} {r : t → Prop} {τ : stream α}
         (h : ∀ i, r i → (p i ~> q) τ)
         : (∃∃ i, (λ _, r i) && p i) ~> q $ τ :=
begin
  unfold tl_leads_to,
  rw [init_exists],
  rw [p_exists_congr (λ i, @init_p_and _ (λ (_x : α), r i) (p i))],
  rw [@p_exists_congr _ _ _ (λ i, (λ (_x : _), r i) && •p i)],
  { rw [p_exists_range_subtype,p_exists_p_imp,henceforth_forall],
    intro i,
    apply h, apply i.property, },
  { intro i, rw init_lam, },
end

protected theorem leads_to_disj {α t}
    {p : t → pred' α}
    {q : pred' α}
    {τ : stream α}
    (P₀ : ∀ i, p i ~> q $ τ)
    : (∃∃ i, p i) ~> q $ τ :=
begin
  assert P₁ : ∀ i, True i → (p i ~> q) τ,
  { intros i h, apply P₀, },
  note P₂ := temporal.leads_to_disj_rng P₁,
  assert P₃ : (∃∃ (i : t), (λ (_x : α), true) && p i) = (∃∃ i, p i),
  { apply p_exists_congr,
    intro,
    apply True_p_and },
  simp [P₃] at P₂,
  apply P₂
end

protected lemma induction
  {τ : stream α} (f : α → β) (p q : α → Prop)
  [decidable_pred p]
  {lt : β → β → Prop}
  (wf : well_founded lt)
  (P : ∀ v, p && eq v ∘ f  ~>  p && flip lt v ∘ f || q $ τ)
: (p ~> q) τ :=
begin
  assert h₂ : ∀ V, ((p && eq V ∘ f) ~> q) τ,
  { intro V,
    apply well_founded.induction wf V _,
    intros x IH,
    assert Hq : q || q ⟹ q,
    { intro, simp [or_self], apply id },
    apply temporal.leads_to_strengthen_rhs _ Hq,
    apply temporal.leads_to_cancellation (P _),
    assert h' : (p && flip lt x ∘ f) = (λ s, ∃v, flip lt x v ∧ (p s ∧ (eq v ∘ f) s)),
    { apply funext,
      intro x,
      rw -iff_eq_eq,
      simp, unfold function.comp,
      rw [exists_one_point_right (f x),eq_true_intro rfl,and_true],
      intro, apply and.right ∘ and.right },
    rw h',
    apply @temporal.leads_to_disj_rng _ β,
    apply IH, },
  note h₃ := temporal.leads_to_disj h₂,
  assert h₄ : (∃∃ (i : β), (λ (V : β), p && eq V ∘ f) i) = p,
  { apply funext, intro i,
    rw -iff_eq_eq, simp,
    unfold function.comp,
    rw [exists_one_point_right (f i),eq_true_intro rfl,and_true],
    intro, apply and.right },
  rw h₄ at h₃,
  apply h₃,
end

section inf_often_induction'

parameters {α' β' : Type}
parameters {τ : stream α'} (V : α' → β') (p q : α' → Prop)
parameters {lt : β' → β' → Prop}
parameters (wf : well_founded lt)

def le (x y : β') := lt x y ∨ x = y



include wf

-- set_option pp.notation false

lemma inf_often_induction'
  (S₀ : ∀ v, ([]<>•(eq v ∘ V)) τ → (<>[]•eq v ∘ V) τ ∨ ([]<>•(flip lt v ∘ V || q)) τ)
  (P₁ : ∀ v, (•(p && eq v ∘ V) ~> •(flip lt v ∘ V || q)) τ)
: ([]<>•p) τ → ([]<>•q) τ :=
begin
  assert Hex : ∀ (v : β'), ((•(p && eq v ∘ V) ~> (•q || []•-p))) τ,
  { intro v,
    apply well_founded.induction wf v _, clear v,
    intros v IH,
    note IH' := temporal.leads_to_disj_rng IH,
    assert H : (∃∃ (i : β'), (λ _, (λ (y : β'), lt y v) i) && (λ (y : β'), •(p && eq y ∘ V)) i)
             = •(flip lt v ∘ V && p),
    { clear IH' IH S₀ P₁,
      apply funext, intro τ,
      simp, unfold init flip function.comp,
      rw [exists_one_point_right (V $ τ 0)],
      simp [eq_true_intro $ @rfl _ (V $ τ 0)],
      intro,
      apply implies.trans and.elim_right,
      apply and.elim_right },
    rw H at IH', clear IH H,
    assert S₂ : ∀ (v : β'), ([]<>•flip lt v ∘ V) τ → (<>[]•flip lt v ∘ V) τ ∨ ([]<>•(flip lt v ∘ V || q)) τ,
    { admit },
    assert S₁ : ∀ (v : β'), (•eq v ∘ V  ~> ([]•eq v ∘ V) || ([]<>•(flip lt v ∘ V || q))) τ,
    { admit }, clear S₀,
    assert H₁ : (•(p && eq v ∘ V) ~> •(flip lt v ∘ V && p) || •q) τ, admit,
--    assert H₂ : (•(flip lt v ∘ V && p) ~> •q) τ , admit,
    note H₃ := temporal.leads_to_cancellation H₁ IH',
--     note H₀ := @temporal.leads_to_trans _ (•(p && eq v ∘ V)) _ _ _ H₁ IH',
--     clear S₀,
--     assert H₃ : (•(p && eq v ∘ V) ~> •q || []•-p) τ, admit,
-- --    apply temporal.leads_to_cancellation _ _, },
    admit },
  note H := @temporal.leads_to_disj _ _ (λ v, •(p && eq v ∘ V)) (•q || []•-p) τ Hex,
  assert H' : (∃∃ (i : β'), (λ (v : β'), •(p && eq v ∘ V)) i) = •p,
  { apply funext, intro τ, simp,
    unfold init function.comp, simp,
    rw [exists_one_point_right (V $ τ 0)], simp,
    intro, apply and.elim_right },
  unfold tl_leads_to at H,
  rw [H',p_or_comm] at H,
  intros h,
  note H₁ := inf_often_of_leads_to H h,
  rw [inf_often_p_or] at H₁,
  cases H₁ with H₁ H₁,
  { exfalso, revert h,
    change (- []<>•p) τ,
    rw [not_henceforth,not_eventually,not_init],
    apply henceforth_str _ H₁ },
  { apply H₁ },
end

end inf_often_induction'

lemma inf_often_induction
  {τ : stream α} (f : α → β) (p q : α → Prop)
  {lt : β → β → Prop}
  (wf : well_founded lt)
  (h₀ : ([]<>•p) τ)
  (h₁ : ([]⟦ λ s s', q s' ∨ lt (f s') (f s) ∨ (¬ p s' ∧ f s = f s') ⟧) τ)
: ([]<>•q) τ :=
begin
  pose EQ := λ v, eq v ∘ f,
  pose LT := λ v, flip lt v ∘ f,
  assert Q : ∀ v, [](•EQ v ⟶ <>•(LT v || q) || []•EQ v) $ τ,
  { intro v,
    apply induct_evt,
    rw [-init_p_or,next_init_eq_action,init_eq_action,-action_imp],
    apply henceforth_entails_henceforth _ _ h₁,
    apply action_entails_action _ _ _,
    intros s s' h₂ h₃,
    revert LT EQ, simp,
    unfold comp flip, simp,
    intros, subst v,
    apply or.imp id _ h₂,
    apply or.imp id _,
    apply and.right, },
  assert Q' : ∀ v, [](•EQ v ⟶ <>([]•LT v || •q) || []•EQ v) $ τ, admit,
  assert P : ∀ v, p && EQ v  ~>  p && LT v || q $ τ,
  { intro v,
    note Q' := eventually_imp_eventually (Q' v),
    admit },
  apply inf_often_of_leads_to _ h₀,
  assertv inst : decidable_pred p := λ _, classical.prop_decidable _,
  apply temporal.induction _ _ _ wf P,
end

lemma congr_inf_often_trace {x : α} {τ : stream α} (f : α → β)
  (Hinj : injective f)
: ([]<>•eq x) τ ↔ ([]<>•(eq (f x))) (f ∘ τ) :=
begin
  rw [ -comp_comp_app_eq_app_comp ([]<>•eq (f x)) f τ ],
  simp [ (henceforth_trading f (<>•eq (f x))).symm  ],
  simp [ (eventually_trading f (•eq (f x))).symm ],
  simp [ (init_trading f (eq (f x))).symm ],
  assert H : eq (f x) ∘ f = eq x,
  { apply funext, intro y,
    unfold comp,
    rw -iff_eq_eq,
    split,
    { apply Hinj },
    apply congr_arg },
  rw H,
end

lemma events_to_states {lbl : Type u} (s : stream lbl)
  (act : lbl → α → α → Prop) {τ : stream α}
  (h : ∀ i, act (s i) (τ i) (τ (succ i)))
  (e : lbl)
: ([]<>•eq e) s → ([]<>⟦act e⟧) τ :=
begin
  intros h' i,
  cases h' i with j h',
  simp [stream.drop_drop, init_drop] at h',
  unfold eventually, existsi j,
  simp [stream.drop_drop, action_drop,h'],
  apply h,
end

end temporal
