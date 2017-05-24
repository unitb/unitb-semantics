
import data.stream

import unity.predicate
import unity.temporal
import unity.safety

import util.logic

universe variables u

namespace unity

section connectors

open predicate

class system (α : Type u) extends has_safety α : Type (u+1) :=
   (transient : α → pred' σ → Prop)
   (init : α → pred' σ → Prop)
   (transient_false : ∀ s : α, transient s $ λ _, false)
   (transient_str : ∀ (s : α) {p q : σ → Prop},
         (∀ i, p i → q i) →
         transient s q →
         transient s p )

def system.state (α : Type u) [system α] := has_safety.σ α

def transient {α} [system α] (s : α) (p : pred' (state α)) : Prop
:= system.transient s p

def init {α} [system α] (s : α) (p : pred' (state α)) : Prop
:= system.init s p

inductive leads_to {α} [system α] (s : α) : pred' (state α) → pred' (state α) → Prop
  | basis : ∀ {p q},
          transient s (p && - q) →
          unless s p q →
          leads_to p q
  | trans : ∀ {p} q {r}, leads_to p q → leads_to q r → leads_to p r
  | disj : ∀ (t : Type) (p : t → pred' (state α)) {q},
         (∀ i, leads_to (p i) q) →
         leads_to (∃∃ i, p i) q

end connectors

notation x ` ↦ `:60 y ` in ` s := leads_to s x y

open predicate

theorem system.unless_conj {α} [system α] (s : α) {p₀ q₀ p₁ q₁ : pred' (state α)} :
         unless s p₀ q₀ →
         unless s p₁ q₁ →
         unless s (p₀ && p₁) (q₀ || q₁) :=
begin
  intros h₀ h₁,
  note h₂ := unless_conj_gen _ h₀ h₁,
  apply unless_weak_rhs _ _ h₂,
  intros i,
  unfold p_and p_or, intro h,
  cases h with h h,
  cases h with h h,
  { cases h with h₂ h₃, exact or.inl h₂ },
  { cases h with h₂ h₃, exact or.inr h₃ },
  { cases h with h₂ h₃, exact or.inl h₂ },
end


theorem leads_to.impl {α} [system α] (s : α) {p q : pred' (state α)}
   (h : p ⟹ q)
   : p ↦ q in s :=
begin
  apply leads_to.basis,
  { assert h' : (p && -q) = λ _, false,
    { apply funext,
      intro x, unfold p_and p_not,
      apply eq_false_of_not_eq_true,
      apply eq_true_intro,
      intros h, cases h with hp hq,
      apply absurd (h _ hp) hq },
    rw h',
    apply system.transient_false },
  apply impl_unless _ h
end

open predicate

theorem leads_to.weaken_lhs {α} [system α] {s : α} (q : pred' (state α)) {p r : pred' (state α)}
    (H  : p ⟹ q)
    (P₀ : q  ↦ r in s)
    : p ↦ r in s :=
begin
  apply leads_to.trans,
  apply leads_to.impl s H,
  apply P₀
end

theorem leads_to.strengthen_rhs {α} [system α] {s : α}
    (q : pred' (state α)) {p r : pred' (state α)}
    (H  : q ⟹ r)
    (P₀ : p  ↦ q in s)
    : p ↦ r in s :=
begin
  apply leads_to.trans,
  apply P₀,
  apply leads_to.impl s H,
end

lemma leads_to.disj_rng {α} [system α] {s : α} {t : Type} {p : t → pred' (state α)} {q} {r : t → Prop}
         (h : ∀ i, r i → p i ↦ q in s)
         : (∃∃ i, (λ _, r i) && p i) ↦ q in s :=
begin
  assert h' : (∃∃ (i : t), (λ _, r i) && p i) =
              (∃∃ (i : { x : t // r x }), p i),
  { apply funext, intro x,
    rw -iff_eq_eq, split,
    { intro h, cases h with j h,
      exact ⟨⟨j, h^.left⟩, h^.right⟩ },
    { intro h₀, cases h₀ with j h₀, cases j with j h₁ h₂,
      exact ⟨j,h₁,h₀⟩, } },
  rw h',
  apply leads_to.disj,
  intro i,
  apply h,
  apply i^.property
end

theorem leads_to.disj' {α} [system α] {s : α} {p q r : pred' (state α)}
    (Pp : p ↦ r in s)
    (Pq : q ↦ r in s)
    : p || q ↦ r in s :=
begin
  apply leads_to.weaken_lhs (λ i, (∃ x : bool, (if x then p else q) i)),
  { intro i,
    apply or.rec,
    { intro h,
      existsi tt, apply h },
    { intro h,
      existsi ff, apply h }, },
  { apply @leads_to.disj _ _ _ bool (λ (x : bool) i, (if x then p else q) i),
    intro i,
    cases i,
    { refine leads_to.weaken_lhs _ _ Pq,
      intros σ h, apply h },
    { refine leads_to.weaken_lhs _ _ Pp,
      intros σ h, apply h }, }
end

theorem leads_to.gen_disj {α} [system α] {s : α} {p q r₀ r₁ : pred' (state α)}
    (Pp : p ↦ r₀ in s)
    (Pq : q ↦ r₁ in s)
    : p || q ↦ r₀ || r₁ in s :=
begin
  apply leads_to.disj',
  { apply leads_to.strengthen_rhs _ _ Pp,
    intro i, apply or.inl },
  { apply leads_to.strengthen_rhs _ _ Pq,
    intro i, apply or.inr },
end

theorem leads_to.gen_disj' {t : Type} {α} [system α] {s : α} {p q : t → pred' (state α)}
    (P : ∀ x, p x ↦ q x in s)
    : (∃∃ x, p x) ↦ (∃∃ x, q x) in s :=
begin
  apply leads_to.disj _ p,
  intro x,
  apply leads_to.strengthen_rhs _ _ (P x),
  intros i h,
  exact ⟨_,h⟩,
end

theorem leads_to.cancellation {α} [system α] {s : α} (q : pred' (state α)) {p r b : pred' (state α)}
    (P₀ : p ↦ q || b in s)
    (P₁ : q ↦ r in s)
    : p ↦ r || b in s :=
begin
  apply leads_to.trans _ P₀,
  apply leads_to.gen_disj P₁,
  apply leads_to.impl,
  intro, apply id
end

def rel α [system α] : Type := system.state α → system.state α → Prop

theorem leads_to.induction' {α} {β : Type} [system α] {s : α} {lt' : β → β → Prop}
    (wf : well_founded lt')
    (V : state α → β)
    {p q : pred' (state α)}
    (P : ∀ v, p && (eq v ∘ V)  ↦ p && (flip lt' v ∘ V) || q in s)
  : p ↦ q in s :=
begin
  pose lt := flip lt',
  assert P' : (∃∃ v, p && eq v ∘ V)  ↦ q in s,
  { apply leads_to.disj β (λ v, p && eq v ∘ V), intro i,
    pose PP := λ i, p && eq i ∘ V  ↦  q in s,
    change PP i,
    apply @well_founded.induction _ lt' wf PP,
    intros j IH,
    change leads_to _ _ _,
    apply leads_to.strengthen_rhs (q || q),
    { intro, simp, exact id },
    apply leads_to.cancellation (p && lt j ∘ V) (P _),
    assert h' : (p && lt j ∘ V) = (λ s, ∃v, lt j v ∧ p s ∧ v = V s),
    { apply funext,
      intro x,
      rw -iff_eq_eq, split,
      { intros H₀, cases H₀ with H₀ H₁,
        existsi V x,
        repeat { split, assumption }, refl },
      { intro h, apply exists.elim h,
        intros s h', cases h' with h₀ h₁, cases h₁, subst s,
        exact ⟨a,h₀⟩ }, },
    rw h', clear h',
    apply leads_to.disj_rng,
    apply IH, },
  { assert h : (∃∃ (v : β), p && eq v ∘ V) = p,
    { apply funext,
      intro x, unfold function.comp,
      simp, rw [exists_one_point_right (V x) _], simp,
      { intro, apply and.right }, },
    rw h at P',
    apply P' }
end

theorem leads_to.induction {α} [system α] {s : α} {lt' : rel α} (wf : well_founded lt')
    {p q : pred' (state α)}
    (P : ∀ v, p && eq v  ↦ p && flip lt' v || q in s)
  : p ↦ q in s :=
leads_to.induction' wf id P

theorem leads_to.PSP {α} [system α] {s : α} {p q r b : pred' (state α)}
    (P : p ↦ q in s)
    (S : unless s r b)
    : p && r  ↦  (q && r) || b in s :=
begin
  induction P with p₀ q₀ t₀ u₀ p₁ q₁ r₁ PP₀ PP₁,
  { apply leads_to.basis,
    { apply system.transient_str _ _ t₀, intro i,
      simp, intro h,
      cases h with h h', cases h' with h₀ h₁,
      split, assumption,
      intro h₂, apply h₁, apply or.inr,
      split, assumption, assumption, },
    { assert H : unless s r (r || b),
      { apply impl_unless, intro, apply or.inl },
      assert H' : unless s p₀ (q₀ || b),
      { apply unless_weak_rhs _ _ u₀,
        intro, apply or.inl },
      note H'' := unless_conj_gen _ u₀ S,
      apply unless_weak_rhs _ _ H'',
      intro i, unfold p_or p_and,
      intro hh, cases hh with hh₀ hh₀, cases hh₀ with hh₀ hh₀,
      { cases hh₀ with hh₀ hh₁, exact or.inl ⟨hh₀,hh₁⟩ },
      { cases hh₀ with hh₀ hh₁, exact or.inr hh₁ },
      { cases hh₀ with hh₀ hh₁, exact or.inr hh₁ } } },
  { note H := leads_to.cancellation _ ih_1 ih_2,
    assert H' : (r₁ && r || b || b) = (r₁ && r || b),
    { apply funext, intro,
      rw -iff_eq_eq,
      simp, rw [-or_assoc,or_self] },
    rw -H', apply H },
  { apply leads_to.weaken_lhs (λ s, ∃i, p_1 i s ∧ r s),
    { intros s h, cases h with h h',
      cases h with i h, existsi i,
      exact ⟨h,h'⟩ },
    apply leads_to.disj, intro i,
    apply ih_1 i, },
end

lemma True_leads_to_True {α} [system α] (s : α)
: True ↦ True in s :=
begin
  apply leads_to.basis,
  { assert H : (True && -True) = (False : pred' (state α)),
    { apply funext, intro x, simp },
    rw H,
    apply system.transient_false },
  { apply True_unless }
end

inductive often_imp_often {α} [system α] (s : α) : pred' (state α) → pred' (state α) → Prop
  | trans : ∀ {p} q {r}, often_imp_often p q → often_imp_often q r → often_imp_often p r
  | induct : ∀ (t : Type) (V : state α → t) (lt : t → t → Prop)
         (wf : well_founded lt)
         {p q}
         (P : ∀ v, p && eq v ∘ V  ↦  flip lt v ∘ V || q  in  s)
         (S : ∀ v, unless s (eq v ∘ V) (flip lt v ∘ V || q)),
         often_imp_often p q

section lemmas

parameters {α : Type u} [system α] (s : α)

lemma often_imp_often.basis {p q}
          (h : p ↦ q in s)
          : often_imp_often s p q :=
begin
  assert H : ∀ t t' (v : t) (f : t' → t), flip empty_relation v ∘ f = False,
  { intros, refl },
  assert H' : ∀ t' (v : unit) (f : t' → unit), eq v ∘ f = True,
  { intros, apply funext, intro x,
    unfold function.comp,
    apply eq_true_intro (unit_eq v (f x)), },
  apply often_imp_often.induct _ (λ _, ()) _ empty_wf
  ; intro,
  { rw [H,False_p_or],
    apply leads_to.weaken_lhs _ _ h,
    apply p_and_left, },
  { rw [H'],
    apply True_unless }
end

end lemmas

open predicate

class system_sem (α : Type u) extends system α :=
  (ex : α → stream _ → Prop)
  (safety : ∀ s, ex s ⟹ saf_ex s)
  (inhabited : ∀s, ∃τ, ex s τ)
  (init_sem : ∀ {s : α} {p : pred' _} (τ : stream _),
         ex s τ →
         init s p →
         (•p) τ)
  (transient_sem : ∀ {s : α} {p : pred' _} (τ : stream _),
         ex s τ →
         transient s p →
         ([]<>-•p) τ)

namespace system_sem

variables {α : Type u}

open temporal

section

variable [system_sem α]

lemma leads_to_sem {s : α} {p q : pred' (state α)}
    (P : p ↦ q in s)
    (τ : stream _)
    (sem : ex s τ)
: (•p ~> •q) τ :=
begin
  note saf : saf_ex s τ := system_sem.safety s _ sem,
  induction P with p' q' T S
        p q r P₀ P₁ H₀ H₁
        X p q P₀ H₀ x y z,
    -- transient and unless
  { intros i hp,
    note saf' := unless_sem' _ _ saf S (temporal.eventually_weaken _ hp),
    cases saf' with saf' saf',
    { note T' := transient_sem τ sem T,
      note T'' := (coincidence saf' (henceforth_drop i T')),
      apply eventually_entails_eventually _ _ (henceforth_str _ T''),
      intros τ',
      simp [init_to_fun],
      intro,
      begin [smt] eblast end },
    { apply saf', } },
    -- transitivity
  { apply leads_to_trans _ H₀ H₁ },
    -- disjunction
  { intros i hp,
    cases hp with x hp,
    apply H₀ x i hp,  }
end

end

section

variable [system_sem α]

lemma often_imp_often_sem'
    {s : α}
    (τ : stream _)
     (sem : ex s τ)
: ∀ {p q : pred' (state α)} (P : often_imp_often s p q),
    ([]<>•p ⟶ []<>•q) τ :=
  @often_imp_often.drec α _ s _
      (take p q r P₀ P₁,
       assume Lpq : ([]<>•p ⟶ []<>•q) τ,
       assume Lqr : ([]<>•q ⟶ []<>•r) τ,
       assume Hp : ([]<>•p) τ,
       show ([]<>•r) τ, from Lqr (Lpq Hp))
      begin
        intros t V lt wf p q P₀ S₀,
        apply inf_often_induction' V p q wf,
        { intro v,
          apply unless_sem_str _ _ (S₀ v),
          apply system_sem.safety _ _ sem, },
        { intro v,
          apply leads_to_sem (P₀ v) _ sem, }
      end

end

end system_sem

end unity
