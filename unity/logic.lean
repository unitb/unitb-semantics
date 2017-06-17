
import data.stream

import unity.predicate
import unity.temporal
import unity.safety

import util.logic

universe variables u v

namespace unity

section connectors

open predicate

class system (α : Type u) extends has_safety α : Type (u+1) :=
   (transient : α → pred' σ → pred' σ → Prop)
   (transient_false : ∀ {s} (p : pred' σ), transient s p False)
   (transient_antimono : ∀ {s : α} {p q p' q' : pred' σ},
         (s ⊢ p' ⟶ p) →
         (s ⊢ q' ⟶ q) →
         transient s p q →
         transient s p' q' )

parameters (α : Type u) [system α] (s : α)

def system.state := has_safety.σ α
parameters {α}

def transient (p : pred' (state α)) : Prop
:= system.transient s True p

def transient' (p q : pred' (state α)) : Prop
:= system.transient s p q

parameter {s}

lemma system.transient_str' {p q r : pred' (state α)}
  (H : s ⊢ r ⟶ q)
: transient' p q → transient' p r :=
system.transient_antimono (relative _ (entails_refl _)) H

lemma system.transient_str {p q r : pred' (state α)}
  (H : r ⟹ q)
: transient' p q → transient' p r :=
system.transient_str' (relative _ H)

parameter (s)

inductive leads_to : pred' (state α) → pred' (state α) → Prop
  | trivial {} : ∀ {p}, leads_to p True
  | basis' : ∀ {p q : pred' (state α)} r,
          transient' r (p && - q) →
          unless s p q →
          leads_to (p && -q) (r || q) →
          leads_to p q
  | trans : ∀ {p} q {r}, leads_to p q → leads_to q r → leads_to p r
  | disj : ∀ (t : Type) (p : t → pred' (state α)) {q},
         (∀ i, leads_to (p i) q) →
         leads_to (∃∃ i, p i) q

local notation x ` ↦ `:60 y ` in ` s := leads_to x y

inductive often_imp_often : pred' (state α) → pred' (state α) → Prop
  | transient : ∀ {p q}, transient' p (-q) → often_imp_often p q
  | trans : ∀ {p} q {r}, often_imp_often p q → often_imp_often q r → often_imp_often p r
  | induct : ∀ (t : Type) (V : state α → t) (lt : t → t → Prop)
         (wf : well_founded lt)
         {p q}
         (P : ∀ v, p && eq v ∘ V  ↦  flip lt v ∘ V || q  in  s)
         (S : ∀ v, unless s (eq v ∘ V) (flip lt v ∘ V || q)),
         often_imp_often p q

end connectors

notation x `  ↦  `:60 y ` in ` s := leads_to s x y
notation x `  >~>  `:60 y ` in ` s := often_imp_often s x y

section conversion

parameter {α  : Type u}
parameter {α' : Type v}
parameter [system α]
parameter [system α']
parameter (f : state α' → state α)
parameters (s : α) (s' : α')
parameter (Tf : ∀ {p q}, transient' s p q → transient' s' (p ∘ f) (q ∘ f))
parameter (Uf : ∀ {p q}, unless s p q → unless s' (p ∘ f) (q ∘ f))

include Tf Uf

lemma leads_to.subst : ∀ {p q}
  (H : p ↦ q in s),
  (p ∘ f) ↦ (q ∘ f) in s' :=
begin
  apply leads_to.drec,
  { intro p, apply leads_to.trivial },
  { intros p q b t u P₀ P₁,
    apply leads_to.basis' (b ∘ f),
    { apply Tf t },
    { apply Uf u },
    { apply P₁ }, },
  { intros p q r Pa₀ Pa₁ Pb₀ Pb₁,
    apply leads_to.trans (q ∘ f) Pb₀ Pb₁, },
  { intros t p q Pa Pb,
    apply leads_to.disj t _ Pb },
end

lemma often_imp_often.subst : ∀ {p q}
  (H : p >~> q in s),
  (p ∘ f) >~> (q ∘ f) in s' :=
begin
  apply often_imp_often.drec,
  { intros p q T,
    apply often_imp_often.transient (Tf T) },
  { intros p q r _ _ Pb₀ Pb₁,
    apply often_imp_often.trans _ Pb₀ Pb₁ },
  { intros t V lt wf p q P S,
    apply often_imp_often.induct t (V ∘ f) lt wf,
    { intro v, apply leads_to.subst f s s' @Tf @Uf (P v), },
    { intro v, apply Uf (S v) } },
end

end conversion

open predicate

section rules

parameters {α : Type u} [system α]
parameter {s : α}

lemma leads_to.basis {p q : pred' (state α)}
  (h₀ : transient s (p && - q))
  (h₁ : unless s p q)
: leads_to s p q :=
begin
  apply leads_to.basis' _ h₀ h₁,
  rw True_p_or, apply leads_to.trivial
end

parameter s

theorem leads_to.impl' {p q : pred' (state α)}
   (h : s ⊢ p ⟶ q)
   : p ↦ q in s :=
begin
  apply leads_to.basis,
  { assert h' : s ⊢ (p && -q) ⟶ False,
    { rw [p_and_p_imp,-p_not_eq_imp_False,p_not_p_not_iff_self],
      apply h },
    apply system.transient_str' h' _,
    apply system.transient_false },
  apply impl_unless' _ h
end

theorem leads_to.impl {p q : pred' (state α)}
   (h : p ⟹ q)
   : p ↦ q in s :=
by { apply leads_to.impl', apply relative _ h }

parameter {s}

theorem leads_to.monotonicity'
  {p p' q q' : pred' (state α)}
  (Hp : s ⊢ p' ⟶ p)
  (Hq : s ⊢ q  ⟶ q')
  (P₀ : p  ↦ q in s)
: p' ↦ q' in s :=
begin
  note Hlt_p := leads_to.impl' s Hp,
  note Hlt_q := leads_to.impl' s Hq,
  apply leads_to.trans _ Hlt_p,
  apply leads_to.trans _ P₀ Hlt_q,
end

theorem leads_to.monotonicity
  {p p' q q' : pred' (state α)}
  (Hp : p' ⟹ p)
  (Hq : q  ⟹ q')
  (P₀ : p  ↦ q in s)
: p' ↦ q' in s :=
begin
  apply leads_to.monotonicity' _ _ P₀,
  { apply relative _ Hp },
  { apply relative _ Hq },
end

theorem leads_to.weaken_lhs' (q : pred' (state α)) {p r : pred' (state α)}
    (H  : s ⊢ p ⟶ q)
    (P₀ : q  ↦ r in s)
    : p ↦ r in s :=
leads_to.monotonicity' H (holds_impl_refl _) P₀

theorem leads_to.weaken_lhs (q : pred' (state α)) {p r : pred' (state α)}
    (H  : p ⟹ q)
    (P₀ : q  ↦ r in s)
    : p ↦ r in s :=
leads_to.monotonicity H (by refl) P₀

theorem leads_to.strengthen_rhs'
    (q : pred' (state α)) {p r : pred' (state α)}
    (H  : s ⊢ q ⟶ r)
    (P₀ : p  ↦ q in s)
    : p ↦ r in s :=
leads_to.monotonicity' (holds_impl_refl _) H P₀

theorem leads_to.strengthen_rhs
    (q : pred' (state α)) {p r : pred' (state α)}
    (H  : q ⟹ r)
    (P₀ : p  ↦ q in s)
    : p ↦ r in s :=
leads_to.monotonicity (by refl) H P₀

lemma leads_to.disj_rng {t : Type} {p : t → pred' (state α)} {q} {r : t → Prop}
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

theorem leads_to.disj' {p q r : pred' (state α)}
    (Pp : p ↦ r in s)
    (Pq : q ↦ r in s)
    : p || q ↦ r in s :=
begin
  apply leads_to.weaken_lhs (∃∃ x : bool, (if x then p else q)),
  { intro i,
    apply or.rec ; unfold p_exists,
    { intro h,
      existsi tt, apply h },
    { intro h,
      existsi ff, apply h }, },
  { apply @leads_to.disj _ _ _ bool,
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

theorem leads_to.induction' {β : Type} {lt' : β → β → Prop}
    (wf : well_founded lt')
    (V : state α → β)
    {p q : pred' (state α)}
    (P : ∀ v, p && (eq v ∘ V)  ↦  p && (flip lt' v ∘ V) || q  in  s)
  : p ↦ q in s :=
begin
  pose lt := flip lt',
  assert P' : (∃∃ v, p && eq v ∘ V)  ↦ q in s,
  { apply leads_to.disj β, intro i,
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

def rel : Type := system.state α → system.state α → Prop

theorem leads_to.induction {lt' : rel} (wf : well_founded lt')
    {p q : pred' (state α)}
    (P : ∀ v, p && eq v  ↦  p && flip lt' v || q  in  s)
  : p ↦ q in s :=
leads_to.induction' wf _ P

theorem leads_to.PSP {p q r b : pred' (state α)}
  (P : p ↦ q in s)
  (S : unless s r b)
: p && r  ↦  (q && r) || b in s :=
begin
  induction P with p p₀ q₀ b₀ t₀ u₀ P PSP₀
         p₁ q₁ r₁ PP₀ PP₁,
  { apply leads_to.impl,
    apply p_and_entails_of_entails_right,
    apply entails_p_or_of_entails_left,
    simp, },
  { apply leads_to.basis' b₀,
    { apply system.transient_str _ t₀,
      { intro, simp, clear P PSP₀ u₀ t₀,
        begin [smt] by_cases r i end }, },
    { assert H : unless s r (r || b),
      { apply impl_unless, intro, apply or.inl },
      assert H' : unless s p₀ (q₀ || b),
      { apply unless_weak_rhs _ u₀,
        intro, apply or.inl },
      note H'' := unless_conj_gen u₀ S,
      apply unless_weak_rhs _ H'',
      intro i, unfold p_or p_and,
      intro hh, cases hh with hh₀ hh₀, cases hh₀ with hh₀ hh₀,
      { cases hh₀ with hh₀ hh₁, exact or.inl ⟨hh₀,hh₁⟩ },
      { cases hh₀ with hh₀ hh₁, exact or.inr hh₁ },
      { cases hh₀ with hh₀ hh₁, exact or.inr hh₁ } },
    { apply leads_to.monotonicity _ _ PSP₀,
      { intro, simp, begin [smt] by_cases r i end },
      { intro, simp, clear PSP₀ P u₀ t₀ S,
        begin [smt] by_cases b i, by_cases q₀ i, end }, } },
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

lemma leads_to.completion {n : ℕ} {p q : fin n → pred' (state α)} {b : pred' (state α)}
  (P : ∀ i, p i ↦ q i || b in s)
  (S : ∀ i, unless s (q i) b)
: (∀∀ i, p i) ↦ (∀∀ i, q i) || b in s :=
sorry

lemma True_leads_to_True
: True ↦ True in s :=
leads_to.trivial

lemma often_imp_often.basis {p q}
  (h : p ↦ q in s)
: p >~> q in s :=
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
    apply p_and_elim_left, },
  { rw [H'],
    apply True_unless }
end

lemma True_often_imp_often_True
: True >~> True in s :=
begin
  apply often_imp_often.basis,
  apply leads_to.impl,
  refl
end

lemma leads_to.abstract_basis {p q r : pred' (state α)}
  (T : r >~> -(p && - q) in s)
  (U : unless s p q)
  (P : (p && -q) ↦ (r || q) in s)
: p ↦ q in s :=
begin
  admit,
  -- revert U P,
  -- note H := often_imp_often.drec_on T _ _,
  -- induction T,
  -- apply @often_imp_often.drec_on,
end

end rules

open predicate

class system_sem (α : Type u) extends system α :=
  (ex : α → stream _ → Prop)
  (safety : ∀ s, ex s ⟹ saf_ex s)
  (inhabited : ∀s, ∃τ, ex s τ)
  (transient_sem : ∀ {s : α} {p q : pred' _} (τ : stream _),
         ex s τ →
         transient' s p q →
         ([]<>•p) τ → ([]<>-•q) τ)

def ex {α : Type u} [system_sem α] (s : α) := system_sem.ex s
def safety {α : Type u} [system_sem α] {s : α} := system_sem.safety s

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
  induction P with
        p'
        p q b T S B Bsem
        p q r P₀ P₁ H₀ H₁
        X p q P₀ H₀ x y z,
    -- trivial
  { apply temporal.leads_to_of_inf_often,
    simp, },
    -- transient and unless
  { intros i hp,
    note saf' := unless_sem' _ saf S (temporal.eventually_weaken _ hp),
    cases saf' with saf' saf',
    { assert T' : ([]<>-•(p && -q)) τ,
      { rw [-or_self (([]<>-•(p && -q)) τ),or_iff_not_imp],
        rw [p_not_eq_not,not_henceforth,not_eventually,p_not_p_not_iff_self],
        apply function.comp _ (inf_often_of_stable _),
        intro H,
        rw [-or_self (([]<>-•(p && -q)) τ)],
        apply or.imp_left (transient_sem τ sem T),
        rw [-p_or_to_fun,-inf_often_p_or],
        rw [not_init,p_not_p_and,p_not_p_not_iff_self,-init_p_or],
        apply inf_often_entails_inf_often' _ _ (inf_often_of_leads_to Bsem H),
        { apply p_or_entails_p_or_right,
          apply p_or_intro_right, }, },
      note T'' := (coincidence saf' (henceforth_drop i T')),
      apply eventually_entails_eventually _ _ (henceforth_str _ T''),
      intros τ',
      simp [init_to_fun],
      intro,
      begin [smt] eblast end },
    { apply saf', } },
    -- transitivity
  { apply leads_to_trans H₀ H₁ },
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
: ∀ {p q : pred' (state α)} (P : p >~> q in s),
    ([]<>•p ⟶ []<>•q) τ :=
begin
  apply @often_imp_often.drec α _ s _ _ _ _,
  { intros p q T,
    note Tsem : ([]<>•p ⟶ []<>-•-q) τ
              := system_sem.transient_sem _ sem T,
    rw [not_init,p_not_p_not_iff_self] at Tsem,
    apply Tsem },
  { intros p q r P₀ P₁,
    intros Lpq Lqr Hp,
    apply Lqr (Lpq Hp) },
  { intros t V lt wf p q P₀ S₀,
    apply inf_often_induction' V p q wf,
    { intro v,
      apply unless_sem_str _ (S₀ v),
      apply system_sem.safety _ _ sem, },
    { intro v,
      apply leads_to_sem (P₀ v) _ sem, } }
end

end

end system_sem

end unity
