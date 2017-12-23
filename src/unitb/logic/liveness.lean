
import data.stream

import unitb.category
import unitb.logic.safety

import util.logic
import util.meta.expr
import util.meta.tactic
import util.predicate

import temporal_logic

universe variables u v

namespace unitb

local attribute [instance] classical.prop_decidable

section connectors

open predicate

class system (α : Type u) extends has_safety α : Type (u+1) :=
   (transient : α → pred' σ → pred' σ → Prop)
   (init : α → pred' σ → Prop)
   (transient_false : ∀ {s} (p : pred' σ), transient s p False)
   (transient_antimono : ∀ {s : α} {p q p' q' : pred' σ},
         (p' ⟹ p) →
         (q' ⟹ q) →
         transient s p q →
         transient s p' q' )

parameters (α : Type u) [system α] (s : α)

def system.state := has_safety.σ α

parameters {α}

def transient (p : pred' (state α)) : Prop :=
system.transient s True p

def transient' (p q : pred' (state α)) : Prop :=
system.transient s p q

lemma system.transient_str {p q r : pred' (state α)}
  (H : r ⟹ q)
: transient' p q → transient' p r :=
system.transient_antimono (by refl) H

def init (p : pred' (state α)) : Prop :=
system.init s p

inductive leads_to : pred' (state α) → pred' (state α) → Prop
  | trivial {} : ∀ {p}, leads_to p True
  | basis' : ∀ {p q : pred' (state α)} r,
          transient' r (p ⋀ - q) →
          unless s p q →
          leads_to (p ⋀ -q) (r ⋁ q) →
          leads_to p q
  | trans : ∀ {p} q {r}, leads_to p q → leads_to q r → leads_to p r
  | disj : ∀ (t : Type u) (p : t → pred' (state α)) {q},
         (∀ i, leads_to (p i) q) →
         leads_to (∃∃ i, p i) q

attribute [trans] leads_to.trans

local notation x ` ↦ `:60 y ` in ` s := leads_to x y

inductive often_imp_often : pred' (state α) → pred' (state α) → Prop
  | transient : ∀ {p q}, transient' p (-q) → often_imp_often p q
  | trans : ∀ {p} q {r}, often_imp_often p q →
                         often_imp_often q r →
                         often_imp_often p r
  | disj : ∀ {p q r}, often_imp_often p r →
                      often_imp_often q r →
                      often_imp_often (p ⋁ q) r
  | induct : ∀ (t : Type) (V : state α → t) (lt : t → t → Prop)
         (wf : well_founded lt)
         {p q}
         (P : ∀ v, p ⋀ eq v ∘ V  ↦  flip lt v ∘ V ⋁ q  in  s)
         (S : ∀ v, unless s (eq v ∘ V) (flip lt v ∘ V ⋁ q)),
         often_imp_often p q

attribute [trans] often_imp_often.trans

end connectors

notation x `  ↦  `:60 y ` in ` s := leads_to s x y
notation x `  >~>  `:60 y ` in ` s := often_imp_often s x y

section conversion

parameter {α  : Type u}
parameter {α' : Type u}
parameter [system α]
parameter [system α']
parameter (f : state α' → state α)
parameters (s : α) (s' : α')
parameter (Tf : ∀ {p q}, transient' s p q → transient' s' (p '∘ f) (q '∘ f))
parameter (Uf : ∀ {p q}, unless s p q → unless s' (p '∘ f) (q '∘ f))

include Tf Uf

lemma leads_to.subst {p q}
  (H : p ↦ q in s)
: (p '∘ f) ↦ (q '∘ f) in s' :=
begin
  induction H,
  case leads_to.trivial p
  { apply leads_to.trivial },
  case leads_to.basis' p q b t u P₀ P₁
  { apply leads_to.basis' (b '∘ f),
    { specialize Tf t, simp at Tf, simp [Tf], },
    { apply Uf u },
    { simp at P₁, simp [P₁], }, },
  case leads_to.trans p q r Pa₀ Pa₁ Pb₀ Pb₁
  { apply leads_to.trans (q '∘ f) Pb₀ Pb₁, },
  case leads_to.disj t p q Pa Pb
  { simp, apply leads_to.disj t (λ x, p x '∘ f),
    intro, apply Pb, },
end

lemma often_imp_often.subst {p q}
  (H : p >~> q in s)
: (p '∘ f) >~> (q '∘ f) in s' :=
begin
  induction H,
  case often_imp_often.transient p q T
  { specialize Tf T, simp at Tf,
    apply often_imp_often.transient Tf },
  case often_imp_often.trans p q r _ _ Pb₀ Pb₁
  { apply often_imp_often.trans _ Pb₀ Pb₁ },
  case often_imp_often.induct t V lt wf p q P S
  { apply often_imp_often.induct t (V ∘ f) lt wf,
    { intro v, have := leads_to.subst f s s' @Tf @Uf (P v),
      simp at this, apply this },
    { intro v, specialize Uf (S v),
      simp at Uf, apply Uf } },
  case often_imp_often.disj p q r P₀ P₁
  { have := often_imp_often.disj ih_1 ih_2, simp [this] }
end

end conversion

open predicate

section rules

parameters {α : Type u} [system α]
parameter {s : α}

lemma leads_to.basis {p q : pred' (state α)}
  (h₀ : transient s (p ⋀ - q))
  (h₁ : unless s p q)
: leads_to s p q :=
begin
  apply leads_to.basis' _ h₀ h₁,
  rw True_p_or, apply leads_to.trivial
end

parameter s

theorem leads_to.imp {p q : pred' (state α)}
   (h : p ⟹ q)
   : p ↦ q in s :=
begin
  apply leads_to.basis,
  { have h' : (p ⋀ -q) = False,
    { lifted_pred [not_not_iff_self] using h,
      assumption, },
    rw h',
    apply system.transient_false },
  apply unless_imp h
end

@[refl]
theorem leads_to_refl {p : pred' (state α)}
: p ↦ p in s :=
by { apply leads_to.imp, refl }

parameter {s}

instance category_leads_to : disjunctive (leads_to s) :=
  { ident := @leads_to_refl
  , comp := λ p q r P₀ P₁, leads_to.trans _ P₁ P₀
  , assoc := by { intros, refl }
  , left_ident := by { intros, refl }
  , disj' := @leads_to.disj _ _ _
  , right_ident := by { intros, refl }
  , imp := @leads_to.imp
  , imp_comp_imp_eq_imp_trans := by { intros, refl }
  , imp_self_eq_ident := by { intros, refl }
  , disj_imp_imp := by { intros, refl }
  , select_left_disj := by { intros, refl }
  , comp_over_disj_right := by { intros, refl }
  , disj_flip := by { intros, refl } }

theorem leads_to.antimono_left (q : pred' (state α)) {p r : pred' (state α)}
  (H  : p ⟹ q)
  (P₀ : q  ↦ r in s)
: p ↦ r in s :=
unitb.antimono_left _ _ H P₀

theorem leads_to.mono_right
  (q : pred' (state α)) {p r : pred' (state α)}
  (H  : q ⟹ r)
  (P₀ : p  ↦ q in s)
: p ↦ r in s :=
lifted_pred.mono_right _ _ H P₀

theorem leads_to.monotonicity
  {p p' q q' : pred' (state α)}
  (Hp : p' ⟹ p)
  (Hq : q  ⟹ q')
  (P₀ : p  ↦ q in s)
: p' ↦ q' in s :=
monotonicity _ Hp Hq P₀

lemma leads_to.disj_rng {t : Type u} {p : t → pred' (state α)} {q} {r : t → Prop}
  (h : ∀ i, r i → p i ↦ q in s)
: (∃∃ i, (r i) ⋀ p i) ↦ q in s :=
unitb.disj_rng _ h

theorem leads_to.disj' {p q r : pred' (state α)}
  (Pp : p ↦ r in s)
  (Pq : q ↦ r in s)
: p ⋁ q ↦ r in s :=
finite_disjunctive.disj _ Pp Pq

theorem leads_to.gen_disj {p q r₀ r₁ : pred' (state α)}
  (Pp : p ↦ r₀ in s)
  (Pq : q ↦ r₁ in s)
: p ⋁ q ↦ r₀ ⋁ r₁ in s :=
unitb.gen_disj _ Pp Pq

theorem leads_to.gen_disj' {t : Type u} {p q : t → pred' (state α)}
  (P : ∀ x, p x ↦ q x in s)
: (∃∃ x, p x) ↦ (∃∃ x, q x) in s :=
unitb.gen_disj' _ P

theorem leads_to.cancellation
  {p : pred' (state α)} (q : pred' (state α))
  {r b : pred' (state α)}
  (P₀ : p ↦ q ⋁ b in s)
  (P₁ : q ↦ r ⋁ b in s)
: p ↦ r ⋁ b in s :=
unitb.cancellation _ q P₀ P₁

theorem leads_to.cancellation'
  {p : pred' (state α)} (q : pred' (state α))
  {r b : pred' (state α)}
  (P₀ : p ↦ q ⋁ b in s)
  (P₁ : q ↦ r in s)
: p ↦ r ⋁ b in s :=
unitb.cancellation' _ q P₀ P₁

theorem leads_to.induction' {β : Type u} {lt' : β → β → Prop}
  (wf : well_founded lt')
  (V : state α → β)
  {p q : pred' (state α)}
  (P : ∀ v, p ⋀ (eq v ∘ V)  ↦  p ⋀ (flip lt' v ∘ V) ⋁ q  in  s)
: p ↦ q in s :=
unitb.induction _ wf V P

def rel : Type u := state α → state α → Prop

theorem leads_to.induction {lt' : rel} (wf : well_founded lt')
  {p q : pred' (state α)}
  (P : ∀ v : state α, p ⋀ (eq v : pred' $ state α)  ↦  p ⋀ (flip lt' v : pred' $ state α) ⋁ q  in  s)
: p ↦ q in s :=
leads_to.induction' wf _ P

theorem leads_to.PSP {p q r b : pred' (state α)}
  (P : p ↦ q in s)
  (S : unless s r b)
: p ⋀ r  ↦  (q ⋀ r) ⋁ b in s :=
begin
  induction P with p p₀ q₀ b₀ t₀ u₀ P PSP₀
         p₁ q₁ r₁ PP₀ PP₁,
  { apply leads_to.imp,
    apply p_and_entails_of_entails_right,
    apply entails_p_or_of_entails_left,
    simp, },
  { apply leads_to.basis' b₀,
    { apply system.transient_str _ _ t₀,
      lifted_pred, begin [smt] intros end },
    { have H : unless s r (r ⋁ b),
      { apply unless_imp, propositional, },
      have H' : unless s p₀ (q₀ ⋁ b),
      { apply unless_weak_rhs _ u₀,
        propositional },
      have H'' := unless_conj_gen u₀ S,
      apply unless_weak_rhs _ H'',
      lifted_pred, begin [smt] intros, break_asms, end },
    { apply leads_to.monotonicity _ _ PSP₀,
      { lifted_pred, begin [smt] intros, end },
      { lifted_pred, begin [smt] intros, break_asms end }, } },
  { have H := leads_to.cancellation _ ih_1 ih_2,
    apply H },
  { apply leads_to.antimono_left (∃∃i, p_1 i ⋀ r),
    { lifted_pred only [p_and_over_p_exists_right],
      exact id, },
    apply leads_to.disj, intro i,
    apply ih_1 i, },
end

lemma leads_to.trading {p q r : pred' (state α)}
  (P : p ⋀ -q ↦ r in s)
: p ↦ q ⋁ r in s :=
begin
  have P₀ : p ⋀ q ↦ q in s,
  { apply leads_to.imp,
    apply p_and_elim_right },
  have P₁ := leads_to.gen_disj P₀ P,
  rw [←  p_and_over_or_left] at P₁,
  simp at P₁,
  apply P₁,
end

lemma True_leads_to_True
: True ↦ True in s :=
leads_to.trivial

lemma leads_to.completion_a {p p' q q' : pred' (state α)} {b : pred' (state α)}
  (P₀ : p  ↦ q  in s)
  (P₁ : p' ↦ q' in s)
  (S₀ : unless s q  b)
  (S₁ : unless s q' b)
: p ⋀ p' ↦ (q ⋀ q') ⋁ b in s :=
begin
  revert p' q' b,
  induction P₀
  ; intros p' q' b P₁ S₀ S₁,
  case leads_to.trivial p₀
  { apply leads_to.monotonicity _ _ P₁,
    { propositional, },
    { propositional, }, },
  case leads_to.basis' p₀ q₀ b₀ T S₂ P₂
  { -- have P₃ : p₀ ⋀ p' ↦ _ in s,
    apply leads_to.basis' (b₀ ⋀ q'),
    { apply system.transient_antimono _ _ T,
      { propositional, },
      { lifted_pred [p_not_p_and,p_not_p_or],
        intros, split,
        -- by_contradiction,
        -- classical_simp,
        { begin [smt] intros, end },
        { admit }, } },
    { admit },
    { admit }, },
  case leads_to.trans pp qq rr P₂ P₃
  { rw [← p_or_self b,p_or_assoc],
    have H' : pp ⋀ p'  ↦  rr ⋀ q' ⋁ b ⋁ b in s,
    { apply leads_to.cancellation' (qq ⋀ q'),
      { have h : qq ⋀ q' ⋁ b = qq ⋀ q' ⋁ (qq ⋀ q' ⋁ b),
        { admit },
        rw h,
        apply ih_1,
        { apply P₁ },
        { apply unless_imp, admit, },
        { apply unless_weak_rhs _ S₁,
          propositional, }, },
      { apply ih_2,
        { refl },
        { apply S₀ },
        { apply S₁ }, } },
    apply leads_to.mono_right _ _ H',
    propositional, },
  case leads_to.disj t pp qq P₂
  { rw p_and_over_p_exists_right,
    apply leads_to.disj,
    intro i, apply ih_1 _ P₁ S₀ S₁, }
end

lemma leads_to.completion_b {p p' q q' : pred' (state α)} {b : pred' (state α)}
  (P₀ : p  ↦ q  ⋁ b in s)
  (P₁ : p' ↦ q' ⋁ b in s)
  (S₀ : unless s q  b)
  (S₁ : unless s q' b)
: p ⋀ p' ↦ (q ⋀ q') ⋁ b in s :=
begin
  have H : unless s b b := unless_refl _,
  have H₀ : unless s (q  ⋁ b) b,
  { have H' := unless_disj' S₀ H,
    simp at H', apply H', },
  have H₁ : unless s (q' ⋁ b) b,
  { have H' := unless_disj' S₁ H,
    simp at H', apply H', },
  have H₂ : p ⋀ p' ↦ ( (q ⋁ b) ⋀ (q' ⋁ b) ) ⋁ b in s,
  { apply leads_to.completion_a P₀ P₁ H₀ H₁, },
  apply leads_to.mono_right _ _ H₂,
  { lifted_pred,
    begin [smt] intros, break_asms, end },
end

lemma leads_to.completion {n : ℕ} {p q : fin n → pred' (state α)} {b : pred' (state α)}
  (P : ∀ i, p i ↦ q i ⋁ b in s)
  (S : ∀ i, unless s (q i) b)
: (∀∀ i, p i) ↦ (∀∀ i, q i) ⋁ b in s :=
begin
  revert p q,
  induction n with n IH ; intros p q P S,
  { simp [p_forall_fin_zero] },
  { simp [p_forall_split_one],
    apply leads_to.completion_b,
    { apply P },
    { apply IH,
      { intro, apply P },
      { intro, apply S }, },
    { apply S },
    { apply forall_unless,
      intro, apply S }, },
end
open predicate

lemma often_imp_often.basis {p q}
  (h : p ↦ q in s)
: p >~> q in s :=
begin
  let f := (λ _ : state α, ()),
  have H : ∀ (v : unit), ↑(flip empty_relation v ∘ f : state α → Prop) = @False (state α),
  { intros, refl },
  have H' : ∀ (v : unit), ↑(eq v ∘ f : state α → Prop) = @True (state α),
  { intros, funext x,
    apply iff_true_intro (unit_eq v (f x)), },
  apply often_imp_often.induct _ f _ empty_wf
  ; intro,
  { simp [H,H',h], },
  { rw [H'],
    apply True_unless }
end

@[refl]
lemma often_imp_often_refl {p}
: p >~> p in s :=
begin
  apply often_imp_often.basis,
  refl
end

lemma often_imp_often.imp {p q}
  (H : p ⟹ q)
: p >~> q in s :=
by { apply often_imp_often.basis, apply leads_to.imp _ H, }

lemma True_often_imp_often_True
: True >~> True in s :=
by refl

instance often_imp_often_fin_disj : finite_disjunctive (often_imp_often s) :=
 { ident := by { intro, refl }
 , comp  := by { introv h₀ h₁, apply often_imp_often.trans _ h₁ h₀ }
 , left_ident  := by { intros, refl }
 , right_ident := by { intros, refl }
 , assoc := by { intros, refl }
 , imp :=
   begin
     introv P,
     apply often_imp_often.imp P,
   end
 , imp_self_eq_ident := by { intros, refl }
 , imp_comp_imp_eq_imp_trans := by { intros, refl }
 , disj := @often_imp_often.disj _ _ s
 , disj_flip := by { intros, refl }
 , disj_imp_imp := by { intros, refl }
 , select_left_disj := by { intros, refl }
 , comp_over_disj_right := by { intros, refl } }
end rules

open predicate temporal

class system_sem (α : Type u) extends system α :=
  (ex : α → cpred _)
  (safety : ∀ s, ex s ⟹ saf_ex s)
  (inhabited : ∀s, ∃τ, τ ⊨ ex s)
  (init_sem : ∀ {s : α} {p : pred' _},
         init s p →
         ⊩ ex s ⟶ •p)
  (transient_sem : ∀ {s : α} {p q : pred' _},
         transient' s p q →
         ⊩ ex s ⟶ ◻◇•p ⟶ ◻◇-•q)

namespace system_sem

variables {α : Type u}

open temporal

section

variable [system_sem α]

set_option trace.check true

lemma leads_to_sem {s : α} {p q : pred' (state α)}
    {Γ : cpred _}
    (P : p ↦ q in s)
    (sem : Γ ⊢ ex s)
: Γ ⊢ •p ~> •q :=
begin
  have saf : Γ ⊢ saf_ex s := system_sem.safety s Γ sem,
  induction P ,
  case leads_to.trivial
  { apply temporal.leads_to_of_inf_often, simp, },
  case leads_to.basis' p q b T S B Bsem
  begin [temporal]
    have := transient_sem T Γ sem,
    clear sem,
    henceforth,
    intros hp,
    have saf' : _ ⋁ _ := unless_sem saf S hp, -- (temporal.eventually_weaken _ hp),
    cases saf' with saf' saf',
    { have T' : ◻◇-•(p ⋀ -q),
      -- timetac "have T'"
      { rw [← p_or_self (◻◇-•(p ⋀ -q))],
        focus_left with h, simp [p_not_p_not_iff_self] at h,
        suffices : ◻◇-•(p ⋀ -q) ⋁ ◻◇•q,
        { cases this with this this ; revert this
          ; persistent ; monotonicity
          ; lifted_pred,
          show _, { intros, auto } },
        focusing_left
        { apply this _,  clear this },
        rw ← inf_often_p_or,
        simp at Bsem,
        replace h : (◻◇(•p ⋀ -•q)) := inf_often_of_stable (•p ⋀ -•q) Γ h,
        apply inf_often_of_leads_to Bsem h, },
      have T'' := (coincidence' saf' T'),
      henceforth at T'', revert T'', persistent,
      monotonicity, lifted_pred,
      show _, { intros, auto } },
    { assumption, }
  end,
  case leads_to.trans p q r P₀ P₁ H₀ H₁
  { apply leads_to_trans H₀ H₁ },
  case leads_to.disj X p' q' P₀ H₀ x y z
  begin [temporal]
    clear sem,
    henceforth,
    rw [init_exists,p_exists_p_imp ],
    intros x hp,
    apply H₀ x hp,
  end
end

end

-- section

-- variable [system_sem α]

-- lemma often_imp_often_sem'
--     {s : α}
--     (τ : stream _)
--      (sem : ex s τ)
--   {p q : pred' (state α)}
--   (P : p >~> q in s)
-- : (◻◇•p ⟶ ◻◇•q) τ :=
-- begin
--   induction P,
--   case often_imp_often.transient p q T
--   { have Tsem : (◻◇•p ⟶ ◻◇-•-q) τ
--               := system_sem.transient_sem _ sem T,
--     rw [not_init,p_not_p_not_iff_self] at Tsem,
--     apply Tsem },
--   case often_imp_often.trans p q r P₀ P₁ Lpq Lqr
--   { intro Hp,
--     apply Lqr (Lpq Hp) },
--   case often_imp_often.induct  t V lt wf p q P₀ S₀
--   { apply inf_often_induction' V p q wf,
--     { intro v,
--       apply unless_sem_str _ (S₀ v),
--       apply system_sem.safety _ _ sem, },
--     { intro v,
--       apply leads_to_sem (P₀ v) _ sem, } },
--   case often_imp_often.disj p q r P₀ P₁
--   { intros H,
--     rw [init_p_or,inf_often_p_or] at H,
--     cases H with H H,
--     { apply ih_1 H },
--     { apply ih_2 H } }
-- end

-- end

end system_sem

end unitb
