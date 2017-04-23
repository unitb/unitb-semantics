
import unity.logic
import unity.temporal

import util.logic

universe variables u u'
namespace nondet

section nondet

open predicate

parameter {α : Type}

@[reducible]
def pred := α → Prop

structure event : Type :=
  (coarse_sch : pred)
  (fine_sch : pred)
  (step : ∀ s, coarse_sch s → fine_sch s → α → Prop)
  (fis : ∀ s CS FS, ∃ s', step s CS FS s')

def event.step_of (e : event) (σ σ' : α) : Prop :=
∃ Hc Hf, e.step σ Hc Hf σ'

structure prog : Type 2 :=
  (lbl : Type)
  (first : α → Prop)
  (first_fis : ∃ s, first s)
  (event' : lbl → event)

def skip : event :=
{ coarse_sch := True
, fine_sch := True
, step := λ s _ _ s', s = s'
, fis := take s _ _, ⟨s,rfl⟩ }

def prog.event (s : prog) : option s.lbl → event
  | none := skip
  | (some e) := s^.event' e

def prog.init (s : prog) (p : pred) : Prop
:= s^.first ⟹ p

def prog.guard  (s : prog) (e : option s.lbl) : α → Prop :=
(s^.event e)^.coarse_sch && (s^.event e)^.fine_sch

def prog.coarse_sch_of (s : prog) (act : option s.lbl) : α → Prop :=
(s.event act).coarse_sch

@[simp]
lemma prog.coarse_sch_of_none (s : prog)
: s.coarse_sch_of none = True :=
by refl

def prog.fine_sch_of (s : prog) (act : option s.lbl) : α → Prop :=
(s.event act).fine_sch

@[simp]
lemma prog.fine_sch_of_none (s : prog)
: s.fine_sch_of none = True :=
by refl

def prog.take_step (s : prog)
: ∀ (e : option s.lbl) (σ : α), s^.coarse_sch_of e σ → s^.fine_sch_of e σ → α → Prop
  | none σ _ _ := λ σ', σ = σ'
  | (some e) σ Hc Hf := (s^.event e)^.step σ Hc Hf

def prog.step_of (s : prog) (act : option s.lbl) : α → α → Prop :=
(s.event act).step_of

def is_step (s : prog) (σ σ' : α) : Prop :=
∃ ev, s.step_of ev σ σ'

open temporal

lemma step_of_none  (s : prog) : s.step_of none = eq :=
begin
  unfold prog.step_of prog.event skip,
  apply funext, intro σ,
  apply funext, intro σ',
  unfold event.step_of,
  unfold event.coarse_sch event.fine_sch event.step,
  unfold True lifted₀,
  simp [exists_true],
end

lemma is_step_exists_event  (s : prog)
 : temporal.action (is_step s) = (⟦ eq ⟧ || ∃∃ ev : s.lbl, ⟦ (s.event' ev).step_of ⟧) :=
begin
  simp [exists_action,or_action],
  apply congr_arg,
  apply funext, intro σ,
  apply funext, intro σ',
  unfold is_step,
  simp [exists_option],
  rw or_congr,
  { simp [step_of_none] },
  { apply exists_congr, intro e,
    refl }
end

lemma is_step_exists_event'  (s : prog)
 : temporal.action (is_step s) = (∃∃ ev : option s.lbl, ⟦ s.step_of ev ⟧) :=
begin
  simp [exists_action,or_action],
  apply congr_arg,
  apply funext, intro σ,
  apply funext, intro σ',
  unfold is_step,
  simp [exists_option],
end

instance : unity.has_safety prog :=
  { σ := α
  , step := is_step }

structure prog.ex (s : prog) (τ : stream α) : Prop :=
    (init : s^.first (τ 0))
    (safety : unity.saf_ex s τ)
    (liveness : ∀ e, (<>[]• s^.coarse_sch_of e) τ →
                     ([]<>• s^.fine_sch_of e) τ →
                     ([]<> ⟦ s.step_of e ⟧) τ)

structure prog.falsify (s : prog) (act : option s.lbl) (p : pred' α) : Prop :=
  (enable : p ⟹ s^.coarse_sch_of act)
  (schedule : prog.ex s ⟹ (<>[]•p ⟶ []<>• s^.fine_sch_of act) )
  (negate' : ⦃ •p ⟶ ⟦ s^.step_of act ⟧ ⟶ ⊙-•p ⦄)

open temporal

lemma prog.falsify.negate
   {s : prog} {act : option s.lbl} {p : pred}
:  prog.falsify s act p
→  •p && ⟦ s^.step_of act ⟧ ⟹ <>-•p :=
begin
  intros h₀ τ h₁,
  note h₂ := h₀.negate' _ h₁^.left h₁^.right,
  unfold eventually p_not init,
  existsi 1,
  apply h₂,
end

def prog.transient (s : prog) (p : pred' α) : Prop :=
∃ (act : option s.lbl), prog.falsify s act p

section theorems

variable (s : prog)

open prog
open event

theorem prog.transient_false : transient s False :=
begin
  unfold prog.transient,
  existsi none,
  apply falsify.mk,
  { intros σ h, cases h },
  { intros τ i h₀ h₁,
    simp at h₀,
    cases h₀, },
  { intros σ h₀ h₁, cases h₀ with h₂ }
end

def prog.transient_str : ∀ (s : prog) {p q : α → Prop}, (∀ (i : α), p i → q i) → prog.transient s q → prog.transient s p :=
begin
  intros s p q h,
  unfold transient,
  apply exists_imp_exists,
  intros e h',
  apply falsify.mk,
  { apply forall_imp_forall _ h'.enable,
    intro x,
    apply imp_imp_imp_left,
    apply h },
  { apply forall_imp_forall _ h'.schedule,
    intro τ,
    apply forall_imp_forall _,
    intro j,
    apply p_imp_p_imp_p_imp_left _,
    apply ex_map,
    apply hence_map,
    apply init_map,
    apply h },
  { apply forall_imp_forall _ h'.negate',
    intro τ,
    apply imp_mono _ _,
    { apply h },
    apply imp_imp_imp_right _,
    apply next_imp_next _ _,
    apply entail_contrapos,
    apply init_map,
    apply h }
end

end theorems

instance prog_is_system : unity.system prog :=
{ σ := α
, transient := @prog.transient
, step := is_step
, init   := prog.init
, transient_false := prog.transient_false
, transient_str := prog.transient_str }

section soundness

open prog

variables {s : prog} {p : pred' α}
variables (T₀ : prog.transient s p)
include T₀
variables (τ : stream α)

lemma transient.semantics (h : ex s τ)
: ([]<>-•p) τ :=
begin
  cases (temporal.em' (•p) τ) with h_p ev_np,
  { unfold prog.transient at T₀,
    cases T₀ with ev T₀,
    assert Hc : (<>[]•s.coarse_sch_of ev) τ,
    { apply ex_map _ _ h_p,
      apply hence_map _ ,
      apply init_map _ ,
      apply T₀.enable },
    assert Hf : ([]<>•s.fine_sch_of ev) τ,
    { apply T₀.schedule _ h h_p, },
    note act := coincidence h_p (h.liveness ev Hc Hf),
    rw [-eventually_eventually],
    apply hence_map _ _ act,
    apply ex_map _ ,
    apply T₀.negate },
  { apply ev_np },
end

end soundness

-- instance {α} [sched lbl] : system_sem (prog lbl) :=
instance : unity.system_sem prog :=
  { (_ : unity.system prog) with
    ex := prog.ex
  , safety := @prog.ex.safety _
  , inhabited := sorry
  , transient_sem := @transient.semantics }

open unity

def unless_except (s : prog) (p q : pred' α) (evts : set event) : Prop :=
unless' s p q (λ σ σ', ∃ e, e ∈ evts ∧ event.step_of e σ σ')

theorem unless_except_rule {s : prog} {p q : pred' α} (exp : set event)
  (ACT : ∀ (e : s.lbl) σ Hc Hf σ',
        ¬ s.event' e ∈ exp
      → (s.event' e).step σ Hc Hf σ'
      → p σ → ¬ q σ → p σ' ∨ q σ')
: unless_except s p q exp :=
begin
  intros σ σ' STEP EXP H,
  cases H with Hp Hq,
  unfold step has_safety.step is_step at STEP,
  cases STEP with e STEP,
  unfold prog.step_of event.step_of at STEP,
  cases STEP with Hc STEP,
  cases STEP with Hf STEP,
  cases e with e,
  { unfold prog.event skip event.step at STEP,
    subst σ',
    left, apply Hp },
  { apply ACT e _ Hc Hf _ _ STEP Hp Hq,
    intro Hin,
    apply EXP,
    clear ACT EXP,
    unfold prog.step_of event.step_of prog.event,
    existsi s.event' e, split, apply Hin,
    existsi Hc, existsi Hf,
    apply STEP }
end

theorem unless_rule {s : prog} {p q : pred' α}
  (ACT : ∀ (e : s.lbl) σ Hc Hf σ', (s.event' e).step σ Hc Hf σ' → p σ → ¬ q σ → p σ' ∨ q σ')
: unless s p q :=
begin
  rw unless_eq_unless_except,
  assert H : unless_except s p q ∅,
  { apply unless_except_rule,
    intros,
    apply ACT
    ; try { assumption }, },
  unfold unless_except at H,
  assert Heq : (λ (σ σ' : α), ∃ (e : event), e ∈ (∅ : set event) ∧ e.step_of σ σ')
             = (λ (_x : α), False),
  { apply funext, intro,
    apply funext, intro,
    simp,
    apply eq_false_of_not_eq_true,
    apply eq_true_intro,
    intro H,
    cases H with e H,
    cases H with H₀ H₁,
    apply H₁, },
  apply iff.elim_left _ H,
  rw iff_eq_eq,
  apply congr_arg _ Heq,
end

theorem transient_rule {s : prog} {p : pred' α} (ev : option s.lbl)
   (EN : p ⟹ s.coarse_sch_of ev)
   (FLW : leads_to s (p && s.coarse_sch_of ev) (s.fine_sch_of ev))
   (NEG : ∀ σ σ', p σ → s.step_of ev σ σ' → ¬p σ')
: s.transient p :=
begin
  unfold prog.transient,
  existsi ev,
  apply falsify.mk,
    -- enablement
  { apply EN },
    -- follow
  { intros τ sem H,
    apply inf_often_of_leads_to (system_sem.leads_to_sem FLW _ sem),
    note H' := inf_often_of_stable _ H,
    apply hence_map _ _ H',
    apply ex_map _ ,
    apply init_map _ ,
    intros σ Hp,
    apply and.intro Hp,
    apply EN _ Hp },
    -- negation
  { intros σ Hp Hact,
    apply NEG _ _ Hp Hact }
end

end nondet

end nondet
