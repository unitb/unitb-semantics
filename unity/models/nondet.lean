
import unity.logic
import unity.safety
import unity.scheduling
import unity.temporal

import util.logic

universe variables u u'
namespace nondet

section nondet

open predicate unity

parameter α : Type

@[reducible]
def pred := α → Prop

structure event : Type :=
  (coarse_sch : pred)
  (fine_sch : pred)
  (step : ∀ s, coarse_sch s → fine_sch s → pred)
  (fis : ∀ s CS FS, ∃ s', step s CS FS s')

structure program : Type 2 :=
  (lbl : Type)
  (lbl_is_sched : scheduling.sched lbl)
  (first : α → Prop)
  (first_fis : ∃ s, first s)
  (event' : lbl → event)

parameter {α}

def event.step_of (e : event) (σ σ' : α) : Prop :=
∃ Hc Hf, e.step σ Hc Hf σ'

def skip : event :=
{ coarse_sch := True
, fine_sch := True
, step := λ s _ _ s', s = s'
, fis := take s _ _, ⟨s,rfl⟩ }

def program.event (s : program) : option s.lbl → event
  | none := skip
  | (some e) := s^.event' e

def program.init (s : program) (p : pred) : Prop
:= s^.first ⟹ p

def program.guard  (s : program) (e : option s.lbl) : α → Prop :=
(s^.event e)^.coarse_sch && (s^.event e)^.fine_sch

def program.guard_none_holds (s : program) (σ : α)
: s.guard none σ :=
⟨trivial,trivial⟩

def program.coarse_sch_of (s : program) (act : option s.lbl) : α → Prop :=
(s.event act).coarse_sch

@[simp]
lemma program.coarse_sch_of_none (s : program)
: s.coarse_sch_of none = True :=
by refl

def program.fine_sch_of (s : program) (act : option s.lbl) : α → Prop :=
(s.event act).fine_sch

@[simp]
lemma program.fine_sch_of_none (s : program)
: s.fine_sch_of none = True :=
by refl

def program.take_step (s : program)
: ∀ (e : option s.lbl) (σ : α), s^.coarse_sch_of e σ → s^.fine_sch_of e σ → α → Prop
  | none σ _ _ := λ σ', σ = σ'
  | (some e) σ Hc Hf := (s^.event e)^.step σ Hc Hf

def program.step_of (s : program) (act : option s.lbl) : α → α → Prop :=
(s.event act).step_of

def is_step (s : program) (σ σ' : α) : Prop :=
∃ ev, s.step_of ev σ σ'

open temporal

lemma step_of_none  (s : program) : s.step_of none = eq :=
begin
  unfold program.step_of program.event skip,
  apply funext, intro σ,
  apply funext, intro σ',
  unfold event.step_of,
  unfold event.coarse_sch event.fine_sch event.step,
  unfold True lifted₀,
  simp [exists_true],
end

lemma is_step_exists_event  (s : program)
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

lemma is_step_exists_event'  (s : program)
 : temporal.action (is_step s) = (∃∃ ev : option s.lbl, ⟦ s.step_of ev ⟧) :=
begin
  simp [exists_action,or_action],
  apply congr_arg,
  apply funext, intro σ,
  apply funext, intro σ',
  unfold is_step,
  simp [exists_option],
end

lemma is_step_inst' (s : program) (ev : option s.lbl)
: ⟦ s.step_of ev ⟧ ⟹ ⟦ is_step s ⟧ :=
begin
  rw is_step_exists_event',
  intros τ, simp,
  apply exists.intro ev,
end

def pair  (σ σ' : α) : stream α
  | 0 := σ
  | (nat.succ i) := σ'

lemma is_step_inst {s : program} {ev : option s.lbl} {σ σ' : α}
  (h : s.step_of ev σ σ')
: is_step s σ σ' :=
begin
  change ⟦ is_step s ⟧ (pair σ σ'),
  apply is_step_inst' _ ev,
  apply h
end

local attribute [instance] classical.prop_decidable

noncomputable def program.object_mch (p : program)
: scheduling.unity.target_mch (option p.lbl) :=
{ σ := α
, s₀ := classical.some p.first_fis
, req := λ s, { l | p.guard l s }
, req_nemp := take x,
  begin
    apply @set.ne_empty_of_mem _ _ none,
    simp [mem_set_of], exact ⟨trivial,trivial⟩,
  end
, next := λ l s (h : p.guard l s),
                 classical.some ((p.event l).fis s h.left h.right)
                  }

instance : unity.has_safety program :=
  { σ := α
  , init  := program.first
  , step := is_step }

structure program.falsify (s : program) (act : option s.lbl) (p q : pred' α) : Prop :=
  (enable : s ⊢ q ⟶ s.coarse_sch_of act)
  (schedule : s ⊢ p ⟶ s^.fine_sch_of act)
  (negate' : s ⊢ λ σ, ∀ σ', q σ → s.step_of act σ σ' → ¬ q σ')

def program.transient (s : program) (p q : pred' α) : Prop :=
∃ (act : option s.lbl), s.falsify act p q

open temporal has_mem scheduling.unity function

lemma object_mch_action_eq_step_of (s : program) (e : option s.lbl)
: •mem e ∘ s.object_mch.req && action (s.object_mch.action e) ⟹ action (s.step_of e) :=
begin
  rw [init_eq_action,action_and_action],
  apply action_entails_action,
  intro σ, intro σ',
  unfold comp program.object_mch,
  unfold  target_mch.action target_mch.next target_mch.req,
  simp [mem_set_of],
  intro h, cases h with h₀ h₁,
  cases h₁ with P h₁,
  rw [h₁],
  unfold program.step_of event.step_of program.object_mch._proof_3,
  existsi h₀.left, existsi h₀.right,
  apply classical.some_spec,
end

lemma mem_object_req_eq_csch_and_fsch (s : program) (e : option s.lbl)
: mem e ∘ s.object_mch.req = s.coarse_sch_of e && s.fine_sch_of e :=
rfl

lemma program.falsify.negate
   {s : program} {act : option s.lbl} {p q : pred}
:  s.falsify act p q
→  •unity.reachable s && •q && ⟦ s^.step_of act ⟧ ⟹ <>-•q :=
begin
  intros h₀ τ h₁,
  cases h₁ with Hr Hstep,
  cases Hr with Hr Hq,
  note h₂ := h₀.negate' _ Hr _ Hq Hstep,
  unfold eventually p_not init,
  existsi 1,
  apply h₂,
end


section theorems

variable (s : program)

open program
open event

theorem program.transient_false {p : pred}
: transient s p False :=
begin
  unfold program.transient,
  existsi none,
  apply falsify.mk,
  { intros σ h _, apply trivial },
  { intros τ i _,
    apply trivial, },
  { intros σ _ _ h₀, cases h₀ },
end

def program.transient_antimono (s : program) {p q p' q' : pred}
  (hp : s ⊢ p' ⟶ p)
  (hq : s ⊢ q' ⟶ q)
: s.transient p q → s.transient p' q' :=
begin
  unfold transient,
  apply exists_imp_exists,
  intros e h',
  apply falsify.mk,
  { apply holds_impl_trans s _ hq h'.enable, },
  { apply holds_impl_trans s _ hp h'.schedule, },
  { intros σ hr σ',
    note hp' := hp _ hr,
    note hq' := hq _ hr,
    apply imp_mono _ _ (h'.negate' _ hr σ'),
    { apply hq' },
    { apply imp_imp_imp_right' _,
      intro hs,
      note hr' := reachable.step σ σ' hr (is_step_inst hs),
      apply mt (hq _ hr'), }, }
end

end theorems

instance prog_is_system : unity.system program :=
{ σ := α
, init := first
, step  := is_step
, transient := program.transient
, transient_false := λ s p, program.transient_false s
, transient_antimono := nondet.program.transient_antimono }

section soundness

structure program.ex (s : program) (τ : stream α) : Prop :=
    (init : s^.first (τ 0))
    (safety : unity.saf_ex s τ)
    (liveness : ∀ e, (<>[]• s^.coarse_sch_of e) τ →
                     ([]<>•s.fine_sch_of e) τ →
                     ([]<>⟦ s.step_of e ⟧) τ)

open program

variables {s : program} {p q : pred' α}
variables (τ : stream α)
variables (h : ex s τ)
include h

lemma init_sem
  (I₀ : init s p)
: (•p) τ :=
begin
  unfold temporal.init,
  unfold init program.init at I₀,
  apply I₀,
  apply h.init,
end

lemma transient.semantics
  (T₀ : s.transient p q)
: ([]<>•p) τ → ([]<>-•q) τ :=
begin
  cases (temporal.em' (•q) τ) with h_q ev_nq,
  { unfold program.transient at T₀,
    cases T₀ with ev T₀,
    assert Hc : (<>[]•s.coarse_sch_of ev) τ,
    { apply stable_entails_stable' _ _ h_q,
      apply T₀.enable },
    intro Hp,
    assert Hf : ([]<>•s.fine_sch_of ev) τ,
    { apply inf_often_entails_inf_often' _ _ Hp,
      apply T₀.schedule, },
    note live := h.liveness ev Hc Hf,
    note act := coincidence h_q (h.liveness ev Hc Hf),
    rw [-eventually_eventually],
    apply inf_often_entails_inf_often _ _ act,
    apply entails_imp_entails_left _ T₀.negate,
    refl, },
  { intro, apply ev_nq },
end

end soundness

open scheduling nat list

noncomputable def program.first_state (s : program) := (classical.some s.first_fis)

open unity has_mem

lemma program.witness (s : program)
: ∃ (τ : stream α), s.ex τ :=
begin
  note _inst := s.lbl_is_sched,
  apply exists_imp_exists _ (sched.sched_str s.object_mch),
  intros τ h,
  apply ex.mk,
  { rw h.init,
    apply classical.some_spec },
  { unfold saf_ex,
    apply henceforth_entails_henceforth _ _ h.valid,
    rw p_exists_entails_eq_p_forall_entails,
    intro l,
    intros τ h,
    apply is_step_inst' _ l,
    apply object_mch_action_eq_step_of,
    revert h, apply and.imp_left _,
    apply id, },
  { apply forall_imp_forall _ h.fair,
    intros e Hsch Hc Hf,
    apply inf_often_entails_inf_often (object_mch_action_eq_step_of _ _),
    apply Hsch,
    rw mem_object_req_eq_csch_and_fsch,
    apply coincidence Hc Hf },
end

-- instance {α} [sched lbl] : system_sem (program lbl) :=
instance : unity.system_sem program :=
  { (_ : unity.system program) with
    ex := program.ex
  , safety := @program.ex.safety _
  , inhabited := program.witness
  , init_sem := @init_sem
  , transient_sem := @transient.semantics }

open unity

def unless_except (s : program) (p q : pred' α) (evts : set event) : Prop :=
unless' s p q (λ σ σ', ∃ e : event, e ∈ evts ∧ e.step_of σ σ')

theorem unless_except_rule {s : program} {p q : pred' α} (exp : set event)
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
  unfold program.step_of event.step_of at STEP,
  cases STEP with Hc STEP,
  cases STEP with Hf STEP,
  cases e with e,
  { unfold program.event skip event.step at STEP,
    subst σ',
    left, apply Hp },
  { apply ACT e _ Hc Hf _ _ STEP Hp Hq,
    intro Hin,
    apply EXP,
    clear ACT EXP,
    unfold program.step_of event.step_of program.event,
    existsi s.event' e, split, apply Hin,
    existsi Hc, existsi Hf,
    apply STEP }
end

theorem unless_rule {s : program} {p q : pred' α}
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

theorem ensure_rule {s : program} {p q : pred' α} (ev : option s.lbl)
   (EN : s ⊢ p && -q ⟶ s.coarse_sch_of ev)
   (FLW : p && -q && s.coarse_sch_of ev  ↦  s.fine_sch_of ev || q in s)
   (NEG : s ⊢ λ σ, ∀ σ', ¬ q σ → s.step_of ev σ σ' → q σ')
   (STABLE: unless s p q )
: p ↦ q in s :=
begin
  apply @leads_to.basis' _ _ s _ _ (s.fine_sch_of ev) _ STABLE,
  { apply leads_to.weaken_lhs' _ _ FLW,
    apply holds_imp_holds _ _ EN,
    apply relative _ _,
    apply entails_p_and_of_entails,
    { refl },
    { apply EN } },
  unfold transient' system.transient program.transient,
  existsi ev,
  apply falsify.mk,
    -- enablement
  { apply EN },
    -- follow
  { refl },
    -- negation
  { intros σ Hf Hact,
    note H := NEG (σ 0) (σ 1) Hf.right Hact,
    revert H,
    simp [not_init,next_init,not_and_iff_not_or_not,not_not_iff_self],
    apply or.intro_left }
end

end nondet

end nondet
