
import unitb.predicate
import unitb.semantics.temporal
import unitb.code.syntax
import unitb.code.instances
import unitb.code.rules
import unitb.code.lemmas
import unitb.refinement.superposition

namespace code.semantics

section
open code predicate temporal nondet

parameters (σ : Type)
-- def rel := σ → σ → Prop

-- def ex : code σ rel → cpred σ → cpred σ
--  | (action p a) := stutter ∘ pre p ∘ act a
--  | (seq p₀ p₁) := ex p₀ ∘ ex p₁
--  | (if_then_else p c a₀ a₁) := pre p ∘ test (pre c ∘ ex a₀) (pre (-c) ∘ ex a₁)
--  | (while p c a inv) := _

parameters (p : nondet.program σ)
parameters {term : pred σ}
parameters (c : code p.lbl p.first term)

-- instance : scheduling.sched (control c ⊕ p.lbl) := _

structure state :=
  (pc : option (current c))
  (intl : σ)
  (assertion : assert_of pc intl)

parameter Hcorr : ∀ pc, state_correctness p c pc

include Hcorr

section event

parameter (e : p.lbl)
parameter (s : state)
parameter (h₀ : selects s.pc e)
parameter (h₁ : true)

include h₁

theorem evt_guard
: p.guard e s.intl :=
(Hcorr s.pc).enabled e h₀ s.intl s.assertion

theorem evt_coarse_sch
: p.coarse_sch_of e s.intl :=
evt_guard.left

theorem evt_fine_sch
: p.fine_sch_of e s.intl :=
evt_guard.right

def machine.run_event (s' : state) : Prop :=
(p.event e).step s.intl evt_coarse_sch evt_fine_sch s'.intl

end event

def machine.step
  (e : current c)
  (s  : state)
  (h : some e = s.pc)
  (s' : state) : Prop :=
  s'.pc = next s.intl s.pc
∧ match action_of e with
   | (sum.inr ⟨l,hl⟩) :=
         have h : selects (s.pc) l,
              by { simp [h] at hl, apply hl },
         machine.run_event l s h trivial s'
   | (sum.inl _) := s'.intl = s.intl
  end

def machine.step_fis
  (e : current c)
  (s  : state)
  (h : some e = s.pc)
: ∃ (s' : state), machine.step e s h s' :=
begin
  destruct action_of e
  ; intros l Hl,
  { have Hss' : assert_of (next s.intl s.pc) s.intl,
    { rw assert_of_next,
      cases l with l H, cases H with P H,
      rw ← h,
      cases classical.em (condition (some e) P s.intl) with Hc Hnc,
      { apply (Hcorr $ some e).cond_true _ _ _ Hc,
        rw h,
        apply s.assertion, },
      { apply (Hcorr $ some e).cond_false _ _ _ Hnc,
        rw h,
        apply s.assertion } },
    let ss' := state.mk (next s.intl s.pc) s.intl Hss',
    existsi ss',
    unfold machine.step,
    split,
    { refl },
    { rw Hl, unfold machine.step._match_1 machine.run_event } },
  { cases l with l hl,
    rw h at hl,
    have CS := evt_coarse_sch _ p c Hcorr l s hl trivial,
    have FS := evt_fine_sch _ _ c Hcorr l s hl trivial,
    cases (p.event l).fis s.intl CS FS with s' H,
    have Hss' : assert_of (next s.intl s.pc) s',
    { rw [assert_of_next],
      apply (Hcorr _).correct _ hl s.intl _ _ ⟨CS,FS,H⟩,
      apply s.assertion },
    let ss' := state.mk (next s.intl s.pc) s' Hss',
    existsi ss',
    unfold machine.step,
    split,
    { refl },
    { rw Hl, unfold machine.step._match_1 machine.run_event,
      apply H } }
end

-- section test

-- parameter (s : state)

-- noncomputable def machine.test (s' : state) : Prop :=
--   s.intl = s'.intl
-- ∧ s'.pc = next s.intl s.pc

-- def machine.test_fis
-- : ∃ (s' : state), machine.test s' :=
-- sorry

-- end test

def machine.event (cur : current c) : nondet.event state :=
  { coarse_sch := λ s, some cur = s.pc
  , fine_sch   := True
  , step := λ s hc _ s', machine.step cur s hc s'
  , fis  := λ s hc _, machine.step_fis cur s hc }

-- | (sum.inr e) :=
--   { coarse_sch := λ s, selects s.pc e
--   , fine_sch   := True
--   , step := machine.step e
--   , fis  := machine.step_fis e }
-- | (sum.inl pc) :=
--   { coarse_sch := λ s, s.pc = pc.val
--   , fine_sch   := True
--   , step := λ s _ _ s', machine.test s s'
--   , fis  := λ s _ _, machine.test_fis s }

def machine_of : nondet.program state :=
 { lbl := current c
 , lbl_is_sched := by apply_instance
 , first := λ ⟨s₀,s₁,_⟩, s₀ = first c ∧ p.first s₁
 , first_fis :=
   begin cases p.first_fis with s Hs,
         have Hss : assert_of (first c) s,
         { rw assert_of_first, apply Hs },
         let ss := state.mk (first c) s Hss,
         existsi ss,
         unfold machine_of._match_1,
         exact ⟨rfl,Hs⟩
   end
 , event' := machine.event }

open superposition

def rel (l : option (machine_of.lbl)) : option (p.lbl) → Prop
  | (some e) := selects l e
  | none     := is_control l ∨ l = none

lemma ref_sim (ec : option (machine_of.lbl))
: ⟦nondet.program.step_of machine_of ec⟧ ⟹
      ∃∃ (ea : {ea // rel ec ea}), ⟦nondet.program.step_of p (ea.val) on state.intl⟧ :=
begin
  rw exists_action,
  apply action_entails_action,
  intros s s' H,
  cases ec with pc,
  case none
  { let x : {ea // rel _ p c Hcorr none ea},
    { existsi none, unfold rel is_control, right, refl },
    existsi x, unfold function.on_fun,
    unfold machine_of nondet.program.step_of nondet.program.event
           nondet.skip nondet.event.step_of
           nondet.event.fine_sch nondet.event.coarse_sch
           nondet.event.step  at H,
    unfold nondet.program.step_of nondet.program.event
           nondet.skip nondet.event.step_of
           nondet.event.fine_sch nondet.event.coarse_sch
           nondet.event.step,
    apply exists_imp_exists' (assume _, trivial) _ H, intro,
    apply exists_imp_exists' (assume _, trivial) _, intros _,
    simp, intro, subst s, },
  case some
  { destruct action_of pc,
    case sum.inl
    { intros c Hact,
      cases c with c Hc,
      cases Hc with P Hc,
      let x : {ea // rel _ p _ Hcorr (some pc) ea},
      { existsi none, unfold rel is_control, left, apply P },
      existsi x,
      unfold function.on_fun nondet.program.step_of nondet.program.event
             nondet.event.step_of,
      unfold nondet.program.step_of nondet.program.event
             nondet.event.step_of at H,
      apply exists_imp_exists' (assume _, trivial) _ H, intro,
      apply exists_imp_exists' (assume _, trivial) _, intros _,
      intros H',
      change _ = _,
      dunfold machine_of nondet.program.event' machine.event
              nondet.event.step machine.step at H',
      rw Hact at H',
      have H : s'.intl = s.intl := H'.right,
      rw [H], },
    case sum.inr
    { intros e Hact,
      cases e with e He,
      let x : {ea // rel _ p _ Hcorr (some pc) ea},
      { existsi (some e), apply He },
      existsi x, unfold function.on_fun,
      dunfold machine_of nondet.program.step_of nondet.program.event
              nondet.program.event' machine.event nondet.event.step_of
              nondet.event.coarse_sch nondet.event.fine_sch
              nondet.event.step at H,
      cases H with Hc H, cases H with Hf H,
      dunfold machine.step at H,
      rw Hact at H, unfold machine.step._match_1 machine.run_event at H,
      rw Hc at He,
      have Hen := (Hcorr s.pc).enabled e He _ s.assertion,
      exact ⟨Hen.left,Hen.right,H.right⟩, }, },
end

section ref_resched

parameter ea : option p.lbl

variable ec : { ec // rel ec ea }

lemma evt_resched
: ((p.event ea).coarse_sch && (p.event ea).fine_sch) ∘ state.intl && True
    ↦
      (machine_of.event ec).fine_sch  in  machine_of :=
sorry

lemma evt_delay
: True && ((p.event ea).coarse_sch && (p.event ea).fine_sch) ∘ state.intl
    ↦
      True && (machine_of.event ec).coarse_sch
   in machine_of :=
sorry

lemma evt_stable
: unless_except machine_of
      (True && (machine_of.event ec).coarse_sch)
      (-((p.event ea).coarse_sch ∘ state.intl))
      { e | ∃ (l : {ec // rel ec ea}), machine_of.event l = e } :=
sorry

lemma evt_sim
:    ⟦event.step_of (program.event machine_of (ec.val))⟧
 ⟹ ⟦event.step_of (program.event p ea) on state.intl⟧ :=
sorry

lemma evt_witness_fis (s : state)
: ∃ (e : {ec // rel ec ea}), true :=
sorry

lemma ref_resched
: evt_ref state.intl {ec // rel ec ea} machine_of (nondet.program.event p ea)
      (λ (ec : {ec // rel ec ea}), nondet.program.event machine_of (ec.val)) :=
{ witness := λ _, True
, witness_fis := evt_witness_fis
, resched := evt_resched
, stable  := evt_stable
, delay   := evt_delay
, sim     := evt_sim }

end ref_resched

lemma code_refs_machine
: refined state.intl p machine_of :=
{ sim_init := by { intros i, cases i, apply and.right, }
, ref := rel
, evt_sim := ref_sim
, events := ref_resched }


end

end code.semantics
