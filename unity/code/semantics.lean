
import unity.predicate
import unity.code.syntax
import unity.code.instances

namespace code.semantics

section
open code predicate

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

structure local_correctness : Prop :=
  (enabled : ∀ (pc : option $ current c) l, selects pc l → assert_of pc ⟹ p.guard l)
  (correct : ∀ (pc : option $ current c) l, selects pc l →
       ∀ s s', assert_of pc s → p.step_of l s s' → next_assert pc s')
  (cond_true : ∀ (pc : option $ current c) (H : is_control pc),
       ∀ s, assert_of pc s → condition pc H s → next_assert pc s)
  (cond_false : ∀ (pc : option $ current c) (H : is_control pc),
       ∀ s, assert_of pc s → ¬ condition pc H s → next_assert pc s)

-- instance : scheduling.sched (control c ⊕ p.lbl) := _

structure state :=
  (pc : option (current c))
  (intl : σ)
  (assertion : assert_of pc intl)

parameter Hcorr : local_correctness

include Hcorr

section event

parameter (e : p.lbl)
parameter (s : state)
parameter (h₀ : selects s.pc e)
parameter (h₁ : true)

include h₁

theorem evt_guard
: p.guard e s.intl :=
Hcorr.enabled s.pc e h₀ s.intl s.assertion

theorem evt_coarse_sch
: p.coarse_sch_of e s.intl :=
evt_guard.left

theorem evt_fine_sch
: p.fine_sch_of e s.intl :=
evt_guard.right

def machine.run_event (s' : state) : Prop :=
(p.event e).step s.intl evt_coarse_sch evt_fine_sch s'.intl

end event

noncomputable def machine.step
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
  { assert Hss' : assert_of (next s.intl s.pc) s.intl,
    { rw assert_of_next,
      cases l with l H, cases H with P H,
      rw -h,
      cases classical.em (condition (some e) P s.intl) with Hc Hnc,
      { apply Hcorr.cond_true _ _ _ _ Hc,
        rw h,
        apply s.assertion, },
      { apply Hcorr.cond_false _ _ _ _ Hnc,
        rw h,
        apply s.assertion } },
    pose ss' := state.mk (next s.intl s.pc) s.intl Hss',
    existsi ss',
    unfold machine.step,
    split,
    { refl },
    { rw Hl, unfold machine.step._match_1 machine.run_event,
      refl } },
  { cases l with l hl,
    rw h at hl,
    note CS := evt_coarse_sch _ p c Hcorr l s hl trivial,
    note FS := evt_fine_sch _ _ c Hcorr l s hl trivial,
    cases (p.event l).fis s.intl CS FS with s' H,
    assert Hss' : assert_of (next s.intl s.pc) s',
    { rw [assert_of_next],
      apply Hcorr.correct _ _ hl s.intl _ _ ⟨CS,FS,H⟩,
      apply s.assertion },
    pose ss' := state.mk (next s.intl s.pc) s' Hss',
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

noncomputable def machine.event (cur : current c) : nondet.event state :=
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
         assert Hss : assert_of (first c) s, admit,
         pose ss := state.mk (first c) s Hss,
         existsi ss,
         unfold machine_of._match_1,
         exact ⟨rfl,Hs⟩
   end
 , event' := machine.event }

end
end code.semantics
