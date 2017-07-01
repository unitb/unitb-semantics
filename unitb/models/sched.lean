
import unitb.logic
import unitb.semantics.temporal

import unitb.models.nondet

import util.logic

universe variable u
namespace schedules

section schedules

open predicate

parameter α : Type

def pred := α → Prop

structure event : Type :=
  (coarse_sch : pred)
  (fine_sch : pred)
  (step : ∀ s, coarse_sch s → fine_sch s → α)

parameter {α}

def event.nondet (e : event) : nondet.event α :=
  { coarse_sch := e.coarse_sch
  , fine_sch := e.fine_sch
  , step := λ s Hc Hf s', e.step s Hc Hf = s'
  , fis := λ s Hc Hf, ⟨_,rfl⟩ }

structure program : Type 2 :=
  (lbl : Type)
  (lbl_is_sched : scheduling.sched lbl)
  (first : α)
  (event' : lbl → event)

def program.nondet (p : program) : @nondet.program α :=
  { lbl := p.lbl
  , lbl_is_sched := p.lbl_is_sched
  , first := λ s, s = p.first
  , first_fis := ⟨_, rfl⟩
  , event' := event.nondet ∘ p.event' }

open temporal

def program.coarse_sch_of (s : program) (act : option s.lbl)
: α → Prop :=
nondet.program.coarse_sch_of s.nondet act

def program.fine_sch_of (s : program) (act : option s.lbl) : α → Prop :=
nondet.program.fine_sch_of s.nondet act

def program.step_of (s : program) (act : option s.lbl) : α → α → Prop :=
s.nondet.step_of act

def is_step (s : program) : α → α → Prop :=
nondet.is_step s.nondet

def program.ex (s : program) (τ : stream α) : Prop :=
nondet.program.ex (s.nondet) τ

def program.falsify (s : program) (act : option s.lbl) (p q : pred' α) : Prop :=
nondet.program.falsify s.nondet act p q

open temporal

lemma program.falsify.negate
   {s : program} {act : option s.lbl} {p q : pred' α}
   (F : s.falsify act p q)
:  •q && ⟦ s^.step_of act ⟧ ⟹ <>-•q :=
@nondet.program.falsify.negate _ s.nondet act p q F

def program.transient (s : program) : pred' α → pred' α → Prop :=
nondet.program.transient s.nondet

section theorems

variable (s : program)

open program
open event

theorem program.transient_false (p : pred' α) : transient s p False :=
nondet.program.transient_false _

def program.transient_antimono (s : program) {p q p' q' : α → Prop}
  (hp : p' ⟹ p)
  (hq : q' ⟹ q)
: s.transient p q → s.transient p' q' :=
nondet.program.transient_antimono _ hp hq

end theorems

instance prog_is_system : unitb.system program :=
{ σ := _
, transient := _
, step := is_step
, init   := nondet.program.init ∘ program.nondet
, transient_false := program.transient_false
, transient_antimono := program.transient_antimono }

open unitb

lemma leads_to.nondet (s : program) {p q : pred' α}
   (h : leads_to s p q)
: leads_to s.nondet p q :=
begin
  apply leads_to.subst _ s s.nondet _ _ h,
  { intros p q H, apply H },
  { intros p q H, apply H },
end

-- instance {α} [sched lbl] : system_sem (program lbl) :=
instance : unitb.system_sem program :=
  { (_ : unitb.system program) with
    ex := program.ex
  , safety := λ s, unitb.system_sem.safety s.nondet
  , inhabited := λ s, unitb.system_sem.inhabited s.nondet
  , init_sem := λ s, @unitb.system_sem.init_sem _ _ s.nondet
  , transient_sem := λ s, @unitb.system_sem.transient_sem _ _ s.nondet }

open unitb

theorem transient_rule {s : program} {p q : pred' α} (ev : option s.lbl)
   (EN : p && -q ⟹ s.coarse_sch_of ev)
   (FLW : (p && -q && s.coarse_sch_of ev) ↦ s.fine_sch_of ev || q in s)
   (NEG : ∀ σ σ', ¬ q σ → s.step_of ev σ σ' → q σ')
   (STABLE : unless (program.nondet s) p q)
: p ↦ q in s.nondet :=
@nondet.ensure_rule _ s.nondet p q ev EN (leads_to.nondet _ FLW) NEG STABLE

end schedules

end schedules
