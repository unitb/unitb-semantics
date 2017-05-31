
import unity.logic
import unity.temporal

import unity.models.nondet

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

def program.falsify (s : program) (act : option s.lbl) (p : pred' α) : Prop :=
nondet.program.falsify s.nondet act p

open temporal

lemma program.falsify.negate
   {s : program} {act : option s.lbl} {p : pred' α}
   (F : s.falsify act p)
:  •p && ⟦ s^.step_of act ⟧ ⟹ <>-•p :=
@nondet.program.falsify.negate _ s.nondet act p F

def program.transient (s : program) : pred' α → Prop :=
nondet.program.transient s.nondet

section theorems

variable (s : program)

open program
open event

theorem program.transient_false : transient s False :=
nondet.program.transient_false _

def program.transient_str (s : program) {p q : α → Prop}
: (∀ (i : α), p i → q i) → s.transient q → s.transient p :=
nondet.program.transient_str _

end theorems

instance prog_is_system : unity.system program :=
{ σ := _
, transient := _
, step := is_step
, init   := nondet.program.init ∘ program.nondet
, transient_false := program.transient_false
, transient_str := program.transient_str }

open unity

lemma leads_to.nondet (s : program) {p q : pred' α}
   (h : leads_to s p q)
: leads_to s.nondet p q :=
begin
  induction h with
      p q T S
      p q r P₀ Q₀ P₁ Q₁
      X p q P P'
      XX YY ZZ,
  { apply leads_to.basis,
    apply T,
    apply S },
  { apply leads_to.trans _ P₁ Q₁ },
  { apply leads_to.disj X,
    apply P' }
end

-- instance {α} [sched lbl] : system_sem (program lbl) :=
instance : unity.system_sem program :=
  { (_ : unity.system program) with
    ex := program.ex
  , safety := λ s, unity.system_sem.safety s.nondet
  , inhabited := λ s, unity.system_sem.inhabited s.nondet
  , init_sem := λ s, @unity.system_sem.init_sem _ _ s.nondet
  , transient_sem := λ s, @unity.system_sem.transient_sem _ _ s.nondet }

open unity

theorem transient_rule {s : program} {p : pred' α} (ev : option s.lbl)
   (EN : p ⟹ s.coarse_sch_of ev)
   (FLW : leads_to s (p && s.coarse_sch_of ev) (s.fine_sch_of ev))
   (NEG : ∀ σ σ', p σ → s.step_of ev σ σ' → ¬p σ')
: s.transient p :=
@nondet.transient_rule _ s.nondet p ev EN (leads_to.nondet _ FLW) NEG

end schedules

end schedules
