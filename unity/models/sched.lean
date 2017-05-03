
import unity.logic
import unity.temporal

import unity.models.nondet

import util.logic

universe variable u
namespace schedules

section schedules

open predicate

parameter {α : Type}

def pred := α → Prop

structure event : Type :=
  (coarse_sch : pred)
  (fine_sch : pred)
  (step : ∀ s, coarse_sch s → fine_sch s → α)

def event.nondet (e : event) : nondet.event :=
  { coarse_sch := e.coarse_sch
  , fine_sch := e.fine_sch
  , step := λ s Hc Hf s', e.step s Hc Hf = s'
  , fis := λ s Hc Hf, ⟨_,rfl⟩ }

structure prog : Type 2 :=
  (lbl : Type)
  (lbl_is_sched : scheduling.sched lbl)
  (first : α)
  (event' : lbl → event)

def prog.nondet (p : prog) : @nondet.prog α :=
  { lbl := p.lbl
  , lbl_is_sched := p.lbl_is_sched
  , first := λ s, s = p.first
  , first_fis := ⟨_, rfl⟩
  , event' := event.nondet ∘ p.event' }

open temporal

def prog.coarse_sch_of (s : prog) (act : option s.lbl)
: α → Prop :=
nondet.prog.coarse_sch_of s.nondet act

def prog.fine_sch_of (s : prog) (act : option s.lbl) : α → Prop :=
nondet.prog.fine_sch_of s.nondet act

def prog.step_of (s : prog) (act : option s.lbl) : α → α → Prop :=
s.nondet.step_of act

def is_step (s : prog) : α → α → Prop :=
nondet.is_step s.nondet

def prog.ex (s : prog) (τ : stream α) : Prop :=
nondet.prog.ex (s.nondet) τ

def prog.falsify (s : prog) (act : option s.lbl) (p : pred' α) : Prop :=
nondet.prog.falsify s.nondet act p

open temporal

lemma prog.falsify.negate
   {s : prog} {act : option s.lbl} {p : pred' α}
   (F : prog.falsify s act p)
:  •p && ⟦ s^.step_of act ⟧ ⟹ <>-•p :=
@nondet.prog.falsify.negate _ s.nondet act p F

def prog.transient (s : prog) : pred' α → Prop :=
nondet.prog.transient s.nondet

section theorems

variable (s : prog)

open prog
open event

theorem prog.transient_false : transient s False :=
nondet.prog.transient_false _

def prog.transient_str (s : prog) {p q : α → Prop}
: (∀ (i : α), p i → q i) → prog.transient s q → prog.transient s p :=
nondet.prog.transient_str _

end theorems

instance prog_is_system : unity.system prog :=
{ σ := _
, transient := _
, step := is_step
, init   := nondet.prog.init ∘ prog.nondet
, transient_false := prog.transient_false
, transient_str := prog.transient_str }

open unity

lemma leads_to.nondet (s : prog) {p q : pred' α}
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

-- instance {α} [sched lbl] : system_sem (prog lbl) :=
instance : unity.system_sem prog :=
  { (_ : unity.system prog) with
    ex := prog.ex
  , safety := λ s, unity.system_sem.safety s.nondet
  , inhabited := λ s, unity.system_sem.inhabited s.nondet
  , transient_sem := λ s, @unity.system_sem.transient_sem _ _ s.nondet }

open unity

theorem transient_rule {s : prog} {p : pred' α} (ev : option s.lbl)
   (EN : p ⟹ s.coarse_sch_of ev)
   (FLW : leads_to s (p && s.coarse_sch_of ev) (s.fine_sch_of ev))
   (NEG : ∀ σ σ', p σ → s.step_of ev σ σ' → ¬p σ')
: s.transient p :=
@nondet.transient_rule _ s.nondet p ev EN (leads_to.nondet _ FLW) NEG

end schedules

end schedules
