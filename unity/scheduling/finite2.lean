
import util.data.bijection
import util.data.perm
import util.data.minimum

import unity.logic
import unity.scheduling.basic
import unity.models.simple

namespace scheduling.finite

open nat simple

section

parameter {lbl : Type}
parameter [pos_finite lbl]
parameter requests : list lbl → set lbl

structure sch_state :=
  (hist : list lbl)
  (queue : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)

noncomputable def first (req : set lbl)
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
: fin $ succ $ pos_finite.pred_count lbl :=
minimum { x | l.f x ∈ req }

noncomputable def select (req : set lbl)
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
: bijection (fin $ succ $ pos_finite.pred_count lbl) lbl :=
l ∘ rev (perm.rotate_right (first req l))

def sch.inv (s : sch_state) : Prop :=
requests s.hist = ∅ ∨ s.queue.f fin.max ∈ requests s.hist

noncomputable def sch.first : sch_state :=
  { hist := [ ]
  , queue := select (requests [ ]) (rev (finite.to_nat _)) }

lemma sch.first_inv : sch.inv sch.first := sorry

noncomputable def sch.step : ∀ s : sch_state, sch.inv s → sch_state
 | (sch_state.mk hist queue) P :=
     { hist := hist ++ [queue.f fin.max]
     , queue := select (requests hist) queue
     }

lemma sch.step_inv
  (s : sch_state)
  (P : sch.inv s)
: sch.inv (sch.step s P) := sorry

noncomputable def scheduler : prog (subtype sch.inv) :=
  { first := ⟨sch.first,sch.first_inv⟩
  , step := λ s, ⟨sch.step s.val _,sch.step_inv _ s.property⟩ }

open sch_state unity subtype has_mem

def req (s : subtype sch.inv) : set lbl := requests s.val.hist

def next (s : subtype sch.inv) : lbl := s.val.queue.f fin.max

def rank (l : lbl) (s : subtype sch.inv) : ℕ := (s.val.queue.g l).val

lemma fair_schedule_step  (l : lbl) (v : ℕ)
:  mem l ∘ req && (eq v ∘ rank l) ↦ (flip nat.lt v ∘ rank l) || eq l ∘ next in scheduler :=
sorry

lemma stable_queue_ranking (l : lbl) (v : ℕ)
: unless scheduler (eq v ∘ rank l) (flip nat.lt v ∘ rank l || eq l ∘ next) :=
sorry

-- lemma fair_schedule  (l : lbl)
-- :  mem l ∘ req ↦ eq l ∘ next in scheduler :=
-- sorry
-- begin
--   apply leads_to.induction (measure_wf $ rank requests l ∘ subtype.val),
-- end

lemma INIT
: system.init scheduler (eq list.nil ∘ sch_state.hist ∘ val) :=
begin
  unfold system.init prog.init function.comp scheduler,
  refl,
end

lemma STEP
: co' scheduler
    (λ (σ σ' : subtype sch.inv),
       (sch_state.hist ∘ val) σ' = (sch_state.hist ∘ val) σ ++ [next σ]) :=
begin
  unfold co',
  intros σ σ',
  unfold step has_safety.step is_step,
  intros H,
  rw H,
  unfold function.comp scheduler prog.step subtype.val sch.step,
  cases σ, unfold subtype.val,
  cases val, unfold sch.step sch_state.hist,
  refl,
end

lemma INV (σ)
: requests (sch_state.hist $ val σ) = ∅ ∨ next σ ∈ requests (sch_state.hist $ val σ) :=
σ.property

lemma PROG (l)
: often_imp_often scheduler
      (mem l ∘ requests ∘ sch_state.hist ∘ subtype.val)
      (eq l ∘ next) :=
begin
  apply often_imp_often.induct _ _ _ nat.lt_wf,
  apply fair_schedule_step _ l,
  apply stable_queue_ranking _ l
end

end

variable {lbl : Type}
variable [pos_finite lbl]
variable (r : list lbl → set lbl)

noncomputable def scheduler_spec
: @scheduling.unity.scheduler lbl r :=
  { s := prog $ subtype (sch.inv r)
  , sem := _
  , F := @scheduler _ _ r
  , ch := next r
  , hist := sch_state.hist ∘ subtype.val
  , INIT := INIT r
  , STEP := STEP r
  , INV  := INV r
  , PROG := PROG r }

end scheduling.finite
