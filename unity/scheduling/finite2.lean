
import util.data.bijection
import util.data.perm
import util.data.minimum

import unity.logic
import unity.scheduling.basic
import unity.models.simple

namespace scheduling.finite

open nat simple function

@[reducible]
def rrobin (lbl : Type) [pos_finite lbl] : Type :=
bijection (fin $ succ $ pos_finite.pred_count lbl) lbl

@[reducible]
def index_t (lbl : Type) [pos_finite lbl] :=
fin $ succ $ pos_finite.pred_count lbl

section

parameter {lbl : Type}
parameter [pos_finite lbl]
parameter t : scheduling.unity.target_mch lbl

noncomputable def first (req : set lbl)
  (l : rrobin lbl)
: index_t lbl :=
(↓ x, l.f x ∈ req )

noncomputable def sch.current (r : set lbl) (queue : rrobin lbl) : lbl :=
queue.f (first r queue)

structure sch_state : Type :=
  (target : t.σ)
  (queue : rrobin lbl)
  (inv : sch.current (t.req target) queue ∈ t.req target)

lemma first_mem {req : set lbl}
  (l : rrobin lbl)
  (h : req ≠ ∅)
: l.f (first req l) ∈ req :=
begin
  unfold first, apply @minimum_mem _ _ { x | l.f x ∈ req },
  cases exists_mem_of_ne_empty h with x h,
  apply @set.ne_empty_of_mem _ _ (l.g x),
  change l.f (l.g x) ∈ req,
  rw l.g_inv, apply h
end

noncomputable def select (req : set lbl)
  (l : rrobin lbl)
: rrobin lbl :=
l ∘ rev (perm.rotate_right (first req l))

lemma sch.select_inv
  (s : t.σ)
  (q : rrobin lbl)
: sch.current (t.req s) q ∈ t.req s :=
begin
  unfold select sch.current,
  apply first_mem _ (t.req_nemp s),
end

def sch.first : sch_state :=
{ target := t.s₀
, queue := rev (finite.to_nat _)
, inv := sch.select_inv _ _ }

noncomputable def sch.step : sch_state → sch_state
 | (sch_state.mk target queue P) :=
     { target := t.next (sch.current (t.req target) queue) target P
     , queue := select (t.req target) queue
     , inv := sch.select_inv _ _
     }

noncomputable def scheduler : program sch_state :=
  { first := sch.first
  , step  := sch.step }

open sch_state unity subtype has_mem

def req (s : sch_state) : set lbl :=
t.req s.target

noncomputable def next (s : sch_state) : lbl :=
sch.current (req s) s.queue

def rank (l : lbl) (s : sch_state) : ℕ := (s.queue.g l).val

lemma eq_next_or_rank_eq_or_rank_lt {s : sch_state} {l : lbl} (v : ℕ)
  (h : v = (s.queue.g l).val)
: l = next s ∨
  ( l ∉ req s ∧ rank l (sch.step s) = v ) ∨
  rank l (sch.step s) < v :=
begin
  unfold sch.current select sch.step rank next sch_state.queue sch_state.target req,
  pose target'  := (sch.step _ s).target,
  pose queue' := (sch.step _ s).queue,
  cases s,
  unfold sch.step sch_state.queue sch_state.target,
  cases classical.em (queue.g l = first (t.req target) queue) with Heq Hne,
  { left,
    unfold comp, symmetry,
    rw [bijection.inverse],
    symmetry, apply Heq, },
  cases lt_or_gt_of_ne Hne with Hlt Hgt
  ; clear Hne,
  { right,left,
    split,
    { intro h₀,
      assert h₁ : queue.g l ∈ { x | queue.f x ∈ t.req target },
      { rw [mem_set_of,bijection.g_inv],
        apply h₀ },
      note h₂ := minimum_le h₁,
      apply not_le_of_gt Hlt h₂, },
    { unfold select comp sch.step sch_state.queue,
      rw [comp_g], unfold comp,
      rw [rev_g,perm.rotate_right_f_gt_eq_self _ _ Hlt,h], } },
  { right,right,
    unfold comp select,
    rw [comp_g], unfold comp,
    rw [rev_g,perm.rotate_right_f_lt_shifted _ _ Hgt,fin.pred_def,-h],
    apply pred_lt_self_of_pos,
    unfold gt at Hgt,
    rw [fin.lt_def,-h] at Hgt,
    apply lt_of_le_of_lt _ Hgt,
    apply zero_le },
end

lemma fair_schedule_step  (l : lbl) (v : ℕ)
:  mem l ∘ req && (eq v ∘ rank l) ↦ (flip has_lt.lt v ∘ rank l) || eq l ∘ next in scheduler :=
begin
  unfold scheduler,
  apply leads_to_step,
  intros σ Heq Hnnext,
  simp, simp at Heq,
  unfold function.comp flip sch.step, -- next rank subtype.val,
  cases Heq with Heq Hmem,
  note HH := eq_next_or_rank_eq_or_rank_lt _ v Heq,
  rw or_iff_not_imp at HH,
  simp [not_or_iff_not_and_not] at Hnnext,
  note HH' := HH Hnnext.left,
  rw [or_iff_not_imp,not_and_iff_not_or_not,not_not_iff_self] at HH',
  right, apply HH', clear HH' HH,
  apply or.intro_left _ Hmem,
end

lemma stable_queue_ranking (l : lbl) (v : ℕ)
: unless scheduler (eq v ∘ rank l) (flip has_lt.lt v ∘ rank l || eq l ∘ next) :=
begin
  unfold scheduler,
  apply unless_step,
  intros σ Heq Hnnext,
  simp,
  simp [not_or_iff_not_and_not] at Hnnext,
  unfold function.comp,
  unfold comp at Heq,
  apply or.imp _ _ (eq_next_or_rank_eq_or_rank_lt _ _ Heq),
  { intro h, cases Hnnext.left h, },
  { apply or.imp_left,
    intro h, cases h with _ h, rw h, },
end

lemma INIT
: system.init scheduler (eq t.s₀ ∘ sch_state.target) :=
begin
  unfold system.init program.init function.comp scheduler,
  refl,
end

lemma STEP
: co' scheduler
    (λ (σ σ' : sch_state),
       ∃ P, σ'.target = t.next (next σ) σ.target P) :=
begin
  unfold co',
  intros σ σ',
  unfold step has_safety.step is_step,
  intros H,
  existsi σ.inv,
  rw H,
  unfold function.comp scheduler program.step subtype.val sch.step,
  cases σ, unfold subtype.val,
  unfold sch.step sch_state.target,
  refl,
end

lemma INV (σ : sch_state)
: next σ ∈ t.req (σ.target) :=
σ.inv

lemma PROG (l)
: often_imp_often scheduler
      (mem l ∘ t.req ∘ sch_state.target)
      (eq l ∘ next) :=
begin
  apply often_imp_often.induct _ _ _ nat.lt_wf,
  apply fair_schedule_step _ l,
  apply stable_queue_ranking _ l
end

end

open scheduling.unity stream unity

variable {lbl : Type}
variable [pos_finite lbl]
variable (r : target_mch lbl)

noncomputable def scheduler_spec
: @scheduling.unity.scheduler lbl r :=
  { s := program $ @sch_state lbl _ r
  , sem := _
  , F := @scheduler _ _ _
  , ch := next r
  , object := _
  , INIT := INIT r
  , STEP := STEP r
  , INV  := INV r
  , PROG := PROG r }

noncomputable instance : unity.system_sem ((scheduler_spec r).s) :=
(scheduler_spec r).sem

open scheduling

lemma sched' {lbl : Type} [s : finite lbl] [nonempty lbl]
  (r : target_mch lbl)
: ∃ τ : stream r.σ, fair r τ :=
begin
  assert h : pos_finite lbl,
  { apply pos_of_finite ; apply_instance },
  apply unity.scheduling r (scheduling.finite.scheduler_spec r),
  apply_instance
end

end scheduling.finite
