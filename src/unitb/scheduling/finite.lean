
import util.data.bijection
import util.data.perm
import util.data.minimum

import unitb.logic
import unitb.scheduling.basic
import unitb.models.simple

import data.set.basic

local attribute [-simp] or.comm or.left_comm or.assoc and.comm and.left_comm and.assoc

namespace scheduling.finite

open nat simple function predicate temporal set scheduling
@[reducible]
def rrobin (lbl : Type) [pos_finite lbl] : Type :=
bijection (fin $ succ $ pos_finite.pred_count lbl) lbl

@[reducible]
def index_t (lbl : Type) [pos_finite lbl] :=
fin $ succ $ pos_finite.pred_count lbl

section

parameter {lbl : Type}
parameter [pos_finite lbl]
parameter t : scheduling.unitb.target_mch lbl

noncomputable def first (req : set lbl)
  (l : rrobin lbl)
: index_t lbl :=
(↓ x, l.f x ∈ req )

noncomputable def sch.current (r : set lbl) (queue : rrobin lbl) : lbl :=
queue.f (first r queue)

structure sch_state : Type :=
  (target : t.σ)
  (queue : rrobin lbl)
  (inv : sch.current (t.req.apply target) queue ∈ t.req.apply target)

lemma first_mem {req : set lbl}
  (l : rrobin lbl)
  (h : req ≠ ∅)
: l.f (first req l) ∈ req :=
begin
  unfold first, apply @minimum_mem _ _ { x | l.f x ∈ req },
  cases set.exists_mem_of_ne_empty h with x h,
  apply @set.ne_empty_of_mem _ _ (l.g x),
  change l.f (l.g x) ∈ req,
  rw l.g_inv, apply h
end

noncomputable def select (req : set lbl)
  (l : rrobin lbl)
: rrobin lbl :=
l ∘ (perm.rotate_right (first req l)).rev

lemma sch.select_inv
  (s : t.σ)
  (q : rrobin lbl)
: sch.current (t.req.apply s) q ∈ t.req.apply s :=
begin
  unfold select sch.current,
  apply first_mem _ (t.req_nemp s),
end

def sch.first : sch_state :=
{ target := t.s₀
, queue := bijection.rev (finite.to_nat _)
, inv := sch.select_inv _ _ }

noncomputable def sch.step : sch_state → sch_state
 | (sch_state.mk target queue P) :=
     { target := t.next (sch.current (t.req.apply target) queue) target P
     , queue := select (t.req.apply target) queue
     , inv := sch.select_inv _ _
     }

def sch.is_step : sch_state → sch_state → Prop
 | s s' := s' = sch.step s

noncomputable def scheduler : program sch_state :=
  { first := sch.first
  , step  := sch.step }

open sch_state unitb subtype has_mem classical

def req : var sch_state (set lbl) :=
t.req ∘' (sch_state.target : var sch_state t.σ)

noncomputable def current  : var sch_state lbl :=
sch.current <$> req <*> queue

def rank (l : lbl) : var (sch_state) ℕ :=
↑ λ s : sch_state, (s.queue.g l).val

open scheduling scheduling.unitb

variable (s : sch_state)
section eq_next_or_rank_eq_or_rank_lt_aux
variable {v : ℕ}
variable {l : lbl}
variable h : (rank l).apply s = v
include h

section left
variable Hlt : s.queue.g l < first (req.apply s) s.queue
include Hlt

private lemma not_requested : l ∉ req.apply s :=
begin
  cases s,
  simp [select,comp,sch.step,sch_state.queue,req,rank] at *,
  intro h₀,
  have h₁ : queue.g l ∈ { x | queue.f x ∈ t.req.apply target },
  { rw [mem_set_of,bijection.g_inv],
    apply h₀ },
  have h₂ := minimum_le h₁,
  apply not_le_of_gt Hlt h₂,
end

private lemma rank_stable : (rank l).apply (sch.step s) = v :=
begin
  cases s,
  simp [select,comp,sch.step,sch_state.queue,req,rank] at *,
  rw [comp_g], unfold comp,
  rw [rev_g ,perm.rotate_right_f_gt_eq_self _ _ Hlt,h] ,
end

end left
section right

variable Hgt : s.queue.g l > first (req.apply s) s.queue
include Hgt
private lemma rank_dec : (rank l).apply (sch.step s) < v :=
begin
  cases s,
  simp [rank,sch.step,select,req] at *,
  rw [comp_g], unfold comp,
  rw [rev_g,perm.rotate_right_f_lt_shifted _ _ Hgt,fin.pred_def,← h],
  apply pred_lt_self_of_pos,
  unfold gt at Hgt,
  rw [fin.lt_def] at Hgt,
  apply lt_of_le_of_lt _ Hgt,
  apply zero_le
end
end right

end eq_next_or_rank_eq_or_rank_lt_aux

lemma eq_next_or_rank_eq_or_rank_lt  {l : lbl} (v : ℕ)
  (h : s ⊨ rank l ≃ v)
: s ⊨ current ≃ ↑l ∨
      ( s ⊨ - (↑l ∊ req) ∧ sch.step s ⊨ rank l ≃ v ) ∨ sch.step s ⊨ rank l ≺ v :=
begin
  -- lifted_pred [temporal.init,sch.is_step] using Hstep h,
  -- rw Hstep, clear Hstep,
  -- revert h, generalize : x 0 = s, intro,
  cases classical.em (s.queue.g l = first ((req t).apply s) s.queue) with Heq Hne,
  { left, cases s,
    simp [sch.step,sch_state.queue,sch_state.target,rank,current,req,comp,sch.current] at h ⊢,
    simp [req] at Heq,
    rw bijection.inverse,
    symmetry, apply Heq, },
  cases lt_or_gt_of_ne Hne with Hlt Hgt ; clear Hne,
  { right, left, split, simp,
    apply not_requested t s ; assumption ,
    apply rank_stable t s ; assumption },
  { right, right,
    apply rank_dec t s ; assumption , },
end

lemma fair_schedule_step  (l : lbl) (v : ℕ)
:  ↑l ∊ req ⋀ rank l ≃ v ↦ rank l ≺ v ⋁ current ≃ l in scheduler :=
begin
  unfold scheduler,
  apply leads_to_step,
  intros σ Heq Hnnext,
  -- simp, simp at Heq Hnnext,
  -- unfold rank function.comp flip sch.step, -- next rank subtype.val,
  cases Heq with Hmem Heq,
  have HH := eq_next_or_rank_eq_or_rank_lt _ _ v Heq,
  rw or_iff_not_imp at HH,
  simp [not_or_iff_not_and_not] at Hnnext HH,
  have HH' := HH Hnnext.right,
  rw [or_iff_not_imp,not_and_iff_not_or_not,not_not_iff_self] at HH',
  left, apply HH', clear HH' HH,
  left, simp at Hmem, assumption
end

lemma stable_queue_ranking (l : lbl) (v : ℕ)
: unless scheduler (rank l ≃ v) (rank l ≺ v ⋁ current ≃ l) :=
begin
  unfold scheduler,
  apply unless_step,
  intros σ Heq Hnnext,
  simp,
  simp [not_or_iff_not_and_not] at Hnnext,
  have := eq_next_or_rank_eq_or_rank_lt _ _ _ Heq, revert this,
  simp, monotonicity, intro h,
  cases h with h h,
  { cases Hnnext.right h, },
  { left, rw [h.right], },
end

lemma INIT
: system.init scheduler (↑sch_state.target ≃ (t.s₀ : var sch_state t.σ)) :=
begin
  simp [system.init,program.init,scheduler],
  refl,
end

lemma STEP
: co' scheduler
    (λ (σ σ' : sch_state),
       ∃ P, σ'.target = t.next (current.apply σ) σ.target P) :=
begin
  unfold co',
  intros σ σ',
  dunfold step has_safety.step is_step,
  intros H,
  have P : (current t).apply σ ∈ (t.req).apply (σ.target),
  { simp [current,req], exact σ.inv,  },
  existsi P,
  rw H,
  unfold function.comp scheduler program.step subtype.val sch.step,
  cases σ,
  simp [sch.step,sch_state.target,current,req],
end

lemma INV
: ∀ σ, σ ⊨ current ∊ t.req ∘' sch_state.target :=
by { assume σ, simp [current,req], apply σ.inv, }

lemma PROG (l : lbl)
:     ↑l ∊ req  >~>  current ≃ l
  in scheduler :=
begin
  apply often_imp_often.induct ℕ _ _ ,
  apply stable_queue_ranking _ l,
  apply fair_schedule_step _ l,
end

end

open scheduling.unitb stream unitb

variable {lbl : Type}
variable [pos_finite lbl]
variable (r : target_mch lbl)

noncomputable def scheduler_spec
: @scheduling.unitb.scheduler lbl r :=
  { s := program $ @sch_state lbl _ r
  , sem := _
  , F := @scheduler _ _ _
  , ch := current r
  , object := _
  , INIT := INIT r
  , STEP := STEP r
  , INV  := INV r
  , PROG := PROG r }

noncomputable instance : unitb.system_sem ((scheduler_spec r).s) :=
(scheduler_spec r).sem

lemma sched' {lbl : Type} [s : finite lbl] [nonempty lbl]
  (r : target_mch lbl)
: ∃ τ : stream r.σ, fair r τ :=
begin
  have h : pos_finite lbl,
  { apply pos_of_finite ; apply_instance },
  apply unitb.scheduling r (scheduling.finite.scheduler_spec r),
end

end scheduling.finite
