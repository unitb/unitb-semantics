
import data.stream

import util.data.bijection
import util.data.perm
import util.data.nat
import util.data.minimum

import unity.models.simple
import unity.scheduling.basic

namespace scheduling.infinite

open stream scheduling unity

open nat simple function

@[reducible]
def rrobin (lbl : Type) [infinite lbl] : Type :=
bijection ℕ lbl

@[reducible]
def index_t (lbl : Type) [infinite lbl] := ℕ

section

parameter {lbl : Type}
parameter [infinite lbl]
parameter t : scheduling.unity.target_mch lbl

local attribute [instance] classical.prop_decidable

noncomputable def first (req : set lbl)
  (l : rrobin lbl)
: index_t lbl :=
(↓ x, l.f x ∈ req )

noncomputable def sch.current (r : set lbl) (queue : rrobin lbl) : lbl :=
queue.f (first r queue)

structure sch_state :=
  (target : t.σ)
  (q_len : ℕ)
  (queue : rrobin lbl)
  (inv : sch.current (t.req target) queue ∈ t.req target)

def req (s : sch_state) : set lbl :=
t.req s.target

lemma first_mem {s : t.σ}
  (l : rrobin lbl)
: l.f (first (t.req s) l) ∈ t.req s :=
begin
  unfold first, apply @minimum_mem _ _ { x | l.f x ∈ t.req s },
  cases set.exists_mem_of_ne_empty (t.req_nemp s) with x h,
  apply @set.ne_empty_of_mem _ _ (l.g x),
  change l.f (l.g x) ∈ t.req s,
  rw l.g_inv, apply h
end

noncomputable def shift (s : sch_state)
: rrobin lbl :=
if h : first (req s) s.queue < succ s.q_len
then s.queue ∘ bijection.rotate_right' (first (req s) s^.queue) (succ s.q_len) h
else s.queue

lemma sch.select_inv
  (s : t.σ)
  (q : rrobin lbl)
: sch.current (t.req s) q ∈ t.req s :=
begin
  unfold sch.current,
  apply first_mem _,
end

def sch.first : sch_state :=
{ q_len := 0
, target := t.s₀
, queue := rev (infinite.to_nat _)
, inv := sch.select_inv _ _ }

noncomputable def sch.step (s : sch_state) : sch_state :=
{ q_len := s.q_len + 1
, target := t.next (sch.current (req s) s.queue) s.target s.inv
, queue := shift s
, inv := sch.select_inv _ _ }

noncomputable def scheduler : program sch_state :=
  { first := sch.first
  , step  := sch.step }

open sch_state has_mem

noncomputable def next (s : sch_state) : lbl :=
sch.current (req s) s.queue

def rank (l : lbl) (s : sch_state) : ℕ := s.queue.g l + (s.queue.g l - s.q_len)

lemma pending_not_move (s : sch_state) (l : lbl)
  (h : succ s.q_len ≤ s.queue.g l)
: ((sch.step s).queue).g l = s.queue.g l :=
begin
  unfold sch.step sch_state.queue shift,
  cases decidable.em (first (req t s) s.queue < succ s.q_len) with h' h',
  { rw [dif_pos h',comp_g],
    unfold comp,
    rw bijection.rotate_right'_g_eq_of_ge_j _ h' h, },
  { rw dif_neg h', },
end

lemma shift_down (s : sch_state) (l : lbl)
  (h₀ : first (req s) s.queue < s.queue.g l)
  (h₁ : s.queue.g l < succ s.q_len)
: succ (((sch.step s).queue).g l) = s.queue.g l :=
begin
  unfold sch.step sch_state.queue shift,
  have h : first (req t s) s.queue < succ s.q_len := lt_trans h₀ h₁,
  rw [dif_pos h,comp_g], unfold comp,
  rw bijection.succ_rotate_right'_g_eq_self (s.queue.g l) _ h₀ h₁,
end

lemma q_len_inc (s : sch_state)
: (sch.step s).q_len = succ s.q_len :=
by { rw -add_one_eq_succ, refl }

lemma not_req_not_move (s : sch_state) (l : lbl)
  (h : s.queue.g l < first (req s) s.queue)
: (sch.step s).queue.g l = s.queue.g l :=
begin
  unfold sch.step sch_state.queue shift,
  cases decidable.em (first (req t s) s.queue < succ s.q_len) with h' h',
  { rw [dif_pos h',comp_g],
    unfold comp,
    rw [bijection.rotate_right'_g_eq_of_lt_i _ _ h], },
  { rw [dif_neg h'] },
end

lemma not_mem_req {s : sch_state} {l : lbl}
  (h : first (req s) s.queue > s.queue.g l)
: l ∉ req s :=
begin
  intro h',
  revert h,
  apply not_lt_of_ge,
  unfold first,
  apply minimum_le,
  unfold mem set.mem,
  rw bijection.g_inv,
  apply h'
end

lemma le_rank_of_lt_first {s : sch_state} {l : lbl}
  (Hgt : s.queue.g l < first (req s) s.queue)
: rank l (sch.step s) ≤ rank l s :=
begin
  unfold rank,
  cases le_or_gt (s.queue.g l) (s.q_len) with h h,
  { have h' : s.queue.g l ≤ succ s.q_len := le_succ_of_le h,
    rw [not_req_not_move _ _ _ Hgt,q_len_inc
       ,sub_eq_zero_of_le h,sub_eq_zero_of_le h'] },
  { rw [pending_not_move _ _ _ h,q_len_inc],
    apply add_le_add_left,
    apply nat.sub_le_sub_left,
    apply le_succ, },
end

lemma lt_rank_of_gt_first {s : sch_state} {l : lbl}
  (Hlt : first (req s) (s.queue) < (s.queue).g l)
: rank l (sch.step s) < rank l s :=
begin
  unfold rank,
  cases le_or_gt s.q_len (first (req t s) s.queue) with h h,
    -- h : s.q_len ≤ first (sch_state.req s) (s.queue)
  { have h' : s.q_len < s.queue.g l := lt_of_le_of_lt h Hlt,
    rw [pending_not_move _ _ _ h'],
    unfold sch.step sch_state.q_len,
    rw [add_one_eq_succ,-nat.add_sub_assoc h'
       ,-nat.add_sub_assoc $ le_of_lt h'
       ,sub_succ],
    apply pred_lt_self_of_pos,
    apply nat.sub_pos_of_lt,
    apply lt_of_lt_of_le h',
    apply le_add_left },
    -- h : s.q_len > first (sch_state.req s) (s.queue)
  { cases lt_or_ge (s.queue.g l) (succ s.q_len) with Hlt_len Hge_len,
      -- Hlt_len : (s.queue).g l < succ (s.q_len)
    { rw [-shift_down _ s _ Hlt Hlt_len,q_len_inc],
      { apply add_lt_add_of_lt_of_le,
        { apply lt_succ_self },
        { apply nat.sub_le_sub
          ; apply le_succ, } }, },
      -- Hge_len : (s.queue).g l ≥ succ (s.q_len)
    { unfold gt at h,
      rw [pending_not_move _ _ _ Hge_len,q_len_inc],
      { apply add_lt_add_left,
        apply nat.sub_lt_sub_left Hge_len,
        apply lt_succ_self, }, } }
end

lemma eq_next_or_rank_eq_or_rank_lt {s : sch_state} {l : lbl} (v : ℕ)
  (h : v = rank l s)
: l = next s ∨
  ( l ∉ req s ∧ rank l (sch.step s) = v ) ∨
  rank l (sch.step s) < v :=
begin
  rw or_iff_not_imp,
  rw [eq_comm],
  intro Hnnext,
  unfold next sch.current at Hnnext,
  rw bijection.inverse at Hnnext,
  cases lt_or_gt_of_ne Hnnext with Hlt Hgt,
    -- Hlt : first (sch_state.req s) s.queue < s.queue.g l
  { right,
    rw h,
    apply lt_rank_of_gt_first _ Hlt },
    -- Hgt : s.queue.g l < first (sch_state.req s) s.queue
  { clear Hnnext, unfold gt at Hgt,
    subst v,
    cases lt_or_eq_of_le (le_rank_of_lt_first _ Hgt) with Hlt Heq,
    { right, apply Hlt },
    { left,
      split,
      { apply not_mem_req _ Hgt },
      { apply Heq, }, } },
end

lemma fair_schedule_step  (l : lbl) (v : ℕ)
:  mem l ∘ req && (eq v ∘ rank l) ↦ (flip has_lt.lt v ∘ rank l) || (eq l ∘ next) in scheduler :=
begin
  unfold scheduler,
  apply leads_to_step,
  intros σ Heq Hnnext,
  simp, simp at Heq,
  cases Heq with Heq Hmem,
  have HH := eq_next_or_rank_eq_or_rank_lt _ v Heq,
  rw or_iff_not_imp at HH,
  simp [not_or_iff_not_and_not] at Hnnext,
  have Hnnext' : ¬ l = next t σ := Hnnext.left,
  have HH' := HH Hnnext',
  rw [or_iff_not_imp,not_and_iff_not_or_not,not_not_iff_self] at HH',
  right, apply HH', clear HH' HH,
  apply or.intro_left _ Hmem,
end

lemma stable_queue_ranking (l : lbl) (v : ℕ)
: unless scheduler (eq v ∘ rank l) (flip has_lt.lt v ∘ rank l || (eq l ∘ next)) :=
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
  { apply or.imp_left _,
    intro h, cases h with _ h, rw h, },
end

lemma INIT
: system.init scheduler (eq t.s₀ ∘ sch_state.target) :=
begin
  unfold system.init program.init function.comp scheduler,
  unfold sch.first,
  refl,
end

lemma STEP
: co' scheduler
    (λ (σ σ' : sch_state),
       ∃P, σ'.target = t.next (sch.current (req σ) σ.queue) σ.target P) :=
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
:     (mem l ∘ req)  >~>  (eq l ∘ next)
  in scheduler :=
begin
  apply often_imp_often.induct _ _ _ nat.lt_wf,
  apply fair_schedule_step _ l,
  apply stable_queue_ranking _ l
end

end

variable {lbl : Type}
variable [infinite lbl]
variable t : scheduling.unity.target_mch lbl

noncomputable def scheduler_spec
: @scheduling.unity.scheduler lbl t :=
  { s := program $ sch_state t
  , sem := _
  , F := @scheduler _ _ t
  , ch := next t
  , object := sch_state.target
  , INIT := INIT t
  , STEP := STEP t
  , INV  := INV t
  , PROG := PROG t }

noncomputable instance : unity.system_sem ((scheduler_spec t).s) :=
(scheduler_spec t).sem

lemma sched' {lbl : Type} [s : infinite lbl] [nonempty lbl]
  (t : scheduling.unity.target_mch lbl)
: ∃ τ : stream t.σ, fair t τ :=
begin
  apply unity.scheduling t (scheduling.infinite.scheduler_spec t),
  apply_instance
end

end scheduling.infinite
