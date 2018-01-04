
import data.stream

import util.data.bijection
import util.data.perm
import util.data.nat
import util.data.minimum

import unitb.models.simple
import unitb.scheduling.basic

local attribute [-simp] or.comm or.left_comm or.assoc and.comm and.left_comm and.assoc

namespace scheduling.infinite

open predicate (var) scheduling.unitb unitb scheduling

open nat function simple

@[reducible]
def rrobin (lbl : Type) [infinite lbl] : Type :=
bijection ℕ lbl

@[reducible]
def index_t (lbl : Type) [infinite lbl] := ℕ

section

parameter {lbl : Type}
parameter [infinite lbl]
parameter t : target_mch lbl

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
  (inv : sch.current (t.req.apply target) queue ∈ t.req.apply target)

def req : var sch_state (set lbl) :=
t.req ∘' (sch_state.target : var sch_state t.σ)

lemma first_mem {s : t.σ}
  (l : rrobin lbl)
: l.f (first (t.req.apply s) l) ∈ t.req.apply s :=
begin
  unfold first, apply @minimum_mem _ _ { x | l.f x ∈ t.req.apply s },
  cases set.exists_mem_of_ne_empty (t.req_nemp s) with x h,
  apply @set.ne_empty_of_mem _ _ (l.g x),
  change l.f (l.g x) ∈ t.req.apply s,
  rw l.g_inv, apply h
end

noncomputable def shift (s : sch_state)
: rrobin lbl :=
if h : first (req.apply s) s.queue < succ s.q_len
then s.queue ∘ bijection.rotate_right' (first (req.apply s) s^.queue) (succ s.q_len) h
else s.queue

lemma sch.select_inv
  (s : t.σ)
  (q : rrobin lbl)
: sch.current (t.req.apply s) q ∈ t.req.apply s :=
begin
  unfold sch.current,
  apply first_mem _,
end

def sch.first : sch_state :=
{ q_len := 0
, target := t.s₀
, queue := bijection.rev (infinite.to_nat _)
, inv := sch.select_inv _ _ }

noncomputable def sch.step (s : sch_state) : sch_state :=
{ q_len := s.q_len + 1
, target := t.next (sch.current (_) s.queue) s.target s.inv
, queue := shift s
, inv := sch.select_inv _ _ }

noncomputable def scheduler : program sch_state :=
  { first := sch.first
  , step  := sch.step }

open has_mem

noncomputable def current : var sch_state lbl :=
sch.current <$> req <*> sch_state.queue

def rank (l : lbl) : var sch_state ℕ :=
λ (s : sch_state), s.queue.g l + (s.queue.g l - s.q_len)

lemma pending_not_move (s : sch_state) (l : lbl)
  (h : succ s.q_len ≤ s.queue.g l)
: ((sch.step s).queue).g l = s.queue.g l :=
begin
  dunfold sch.step sch_state.queue shift,
  cases decidable.em (first ((req t).apply s) s.queue < succ s.q_len) with h' h',
  { rw [dif_pos h',comp_g],
    unfold comp,
    rw bijection.rotate_right'_g_eq_of_ge_j _ h' h, },
  { rw dif_neg h', },
end

lemma shift_down (s : sch_state) (l : lbl)
  (h₀ : first (req.apply s) s.queue < s.queue.g l)
  (h₁ : s.queue.g l < succ s.q_len)
: succ (((sch.step s).queue).g l) = s.queue.g l :=
begin
  dunfold sch.step sch_state.queue shift,
  have h : first ((req t).apply s) s.queue < succ s.q_len := lt_trans h₀ h₁,
  rw [dif_pos h,comp_g], unfold comp,
  rw bijection.succ_rotate_right'_g_eq_self (s.queue.g l) _ h₀ h₁,
end

lemma q_len_inc (s : sch_state)
: (sch.step s).q_len = succ s.q_len :=
by { rw ← add_one, refl }

lemma not_req_not_move (s : sch_state) (l : lbl)
  (h : s.queue.g l < first (req.apply s) s.queue)
: (sch.step s).queue.g l = s.queue.g l :=
begin
  dunfold sch.step sch_state.queue shift,
  cases decidable.em (first ((req t).apply s) s.queue < succ s.q_len) with h' h',
  { rw [dif_pos h',comp_g],
    unfold comp,
    rw [bijection.rotate_right'_g_eq_of_lt_i _ _ h], },
  { rw [dif_neg h'] },
end

lemma not_mem_req {s : sch_state} {l : lbl}
  (h : first (req.apply s) s.queue > s.queue.g l)
: l ∉ req.apply s :=
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
  (Hgt : s.queue.g l < first (req.apply s) s.queue)
: (rank l).apply (sch.step s) ≤ (rank l).apply s :=
begin
  unfold rank,
  cases le_or_gt (s.queue.g l) (s.q_len) with h h,
  { have h' : s.queue.g l ≤ succ s.q_len := le_succ_of_le h,
    simp [not_req_not_move _ _ _ Hgt,q_len_inc
         ,sub_eq_zero_of_le h,sub_eq_zero_of_le h'] },
  { simp [pending_not_move _ _ _ h,q_len_inc],
    apply nat.sub_le_sub_left,
    apply le_succ, },
end

lemma lt_rank_of_gt_first {s : sch_state} {l : lbl}
  (Hlt : first (req.apply s) (s.queue) < (s.queue).g l)
: (rank l).apply (sch.step s) < (rank l).apply s :=
begin
  unfold rank,
  cases le_or_gt s.q_len (first ((req t).apply s) s.queue) with h h,
    -- h : s.q_len ≤ first (sch_state.req s) (s.queue)
  { have h' : s.q_len < s.queue.g l := lt_of_le_of_lt h Hlt,
    simp [pending_not_move _ _ _ h'],
    dunfold sch.step sch_state.q_len,
    rw [sub_succ],
    apply pred_lt_self_of_pos,
    apply nat.sub_pos_of_lt,
    apply lt_of_lt_of_le h',
    refl },
    -- h : s.q_len > first (sch_state.req s) (s.queue)
  { cases lt_or_ge (s.queue.g l) (succ s.q_len) with Hlt_len Hge_len,
      -- Hlt_len : (s.queue).g l < succ (s.q_len)
    { simp,
      rw [← shift_down _ s _ Hlt Hlt_len,q_len_inc],
      { apply add_lt_add_of_lt_of_le,
        { apply lt_succ_self },
        { apply nat.sub_le_sub
          ; apply le_succ, } }, },
      -- Hge_len : (s.queue).g l ≥ succ (s.q_len)
    { unfold gt at h,
      simp [pending_not_move _ _ _ Hge_len,q_len_inc],
      { apply nat.sub_lt_sub_left Hge_len,
        apply lt_succ_self, }, } }
end
variable {s : sch_state}

lemma eq_next_or_rank_eq_or_rank_lt {l : lbl} (v : ℕ)
  (h : s ⊨ rank l ≃ v)
: s ⊨ current ≃ l ∨
  ( s ⊨ -(↑l ∊ req) ∧ sch.step s ⊨ rank l ≃ v ) ∨
  sch.step s ⊨ rank l ≺ v :=
begin
  rw or_iff_not_imp,
  intro Hnnext,
  simp [current,sch.current,req] at Hnnext ⊢,
  simp at h,
  rw bijection.inverse at Hnnext,
  cases lt_or_gt_of_ne Hnnext with Hlt Hgt ; clear  Hnnext,
  { right,
    rw ← h,
    apply lt_rank_of_gt_first t _ ,
    simp [req,Hlt] },
  { unfold gt at Hgt,
    subst v,
    have := le_rank_of_lt_first _, simp [req] at this,
    specialize this Hgt,
    cases lt_or_eq_of_le this with Hlt Heq,
    { right, apply Hlt },
    { left,
      split,
      { have := not_mem_req _ , simp [req] at this,
        apply this, assumption },
      { apply Heq, }, } },
end

lemma fair_schedule_step  (l : lbl) (v : ℕ)
:  ↑l ∊ req ⋀ (rank l ≃ ↑v) ↦ (rank l ≺ v) ⋁ (current ≃ l) in scheduler :=
begin
  unfold scheduler,
  apply leads_to_step,
  intros σ Heq Hnnext,
  simp, simp at Heq,
  cases Heq with Hmem Heq,
  have HH := eq_next_or_rank_eq_or_rank_lt t v,
  -- simp [rank,current,req] at HH,
  specialize HH Heq,
  rw or_iff_not_imp at HH,
  simp [not_or_iff_not_and_not] at Hnnext,
  have Hnnext' : ¬ (current t).apply σ = l := Hnnext.right,
  have HH' := HH Hnnext',
  rw [or_iff_not_imp] at HH',
  left, apply HH', clear HH' HH,
  simp [classical.not_and_iff_not_or_not],
  apply or.intro_left _ Hmem,
end

lemma stable_queue_ranking (l : lbl) (v : ℕ)
: unless scheduler (rank l ≃ v) (rank l ≺ v ⋁ current ≃ l) :=
begin
  unfold scheduler,
  apply unless_step,
  intros σ Heq Hnnext,
  simp,
  simp [not_or_iff_not_and_not] at Hnnext,
  have := eq_next_or_rank_eq_or_rank_lt _ _ Heq, simp at this,
  cases this with h h,
  { cases Hnnext.right h },
  cases h with h h,
  { replace Hnnext := Hnnext.right,
    left, rw h.right, },
  { right, left, assumption },
end

lemma INIT
: system.init scheduler (↑sch_state.target ≃ (t.s₀ : var sch_state t.σ)) :=
by simp [system.init,program.init,scheduler,sch.first]

lemma STEP
: co' scheduler
    (λ (σ σ' : sch_state),
       ∃P, σ'.target = t.next (sch.current (req.apply σ) σ.queue) σ.target P) :=
begin
  unfold co',
  intros σ σ',
  unfold step has_safety.step is_step,
  intros H,
  have := σ.inv,
  simp [req],
  -- existsi σ.inv,
  split,
  { rw H,
    unfold scheduler program.step subtype.val sch.step },
  { simp [req,this], }
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

variable {lbl : Type}
variable [infinite lbl]
variable t : scheduling.unitb.target_mch lbl

noncomputable def scheduler_spec
: @scheduling.unitb.scheduler lbl t :=
  { s := program $ sch_state t
  , sem := _
  , F := @scheduler _ _ t
  , ch := current t
  , object := ↑sch_state.target
  , INIT := INIT t
  , STEP := STEP t
  , INV  := INV t
  , PROG := PROG t }

noncomputable instance : unitb.system_sem ((scheduler_spec t).s) :=
(scheduler_spec t).sem

lemma sched' {lbl : Type} [s : infinite lbl] [nonempty lbl]
  (t : target_mch lbl)
: ∃ τ : stream t.σ, fair t τ :=
unitb.scheduling t (scheduling.infinite.scheduler_spec t)

end scheduling.infinite
