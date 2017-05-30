
import data.stream

import util.data.bijection
import util.data.minimum
import util.data.list
import util.data.perm

import unity.scheduling.basic

namespace scheduling.finite

open nat scheduling stream temporal classical

section

parameter {lbl : Type}
parameter [pos_finite lbl]

noncomputable def first (req : set lbl)
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
: fin $ succ $ pos_finite.pred_count lbl :=
has_minimum.minimum { x | l.f x ∈ req }

noncomputable def select (req : set lbl)
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
: bijection (fin $ succ $ pos_finite.pred_count lbl) lbl :=
l ∘ rev (perm.rotate_right (first req l))

local infixr ∘ := function.comp

lemma selected (req : set lbl)
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
  (h : req ≠ ∅)
: (select req l).f fin.max ∈ req :=
begin
  unfold select,
  rw [comp_f,rev_f],
  unfold function.comp,
  rw perm.rotate_right_g_max,
  unfold first,
  apply @minimum_mem _ _ {x : fin (succ (pos_finite.pred_count lbl)) | l.f x ∈ req},
  note h' := exists_mem_of_ne_empty h,
  cases h' with x h',
  apply (@set.ne_empty_of_mem _ _ $ l.g x),
  rw [mem_set_of,bijection.g_inv],
  apply h',
end

lemma safety
  (x : lbl)
  (req : set lbl)
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
: (select req l).f fin.max = x ∨ ((select req l).g x).val ≤ (l.g x).val :=
begin
  unfold select,
  rw [comp_f,comp_g,or_iff_not_imp], unfold function.comp,
  rw [bijection.inverse,rev_f,rev_g],
  rw perm.rotate_right_g_max,
  intro h,
  cases lt_or_gt_of_ne h with Hlt Hgt,
  { rw [perm.rotate_right_f_lt_shifted _ _ Hlt,fin.pred_def],
    apply pred_le },
  { rw [perm.rotate_right_f_gt_eq_self _ _ Hgt], },
end

lemma progress
  {x : lbl}
  {req : set lbl}
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
  (h : x ∈ req)
: (select req l).f fin.max = x ∨ succ ((select req l).g x).val = (l.g x).val :=
begin
  unfold select,
  rw [comp_f,rev_f,comp_g,rev_g],
  unfold function.comp,
  assert H : first req l < l.g x ∨ first req l = l.g x,
  { apply lt_or_eq_of_le,
    unfold first,
    apply minimum_le,
    rw [mem_set_of,bijection.g_inv],
    apply h },
  cases H with H H,
  { right,
    rw [perm.rotate_right_f_lt_shifted _ _ H,fin.pred_def,succ_pred_eq_of_pos],
    rw [fin.lt_def] at H,
    apply lt_of_le_of_lt (zero_le _) H, },
  { left,
    rw [perm.rotate_right_g_max,H],
    apply bijection.g_inv }
end

structure state_t :=
  (hist  : list lbl)
  (queue : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)


def state_t.last (s : state_t) : lbl := s.queue.f fin.max

parameter requests : list lbl → set lbl

def state_t.mk'
       (h : list lbl)
       (q : bijection _ _)
: state_t :=
   { hist := h.concat (q.f fin.max)
   , queue := q }

open list

noncomputable def state
: stream state_t
  | 0 := state_t.mk' nil $ select (requests nil) (rev (finite.to_nat _))
  | (succ n) :=
      match state n with
      | state_t.mk h q := state_t.mk' h $ select (requests h) q
      end

def state_t.req (s : state_t) : set lbl :=
requests s.hist

noncomputable def state_t.select (s : state_t)
: bijection (fin (succ _)) lbl :=
select (s.req requests) s.queue

lemma state_succ_hist
  (i : ℕ)
: (state (succ i)).hist = concat (state i).hist (state (succ i)).last :=
begin
  unfold scheduling.finite.state,
  cases (state requests i),
  refl,
end

lemma state_succ_queue
  (i : ℕ)
: (state (succ i)).queue = state_t.select (state i) :=
begin
  unfold scheduling.finite.state,
  cases (state requests i),
  refl
end

lemma not_hist_eq_nil
  (i : ℕ)
: (state i).hist ≠ [ ] :=
begin
  cases i,
  { contradiction },
  { rw state_succ_hist,
    apply not_concat_eq_nil }
end

lemma select_queue_eq_ilast_hist
  (i : ℕ)
: (state i).queue.f fin.max = ilast (state i).hist :=
begin
  cases i,
  { refl },
  { rw [state_succ_queue,state_succ_hist,ilast_concat],
    unfold state_t.last,
    rw state_succ_queue }
end

lemma state_fst
: req_of requests (state_t.last ∘ state) = requests ∘ front ∘ state_t.hist ∘ state :=
begin
  apply funext, intro i,
  pose r := requests,
  change req_of r _ _ = (r ∘ _) _,
  generalize r r,
  induction i with i IH ; intro r,
  { refl },
  { rw [req_of_succ,IH],
    unfold function.comp flip,
    rw state_succ_hist,
    apply congr_arg, unfold scheduling.finite.state,
    note H := select_queue_eq_ilast_hist requests i,
    note H' := not_hist_eq_nil requests i,
    cases (state requests i),
    unfold state._match_1 state_t.mk' state_t.hist,
    unfold state_t.last last state_t.queue,
    rw front_concat,
    apply front_last_eq,
    { apply not_concat_eq_nil },
    { apply H' },
    rw front_concat ,
    rw [ilast_concat ],
    apply H },
end

lemma hist_eq_approx (i : ℕ)
: (state i).hist = approx (succ i) (state_t.last ∘ state) :=
begin
  induction i with i IH ,
  { refl, },
  { rw [approx_succ_eq_concat,-IH],
    destruct (state requests i),
    intros hist queue Hstate,
    unfold function.comp,
    unfold scheduling.finite.state state_t.hist,
    rw [Hstate],
    unfold state._match_1 state_t.queue  state_t.hist last state_t.mk',
    refl, }
end

section variant

parameter l : lbl

def VAR (s : state_t) : ℕ := ((s.queue).g l).val

lemma variant
: ([]⟦λ (s s' : state_t),
         l = state_t.last s'
       ∨ VAR s' < VAR s
       ∨ ¬(l ∈ requests (front $ state_t.hist s')) ∧ VAR s = VAR s'⟧)
    state :=
begin
  intro i, rw action_drop,
  unfold function.comp,
  cases classical.em (l ∈ requests (front ((state requests (succ i)).hist)))
        with h h,
  { rw [eq_true_intro h,not_true,false_and,or_false],
    rw [state_succ_hist,front_concat] at h,
    apply or.imp _ _ (progress ((state requests i).queue) h),
    { intro h',
      unfold state_t.last,
      rw -h',
      unfold state_t.last,
      rw state_succ_queue,
      refl },
    { intros h',
      unfold measure inv_image,
      unfold VAR,
      rw [state_succ_queue,-h'],
      apply nat.le_of_eq,
      refl, }, },
  { rw [eq_false_intro h,not_false_iff,true_and],
    apply or.imp _ _ (safety l
         (requests (state requests i).hist)
         (state requests i).queue),
    { intro, subst l,
      unfold state_t.last,
      rw state_succ_queue, refl },
    { intro h',
      unfold VAR, unfold VAR,
      note h'' := lt_or_eq_of_le h',
      simp, simp at h'',
      apply or.imp _ _ h'' ; clear h'' h',
      { intro h',
        tactic.whnf_target,
        rw [-h',state_succ_queue], refl },
      { unfold measure inv_image,
        rw state_succ_queue,
        apply id, }, } }
end

end variant
lemma sched'
: ∃ τ : stream lbl, fair (req_of requests τ) τ :=
begin
  pose τ : stream lbl := λ i, (state requests i).last,
  existsi τ,
  apply fair.mk,
  { intro i,
    rw or_iff_not_imp,
    induction i with i IH ; intro h,
    { revert τ, simp,
      apply selected _ (rev (pos_finite.to_nat lbl)), },
    { revert τ, simp, intros h',
      unfold function.comp state_t.last scheduling.finite.state last,
      note HHH := hist_eq_approx requests i,
      cases (state requests i),
      unfold state_t.hist at HHH,
      unfold state._match_1 state_t.queue state_t.mk',
      assert HH' : req_of requests (λ (x : ℕ), ((state requests x).queue).f fin.max) (succ i) = requests hist,
      { rw HHH, refl },
      rw [HH'],
      apply selected }, },
  { intros l,
    revert τ, simp,
    intro h,
    rw [ state_fst requests,-function.comp.assoc,-function.comp.assoc
       , -inf_often_trace_init_trading] at h,
    rw -inf_often_trace_init_trading,
    pose VAR : state_t  → ℕ := (λs, (s.queue.g l).val),
    apply inf_often_induction VAR _ _ lt_wf h,
    apply variant },
end

end

end scheduling.finite
