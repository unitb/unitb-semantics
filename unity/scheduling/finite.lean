
import data.stream

import util.data.bijection
import util.data.minimum
import util.data.list
import util.data.perm
-- import data.stream

import unity.scheduling.basic

namespace scheduling.finite

open nat scheduling stream temporal classical

variable {lbl : Type}

noncomputable def first [pos_finite lbl] (req : set lbl)
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
: fin $ succ $ pos_finite.pred_count lbl :=
minimum { x | l.f x ∈ req }

noncomputable def select [pos_finite lbl] (req : set lbl)
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
: bijection (fin $ succ $ pos_finite.pred_count lbl) lbl :=
l ∘ rev (perm.rotate_right (first req l))

local infixr ∘ := function.comp

lemma selected [pos_finite lbl] (req : set lbl)
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
  (h : req ≠ ∅)
: (select req l).f fin.max ∈ req :=
begin
  unfold select,
  rw [comp_f,rev_f],
  unfold function.comp,
  rw perm.rotate_right_g_max,
  unfold first,
  apply minimum_mem {x : fin (succ (pos_finite.pred_count lbl)) | l.f x ∈ req},
  note h' := exists_mem_of_ne_empty _ h,
  cases h' with x h',
  apply (@set.ne_empty_of_mem _ _ $ l.g x),
  rw [mem_set_of,bijection.g_inv],
  apply h',
end

lemma progress [pos_finite lbl]
  {x : lbl}
  {req : set lbl}
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
  (h : x ∈ req)
: (select req l).f fin.max = x ∨ ((select req l).g x).succ = l.g x :=
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
    rw [perm.rotate_right_f_lt_shifted _ _ H,fin.succ_pred],
    rw [fin.lt_def,fin.zero_def],
    rw [fin.lt_def] at H,
    apply lt_of_le_of_lt (zero_le _) H, },
  { left,
    rw [perm.rotate_right_g_max,H],
    apply bijection.g_inv }
end

structure state_t [pos_finite lbl] :=
  (hist  : list lbl)
  (queue : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)

def last {n α} (l : bijection (fin $ succ n) α) : α :=
l.f fin.max

def state_t.last [pos_finite lbl] (s : state_t) : lbl := last s.queue

def state_t.mk' [pos_finite lbl]
       (req : list lbl → set lbl)
       (h : list lbl)
       (q : bijection _ _)
: state_t :=
   { hist := h.concat (last q)
   , queue := q }

open list

noncomputable def state [pos_finite lbl] (req : list lbl → set lbl)
: stream state_t
  | 0 := state_t.mk' req nil $ select (req nil) (rev (finite.to_nat _))
  | (succ n) :=
      match state n with
      | state_t.mk h q := state_t.mk' req h $ select (req h) q
      end

def state_t.req [pos_finite lbl] (s : state_t) (req : list lbl → set lbl) : set lbl :=
req s.hist

noncomputable def state_t.select [pos_finite lbl] (req : list lbl → set lbl) (s : state_t)
: bijection (fin (succ _)) lbl :=
select (s.req req) s.queue

lemma state_succ_hist {lbl : Type} [s : pos_finite lbl]
  (req : list lbl → set lbl) (i : ℕ)
: (state req (succ i)).hist = concat (state req i).hist (state req (succ i)).last :=
begin
  unfold scheduling.finite.state,
  cases (state req i),
  refl,
end

lemma state_succ_queue {lbl : Type} [s : pos_finite lbl]
  (req : list lbl → set lbl) (i : ℕ)
: (state req (succ i)).queue = state_t.select req (state req i) :=
begin
  unfold scheduling.finite.state,
  cases (state req i),
  refl
end

lemma not_hist_eq_nil
  [pos_finite lbl]
  (req : list lbl → set lbl)
  (i : ℕ)
: (state req i).hist ≠ [ ] :=
begin
  cases i,
  { contradiction },
  { rw state_succ_hist,
    apply not_concat_eq_nil }
end

lemma select_queue_eq_ilast_hist
  [pos_finite lbl]
  (req : list lbl → set lbl)
  (i : ℕ)
: (state req i).queue.f fin.max = ilast (state req i).hist :=
begin
  cases i,
  { refl },
  { rw [state_succ_queue,state_succ_hist,ilast_concat],
    unfold state_t.last,
    rw state_succ_queue,
    refl }
end

lemma state_fst {lbl : Type} [s : pos_finite lbl]
  (req : list lbl → set lbl)
: req_of req (state_t.last ∘ state req) = req ∘ front ∘ state_t.hist ∘ state req :=
begin
  apply funext, intro i,
  pose r := req,
  change req_of r _ _ = (r ∘ _) _,
  generalize r r,
  induction i with i IH ; intro r,
  { refl },
  { rw [req_of_succ,IH],
    unfold function.comp flip,
    rw state_succ_hist,
    apply congr_arg, unfold scheduling.finite.state,
    note H := select_queue_eq_ilast_hist req i,
    note H' := not_hist_eq_nil req i,
    cases (state req i),
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

lemma hist_eq_approx  [s : pos_finite lbl]
  (r : list lbl → set lbl)
  (i : ℕ)
: (state r i).hist = approx (succ i) (last ∘ state_t.queue ∘ state r) :=
begin
  induction i with i IH ;
  unfold scheduling.finite.state state_t.hist,
  { refl, },
  { rw [approx_succ_eq_concat,-IH],
    destruct (state r i),
    intros hist queue Hstate,
    unfold function.comp,
    rw Hstate,
    unfold state._match_1 state_t.hist state_t.select state_t.req,
    unfold state_t.queue  state_t.hist last state_t.mk',
    apply congr_arg,
    unfold scheduling.finite.state,
    rw Hstate,
    unfold state._match_1 state_t.mk' state_t.queue,
    refl }
end

lemma sched' {lbl : Type} [s : pos_finite lbl]
  (r : list lbl → set lbl)
: ∃ τ : stream lbl, fair (req_of r τ) τ :=
begin
  definev τ : stream lbl := state_t.last ∘ state r,
  existsi τ,
  apply fair.mk,
  { intro i,
    rw or_iff_not_imp,
    induction i with i IH ; intro h,
    { revert τ, simp,
      apply selected _ (rev (pos_finite.to_nat lbl)), },
    { revert τ, simp, intros h',
      unfold function.comp state_t.last scheduling.finite.state last,
      note HHH := hist_eq_approx r i,
      cases (state r i),
      unfold state_t.hist at HHH,
      unfold state._match_1 state_t.queue state_t.mk',
      assert HH' : req_of r (λ (x : ℕ), ((state r x).queue).f fin.max) (succ i) = r hist,
      { rw HHH, refl },
      rw [HH'],
      apply selected }, },
  { intros l,
    revert τ, simp,
    intro h,
    rw [ state_fst r,-function.comp.assoc,-function.comp.assoc
       , -inf_often_trace_init_trading] at h,
    rw -inf_often_trace_init_trading,
    definev VAR : @state_t lbl _ → fin (succ (pos_finite.pred_count lbl)) := (λs, s.queue.g l),
    definev inst : decidable_pred (mem l ∘ (r ∘ front) ∘ state_t.hist : @state_t lbl _ → Prop) :=
       (λ x, prop_decidable _),
    apply inf_often_induction VAR _ _ (measure_wf fin.val) h,
    { clear h,
      intro i, rw action_drop,
      unfold function.comp,
      cases decidable.em (l ∈ r (front ((state r (succ i)).hist)))
            with h h,
      { rw if_pos h,
        rw [state_succ_hist,front_concat] at h,
        apply or.imp _ _ (progress ((state r i).queue) h),
        { intro h', admit },
        { admit }, },
      { admit } } }
end

end scheduling.finite
