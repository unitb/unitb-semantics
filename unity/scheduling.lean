
import data.stream
import unity.temporal
import util.data.bijection
import util.data.perm
import util.data.nat
import util.data.stream
import util.data.list
import util.data.minimum
import util.data.fin

namespace scheduling

open temporal
open classical nat

variable {lbl : Type}

structure fair {lbl : Type} (req : stream (set lbl)) (τ : stream lbl) : Prop :=
  (valid : ∀ i, req i = ∅ ∨ τ i ∈ req i)
  (fair : ∀ l, ([]<>•mem l) req → ([]<>•eq l) τ)

open stream

def req_of {lbl} (r : list lbl → set lbl) (τ : stream lbl) : stream (set lbl) :=
λ i, r (approx i τ)

lemma req_of_comp_length {lbl} (r : stream (set lbl)) (τ : stream lbl)
: req_of (r ∘ list.length) τ = r :=
begin
  unfold req_of function.comp,
  simp [length_approx],
end

lemma req_of_succ {lbl} (r : list lbl → set lbl) (τ : stream lbl) (i : ℕ)
: req_of r τ (succ i) = req_of (r ∘ flip list.concat (τ i)) τ i :=
begin
  unfold req_of function.comp flip,
  rw approx_succ_eq_concat,
end

class inductive sched (lbl : Type)
  | fin : finite lbl → sched
  | inf : infinite lbl → sched

noncomputable def fin.first [pos_finite lbl] (req : set lbl)
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
: fin $ succ $ pos_finite.pred_count lbl :=
minimum { x | l.f x ∈ req }

noncomputable def fin.select [pos_finite lbl] (req : set lbl)
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
: bijection (fin $ succ $ pos_finite.pred_count lbl) lbl :=
l ∘ rev (perm.rotate_right (fin.first req l))

local infixr ∘ := function.comp

lemma fin.selected [pos_finite lbl] (req : set lbl)
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
  (h : req ≠ ∅)
: (fin.select req l).f fin.max ∈ req :=
begin
  unfold fin.select,
  rw [comp_f,rev_f],
  unfold function.comp,
  rw perm.rotate_right_g_max,
  unfold fin.first,
  apply minimum_mem {x : fin (succ (pos_finite.pred_count lbl)) | l.f x ∈ req},
  note h' := exists_mem_of_ne_empty _ h,
  cases h' with x h',
  apply (@set.ne_empty_of_mem _ _ $ l.g x),
  rw [mem_set_of,bijection.g_inv],
  apply h',
end

lemma fin.progress [pos_finite lbl]
  {x : lbl}
  {req : set lbl}
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
  (h : x ∈ req)
: (fin.select req l).f fin.max = x ∨ ((fin.select req l).g x).succ = l.g x :=
begin
  unfold fin.select,
  rw [comp_f,rev_f,comp_g,rev_g],
  unfold function.comp,
  assert H : fin.first req l < l.g x ∨ fin.first req l = l.g x,
  { apply lt_or_eq_of_le,
    unfold fin.first,
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

open list

def fin.last {n α} (l : bijection (fin $ succ n) α) : α :=
l.f fin.max

def state_t.last [pos_finite lbl] (s : state_t) : lbl := fin.last s.queue

def state_t.mk' [pos_finite lbl]
       (req : list lbl → set lbl)
       (h : list lbl)
       (q : bijection _ _)
: state_t :=
   { hist := h.concat (fin.last q)
   , queue := q }

noncomputable def fin.state [pos_finite lbl] (req : list lbl → set lbl)
: stream state_t
  | 0 := state_t.mk' req nil $ fin.select (req nil) (rev (finite.to_nat _))
  | (succ n) :=
      match fin.state n with
      | state_t.mk h q := state_t.mk' req h $ fin.select (req h) q
      end

def state_t.req [pos_finite lbl] (s : state_t) (req : list lbl → set lbl) : set lbl :=
req s.hist

noncomputable def state_t.select [pos_finite lbl] (req : list lbl → set lbl) (s : state_t)
: bijection (fin (succ _)) lbl :=
fin.select (s.req req) s.queue

lemma fin.state_succ_hist {lbl : Type} [s : pos_finite lbl]
  (req : list lbl → set lbl) (i : ℕ)
: (fin.state req (succ i)).hist = concat (fin.state req i).hist (fin.state req (succ i)).last :=
begin
  unfold fin.state,
  cases (fin.state req i),
  refl,
end

lemma fin.state_succ_queue {lbl : Type} [s : pos_finite lbl]
  (req : list lbl → set lbl) (i : ℕ)
: (fin.state req (succ i)).queue = state_t.select req (fin.state req i) :=
begin
  unfold fin.state,
  cases (fin.state req i),
  refl
end

lemma fin.not_hist_eq_nil
  [pos_finite lbl]
  (req : list lbl → set lbl)
  (i : ℕ)
: (fin.state req i).hist ≠ [ ] :=
begin
  cases i,
  { contradiction },
  { rw fin.state_succ_hist,
    apply not_concat_eq_nil }
end

lemma fin.select_queue_eq_ilast_hist
  [pos_finite lbl]
  (req : list lbl → set lbl)
  (i : ℕ)
: (fin.state req i).queue.f fin.max = ilast (fin.state req i).hist :=
begin
  cases i,
  { refl },
  { rw [fin.state_succ_queue,fin.state_succ_hist,ilast_concat],
    unfold state_t.last,
    rw fin.state_succ_queue,
    refl }
end

lemma fin.state_fst {lbl : Type} [s : pos_finite lbl]
  (req : list lbl → set lbl)
: req_of req (state_t.last ∘ fin.state req) = req ∘ front ∘ state_t.hist ∘ fin.state req :=
begin
  apply funext, intro i,
  pose r := req,
  change req_of r _ _ = (r ∘ _) _,
  generalize r r,
  induction i with i IH ; intro r,
  { refl },
  { rw [req_of_succ,IH],
    unfold function.comp flip,
    rw fin.state_succ_hist,
    apply congr_arg, unfold fin.state,
    note H := fin.select_queue_eq_ilast_hist req i,
    note H' := fin.not_hist_eq_nil req i,
    cases (fin.state req i),
    unfold fin.state._match_1 state_t.mk' state_t.hist,
    unfold state_t.last fin.last state_t.queue,
    rw front_concat,
    apply front_last_eq,
    { apply not_concat_eq_nil },
    { apply H' },
    -- we need proofs that the history lists are not empty because of last
    -- can we use something else?
    rw front_concat ,
    rw [ilast_concat ],
    apply H },
end

lemma fin.hist_eq_approx  [s : pos_finite lbl]
  (r : list lbl → set lbl)
  (i : ℕ)
: (fin.state r i).hist = approx (succ i) (fin.last ∘ state_t.queue ∘ fin.state r) :=
begin
  induction i with i IH ;
  unfold fin.state state_t.hist,
  { refl, },
  { rw [approx_succ_eq_concat,-IH],
    destruct (fin.state r i),
    intros hist queue Hstate,
    unfold function.comp,
    rw Hstate,
    unfold fin.state._match_1 state_t.hist state_t.select state_t.req,
    unfold state_t.queue  state_t.hist fin.last state_t.mk',
    apply congr_arg,
    unfold fin.state,
    rw Hstate,
    unfold fin.state._match_1 state_t.mk' state_t.queue,
    refl }
end

lemma fin.sched' {lbl : Type} [s : pos_finite lbl]
  (r : list lbl → set lbl)
: ∃ τ : stream lbl, fair (req_of r τ) τ :=
begin
  definev τ : stream lbl := state_t.last ∘ fin.state r,
  existsi τ,
  apply fair.mk,
  { intro i,
    rw or_iff_not_imp,
    induction i with i IH ; intro h,
    { revert τ, simp,
      apply fin.selected _ (rev (pos_finite.to_nat lbl)), },
    { revert τ, simp, intros h',
      unfold function.comp state_t.last fin.state fin.last,
      note HHH := fin.hist_eq_approx r i,
      cases (fin.state r i),
      unfold state_t.hist at HHH,
      unfold fin.state._match_1 state_t.queue state_t.mk',
      assert HH' : req_of r (λ (x : ℕ), ((fin.state r x).queue).f fin.max) (succ i) = r hist,
      { rw HHH, refl },
      rw [HH'],
      apply fin.selected }, },
  { intros l,
    revert τ, simp,
    intro h,
    rw [ fin.state_fst r,-function.comp.assoc,-function.comp.assoc
       , -inf_often_trace_init_trading] at h,
    rw -inf_often_trace_init_trading,
    definev VAR : @state_t lbl _ → fin (succ (pos_finite.pred_count lbl)) := (λs, s.queue.g l),
    definev inst : decidable_pred (mem l ∘ (r ∘ front) ∘ state_t.hist : @state_t lbl _ → Prop) :=
       (λ x, prop_decidable _),
    apply inf_often_induction VAR _ _ (measure_wf fin.val) h,
    { clear h,
      intro i, rw action_drop,
      unfold function.comp,
      cases decidable.em (l ∈ r (front ((fin.state r (succ i)).hist)))
            with h h,
      { rw if_pos h,
        rw [fin.state_succ_hist,front_concat] at h,
        pose HH := (fin.state r i).queue,
        apply or.imp _ _ (fin.progress HH h),
        { intro h', admit },
        { admit }, },
      { admit } } }
end

lemma fin.sched {lbl : Type} [s : pos_finite lbl]
  (req : stream (set lbl))
: ∃ τ : stream lbl, fair req τ :=
begin
  note h := fin.sched' (req ∘ list.length),
  apply exists_imp_exists _ h,
  intro τ,
  assert H : req = req_of (req ∘ list.length) τ,
  { apply funext,
    unfold req_of function.comp,
    intro i, rw length_approx, },
  rw -H,
  apply id,
end

lemma inf.sched' {lbl : Type} [s : infinite lbl] [nonempty lbl]
  (r : list lbl → set lbl)
: ∃ τ : stream lbl, fair (req_of r τ) τ :=
sorry

lemma sched.sched_str {lbl : Type} [s : sched lbl] [nonempty lbl]
  (r : list lbl → set lbl)
: ∃ τ : stream lbl, fair (req_of r τ) τ :=
begin
  cases s with _fin _inf,
  { apply fin.sched' ; apply pos_of_finite  ; apply_instance },
  { apply inf.sched' ; apply_instance },
end

instance {lbl} [i : nonempty lbl] : nonempty (stream lbl) :=
begin
  cases i with l,
  apply nonempty.intro,
  intro i, apply l,
end

noncomputable def fair_sched_of [nonempty lbl] [sched lbl] (req : list lbl → set lbl)
: stream lbl :=
classical.some (sched.sched_str req)

noncomputable def fair_sched_of' [nonempty lbl] [sched lbl] (req : stream (set lbl))
: stream lbl := fair_sched_of (req ∘ list.length)

lemma fair_sched_of_spec {lbl : Type} [nonempty lbl] [sched lbl] (r : list lbl → set lbl)
: fair (req_of r (fair_sched_of r)) (fair_sched_of r) :=
by apply classical.some_spec (sched.sched_str r)

lemma fair_sched_of_spec' {lbl : Type} [nonempty lbl] [sched lbl] (r : stream (set lbl))
: fair r (fair_sched_of' r) :=
begin
  note H :=  fair_sched_of_spec (r ∘ list.length),
  rw req_of_comp_length r (fair_sched_of (r ∘ list.length)) at H,
  apply H,
end

lemma fair_sched_of_mem  {lbl : Type} [nonempty lbl] [sched lbl] (r : list lbl → set lbl)
  (i : ℕ)
  (Hnemp : req_of r (fair_sched_of r) i ≠ ∅)
: fair_sched_of r i ∈ req_of r (fair_sched_of r) i :=
begin
  revert Hnemp, rw -or_iff_not_imp,
  apply (fair_sched_of_spec r).valid i,
end

lemma fair_sched_of_mem'  {lbl : Type} [nonempty lbl] [sched lbl] (r : stream (set lbl))
  (i : ℕ)
  (Hnemp : r i ≠ ∅)
: fair_sched_of' r i ∈ r i :=
begin
  rw -req_of_comp_length r (fair_sched_of $ r ∘ list.length) at Hnemp,
  note H := fair_sched_of_mem (r ∘ list.length) i Hnemp,
  rw req_of_comp_length r (fair_sched_of $ r ∘ list.length) at H,
  apply H,
end

lemma fair_sched_of_is_fair  {lbl : Type} [nonempty lbl] [sched lbl]
  (r : list lbl → set lbl)
  (l : lbl)
: ([]<>•mem l) (req_of r (fair_sched_of r)) → ([]<>•eq l) (fair_sched_of r) :=
(fair_sched_of_spec r).fair l

lemma fair_sched_of_is_fair'  {lbl : Type} [nonempty lbl] [sched lbl]
  (r : stream (set lbl))
  (l : lbl)
: ([]<>•mem l) r → ([]<>•eq l) (fair_sched_of' r) :=
begin
  unfold fair_sched_of',
  intro H,
  rw -req_of_comp_length r (fair_sched_of $ r ∘ list.length) at H,
  apply fair_sched_of_is_fair (r ∘ list.length) l H,
end

noncomputable def fair_sched (lbl : Type) [nonempty lbl] [sched lbl] : stream lbl :=
fair_sched_of (λ _ _, true)

lemma fair_sched_is_fair  {lbl : Type} [nonempty lbl] [sched lbl] (l : lbl)
: ([]<>•eq l) (fair_sched lbl) :=
begin
  apply (fair_sched_of_spec _).fair l,
  intro i,
  apply eventually_weaken,
  simp [init_drop],
end

lemma sched.sched_str' {lbl : Type} [s : sched lbl] [nonempty lbl]
  (r : list lbl → set lbl)
: ∃ τ : stream lbl,
  ∀ (l : lbl),
      ([]<>•mem l) (req_of r τ) →
      ([]<>•(λ x : lbl × set lbl, l = x.fst ∧ (l ∈ x.snd ∨ x.snd = ∅))) (zip' τ $ req_of r τ)  :=
begin
  apply exists_imp_exists _ (sched.sched_str r),
  intros τ h l h',
  assert Heq : (λ (x : lbl × set lbl), l = x.fst ∧ (l ∈ x.snd ∨ x.snd = ∅))
            = (λ (x : lbl × set lbl), (x.fst ∈ x.snd ∨ x.snd = ∅) ∧ l = x.fst),
  { apply funext, intro x, cases x with x₀ x₁,
    unfold prod.fst prod.snd,
    rw [-iff_eq_eq],
    assert Hrw : l = x₀ → (l ∈ x₁ ∨ x₁ = ∅ ↔ x₀ ∈ x₁ ∨ x₁ = ∅),
    { intro h, rw h },
    simp [and_congr_right Hrw], },
  rw Heq,
  apply coincidence,
  { apply eventually_weaken,
    intro i, unfold drop zip', simp,
    apply h.valid i, },
  { change (([]<>•(eq l ∘ prod.fst)) (zip' τ $ req_of r τ)),
    rw [inf_often_trace_init_trading,fst_comp_zip'],
    apply h.fair _ h' },
end

lemma sched.sched' (lbl : Type) [nonempty lbl] [sched lbl]
: ∃ τ : stream lbl, ∀ (l : lbl), ([]<>•(eq l)) τ  := ⟨_,fair_sched_is_fair⟩

lemma sched.sched'' (lbl : Type) [nonempty lbl] [sched lbl]
  (req : stream (set lbl))
: ∃ τ : stream lbl,
  ∀ (l : lbl),
    ([]<>•mem l) req →
    ([]<>•(λ x : lbl × set lbl, l = x.fst ∧ (l ∈ x.snd ∨ x.snd = ∅))) (zip' τ req)  :=
begin
  apply exists_imp_exists _ (sched.sched_str' $ req ∘ list.length),
  intro τ,
  apply forall_imp_forall _,
  intros l,
  apply imp_mono _ _
  ; apply eq.substr _,
  { apply req_of_comp_length req τ },
  { apply congr_arg,
    rw req_of_comp_length req τ },
end

instance fin_sched {lbl : Type} [pos_finite lbl] : sched lbl :=
sched.fin (by apply_instance)

instance inf_sched {lbl : Type} [infinite lbl] : sched lbl :=
sched.inf (by apply_instance)

instance sched_option_inf {lbl : Type} : ∀ [sched lbl], sched (option lbl)
  | (sched.inf inf) := sched.inf (by apply_instance)
  | (sched.fin fin) := sched.fin (by apply_instance)

end scheduling
