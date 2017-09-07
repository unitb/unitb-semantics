
import data.set

import unitb.semantics.temporal
import unitb.refinement.basic
import unitb.scheduling
import unitb.models.nondet

import util.cast

namespace hidden_state

universe variable u

open nondet temporal predicate classical

section defs

variables {α β σ : Type}

structure refined
       (f : α → σ)
       (ma : program α)
       (g : β → σ)
       (mc : program β) :=
  (glue : α → β → Prop)
  (obs_cons : ∀ a c, glue a c → f a = g c)
  (bij : mc.lbl = ma.lbl)
  (sim_init : ∀ c₀, mc^.first c₀
            → ∃ a₀, ma^.first a₀ ∧ glue a₀ c₀)
  (sim' : ∀ e c c' a, glue a c
           → mc.step_of e c c'
           → ∃ a',  ma.step_of (e.cast bij) a a'
                  ∧ glue a' c')
  (coarse : ∀ e a c, glue a c
               → (  mc.coarse_sch_of e c
                  ↔ ma.coarse_sch_of (e.cast bij) a))
  (fine : ∀ e a c, glue a c
               → (  mc.fine_sch_of e c
                  ↔ ma.fine_sch_of (e.cast bij) a))

end defs

open unitb.refinement

section thm

open unitb

parameters {α β σ : Type}

parameters
       {f : α → σ}
       {ma : program α}
       {g : β → σ}
       {mc : program β}

parameter R : refined f ma g mc

parameter [nonempty (unitb.state (program α))]
parameter Tc : stream (unitb.state (program β))
parameter Hc : system_sem.ex mc Tc

open nat

parameters Tc mc
def Tevts  : stream (set (option (mc.lbl))) :=
  λ i, { e | mc.step_of e (Tc i) (Tc (succ i)) }
parameters {Tc mc}

include Hc
lemma Tevts_ne_empty (i : ℕ)
: Tevts i ≠ ∅ :=
begin
  apply set.ne_empty_of_exists_mem,
  unfold Tevts,
  simp [mem_set_of],
  have H := system_sem.safety _ _ Hc i,
  rw action_drop at H,
  apply H,
end
omit Hc

open scheduling

-- noncomputable def Tevt [sched mc.lbl] : stream (option (mc.lbl)) :=
-- fair_sched_of (Tevts ∘ list.length)

-- include Hc

instance mc_sched : sched mc.lbl := mc.lbl_is_sched

instance ma_sched : sched ma.lbl := ma.lbl_is_sched

-- instance option_ma_sched : sched (option ma.lbl) :=
-- by { apply scheduling.sched_option,
--      apply hidden_state.ma_sched }

-- include mc_sched

-- example (i : ℕ) : mc.step_of (Tevt i) (Tc i) (Tc $ succ i) :=
-- begin
--   unfold Tevt Tevts,
--   assert H : Tevts mc Tc i ≠ ∅,
--   { unfold Tevts,
--     note Hsaf := Hc.safety i,
--     rw [action_drop] at Hsaf,
--     cases Hsaf with e He,
--     apply @set.ne_empty_of_mem _ _ e He },
--   note H' := fair_sched_of_mem' (Tevts mc Tc) i H,
--   unfold Tevts at H',
--   apply H',
-- end

-- omit Hc

structure sim_state :=
  (index : ℕ)
  (abs_state : α)
  (glued : R.glue abs_state (Tc index))

noncomputable def mk_state {p : α → Prop}  {i : ℕ} (P : ∃ x, p x ∧ R.glue x (Tc i))
: sim_state :=
⟨i,some P,and.right $ some_spec P⟩

lemma fst_mk_state {p : α → Prop}  {i : ℕ} (P : ∃ x, p x ∧ R.glue x (Tc i))
: (mk_state P).index = i := rfl

include Hc
def object_req_ne_emp (i : ℕ)
: {l' : option (ma.lbl) | option.cast' l' (R.bij) ∈ Tevts i} ≠ ∅ :=
begin
  have H : {l' : option (ma.lbl) | option.cast' l' (R.bij) ∈ Tevts mc Tc i}
          = (λ l, option.cast l R.bij) <$> Tevts mc Tc i,
  { apply set.ext, intro l,
    have Hinj : function.injective (λ (l : option (mc.lbl)), option.cast l (R.bij)) :=
       option_cast_injective R.bij,
    rw [mem_set_of,set.mem_fmap_iff_mem_of_bij Hinj],
    apply option.cast_left_inverse, },
  simp [H,set.fmap_eq_empty_iff_eq_empty],
  apply Tevts_ne_empty Hc,
end
omit Hc

noncomputable def next_state (l : option ma.lbl) (x : α) (i : ℕ)
  (P : R.glue x (Tc i))
  (Q : program.step_of mc (option.cast' l (R.bij)) (Tc i) (Tc (succ i)))
: sim_state :=
mk_state $ R.sim' (l.cast' R.bij) (Tc i) (Tc $ succ i) x P Q

noncomputable def object : unitb.target_mch (option ma.lbl) :=
{ σ := sim_state
, s₀ := mk_state $ R.sim_init (Tc 0) Hc.init
, req := λ s, { l' | l'.cast' R.bij ∈ Tevts s.index }
, req_nemp := λ s, object_req_ne_emp s.index
, next := λ l s Q, next_state l s.abs_state _ s.glued Q }

-- include ma_sched

noncomputable def Ta' : stream object.σ :=
let this : sched (option ma.lbl) :=
by { apply scheduling.sched_option }
in @fair_sched _ this _ object

noncomputable def Ta : stream (unitb.state (program α)) :=
stream.map sim_state.abs_state Ta'

lemma Ta_fair : fair object Ta' :=
fair_sched_of_spec object

lemma object_next_eq_next_state (l : option ma.lbl) (s : object.σ)
   (P : l ∈ object.req s)
: (object.next l _ P) = next_state l s.abs_state _ s.glued P :=
begin
  cases s with i s, refl,
end

lemma Ta_index (i : ℕ)
: (Ta' i).index = i :=
begin
  induction i with i IH,
  { rw Ta_fair.init, refl },
  { cases fair_sched_succ _ i (Ta_fair R Hc) with l h,
    cases h with P h,
    rw [h,object_next_eq_next_state],
    unfold next_state, rw [fst_mk_state,IH] },
end

include Hc

lemma init_simmed
: R.glue (Ta 0) (Tc 0) ∧ ma^.first (Ta 0) :=
begin
  unfold Ta stream.map stream.nth,
  rw Ta_fair.init,
  dunfold object unitb.target_mch.s₀,
  dunfold mk_state sim_state.abs_state,
  rw and_comm,
  apply some_spec (object._proof_1 R Hc),
end

-- include R

-- lemma conc_step (i : ℕ)
-- : mc.step_of (Tevt i) (Tc i) (Tc (succ i)) :=
-- begin
--   unfold Tevt Tevts,
--   assert H : Tevts mc Tc i ≠ ∅,
--   { unfold Tevts,
--     note Hsaf := Hc.safety i,
--     rw [action_drop] at Hsaf,
--     cases Hsaf with e He,
--     apply @set.ne_empty_of_mem _ _ e He },
--   note H' := fair_sched_of_mem' (Tevts mc Tc) i H,
--   unfold Tevts at H',
--   apply H',
-- end

-- lemma abs_step (i : ℕ) [nonempty α]
--   (J : R.glue (Ta i) (Tc i))
-- :   R.glue (Ta (succ i)) (Tc (succ i))
--   ∧ ma.step_of ((Tevt i).cast R.bij) (Ta i) (Ta (succ i)) :=
-- begin
--   unfold Ta,
--   pose P := (λ a, R.glue a (Tc (succ i)) ∧ ma.step_of ((Tevt _ Tc i).cast R.bij) (Ta _ _ _ _ R Tc i) a),
--   apply @epsilon_spec _ P,
--   revert P, simp,
--   note H' := R.sim' (Tevt _ Tc i) _ (Tc $ succ i) (Ta _ ma _ _ R Tc i) J (conc_step _ _ _ _ R Tc Hc i),
--   apply exists_imp_exists _ H',
--   intro, apply (and_comm _ _).mp,
-- end

theorem glued [nonempty α] (i : ℕ) : R.glue (Ta i) (Tc i) :=
begin
  have H := (Ta' R Hc i).glued,
  rw Ta_index at H,
  apply H,
end

-- include R

theorem simmed [nonempty α] (i : ℕ) : is_step ma (Ta i) (Ta (succ i)) :=
begin
  apply exists_imp_exists _ (fair_sched_succ _ i $ Ta_fair R Hc),
  intros e h, cases h with P h,
  unfold Ta stream.map stream.nth,
  rw h,
  admit,
  -- apply is_step_inst _ _,
  -- apply (abs_step _ _ _ _ R _ Hc i _).right,
  -- apply glued _ _ _ _ _ _ Hc,
  -- apply_instance,
end

open unitb

include R

theorem soundness [nonempty α] : data_ref ma f mc g :=
begin
  intros Tc Hc,
  existsi (Ta R Hc),
  split,
  apply program.ex.mk ,
  { apply (init_simmed _ Hc).right },
  { intro i,
    unfold action step has_safety.step stream.drop,
    simp [add_one],
    apply simmed _ Hc,
    apply_instance },
  { intros ea,
    let ec := (option.cast' ea (R.bij)),
    apply imp_mono _ _ (Hc.liveness ec),
    { apply iff.mp,
      apply exists_congr, intro i,
      apply forall_congr, intro j,
      unfold temporal.init stream.drop,
      let ec := (option.cast' ea (R.bij)),
      rw [R.coarse ec,option_cast_cast'],
      apply glued },
    apply imp_mono _ _,
    { apply iff.mp _,
      apply forall_congr, intro j,
      apply exists_congr, intro i,
      unfold temporal.init stream.drop,
      have HHH:= R.fine ec _ _ (glued R Hc $ 0 + i + j),
      repeat { rw [p_and_to_fun,init_to_fun,init_to_fun] },
      rw [HHH,option_cast_cast'] },
    { intro Hevt,
      admit } },
  { apply funext, intro i,
    unfold function.comp,
    symmetry,
    apply R.obs_cons,
    apply glued },
end

end thm

end hidden_state
