
import data.set

import unity.temporal
import unity.refinement
import unity.scheduling
import unity.models.nondet

import util.cast

namespace hidden_state

universe variable u

open nondet
open temporal

section defs

variables {α β σ : Type}

structure refined
       (f : α → σ)
       (ma : @prog α)
       (g : β → σ)
       (mc : @prog β) :=
  (glue : α → β → Prop)
  (obs_cons : ∀ a c, glue a c → f a = g c)
  (bij : mc.lbl = ma.lbl)
  (sim_init : ∀ c₀, mc^.first c₀
            → ∃ a₀, glue a₀ c₀ ∧  ma^.first a₀)
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

open unity.refinement

section thm

open unity

parameters {α β σ : Type}

parameters
       (f : α → σ)
       (ma : @prog α)
       (g : β → σ)
       (mc : @prog β)

parameter R : refined f ma g mc

parameter [nonempty (unity.state (@prog α))]
parameter Tc : stream (unity.state (@prog β))
parameter Hc : system_sem.ex mc Tc

open nat

def Tevts  : stream (set (option (mc.lbl))) :=
  λ i, { e | mc.step_of e (Tc i) (Tc (succ i)) }

open scheduling

noncomputable def Tevt [sched mc.lbl] : stream (option (mc.lbl)) :=
fair_sched_of (Tevts ∘ list.length)

include Hc

parameter [sched mc.lbl]

example (i : ℕ) : mc.step_of (Tevt i) (Tc i) (Tc $ succ i) :=
begin
  unfold Tevt Tevts,
  assert H : Tevts mc Tc i ≠ ∅,
  { unfold Tevts,
    note Hsaf := Hc.safety i,
    rw [action_drop] at Hsaf,
    cases Hsaf with e He,
    apply @set.ne_empty_of_mem _ _ e He },
  note H' := fair_sched_of_mem' (Tevts mc Tc) i H,
  unfold Tevts at H',
  apply H',
end

omit Hc

noncomputable def Ta : stream (unity.state (@prog α))
  | 0 := classical.epsilon (λ a, R.glue a (Tc 0) ∧ ma^.first a)
  | (succ n) := classical.epsilon (λ a, R.glue a (Tc (succ n)) ∧ ma.step_of ((Tevt n).cast R.bij) (Ta n) a)

include Hc

lemma init_simmed
: R.glue (Ta 0) (Tc 0) ∧ ma^.first (Ta 0) :=
begin
  unfold Ta,
  apply @classical.epsilon_spec _ (λ a, R.glue a (Tc 0) ∧ ma.first a),
  note H := Hc.init,
  apply R.sim_init _ H,
end

include R

lemma conc_step (i : ℕ)
: mc.step_of (Tevt i) (Tc i) (Tc (succ i)) :=
begin
  unfold Tevt Tevts,
  assert H : Tevts mc Tc i ≠ ∅,
  { unfold Tevts,
    note Hsaf := Hc.safety i,
    rw [action_drop] at Hsaf,
    cases Hsaf with e He,
    apply @set.ne_empty_of_mem _ _ e He },
  note H' := fair_sched_of_mem' (Tevts mc Tc) i H,
  unfold Tevts at H',
  apply H',
end

lemma abs_step (i : ℕ) [nonempty α]
  (J : R.glue (Ta i) (Tc i))
:   R.glue (Ta (succ i)) (Tc (succ i))
  ∧ ma.step_of ((Tevt i).cast R.bij) (Ta i) (Ta (succ i)) :=
begin
  unfold Ta,
  pose P := (λ a, R.glue a (Tc (succ i)) ∧ ma.step_of ((Tevt _ Tc i).cast R.bij) (Ta _ _ _ _ R Tc i) a),
  apply @classical.epsilon_spec _ P,
  revert P, simp,
  note H' := R.sim' (Tevt _ Tc i) _ (Tc $ succ i) (Ta _ ma _ _ R Tc i) J (conc_step _ _ _ _ R Tc Hc i),
  apply exists_imp_exists _ H',
  intro, apply (and_comm _ _).mp,
end

theorem glued [nonempty α] (i : ℕ) : R.glue (Ta i) (Tc i) :=
begin
  induction i with i,
  { apply (init_simmed _ _ _ _ _ _ Hc).left },
  { apply (abs_step _ _ _ _ R _ Hc i ih_1).left },
end

-- include R

theorem simmed [nonempty α] (i : ℕ) : is_step ma (Ta i) (Ta (succ i)) :=
begin
  apply is_step_inst _ _,
  apply (abs_step _ _ _ _ R _ Hc i _).right,
  apply glued _ _ _ _ _ _ Hc,
  apply_instance,
end

open unity

theorem soundness [nonempty α] : data_ref ma f mc g :=
begin
  intros Tc Hc,
  existsi (Ta _ ma _ mc R Tc),
  split,
  apply prog.ex.mk ,
  { apply (init_simmed _ _ _ _ _ _ Hc).right },
  { intro i,
    unfold action step has_safety.step stream.drop,
    simp [add_one_eq_succ],
    apply simmed _ _ _ _ _ _ Hc,
    apply_instance },
  { intro ea,
    apply imp_mono _ _ (Hc.liveness $ ea.cast' R.bij),
    { apply iff.mp,
      apply exists_congr, intro i,
      apply forall_congr, intro j,
      unfold temporal.init stream.drop,
      pose ec := (option.cast' ea (R.bij)),
      rw [R.coarse ec,option_cast_cast'],
      apply glued, apply Hc },
    apply imp_mono _ _,
    { apply iff.mp _,
      apply forall_congr, intro j,
      apply exists_congr, intro i,
      unfold temporal.init stream.drop,
      pose ec := (option.cast' ea (R.bij)),
      rw [R.fine ec,option_cast_cast'],
      apply glued, apply Hc },
    { intro Hevt,
      definev Tevt' : stream (option ma.lbl) := λ i, (Tevt mc Tc i).cast R.bij,
      apply events_to_states Tevt' (prog.step_of ma),
      intro i,
      apply (abs_step f ma g mc _ _ Hc i _).right,
      { apply glued, apply Hc },
      rw [congr_inf_often_trace (λ e, option.cast' e R.bij)], simp,
      { unfold function.comp, revert  Tevt', simp [option_cast'_cast],
        apply fair_sched_of_is_fair',
        unfold Tevts ,
        pose F := λ σ σ', {e : option (mc.lbl) | prog.step_of mc e σ σ'},
        rw -inf_often_trace_action_trading Tc F,
        apply henceforth_entails_henceforth _ _ Hevt,
        apply eventually_entails_eventually,
        apply action_entails_action, intros s s',
        apply id, },
      { apply option_cast_injective } }, },
  { apply funext, intro i,
    unfold function.comp,
    symmetry,
    apply R.obs_cons,
    apply glued,
    apply Hc },
end

end thm

end hidden_state
