
import data.set

import unity.temporal
import unity.refinement
import unity.scheduling
import unity.models.nondet

import util.cast

namespace hidden_state

universe variable u

open nondet temporal predicate

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
       (ma : program α)
       (g : β → σ)
       (mc : program β)

parameter R : refined f ma g mc

parameter [nonempty (unity.state (program α))]
parameter Tc : stream (unity.state (program β))
parameter Hc : system_sem.ex mc Tc

open nat

def Tevts  : stream (set (option (mc.lbl))) :=
  λ i, { e | mc.step_of e (Tc i) (Tc (succ i)) }

open scheduling

def Tevt [sched mc.lbl] : stream (option (mc.lbl)) :=
sorry

include Hc

parameter [sched mc.lbl]

example (i : ℕ) : mc.step_of (Tevt i) (Tc i) (Tc $ succ i) :=
sorry

omit Hc

noncomputable def Ta : stream (unity.state (program α))
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
sorry

lemma abs_step (i : ℕ) [nonempty α]
  (J : R.glue (Ta i) (Tc i))
:   R.glue (Ta (succ i)) (Tc (succ i))
  ∧ ma.step_of ((Tevt i).cast R.bij) (Ta i) (Ta (succ i)) :=
sorry

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
sorry

end thm

end hidden_state
