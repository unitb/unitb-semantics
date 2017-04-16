
import unity.models.nondet
import unity.refinement

namespace nondet

open predicate
open unity

universe variable u

variables {lbl α : Type}

structure evt_ref (mc : @prog α lbl) (ea ec : @event α) : Prop :=
  (sim : ⟦ ec.step_of ⟧ ⟹ ⟦ ea.step_of ⟧)
  (delay : ea.coarse_sch ↦ ec.coarse_sch in mc)
  (stable : unless mc ec.coarse_sch (~ea.coarse_sch))
  (resched : ea.fine_sch ↦ ec.fine_sch in mc)

structure refined (m₀ m₁ : @prog α lbl) : Prop :=
  (sim_init : m₁^.first ⟹ m₀^.first)
  (sim : ⟦ is_step m₁ ⟧ ⟹ ⟦ is_step m₀ ⟧)
  (delay : ∀ e, m₀^.coarse_sch_of e ↦ m₁^.coarse_sch_of e in m₁)
  (stable : ∀ e, unless m₁ (m₁^.coarse_sch_of e) (~m₀^.coarse_sch_of e))
  (resched : ∀ e, m₀^.fine_sch_of e ↦ m₁^.fine_sch_of e in m₁)

lemma event_refinement {m₀ m₁ : @prog α lbl}
   (INIT : m₁^.first ⟹ m₀^.first)
   (EVT : ∀ e, evt_ref m₁ (m₀.event' e) (m₁.event' e))
: refined m₀ m₁ :=
begin
  apply refined.mk,
  { apply INIT },
  { simp [is_step_exists_event],
    apply p_or_entails_p_or_right,
    apply p_exists_entails_p_exists, intro e,
    apply (EVT e).sim },
  all_goals
    { intro e, cases e with e,
      try { apply True_leads_to_True },
      try { simp, apply True_unless } },
  { apply (EVT e).delay },
  { apply (EVT e).stable },
  { apply (EVT e).resched },
end

variables  (m₀ m₁ : @prog α lbl)

open temporal

theorem soundness : refined m₀ m₁ → unity.refinement.refined m₀ m₁ :=
sorry
-- begin
--   intros R τ M₁,
--   apply nondet.prog.ex.mk,
--   { apply R.sim_init,
--     apply M₁.init },
--   { intro i,
--     apply R.sim,
--     unfold temporal.action is_step nondet.is_step,
--     cases M₁.safety i with ev H,
--     existsi ev,
--     unfold nondet.prog.step_of,
--     rw R.sim _ ,
--     apply H },
--   { intros e COARSE₀ FINE₀,
--     assert COARSE₁ : (<>[]•prog.coarse_sch_of m₁ e) τ,
--     { clear FINE₀,
--       note UNLESS := unless_sem _ τ (R.stable e),
--       note COARSE₀ := inf_often_of_stable _ COARSE₀,
--       note COARSE₀' := inf_often_of_leads_to (system_sem.leads_to_sem (R.delay e) _ M₁) COARSE₀, },
--     assert FINE₁ : ([]<>•prog.fine_sch_of m₁ e) τ,
--     {  },
--     apply hence_map _ _ (M₁.liveness _ COARSE₁ FINE₁),
--     apply ex_map,
--     rw R.sim,
--     intro, apply id },
-- end

end nondet
