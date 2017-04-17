
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
  (sim' : ∀ e, ⟦ m₁.step_of e ⟧ ⟹ ⟦ m₀.step_of e ⟧)
  (delay : ∀ e, m₀^.coarse_sch_of e ↦ m₁^.coarse_sch_of e in m₁)
  (stable : ∀ e, unless m₁ (m₁^.coarse_sch_of e) (~m₀^.coarse_sch_of e))
  (resched : ∀ e, m₀^.fine_sch_of e ↦ m₁^.fine_sch_of e in m₁)

lemma refined.sim {m₀ m₁ : @prog α lbl} (R : refined m₀ m₁)
: ⟦ is_step m₁ ⟧ ⟹ ⟦ is_step m₀ ⟧ :=
begin
  simp [is_step_exists_event],
  apply p_or_entails_p_or_right,
  apply p_exists_entails_p_exists, intro e,
  apply R.sim' (some e),
end

lemma event_refinement {m₀ m₁ : @prog α lbl}
   (INIT : m₁^.first ⟹ m₀^.first)
   (EVT : ∀ e, evt_ref m₁ (m₀.event' e) (m₁.event' e))
: refined m₀ m₁ :=
begin
  apply refined.mk,
  { apply INIT },
  { intro e,
    cases e with e,
    { simp [step_of_none],
      intro, apply id },
    { unfold prog.step_of prog.event,
      apply (EVT e).sim } },
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
begin
  intros R τ M₁,
  apply nondet.prog.ex.mk,
  { apply R.sim_init,
    apply M₁.init },
  { intro i,
    apply R.sim,
    apply M₁.safety },
  { intros e COARSE₀ FINE₀,
    assert COARSE₁ : (<>[]•prog.coarse_sch_of m₁ e) τ,
    { clear FINE₀,
      assert COARSE₂ : ([]<>•prog.coarse_sch_of m₁ e) τ,
      { apply inf_often_of_leads_to (system_sem.leads_to_sem (R.delay e) _ M₁),
        apply inf_often_of_stable _,
        apply COARSE₀ },
      note UNLESS := unless_sem_str _ M₁.safety (R.stable e) COARSE₂,
      cases UNLESS with UNLESS H,
      { apply UNLESS },
      { assert H' : (~<>[]•prog.coarse_sch_of m₀ e) τ,
        { rw [not_eventually,not_henceforth,not_init], apply H },
        cases H' COARSE₀, } },
    assert FINE₁ : ([]<>•prog.fine_sch_of m₁ e) τ,
    { apply inf_often_of_leads_to (system_sem.leads_to_sem (R.resched _) _ M₁) FINE₀, },
    apply hence_map _ _ (M₁.liveness _ COARSE₁ FINE₁),
    apply ex_map,
    apply R.sim', },
end

end nondet