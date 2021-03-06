
import unitb.models.nondet
import unitb.refinement.basic

import util.cast

universe variable u

namespace nondet
open predicate
open unitb
local attribute [instance] classical.prop_decidable
variables α : Type

@[reducible]
private def pred := α → Prop

variables {α}

structure evt_ref (mc : program α) (ea ec : event α) : Prop :=
  (sim : ⟦ ec.step_of ⟧ ⟹ ⟦ ea.step_of ⟧)
  (delay : ea.coarse_sch ⋀ ea.fine_sch  >~>  ec.coarse_sch ⋁ - ea.coarse_sch in mc)
  (stable : unless mc ec.coarse_sch (-ea.coarse_sch))
  (resched : ea.coarse_sch ⋀ ea.fine_sch  >~>  ec.fine_sch ⋁ - ea.coarse_sch in mc)

structure evt_ref_piecewise (mc : program α) (ea ec : event α)
    {n : ℕ} (ccsch : fin n → pred α) : Prop :=
  (ccsch_def : ec.coarse_sch = (∀∀ i, ccsch i))
  (sim : ⟦ ec.step_of ⟧ ⟹ ⟦ ea.step_of ⟧)
  (delay : ∀ i, ea.coarse_sch ⋀ ea.fine_sch  ↦  ccsch i ⋁ - ea.coarse_sch in mc)
  (stable : ∀ i, unless mc (ccsch i) (-ea.coarse_sch))
  (resched : ea.coarse_sch ⋀ ea.fine_sch  >~>  ec.fine_sch ⋁ - ea.coarse_sch in mc)


open temporal

structure refined (ma mc : program α) : Prop :=
  (bij : mc.lbl = ma.lbl)
  (sim_init : mc^.first ⟹ ma^.first)
  (sim' : ∀ e, ⟦ mc.step_of e ⟧ ⟹ action (ma.step_of (e.cast bij) ))
  (delay : ∀ e, ma.coarse_sch_of e ⋀ ma.fine_sch_of e
            >~> mc.coarse_sch_of (e.cast' bij) ⋁ - ma.coarse_sch_of e in mc)
  (stable : ∀ e, unless mc (mc^.coarse_sch_of e) (-ma^.coarse_sch_of (e.cast bij)))
  (resched : ∀ e, ma^.coarse_sch_of e ⋀ ma^.fine_sch_of e
              >~> mc^.fine_sch_of (e.cast' bij) ⋁ - ma.coarse_sch_of e in mc)

lemma refined.sim {m₀ m₁ : program α} (R : refined m₀ m₁)
: ⟦ is_step m₁ ⟧ ⟹ ⟦ is_step m₀ ⟧ :=
begin
  simp [is_step_exists_event,R.bij],
  apply p_or_entails_p_or_right,
  apply p_exists_entails_p_exists' _ _ (λ l, cast R.bij l), intros e τ H,
  simp,
  have H'' : option.cast (some e) (R.bij) = some (cast (R.bij) e),
  { generalize : R.bij = P,
    rw cast_some },
  have H' := R.sim' (some e) τ H,
  rw H'' at H',
  apply H',
end

section piecewise_event_refinement

variables {mc : program α}
variables {ea ec : event α}
variables {n : ℕ}
variables {ccsch : fin n → α → Prop}
variables (H : evt_ref_piecewise mc ea ec ccsch)

include H

lemma piecewise_delay
: ea.coarse_sch ⋀ ea.fine_sch  >~>  ec.coarse_sch ⋁ -ea.coarse_sch in mc :=
begin
  apply often_imp_often.basis,
  rw H.ccsch_def,
  have H' := leads_to.completion H.delay H.stable,
  apply leads_to.antimono_left _ _ H', clear H H',
  intro, simp, begin [smt] by_cases ea.coarse_sch i end
end

lemma piecewise_event_refinement
: evt_ref mc ea ec :=
{ resched := H.resched
, stable  := by { rw H.ccsch_def, apply forall_unless H.stable }
, delay   := piecewise_delay H
, sim     := H.sim }

end piecewise_event_refinement

lemma event_refinement {ma mc : program α}
   (BIJ : mc.lbl = ma.lbl)
   (INIT : mc^.first ⟹ ma^.first)
   (EVT : ∀ e, evt_ref mc (ma.event' e) (mc.event' $ cast BIJ.symm e))
: refined ma mc :=
begin
  apply refined.mk BIJ,
  { apply INIT },
  { intro e,
    cases e with e,
    { simp [cast_none,step_of_none] },
    { unfold program.step_of program.event,
      simp [cast_some],
      have H := (EVT $ cast BIJ e).sim,
      simp [cast_cast] at H,
      apply H } },
  all_goals
    { intro e,
      cases e with e,
      simp [ program.coarse_sch_of_none,program.fine_sch_of_none,cast_none'],
      try { apply True_often_imp_often_True },
      try { apply True_unless } },
  { simp [cast_some'],
    apply (EVT e).delay },
  { simp [cast_some],
    have H := (EVT $ cast BIJ e).stable,
    simp [cast_cast] at H,
    apply H },
  { simp [cast_some'],
    apply (EVT e).resched },
end

variables  (ma mc : program α)

open temporal

theorem soundness : refined ma mc → unitb.refinement.refined ma mc :=
begin
  intros R τ M₁,
  apply nondet.program.ex.mk,
  { apply R.sim_init,
    apply M₁.init },
  { intro i,
    apply R.sim,
    apply M₁.safety },
  { intros e COARSE₀ FINE₀,
    let e' := e.cast' R.bij,
    have CF_SCH : (◻◇•(program.coarse_sch_of ma e ⋀ program.fine_sch_of ma e)) τ,
    { apply coincidence,
      apply COARSE₀,
      apply FINE₀, },
    have COARSE₁ : (◇◻•program.coarse_sch_of mc e') τ,
    { have COARSE₂ : (◻◇•program.coarse_sch_of mc e') τ,
      { revert COARSE₀,
        rw [imp_iff_not_or,p_not_eq_not,not_eventually,not_henceforth,not_init],
        rw [← p_or_to_fun,p_or_comm,← inf_often_p_or],
        apply (system_sem.often_imp_often_sem' _ M₁ (R.delay e)),
        apply CF_SCH },
      have UNLESS := unless_sem_str M₁.safety (R.stable e') COARSE₂,
      cases UNLESS with UNLESS H,
      { apply UNLESS },
      { have H' : (-◇◻•program.coarse_sch_of ma e) τ,
        { rw [not_eventually,not_henceforth,not_init],
          simp [option_cast_cast'] at H,
          apply H },
        cases H' COARSE₀, } },
    have FINE₁ : (◻◇•program.fine_sch_of mc e') τ,
    { revert COARSE₀,
      rw [imp_iff_not_or,p_not_eq_not,not_eventually,not_henceforth,not_init],
      rw [← p_or_to_fun,p_or_comm,← inf_often_p_or],
      apply system_sem.often_imp_often_sem' _ M₁ (R.resched _),
      apply CF_SCH, },
    apply inf_often_entails_inf_often _ _ (M₁.liveness _ COARSE₁ FINE₁),
    have H := R.sim' e',
    simp [option_cast_cast'] at H,
    apply H, },
end

end nondet
