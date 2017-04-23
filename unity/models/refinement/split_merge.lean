
import unity.models.nondet
import unity.refinement

namespace nondet

open temporal
open predicate
open unity

universe variable u

section defs

variables {α β : Type}

structure evt_ref (lbl : Type) (mc : @prog α) (ea : @event α) (ecs : lbl → @event α) : Type :=
  (witness : lbl → α → Prop)
  (witness_fis : ⦃ ∃∃ e, witness e ⦄)
  (sim : ∀ ec, ⟦ (ecs ec).step_of ⟧ ⟹ ⟦ ea.step_of ⟧)
  (delay : ∀ ec, witness ec && ea.coarse_sch && ea.fine_sch ↦ witness ec && (ecs ec).coarse_sch in mc)
  (stable : ∀ ec, unless mc (witness ec && (ecs ec).coarse_sch) (-ea.coarse_sch))
  (resched : ∀ ec, ea.coarse_sch && ea.fine_sch && witness ec ↦ (ecs ec).fine_sch in mc)

structure refined (ma mc : @prog α) : Type :=
  (sim_init : mc^.first ⟹ ma^.first)
  (ref : option mc.lbl → option ma.lbl → Prop)
  (ref_wit : ∀ ec, ∃ ea, ref ec ea)
  (evt_sim : ∀ ec, ⟦ mc.step_of ec ⟧ ⟹ ∃∃ ea : { ea // ref ec ea }, ⟦ ma.step_of ea.val ⟧)
  (events : ∀ ae, evt_ref { ec // ref ec ae } mc (ma.event ae) (λ ec, mc.event ec.val) )

lemma refined.sim {ma mc : @prog α}
  (R : refined ma mc)
: ⟦ is_step mc ⟧ ⟹ ⟦ is_step ma ⟧ :=
begin
  simp [is_step_exists_event'],
  intro τ,
  simp,
  intros H,
  cases H with ce H,
  apply exists_imp_exists' subtype.val _ (R.evt_sim ce τ H),
  intro, apply id,
end

end defs

section soundness

parameters {α β : Type}

parameter (ma : @prog α)
parameter (mc : @prog α)

open temporal

parameter R : refined ma mc
parameter τ : stream α
parameter M₁ : system_sem.ex mc τ

section schedules

parameter e : option ma.lbl
def imp_lbl := { ec : option mc.lbl // R.ref ec e }

def AC := (prog.event ma e).coarse_sch
def AF := (prog.event ma e).fine_sch
def W (e' : imp_lbl) := (R.events e).witness e'
def CC (e' : option mc.lbl) := mc.coarse_sch_of e'
def CF (e' : option mc.lbl) := mc.fine_sch_of e'

parameter abs_coarse : (<>[]•AC) τ

parameter abs_fine : ([]<>•AF) τ

include M₁
include abs_coarse
include abs_fine

lemma abs_coarse_and_fine
: ([]<>(•AC && •AF)) τ :=
begin
  apply coincidence,
  apply abs_coarse,
  apply abs_fine,
end

lemma conc_coarse : ∃ e', (<>[](• W e' && • CC e'.val) ) τ :=
begin
  assert H : ((∃∃ e', <>[](• W ma mc R e e' && • CC mc e'.val)) || []<>-•AC ma e) τ,
  { apply unless_sem_exists mc M₁.safety (R.events e).stable,
    note H' := leads_to.gen_disj' (R.events e).delay,
    apply inf_often_of_leads_to (system_sem.leads_to_sem H' _ M₁),
    simp,
    note H' := ew_eq_true (R.events e).witness_fis,
    rw [-p_and_over_p_exists_right
       ,-p_and_over_p_exists_right],
    simp [H'],
    apply abs_coarse_and_fine ma mc _ M₁ _ abs_coarse abs_fine, },
  simp at H,
  cases H with H H,
  { exfalso,
    revert abs_coarse,
    change ¬ _,
    rw [p_not_eq_not,not_eventually,not_henceforth],
    apply H },
  { apply H }
end

lemma conc_fine : ∀ e',
         (<>[]•W e') τ →
         ([]<>•CF e'.val) τ :=
begin
  intros e' H,
  note H' := system_sem.leads_to_sem ((R.events e).resched e') _ M₁,
  apply inf_often_of_leads_to H',
  rw p_and_comm,
  apply coincidence H,
  apply abs_coarse_and_fine _ _ _ M₁ _ abs_coarse abs_fine,
end

end schedules

include M₁
include R

theorem soundness : system_sem.ex ma τ :=
begin
  apply nondet.prog.ex.mk,
  { apply R.sim_init,
    apply M₁.init },
  { intro i,
    apply R.sim,
    apply M₁.safety },
  { intros e COARSE₀ FINE₀,
    cases conc_coarse ma mc R τ M₁ _ COARSE₀ FINE₀ with e' C_COARSE',
    assert C_COARSE : (<>[]•CC mc e'.val) τ,
    { apply ex_map _ _ C_COARSE',
      apply hence_map,
      intro, apply and.right },
    assert WIT : (<>[]•W ma mc R e e') τ,
    { apply ex_map _ _ C_COARSE',
      apply hence_map,
      intro, apply and.left },
    note C_FINE := conc_fine ma mc R τ M₁ e COARSE₀ FINE₀ e' WIT,
    apply hence_map _ _ (M₁.liveness _ C_COARSE C_FINE),
    apply ex_map,
    apply (R.events e).sim e', },
end

end soundness

end nondet
