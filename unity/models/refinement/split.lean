
import unity.models.nondet
import unity.refinement

namespace nondet

open temporal
open predicate
open unity

universe variable u

section defs

variables {α β : Type}

structure evt_ref (lbl : Type) (mc : program α) (ea : event α) (ecs : lbl → event α) : Type :=
  (witness : lbl → α → Prop)
  (witness_fis : ⦃ ∃∃ e, witness e ⦄)
  (delay : ∀ ec, witness ec && ea.coarse_sch && ea.fine_sch ↦ witness ec && (ecs ec).coarse_sch in mc)
  (stable : ∀ ec, unless_except mc (witness ec && (ecs ec).coarse_sch) (-ea.coarse_sch) { e | ∃ l, ecs l = e })
  (resched : ∀ ec, ea.coarse_sch && ea.fine_sch && witness ec ↦ (ecs ec).fine_sch in mc)

structure refined (ma mc : program α) : Type :=
  (sim_init : mc^.first ⟹ ma^.first)
  (abs : option mc.lbl → option ma.lbl)
  (evt_sim : ∀ ec, ⟦ mc.step_of ec ⟧ ⟹ ⟦ ma.step_of (abs ec) ⟧)
  (events : ∀ ae, evt_ref { ec // abs ec = ae } mc (ma.event ae) (λ ec, mc.event ec.val) )

lemma refined.sim {ma mc : program α}
  (R : refined ma mc)
: ⟦ is_step mc ⟧ ⟹ ⟦ is_step ma ⟧ :=
begin
  simp [is_step_exists_event'],
  intro τ,
  simp,
  intros H,
  cases H with ce H,
  existsi (R.abs ce),
  unfold program.event, unfold program.event at H,
  apply R.evt_sim _ _ H,
end

end defs

section soundness

parameters {α β : Type}

parameter (ma : program α)
parameter (mc : program α)

open temporal

parameter R : refined ma mc
parameter τ : stream α
parameter M₁ : system_sem.ex mc τ

section schedules

parameter e : option ma.lbl
def imp_lbl := { ec : option mc.lbl // R.abs ec = e }

def AC := (program.event ma e).coarse_sch
def AF := (program.event ma e).fine_sch
def W (e' : imp_lbl) := (R.events e).witness e'
def CC (e' : option mc.lbl) := mc.coarse_sch_of e'
def CF (e' : option mc.lbl) := mc.fine_sch_of e'

parameter abs_coarse : (<>[](•AC && -⟦ ma.step_of e ⟧)) τ

parameter abs_fine : ([]<>•AF) τ

include M₁
include W
include abs_coarse
include abs_fine

lemma abs_coarse_and_fine
: ([]<>(•AC && •AF)) τ :=
begin
  apply coincidence,
  { apply stable_entails_stable _ _ abs_coarse,
    apply λ _, and.left },
  { apply abs_fine },
end

lemma conc_coarse : ∃ e', (<>[](• W e' && • CC e'.val) ) τ :=
begin
  assert H : ((∃∃ e', <>[](• W ma mc R e e' && • CC mc e'.val))
                   || []<>((-•AC ma e) || ∃∃ e' : imp_lbl ma mc R e, ⟦ mc.step_of e'.val ⟧)) τ,
  { rw exists_action,
    apply p_or_p_imp_p_or_right _ (unless_sem_exists' mc M₁.safety (R.events e).stable _),
    { apply inf_often_entails_inf_often,
      apply p_or_p_imp_p_or_right' _,
      apply action_entails_action,
      intros σ σ',
      simp [mem_set_of,and_exists], rw [exists_swap],
      apply exists_imp_exists,
      intros ec H,
      cases H with e' H,
      cases H with H₀ H₁,
      unfold program.step_of,
      rw H₁, apply H₀, },
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
  { apply H },
  { exfalso,
    revert abs_coarse,
    change ¬ _,
    rw [p_not_eq_not,not_eventually,not_henceforth,p_not_p_and,p_not_p_not_iff_self],
    apply inf_often_entails_inf_often _ _ H,
    apply p_or_p_imp_p_or_right',
    rw p_exists_entails_eq_p_forall_entails,
    intro ec, cases ec with ec Hec,
    subst e, apply R.evt_sim },
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
  apply nondet.program.ex.mk,
  { apply R.sim_init,
    apply M₁.init },
  { intro i,
    apply R.sim,
    apply M₁.safety },
  { intros e COARSE₀ FINE₀,
    apply assume_neg _, intro ACT,
    assert COARSE₁ :  (<>[](•AC ma e && -⟦program.step_of ma e⟧)) τ,
    { rw [p_not_eq_not,not_henceforth,not_eventually] at ACT,
      apply stable_and_of_stable_of_stable COARSE₀ ACT },
    clear COARSE₀ ACT,
    cases conc_coarse ma mc R τ M₁ _ COARSE₁ FINE₀ with e' C_COARSE',
    assert C_COARSE : (<>[]•CC mc e'.val) τ,
    { apply eventually_entails_eventually _ _ C_COARSE',
      apply henceforth_entails_henceforth,
      intro, apply and.right },
    assert WIT : (<>[]•W ma mc R e e') τ,
    { apply stable_entails_stable _ _ C_COARSE',
      intro, apply and.left },
    note C_FINE := conc_fine ma mc R τ M₁ e COARSE₁ FINE₀ e' WIT,
    apply inf_often_entails_inf_often _ _ (M₁.liveness _ C_COARSE C_FINE),
    note H := R.evt_sim e'.val,
    rw [subtype.property e'] at H,
    apply H, },
end

end soundness

end nondet
