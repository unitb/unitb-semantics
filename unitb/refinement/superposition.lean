
import unitb.models.nondet
import unitb.refinement.basic

namespace superposition

open stream
open temporal
open predicate
open unitb nondet

universe variable u

section defs

parameters {α α' β : Type}
parameters abs : α' → α

structure evt_ref (lbl : Type) (mc : program α') (ea : event α) (ecs : lbl → event α') : Type :=
  (witness : lbl → α' → Prop)
  (witness_fis : ⦃ ∃∃ e, witness e ⦄)
  (sim : ∀ ec, ⟦ (ecs ec).step_of ⟧ ⟹ ⟦ ea.step_of on abs ⟧)
  (delay : ∀ ec, witness ec && (ea.coarse_sch && ea.fine_sch) ∘ abs ↦ witness ec && (ecs ec).coarse_sch in mc)
  (stable : ∀ ec, unless_except mc (witness ec && (ecs ec).coarse_sch) (-(ea.coarse_sch ∘ abs))
                                   { e | ∃ l, ecs l = e })
  (resched : ∀ ec, (ea.coarse_sch && ea.fine_sch) ∘ abs && witness ec ↦ (ecs ec).fine_sch in mc)

structure evt_ref_wk (lbl : Type) (mc : program α') (ea : event α) (ecs : lbl → event α')
: Type :=
  (witness : lbl → α' → Prop)
  (sim : ∀ ec, ⟦ (ecs ec).step_of ⟧ ⟹ ⟦ ea.step_of on abs ⟧)
  (delay : (ea.coarse_sch && ea.fine_sch) ∘ abs
            >~>
           -(ea.coarse_sch ∘ abs)
            || ∃∃ ec, witness ec && (ecs ec).coarse_sch in mc)
  (stable : ∀ ec, unless_except mc (witness ec && (ecs ec).coarse_sch) (-(ea.coarse_sch ∘ abs))
                                   { e | ∃ l, ecs l = e })
  (resched : ∀ ec, (ea.coarse_sch && ea.fine_sch) ∘ abs && witness ec && (ecs ec).coarse_sch
                    >~>
                   (ecs ec).fine_sch in mc)

lemma evt_ref_wk_of_evt_ref
  (lbl : Type) (mc : program α')
  (ea : event α)
  (ecs : lbl → event α')
  (H : evt_ref lbl mc ea ecs)
: evt_ref_wk lbl mc ea ecs :=
begin
  apply evt_ref_wk.mk H.witness,
  { apply H.sim },
  { have Hsch : ∀ ec, H.witness ec && (ea.coarse_sch && ea.fine_sch) ∘ abs
               ↦
              -(ea.coarse_sch ∘ abs)
              || H.witness ec && (ecs ec).coarse_sch && (ecs ec).fine_sch in mc,
    { intro ec,
      have P₀ : H.witness ec && (ea.coarse_sch && ea.fine_sch) ∘ abs
                 ↦
                H.witness ec && (ecs ec).coarse_sch || (ecs ec).fine_sch in mc,
      { have H' := leads_to.gen_disj (H.delay ec) (H.resched ec),
        rw [p_and_comm,p_or_self,p_and_comm] at H',
        apply H', },
      have P₁ : H.witness ec && (ecs ec).coarse_sch || (ecs ec).fine_sch
                 ↦
                -(ea.coarse_sch ∘ abs)
                || H.witness ec && (ecs ec).coarse_sch && (ecs ec).fine_sch in mc,
      { admit },
      apply leads_to.trans _ P₀ P₁ },
    have Hsch' := leads_to.gen_disj' Hsch,
    have H₀ : (∃∃ (ec : lbl), H.witness ec && (ea.coarse_sch ∘ abs && ea.fine_sch ∘ abs))
            = (ea.coarse_sch && ea.fine_sch) ∘ abs,
    { rw [← p_and_over_p_exists_right,ew_eq_true H.witness_fis],
      simp },
    simp [H₀] at Hsch',
    simp [p_or_over_p_exists_left _ _ H.witness_fis],
    apply often_imp_often.basis,
    revert Hsch',
    apply leads_to.strengthen_rhs,
    apply p_exists_entails_p_exists,
    intros e,
    apply p_or_entails_p_or_right,
    apply p_and_elim_left },
  { apply H.stable },
  { admit }
end

parameters (ma : program α) (mc : program α')

structure refined : Type :=
  (sim_init : mc^.first ⟹ ma^.first∘abs)
  (ref : option mc.lbl → option ma.lbl → Prop)
  (evt_sim : ∀ ec, ⟦ mc.step_of ec ⟧
               ⟹ ∃∃ ea : { ea // ref ec ea }, ⟦ ma.step_of ea.val on abs ⟧)
  (events : ∀ ae, evt_ref_wk { ec // ref ec ae } mc (ma.event ae) (λ ec, mc.event ec.val) )

parameters {ma mc}

lemma refined.sim
  (R : refined)
: ⟦ is_step mc ⟧ ⟹ ⟦ is_step ma on abs ⟧ :=
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

parameters {α α' β : Type}
parameters {abs : α' → α}
parameter {ma : program α}
parameter {mc : program α'}

open temporal

parameter R : refined abs ma mc
parameter {τ : stream α'}
parameter M₁ : system_sem.ex mc τ

section schedules

parameter e : option ma.lbl
def imp_lbl := { ec : option mc.lbl // R.ref ec e }

def AC := (program.event ma e).coarse_sch ∘ abs
def AF := (program.event ma e).fine_sch ∘ abs
def W (e' : imp_lbl) := (R.events e).witness e'
def CC (e' : option mc.lbl) := mc.coarse_sch_of e'
def CF (e' : option mc.lbl) := mc.fine_sch_of e'

parameter abs_coarse : (<>[](•AC && -⟦ ma.step_of e on abs ⟧)) τ

parameter abs_fine : ([]<>•AF) τ

include M₁
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

include R

lemma evt_ref_wk.delay_sem
: []<>(∃∃ ce, •W ce && •CC ce.val) $ τ :=
begin
  have Hdelay := (R.events e).delay,
  have H := system_sem.often_imp_often_sem' _ M₁ Hdelay
                (abs_coarse_and_fine M₁ e abs_coarse abs_fine),
  clear Hdelay,
  rw [init_p_or,inf_often_p_or,← p_not_p_imp,not_henceforth,not_eventually] at H,
  rw [not_init,p_not_p_not_iff_self] at H,
  have Hc := stable_entails_stable (λ _, and.left) τ abs_coarse,
  apply H Hc,
end
-- lemma conc_coarse : ∃ e', (<>[](• W e' && • CC e'.val) ) τ :=

lemma conc_event : ∃ e' : imp_lbl, (<>[]• CC e'.val && []<>•CF e'.val ) τ :=
begin
  have H : ((∃∃ e', <>[](• W R e e' && • CC e'.val))
                   || []<>((-•AC  e) || ∃∃ e' : imp_lbl R e, ⟦ mc.step_of e'.val ⟧)) τ,
  { rw exists_action,
    apply p_or_p_imp_p_or_right _ (unless_sem_exists' M₁.safety (R.events e).stable _),
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
    have H' := (R.events e).delay,
    have H'' := system_sem.often_imp_often_sem' _ M₁ H' , clear H',
    rw [init_p_or, inf_often_p_or,shunting,init_exists] at H'',
    apply evt_ref_wk.delay_sem R M₁ e abs_coarse abs_fine },
  cases H with H H,
  { apply exists_imp_exists _ H,
    intros ce Hcc,
    simp, split,
    { revert Hcc,
      apply stable_entails_stable,
      apply p_and_elim_right },
    have Hc := stable_and_of_stable_of_stable Hcc abs_coarse,
    have Ha := coincidence Hc abs_fine,
    apply system_sem.often_imp_often_sem' _ M₁ ((R.events e).resched ce),
    revert Ha,
    apply inf_often_entails_inf_often,
    intro, simp [init_p_and,W,CC,AC,AF,W,program.coarse_sch_of],
    generalize ((•(program.event ma e).coarse_sch ∘ abs) i)  X₀,
    generalize ((•(program.event ma e).fine_sch ∘ abs) i)    X₁,
    generalize ((•(program.event mc (ce.val)).coarse_sch) i) X₂,
    generalize ((•(R.events e).witness ce) i) X₃,
    intros, begin [smt] by_cases X₀ end, },
  { exfalso,
    revert abs_coarse,
    change ¬ _,
    rw [p_not_eq_not,not_eventually,not_henceforth,p_not_p_and,p_not_p_not_iff_self],
    revert H,
    apply inf_often_entails_inf_often,
    apply p_or_p_imp_p_or_right',
    rw p_exists_entails_eq_p_forall_entails,
    intros ec,
    apply (R.events e).sim _ , },
end


end schedules

include M₁
include R

theorem soundness : system_sem.ex ma (map abs τ) :=
begin
  apply nondet.program.ex.mk,
  { apply R.sim_init,
    apply M₁.init },
  { intro i,
    rw [drop_map],
    rw [comp_map_app_eq_map ⟦ step ma ⟧, ← action_trading ],
    apply R.sim abs,
    apply M₁.safety },
  { intros e COARSE₀ FINE₀,
    apply assume_neg _, intro ACT,
    have COARSE₁ :  (<>[](•AC e && -⟦program.step_of ma e on abs⟧)) τ,
    { rw [← inf_often_trace_action_trading] at ACT,
      rw [← stable_trace_init_trading] at COARSE₀,
      rw [p_not_eq_not,not_henceforth,not_eventually] at ACT,
      apply stable_and_of_stable_of_stable COARSE₀ ACT },
    clear COARSE₀ ACT,
    cases conc_event R M₁ _ COARSE₁ FINE₀ with e' C_EVT,
    cases C_EVT with C_COARSE C_FINE,
    rw [← inf_often_trace_trading,← action_trading],
    apply inf_often_entails_inf_often _ _ (M₁.liveness _ C_COARSE C_FINE),
    have H := (R.events e).sim e',
    apply H, },
end

end soundness

end superposition
