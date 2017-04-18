
import unity.models.nondet
import unity.refinement

namespace nondet

open temporal
open predicate
open unity

universe variable u

variables {α β : Type}

structure evt_ref (mc : @prog α) (ea : @event α) (ecs : set (@event α)) : Type :=
  (sim : ∀ ec : event, ec ∈ ecs → (action ec.step_of) ⟹ ⟦ ea.step_of ⟧)
  (witness : subtype ecs → α → Prop)
  (witness_fis : ⦃ ∃∃ e : subtype ecs, witness e ⦄)
  (delay : ∀ ec, witness ec && ea.coarse_sch && ea.fine_sch ↦ ec.val.coarse_sch in mc)
  (stable : ∀ ec, unless mc (witness ec && ec.val.coarse_sch) (~ea.coarse_sch))
  (resched : ∀ ec, ea.coarse_sch && ea.fine_sch && witness ec ↦ ec.val.fine_sch in mc)

def surjective (f : α → β) : Prop :=
∀ y, ∃ x, f x = y

structure refined (ma mc : @prog α) : Type :=
  (sim_init : mc^.first ⟹ ma^.first)
  (abs : mc.lbl → ma.lbl)
  (abs_surj : surjective abs)
  (events : ∀ ae, evt_ref mc (ma.event' ae) { ce | ∃ l, abs l = ae ∧ ce = mc.event' l } )

lemma refined.sim {ma mc : @prog α}
  (R : refined ma mc)
: ⟦ is_step mc ⟧ ⟹ ⟦ is_step ma ⟧ :=
begin
  simp [is_step_exists_event],
  apply p_or_entails_p_or_right,
  intros τ,
  simp,
  intros H,
  cases H with ce H,
  existsi R.abs ce,
  note H' := (R.events $ R.abs ce).sim,
  apply H' _ _ _ H,
  unfold set_of mem has_mem.mem set.mem,
  existsi ce,
  split ; refl
end

end nondet
