import unity.scheduling.basic
import unity.scheduling.finite
import unity.scheduling.infinite

import unity.temporal

import util.data.stream

namespace scheduling

open stream temporal has_mem scheduling.unity nat

section rules

variables  {lbl : Type}
variables [sched lbl] [nonempty lbl]

lemma sched.sched_str
  (r : target_mch lbl)
: ∃ τ : stream r.σ, fair r τ :=
begin
  cases _inst_1 with _fin _inf,
  { apply finite.sched' ; apply_instance },
  { apply infinite.sched' ; apply_instance },
end

end rules

variables {lbl : Type}
variables [sched lbl] [nonempty lbl]
variables (t : target_mch lbl)

noncomputable def fair_sched_of
: stream t.σ :=
classical.some (sched.sched_str t)

noncomputable def fair_sched : stream t.σ :=
fair_sched_of _

variables {lbl}

lemma fair_sched_of_spec
: fair t (fair_sched_of t) :=
by apply classical.some_spec (sched.sched_str t)

lemma fair_sched_succ (i : ℕ) {τ : stream t.σ}
  (H : fair t τ)
: ∃ l (P : l ∈ t.req (τ i)), τ (succ i) = t.next l (τ i) P :=
begin
  apply exists_imp_exists _ (H.valid i),
  intros l h,
  simp [init_drop,action_drop] at h,
  exact h.left
end

lemma fair_sched_of_is_fair
  (l : lbl)
  (h : ([]<>•mem l ∘ t.req) $ fair_sched_of t)
: ([]<>(•mem l ∘ t.req && ⟦ t.action l ⟧)) $ fair_sched_of t :=
(fair_sched_of_spec t).fair l h

instance {lbl} [i : nonempty lbl] : nonempty (stream lbl) :=
begin
  cases i with l,
  apply nonempty.intro,
  intro i, apply l,
end

end scheduling
