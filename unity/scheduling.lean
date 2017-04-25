
import data.stream
import unity.temporal
import util.data.bijection

namespace scheduling

open temporal
open classical

structure fair {lbl : Type} (req : stream (set lbl)) (τ : stream lbl) : Prop :=
  (valid : ∀ i, req i = ∅ ∨ τ i ∈ req i)
  (fair : ∀ l, ([]<>•mem l) req → ([]<>•eq l) τ)

class inductive sched (lbl : Type)
  | fin : finite lbl → sched
  | inf : infinite lbl → sched

lemma sched.sched {lbl : Type} [sched lbl] [nonempty lbl]
: ∀ req : stream (set lbl), ∃ τ : stream lbl, fair req τ :=
sorry

instance {lbl} [i : nonempty lbl] : nonempty (stream lbl) :=
begin
  cases i with l,
  apply nonempty.intro,
  intro i, apply l,
end

noncomputable def fair_sched_of {lbl : Type} [nonempty lbl] [sched lbl] (req : stream (set lbl)) : stream lbl :=
epsilon (fair req)

lemma fair_sched_of_spec {lbl : Type} [nonempty lbl] [sched lbl] (req : stream (set lbl))
: fair req (fair_sched_of req) :=
begin
  unfold fair_sched_of,
  apply epsilon_spec,
  apply sched.sched req
end

lemma fair_sched_of_mem  {lbl : Type} [nonempty lbl] [sched lbl] (req : stream (set lbl))
  (i : ℕ)
  (Hnemp : req i ≠ ∅)
: fair_sched_of req i ∈ req i :=
begin
  cases (fair_sched_of_spec req).valid i with H' H',
  { cases Hnemp H' },
  { apply H' }
end

lemma fair_sched_of_is_fair  {lbl : Type} [nonempty lbl] [sched lbl] (req : stream (set lbl)) (l : lbl)
: ([]<>•mem l) req → ([]<>•eq l) (fair_sched_of req) :=
(fair_sched_of_spec req).fair l

noncomputable def fair_sched (lbl : Type) [nonempty lbl] [sched lbl] : stream lbl :=
fair_sched_of (λ _ _, true)

lemma fair_sched_is_fair  {lbl : Type} [nonempty lbl] [sched lbl] (l : lbl)
: ([]<>•eq l) (fair_sched lbl) :=
begin
  apply (fair_sched_of_spec _).fair l,
  intro i,
  apply eventually_weaken,
  simp [init_drop],
end

lemma sched.sched' (lbl : Type) [nonempty lbl] [sched lbl]
: ∃ τ : stream lbl, ∀ (l : lbl), ([]<>•eq l) τ  := ⟨_,fair_sched_is_fair⟩

instance fin_sched {lbl : Type} [pos_finite lbl] : sched lbl :=
sched.fin (by apply_instance)

instance inf_sched {lbl : Type} [infinite lbl] : sched lbl :=
sched.inf (by apply_instance)

instance sched_option_inf {lbl : Type} : ∀ [sched lbl], sched (option lbl)
  | (sched.inf inf) := sched.inf (by apply_instance)
  | (sched.fin fin) := sched.fin (by apply_instance)

end scheduling
