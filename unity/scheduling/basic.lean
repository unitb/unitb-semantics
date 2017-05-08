
import data.stream
import unity.temporal
import util.data.bijection
import util.data.stream

namespace scheduling

variable {lbl : Type}

structure fair {lbl : Type} (req : stream (set lbl)) (τ : stream lbl) : Prop :=
  (valid : ∀ i, req i = ∅ ∨ τ i ∈ req i)
  (fair : ∀ l, ([]<>•mem l) req → ([]<>•eq l) τ)

open stream nat

def req_of {lbl} (r : list lbl → set lbl) (τ : stream lbl) : stream (set lbl) :=
λ i, r (approx i τ)

lemma req_of_comp_length {lbl} (r : stream (set lbl)) (τ : stream lbl)
: req_of (r ∘ list.length) τ = r :=
begin
  unfold req_of function.comp,
  simp [length_approx],
end

lemma req_of_succ {lbl} (r : list lbl → set lbl) (τ : stream lbl) (i : ℕ)
: req_of r τ (succ i) = req_of (r ∘ flip list.concat (τ i)) τ i :=
begin
  unfold req_of function.comp flip,
  rw approx_succ_eq_concat,
end

class inductive sched (lbl : Type)
  | fin : finite lbl → sched
  | inf : infinite lbl → sched

instance fin_sched {lbl : Type} [pos_finite lbl] : sched lbl :=
sched.fin (by apply_instance)

instance inf_sched {lbl : Type} [infinite lbl] : sched lbl :=
sched.inf (by apply_instance)

instance sched_option_inf {lbl : Type} : ∀ [sched lbl], sched (option lbl)
  | (sched.inf inf) := sched.inf (by apply_instance)
  | (sched.fin fin) := sched.fin (by apply_instance)

end scheduling
