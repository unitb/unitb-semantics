
import data.stream
import unity.temporal
import unity.logic
import util.data.bijection
import util.data.stream

universe variables u

namespace scheduling

open stream nat

section

parameters {lbl : Type}

structure fair (req : stream (set lbl)) (τ : stream lbl) : Prop :=
  (valid : ∀ i, req i = ∅ ∨ τ i ∈ req i)
  (fair : ∀ l, ([]<>•mem l) req → ([]<>•eq l) τ)

def req_of (r : list lbl → set lbl) (τ : stream lbl) : stream (set lbl) :=
λ i, r (approx i τ)

lemma req_of_comp_length (r : stream (set lbl)) (τ : stream lbl)
: req_of (r ∘ list.length) τ = r :=
begin
  unfold req_of function.comp,
  simp [length_approx],
end

lemma req_of_succ (r : list lbl → set lbl) (τ : stream lbl) (i : ℕ)
: req_of r τ (succ i) = req_of (r ∘ flip list.concat (τ i)) τ i :=
begin
  unfold req_of function.comp flip,
  rw approx_succ_eq_concat,
end

class inductive sched (l : Type)
  | fin : finite l → sched
  | inf : infinite l → sched

instance fin_sched [pos_finite lbl] : sched lbl :=
sched.fin (by apply_instance)

instance inf_sched [infinite lbl] : sched lbl :=
sched.inf (by apply_instance)

instance sched_option_inf : ∀ [sched lbl], sched (option lbl)
  | (sched.inf inf) := sched.inf (by apply_instance)
  | (sched.fin fin) := sched.fin (by apply_instance)

end

namespace unity

section

open unity

parameters {lbl : Type}
parameters {s : Type u}
parameters [system_sem s]
parameters r : list lbl → set lbl
parameters {F : s}
parameters ch : unity.state s → lbl
parameters hist : unity.state s → list lbl
def req (σ) := r (hist σ)
parameters P : ∀ l, often_imp_often F (mem l ∘ req) (eq l ∘ ch)
parameters INIT : system.init F (eq [ ] ∘ hist)
parameters STEP : unity.co' F (λ σ σ', hist σ' = hist σ ++ [ch σ])
parameters INV : ∀ σ, req σ = ∅ ∨ ch σ ∈ req σ

include INIT STEP

section

lemma keep_history {τ : stream (unity.state s)} (i : ℕ)
  (h : system_sem.ex F τ)
: approx i (map ch τ) = hist (τ i) :=
begin
  induction i with i IH,
  { note h' := system_sem.init_sem τ h INIT,
    unfold temporal.init function.comp at h',
    rw -h', refl },
  { rw [stream.approx_succ_eq_append,IH],
    unfold map nth,
    symmetry,
    apply STEP,
    note h' := system_sem.safety _ _ h i,
    rw temporal.action_drop at h',
    apply h' },
end

end

include F

lemma local_req (τ : stream (unity.state s))
  (h : system_sem.ex F τ)
  (i : ℕ)
: req_of r (map ch τ) i = r (hist $ τ i) :=
begin
  unfold req_of,
  rw keep_history _ _ INIT STEP i h,
end

include ch P hist INV

lemma scheduling'
: ∃ τ : stream lbl, fair (req_of r τ) τ :=
begin
  apply exists_imp_exists' (stream.map ch) _ (system_sem.inhabited F),
  intros τ sem,
  apply fair.mk,
  { intro i,
    rw local_req _ _ _ INIT STEP _ sem i,
    unfold map nth,
    apply INV, },
  { intro l,
    assert h : req_of r (map ch τ) = (function.comp (req r hist) τ),
    { apply funext (local_req _ _ _ INIT STEP _ sem) },
    assert h' : (map ch τ) = ch ∘ τ,
    { refl },
    rw [h,-temporal.inf_often_trace_init_trading],
    rw [h',-temporal.inf_often_trace_init_trading _ ch],
    apply system_sem.often_imp_often_sem' _ sem,
    apply P }
end

end

open unity

variable {lbl : Type}
variable r : list lbl → set lbl

structure scheduler :=
 (s : Type u)
 (sem : system_sem s)
 (F : s)
 (ch : unity.state s → lbl)
 (hist : unity.state s → list lbl)
 (req := λ σ, r (hist σ))
 (INIT : system.init F (eq [ ] ∘ hist))
 (STEP : unity.co' F (λ σ σ', hist σ' = hist σ ++ [ch σ]))
 (INV  : ∀ σ, req σ = ∅ ∨ ch σ ∈ req σ)
 (PROG : ∀ l, often_imp_often F (mem l ∘ req) (eq l ∘ ch))

lemma scheduling
  (sch : scheduler r)
  (sem : system_sem (sch.s))
: ∃ τ : stream lbl, fair (req_of r τ) τ :=
@scheduling' lbl sch.s sch.sem _ sch.F sch.ch _ sch.PROG sch.INIT sch.STEP sch.INV

end unity

end scheduling
