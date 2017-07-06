
import data.stream
import unitb.semantics.temporal
import unitb.logic
import util.data.array
import util.data.bijection
import util.data.stream

universe variables u v

namespace scheduling

open stream nat function

namespace unitb

section target

parameters (lbl : Type)

structure target_mch :=
  (σ : Type)
  (s₀ : σ)
  (req : σ → set lbl)
  (req_nemp : ∀ x, req x ≠ ∅)
  (next : ∀ l s, l ∈ req s → σ)

parameters {lbl}

def target_mch.action (t : target_mch) (l : lbl) (s s' : t.σ) : Prop :=
∃ P, s' = t.next l s P

-- def run (t : target_mch) (τ : stream lbl) : stream t.σ
--   | 0 := t.s₀
--   | (succ i) := t.next (τ i) (run i)

end target

end unitb

section

parameters {lbl lbl₀ lbl₁ : Type}

open has_mem scheduling.unitb temporal

structure fair (t : target_mch lbl) (τ : stream t.σ) : Prop :=
  (init : τ 0 = t.s₀)
  (valid : [] (∃∃ l, •(mem l ∘ t.req) && ⟦ t.action l ⟧) $ τ)
  (fair : ∀ l, ([]<>•mem l ∘ t.req) ⟶ ([]<>(•mem l ∘ t.req && ⟦ t.action l ⟧)) $ τ)
  -- (evts : stream lbl)
  -- (run_evts_eq_τ : run t evts = τ)

class inductive sched (l : Type u)
  | fin : finite l → sched
  | inf : infinite l → sched

instance fin_sched [pos_finite lbl] : sched lbl :=
sched.fin (by apply_instance)

instance inf_sched [infinite lbl] : sched lbl :=
sched.inf (by apply_instance)

instance sched_option : ∀ [sched lbl], sched (option lbl)
  | (sched.inf inf) := sched.inf (by apply_instance)
  | (sched.fin fin) := sched.fin (by apply_instance)

instance sched_sum : ∀ [sched lbl₀] [sched lbl₁], sched (lbl₀ ⊕ lbl₁)
  | (sched.fin fin) (sched.fin fin') := sched.fin (by apply_instance)
  | (sched.inf inf) (sched.fin fin') := sched.inf (by apply_instance)
  | (sched.fin fin) (sched.inf inf') := sched.inf (by apply_instance)
  | (sched.inf inf) (sched.inf inf') := sched.inf (by apply_instance)

def is_finite (l : Type u) : ∀ [sched l], Prop
  | (sched.fin x) := true
  | (sched.inf x) := false

def is_infinite (l : Type u) : ∀ [sched l], Prop
  | (sched.fin x) := false
  | (sched.inf x) := true

def is_empty (l : Type u) : ∀ [sched l], Prop
  | (sched.fin fn) := @finite.count l fn = 0
  | (sched.inf x)  := false

local attribute [instance] classical.prop_decidable

open bijection

def index_of {t : Type u} : ∀ [sched t], t → ℕ
  | (sched.inf inst) x := inst.to_nat.f x
  | (sched.fin inst) x := (inst.to_nat.f x).val

lemma injective_index_of {t : Type u} [sched t]
: injective (@index_of t _) :=
begin
  cases _inst_1
  ; intros i j
  ; unfold index_of,
  case sched.fin ifin
  { intros H,
    have H' := fin.eq_of_veq H,
    apply bijection.f_injective (finite.to_nat t) H', },
  case sched.inf iinf
  { apply bijection.f_injective },
end

def from_index {t : Type u} [inst : sched t] (Hinf : is_infinite t) (n : ℕ) : t :=
have infinite t, by { cases inst, cases Hinf, apply a },
(@infinite.to_nat t this).g n

lemma injective_from_index {t : Type u} [sched t]
  (Hinf : is_infinite t)
: injective (from_index Hinf) :=
by apply bijection.g_injective

section d

parameters {t : Type u} {f : t → Type v}
variable [sched t]
variable [∀ i, sched (f i)]
variable H : ∃ (i : t), is_infinite (f i)

def d' : (Σ (i : t), f i) → ℕ × ℕ
  | ⟨x,y⟩ := (index_of x,index_of y)

def d : (Σ (i : t), f i) → ℕ :=
bij.prod.g ∘ d'

lemma injective_d
: injective d :=
begin
  unfold d,
  apply @injective_comp _ _ _ (bij.prod).f d',
  { apply bijection.f_injective bij.prod },
  { intros i j,
    cases i with i₀ i₁,
    cases j with j₀ j₁,
    unfold d',
    intros H,
    injection H with H₀ H₁,
    have Hij : i₀ = j₀ := injective_index_of H₀,
    subst j₀,
    rw injective_index_of H₁, }
end

noncomputable def b (x : ℕ) : (Σ (i : t), f i) :=
⟨classical.some H,from_index (classical.some_spec H) x⟩

lemma injective_b
: injective (b H) :=
begin
  intros i j,
  unfold b,
  intros H,
  injection H with H₀ H₁,
  have H₂ := eq_of_heq H₁, clear H₁,
  unfold b._proof_1 from_index at H₂,
  apply bijection.g_injective _ H₂,
end

end d

section fg

parameters {t : Type u} {f : t → Type v}
parameter [sched t]
parameter [finite t]
parameter [Hs : ∀ i, sched (f i)]
parameter H : ¬ ∃ (i : t), is_infinite (f i)
include H
def m := finite.count t


@[instance]
def H' (i : t) : finite (f i) :=
begin
  destruct (Hs i),
  case sched.fin
  { intros inst H', apply inst },
  case sched.inf
  { intros inst H',
    exfalso,
    apply H,
    existsi i, rw H',
    trivial }
end

def n : ℕ :=
array.maximum ( array.mk (λ i, (H' $ (finite.to_nat t).g i).count) )

lemma Hmn : ∀ i, (H' i).count ≤ n :=
begin
  intro i,
  unfold n,
  rw -_inst_2.to_nat.f_inv i,
  change (array.mk $ λ i, (H' H ((finite.to_nat t).g i)).count).read _ ≤ _,
  apply array.le_maximum,
end

def fd' : (Σ (i : t), f i) → fin m × fin n
  | ⟨x,y⟩ := ((finite.to_nat t).f x,fin.nest' (Hmn x) $ (H' x).to_nat.f y)

def fd : (Σ (i : t), f i) → fin (m * n) :=
(@bij.prod.append.f m n) ∘ fd'

lemma injective_fd
: injective fd :=
begin
  unfold fd,
  apply injective_comp,
  { apply bijection.f_injective (bij.prod.append (m _) (n _)) },
  { intros i j,
    cases i with i₀ i₁, cases j with j₀ j₁,
    unfold fd', intros H,
    injection H with H₀ H₁,
    have H₂ := bijection.f_injective _ H₀,
    subst j₀,
    have H₃ := fin.nest'_injective _ H₁,
    have H₄ := bijection.f_injective _ H₃,
    subst j₁ },
end

end fg

noncomputable instance sched_sigma {t : Type u} {f : t → Type v} [∀ l, sched (f l)]
: ∀ [sched t], sched (Σ i, f i)
  | (sched.fin x) := have sched t, from sched.fin x,
                     if h : (∃ i, is_infinite (f i))
                     then sched.inf (infinite_of_injective
                                     (@injective_d _ _ this _)
                                     (@injective_b _ _ this _ h) )
                     else sched.fin (finite_of_injective
                                     (@injective_fd _ _ this x _inst_1 h) )
  | (sched.inf x) := if (∃ i, ∀ j : ℕ, i ≤ j → is_empty (f $ (@infinite.to_nat t x).g j))
                     then sorry
                     else sorry

end

namespace unitb

section

open unitb has_mem temporal

parameters {lbl : Type}
parameters {s : Type u}
parameters [system_sem s]
parameters {α : Type}
parameters r : α → set lbl
parameters r_nemp : ∀ x, r x ≠ ∅
parameters s₀ : α
parameters next : ∀ l s, r s l → α
parameters {F : s}
parameters ch : unitb.state s → lbl
parameters object : unitb.state s → α
def req (σ) := r (object σ)
parameters P : ∀ l, (mem l ∘ req)  >~>  (eq l ∘ ch)  in  F
parameters INIT : system.init F (eq s₀ ∘ object)
parameters STEP : unitb.co' F (λ σ σ', ∃ P, object σ' = next (ch σ) (object σ) P)
parameters INV : ∀ σ, ch σ ∈ req σ

def t := target_mch.mk _ s₀ r r_nemp next

include ch F INIT STEP INV P
lemma scheduling'
: ∃ τ : stream α, fair t τ :=
begin
  apply exists_imp_exists' (map object) _ (system_sem.inhabited F),
  intros τ sem,
  apply fair.mk,
  { have h := system_sem.init_sem τ sem INIT,
    unfold temporal.init function.comp at h,
    unfold map nth, rw -h, refl },
  { intro i,
    simp [temporal.init_drop,temporal.action_drop],
    existsi (ch $ τ i),
    split,
    { have Hsaf := system_sem.safety _ _ sem i,
      rw action_drop at Hsaf,
      unfold map nth target_mch.action,
      apply (STEP (τ i) (τ $ succ i) Hsaf), },
    { unfold map nth target_mch.action function.comp,
      apply INV } },
  { intros l h,
    let t := t r r_nemp s₀ next,
    have H : ⟦λ s s', t.action (ch s) (object s) (object s')⟧ && •eq l ∘ ch
          ⟹ (•mem l ∘ t.req ∘ object && ⟦t.action l on object⟧),
    { simp [init_eq_action,action_and_action],
      unfold comp,
      apply action_entails_action, intros σ σ' H,
      cases H with H₀ H₁, subst l,
      split,
      { apply H₀ }, { apply INV } },
    apply inf_often_entails_inf_often H,
    apply coincidence',
    { apply henceforth_entails_henceforth _ _ (system_sem.safety _ _ sem),
      apply action_entails_action,
      intros σ σ' H, apply STEP σ σ' H, },
    { apply system_sem.often_imp_often_sem' _ sem (P l) h, }, },
end

end

open unitb has_mem

variable {lbl : Type}

variable t : target_mch lbl

structure scheduler :=
 (s : Type u)
 (sem : system_sem s)
 (F : s)
 (ch : unitb.state s → lbl)
 (object : unitb.state s → t.σ)
 (INIT : system.init F (eq t.s₀ ∘ object))
 (STEP : unitb.co' F (λ σ σ', ∃ P, object σ' = t.next (ch σ) (object σ) P))
 (INV  : ∀ σ, ch σ ∈ t.req (object σ))
 (PROG : ∀ l, (mem l ∘ t.req ∘ object)  >~>  (eq l ∘ ch) in F)

lemma scheduling
  (sch : scheduler t)
  (sem : system_sem (sch.s))
: ∃ τ : stream t.σ, fair t τ :=
begin
  have H : t = scheduling.unitb.t t.req t.req_nemp t.s₀ t.next,
  { cases t, refl },
  rw H,
  apply @scheduling' lbl sch.s sch.sem t.σ _ _ t.s₀ _ _
        sch.ch sch.object sch.PROG sch.INIT sch.STEP sch.INV
end
end unitb

end scheduling

-- TODO:
--   generalize finite and infinite so that all that each module only has to provide
--   a ranking system for events.
