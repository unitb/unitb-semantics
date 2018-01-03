
import data.stream
import unitb.logic
import util.logic
import util.classical
import util.data.array
import util.data.bijection
import util.data.stream
import util.meta.tactic

import temporal_logic

universe variables u v

namespace scheduling

open stream nat function
open predicate
namespace unitb

section target

parameters (lbl : Type)

structure target_mch :=
  (σ : Type)
  (s₀ : σ)
  (req : var σ (set lbl))
  (req_nemp : ∀ x, req.apply x ≠ ∅)
  (next : ∀ l s, l ∈ req.apply s → σ)

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
  (valid : τ ⊨ ◻ (∃∃ l, •(↑l ∊ t.req) ⋀ ⟦ t.action l ⟧))
  (fair : ∀ l, τ ⊨ ◻◇•(↑l ∊ t.req) ⟶ ◻◇(•(↑l ∊ t.req) ⋀ ⟦ t.action l ⟧))
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

lemma is_empty_elim {α : Sort v} {l : Type u} (x : l) [sched l]
: is_empty l → α :=
begin
  intros H,
  cases _inst_1 with Hinst ;
  unfold is_empty at H,
  { have y := Hinst.to_nat.f x,
    rw H at y,
    apply y.elim0 },
  { cases H },
end

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

set_option pp.implicit false

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
array.maximum ( d_array.mk (λ i, (H' $ (finite.to_nat t).g i).count) )

lemma Hmn : ∀ i, (H' i).count ≤ n :=
begin
  intro i,
  unfold n,
  rw ← _inst_2.to_nat.f_inv i,
  change (d_array.mk $ λ i, (H' H ((finite.to_nat t).g i)).count).read _ ≤ _,
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

section infinite_sigma

parameter {t : Type u}
parameter {f : t → Type v}
parameter [infinite t]
parameter [∀ i, sched (f i)]

def inf_to_nat' : (Σ (i : t), f i) → ℕ × ℕ
  | ⟨x,y⟩ := ((infinite.to_nat t).f x,index_of y)

def inf_to_nat : (Σ (i : t), f i) → ℕ :=
(bij.prod).f ∘ inf_to_nat'

lemma injective_inf_to_nat
: injective inf_to_nat :=
begin
  unfold inf_to_nat,
  apply injective_comp,
  { apply bijection.f_injective },
  { intros i j,
    cases i with i₀ i₁, cases j with j₀ j₁,
    unfold inf_to_nat',
    intros H,
    injection H with H₀ H₁,
    have H₂ := bijection.f_injective _ H₀,
    subst j₀,
    rw injective_index_of H₁, },
end

parameter H₀ : ¬ (∃ i, ∀ j : ℕ, i ≤ j → is_empty (f $ (infinite.to_nat t).g j))
include H₀

lemma H₁ (i : ℕ)
: ∃ j : ℕ, i ≤ j ∧ ¬ is_empty (f $ (infinite.to_nat t).g j) :=
begin
  simp [not_exists_iff_forall_not,not_forall_iff_exists_not,not_imp_iff_and_not] at H₀,
  apply exists_imp_exists _ (H₀ i),
  intros j H, apply H
end

noncomputable def inf_from_nat : ℕ → (Σ (i : t), f i) :=
begin
  have H₁ := H₁ H₀, clear H₀,
  let s := solutions H₁,
  intros i,
  let j := (infinite.to_nat t).g (s i),
  existsi j,
  destruct _inst_2 j ; intros _inst_3 Hinst,
  { apply _inst_3.to_nat.g,
    existsi 0,
    apply lt_of_le_of_ne,
    apply zero_le,
    have H := solutions_spec H₁ i,
    rw Hinst at H, unfold is_empty at H,
    rw eq_comm at H, apply H },
  { apply _inst_3.to_nat.g 0 },
end

lemma injective_inf_from_nat
: injective inf_from_nat :=
begin
  unfold inf_from_nat, simp,
  intros i j H,
  injection H with H₀ H₁,
  have H₂ := bijection.g_injective _ H₀,
  apply solutions_injective _ H₂,
end

end infinite_sigma

section inf_embed

parameters {t : Type u} {f : t → Type v}
parameters [infinite t] [∀ l, sched (f l)]
parameters h₀ : (∃ i, ∀ j : ℕ, i ≤ j → is_empty (f $ (infinite.to_nat t).g j))
parameters h₁ : ∀ [finite { i // nonempty (f i)}], sched (Σ i : { i // nonempty (f i)}, f i.1)
private noncomputable def n := classical.some h₀

noncomputable def embedded_F : { i // nonempty (f i)} → fin n
  | ⟨x,Hx⟩ :=
begin
  existsi (infinite.to_nat t).f x,
  apply classical.by_contradiction,
  intros h₁,
  have H' := classical.some_spec h₀ _ (le_of_not_gt h₁),
  rw bijection.f_inv at H',
  cases Hx with i,
  apply is_empty_elim i H'
end

def b_f : (Σ i, f i) → (Σ i : {i // nonempty (f i)}, f i.val)
  | ⟨x,Hx⟩ := ⟨⟨x,nonempty.intro Hx⟩,Hx⟩

def b_g : (Σ i : {i // nonempty (f i)}, f i.val) → (Σ i, f i)
  | ⟨⟨x,_⟩,Hx⟩ := ⟨x,Hx⟩

parameter (f)

def bij_ne : bijection (Σ i, f i) (Σ i : {i // nonempty (f i)}, f (i.val)) :=
bijection.mk b_f b_g
(by { intro x, cases x, refl })
(by { intro x, cases x with x, cases x, refl })

parameter {f}

include h₀ h₁

noncomputable def embedded : sched (Σ i, f i) :=
begin
  let n := classical.some h₀,
  have h : finite { i // nonempty (f i)},
  { apply @finite_of_injective _ n (embedded_F h₀),
    intros i j,
    cases i with i₀ i₁, cases j with j₀ j₁,
    unfold embedded_F, intros H,
    injection H with H₀,
    have H₁ := bijection.f_injective _ H₀,
    subst j₀ },
  have h₂ := @h₁ h,
  have h₀ :=  (bij_ne f),
  cases h₂ with Hfin Hinf,
  { apply sched.fin,
    have h₁ := Hfin.to_nat,
    apply finite.mk Hfin.count (h₁ ∘ h₀), },
  { apply sched.inf,
    have h₁ := Hinf.to_nat,
    apply infinite.mk (h₁ ∘ h₀), },
end

end inf_embed

noncomputable instance sched_sigma_of_finite {t : Type u} {f : t → Type v}
  [∀ l, sched (f l)] [finite t]
: sched (Σ i, f i) := have sched t, by { apply sched.fin, apply_instance },
                      if h : (∃ i, is_infinite (f i))
                      then sched.inf (infinite_of_injective
                                      (@injective_d _ _ this _)
                                      (@injective_b _ _ this _ h) )
                      else sched.fin (finite_of_injective
                                      (@injective_fd _ _ this _ _inst_1 h) )

noncomputable instance sched_sigma {t : Type u} {f : t → Type v} [∀ l, sched (f l)]
: ∀ [sched t], sched (Σ i, f i)
  | (sched.fin _) := by { apply scheduling.sched_sigma_of_finite }
  | (sched.inf x) := if h : (∃ i, ∀ j : ℕ, i ≤ j → is_empty (f $ (@infinite.to_nat t x).g j))
                     then @embedded _ _ x _ h (@scheduling.sched_sigma_of_finite _ _ _)
                     else sched.inf (infinite_of_injective
                                      (@injective_inf_to_nat _ _ x _)
                                      (@injective_inf_from_nat _ _ x _ h))

end

namespace unitb

section

open unitb has_mem temporal

parameters {lbl : Type}
parameters {s : Type u}
parameters [system_sem s]
parameters {α : Type}
parameters r : var α (set lbl)
parameters r_nemp : ∀ x, r.apply x ≠ ∅
parameters s₀ : α
parameters next : ∀ l s, r.apply s l → α
parameters {F : s}
parameters ch : var (unitb.state s) lbl
parameters object : var (unitb.state s) α
def req : var _ _  := r ∘' object
parameters P : ∀ l : lbl, (↑l ∊ req)  >~>  (ch ≃ l)  in  F
parameters INIT : system.init F (object ≃ s₀)
parameters STEP : unitb.co' F (λ σ σ', ∃ P, object.apply σ' = next (ch.apply σ) (object.apply σ) P)
parameters INV : ∀ σ, σ ⊨ ch ∊ req

def t := target_mch.mk _ s₀ r r_nemp next
open unitb.system_sem  unitb.system target_mch
include ch F INIT STEP INV P
lemma scheduling'
: ∃ τ : stream α, fair t τ :=
begin
  apply exists_imp_exists' (map object.apply) _ (system_sem.inhabited F),
  intros τ sem,
  apply fair.mk,
  { rw ← eq_judgement at sem,
    have h := system_sem.init_sem sem INIT,
    simp [temporal.init,comp] at h,
    unfold map nth, rw ← h, refl },
  { simp,
    begin [temporal]
      have Hsaf := system_sem.safety F Γ,
      replace Hsaf := Hsaf sem,
      clear sem,
      henceforth,
      existsi ch,
      split,
      explicit
      { simp [h], have := INV,
        simp [req] at this, apply this },
      { replace STEP := co_sem' Hsaf STEP,
        henceforth at STEP,
        revert STEP h,
        action
        { simp [on_fun,target_mch.action,comp],
          introv H₀ H₁, subst ch₀,
          split, rw H₁, refl }, }
    end, },
  { intros l h, simp at h ⊢,
    begin [temporal]
      replace P := often_imp_often_sem' (P l) sem,
      simp [req] at P h, replace  P := P h,
      have Hsaf := (system_sem.safety F Γ sem), clear sem,
      henceforth at P ⊢, eventually P ⊢,
      split, revert P,
      action { simp [req] at ⊢ INV,
               intros, subst l,
               apply INV, },
      { have H := co_sem' Hsaf STEP,
        henceforth at H,
        revert H P,
        action
        { simp [req] at ⊢ INV,
          intros, simp [target_mch.action,on_fun],
          subst l,
          existsi (INV σ), rw [a_1], refl, } }
      end },
end

end

open unitb has_mem

variable {lbl : Type}

variable t : target_mch lbl

def t_req : var t.σ (set lbl) := t.req

structure scheduler :=
 (s : Type u)
 (sem : system_sem s)
 (F : s)
 (ch : var (unitb.state s) lbl)
 (object : var (unitb.state s) t.σ)
 (INIT : system.init F (object ≃ t.s₀))
 (STEP : unitb.co' F (λ σ σ', ∃ P, object.apply σ' = t.next (ch.apply σ) (object.apply σ) P))
 (INV  : ∀ σ, σ ⊨ ch ∊ t.req ∘' object)
 (PROG : ∀ l : lbl, ↑l ∊ t_req t ∘' object  >~>  ch ≃ l in F)

instance (s : scheduler t) : system_sem (s.s) := s.sem

lemma scheduling
  (sch : scheduler t)
: ∃ τ : stream t.σ, fair t τ :=
begin
  have H : t = scheduling.unitb.t t.req t.req_nemp t.s₀ t.next,
  { cases t, refl },
  rw H,
  apply @scheduling' lbl sch.s sch.sem t.σ _ _ t.s₀ _ _
                     sch.ch sch.object sch.PROG sch.INIT sch.STEP sch.INV,
end
end unitb

end scheduling

-- TODO:
--   generalize finite and infinite so that all that each module only has to provide
--   a ranking system for events.
