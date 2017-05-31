
import unity.logic
import unity.scheduling
import unity.temporal

import util.logic

universe variables u u'
namespace nondet

section nondet

open predicate

parameter α : Type

@[reducible]
def pred := α → Prop

structure event : Type :=
  (coarse_sch : pred)
  (fine_sch : pred)
  (step : ∀ s, coarse_sch s → fine_sch s → α → Prop)
  (fis : ∀ s CS FS, ∃ s', step s CS FS s')

structure prog : Type 2 :=
  (lbl : Type)
  (lbl_is_sched : scheduling.sched lbl)
  (first : α → Prop)
  (first_fis : ∃ s, first s)
  (event' : lbl → event)

parameter {α}

def event.step_of (e : event) (σ σ' : α) : Prop :=
∃ Hc Hf, e.step σ Hc Hf σ'

def skip : event :=
{ coarse_sch := True
, fine_sch := True
, step := λ s _ _ s', s = s'
, fis := take s _ _, ⟨s,rfl⟩ }

def prog.event (s : prog) : option s.lbl → event
  | none := skip
  | (some e) := s^.event' e

def prog.init (s : prog) (p : pred) : Prop
:= s^.first ⟹ p

def prog.guard  (s : prog) (e : option s.lbl) : α → Prop :=
(s^.event e)^.coarse_sch && (s^.event e)^.fine_sch

def prog.coarse_sch_of (s : prog) (act : option s.lbl) : α → Prop :=
(s.event act).coarse_sch

@[simp]
lemma prog.coarse_sch_of_none (s : prog)
: s.coarse_sch_of none = True :=
by refl

def prog.fine_sch_of (s : prog) (act : option s.lbl) : α → Prop :=
(s.event act).fine_sch

@[simp]
lemma prog.fine_sch_of_none (s : prog)
: s.fine_sch_of none = True :=
by refl

def prog.take_step (s : prog)
: ∀ (e : option s.lbl) (σ : α), s^.coarse_sch_of e σ → s^.fine_sch_of e σ → α → Prop
  | none σ _ _ := λ σ', σ = σ'
  | (some e) σ Hc Hf := (s^.event e)^.step σ Hc Hf

def prog.step_of (s : prog) (act : option s.lbl) : α → α → Prop :=
(s.event act).step_of

def is_step (s : prog) (σ σ' : α) : Prop :=
∃ ev, s.step_of ev σ σ'

open temporal

lemma step_of_none  (s : prog) : s.step_of none = eq :=
begin
  unfold prog.step_of prog.event skip,
  apply funext, intro σ,
  apply funext, intro σ',
  unfold event.step_of,
  unfold event.coarse_sch event.fine_sch event.step,
  unfold True lifted₀,
  simp [exists_true],
end

lemma is_step_exists_event  (s : prog)
 : temporal.action (is_step s) = (⟦ eq ⟧ || ∃∃ ev : s.lbl, ⟦ (s.event' ev).step_of ⟧) :=
begin
  simp [exists_action,or_action],
  apply congr_arg,
  apply funext, intro σ,
  apply funext, intro σ',
  unfold is_step,
  simp [exists_option],
  rw or_congr,
  { simp [step_of_none] },
  { apply exists_congr, intro e,
    refl }
end

lemma is_step_exists_event'  (s : prog)
 : temporal.action (is_step s) = (∃∃ ev : option s.lbl, ⟦ s.step_of ev ⟧) :=
begin
  simp [exists_action,or_action],
  apply congr_arg,
  apply funext, intro σ,
  apply funext, intro σ',
  unfold is_step,
  simp [exists_option],
end

lemma is_step_inst' (s : prog) (ev : option s.lbl)
: ⟦ s.step_of ev ⟧ ⟹ ⟦ is_step s ⟧ :=
begin
  rw is_step_exists_event',
  intros τ, simp,
  apply exists.intro ev,
end

def pair  (σ σ' : α) : stream α
  | 0 := σ
  | (nat.succ i) := σ'

lemma is_step_inst (s : prog) (ev : option s.lbl) (σ σ' : α)
  (h : s.step_of ev σ σ')
: is_step s σ σ' :=
begin
  change ⟦ is_step s ⟧ (pair σ σ'),
  apply is_step_inst' _ ev,
  apply h
end

instance : unity.has_safety prog :=
  { σ := α
  , step := is_step }

structure prog.ex (s : prog) (τ : stream α) : Prop :=
    (init : s^.first (τ 0))
    (safety : unity.saf_ex s τ)
    (liveness : ∀ e, (<>[]• s^.coarse_sch_of e) τ →
                     ([]<>• s^.fine_sch_of e) τ →
                     ([]<> ⟦ s.step_of e ⟧) τ)

structure prog.falsify (s : prog) (act : option s.lbl) (p : pred' α) : Prop :=
  (enable : p ⟹ s^.coarse_sch_of act)
  (schedule : prog.ex s ⟹ (<>[]•p ⟶ []<>• s^.fine_sch_of act) )
  (negate' : ⦃ •p ⟶ ⟦ s^.step_of act ⟧ ⟶ ⊙-•p ⦄)

open temporal

lemma prog.falsify.negate
   {s : prog} {act : option s.lbl} {p : pred}
:  prog.falsify s act p
→  •p && ⟦ s^.step_of act ⟧ ⟹ <>-•p :=
begin
  intros h₀ τ h₁,
  note h₂ := h₀.negate' _ h₁^.left h₁^.right,
  unfold eventually p_not init,
  existsi 1,
  apply h₂,
end

def prog.transient (s : prog) (p : pred' α) : Prop :=
∃ (act : option s.lbl), prog.falsify s act p

section theorems

variable (s : prog)

open prog
open event

theorem prog.transient_false : transient s False :=
begin
  unfold prog.transient,
  existsi none,
  apply falsify.mk,
  { intros σ h, cases h },
  { intros τ i h₀ h₁,
    simp at h₀,
    cases h₀, },
  { intros σ h₀ h₁, cases h₀ with h₂ }
end

def prog.transient_str : ∀ (s : prog) {p q : α → Prop}, (∀ (i : α), p i → q i) → prog.transient s q → prog.transient s p :=
begin
  intros s p q h,
  unfold transient,
  apply exists_imp_exists,
  intros e h',
  apply falsify.mk,
  { apply forall_imp_forall _ h'.enable,
    intro x,
    apply imp_imp_imp_left,
    apply h },
  { apply forall_imp_forall _ h'.schedule,
    intro τ,
    apply forall_imp_forall _,
    intro j,
    apply p_imp_p_imp_p_imp_left _,
    apply eventually_entails_eventually,
    apply henceforth_entails_henceforth,
    apply init_entails_init,
    apply h },
  { apply forall_imp_forall _ h'.negate',
    intro τ,
    apply imp_mono _ _,
    { apply h },
    apply imp_imp_imp_right _,
    apply next_imp_next _ _,
    apply entail_contrapos,
    apply init_entails_init,
    apply h }
end

end theorems

instance prog_is_system : unity.system prog :=
{ σ := α
, transient := @prog.transient
, step := is_step
, init   := prog.init
, transient_false := prog.transient_false
, transient_str := prog.transient_str }

section soundness

open prog

variables {s : prog} {p : pred' α}
variables (τ : stream α)
variables (h : ex s τ)
include h

lemma init_sem
  (I₀ : init s p)
: (•p) τ :=
begin
  unfold temporal.init,
  unfold init prog.init at I₀,
  apply I₀,
  apply h.init,
end

lemma transient.semantics
  (T₀ : prog.transient s p)
: ([]<>-•p) τ :=
begin
  cases (temporal.em' (•p) τ) with h_p ev_np,
  { unfold prog.transient at T₀,
    cases T₀ with ev T₀,
    assert Hc : (<>[]•s.coarse_sch_of ev) τ,
    { apply eventually_entails_eventually _ _ h_p,
      apply henceforth_entails_henceforth _ ,
      apply init_entails_init _ ,
      apply T₀.enable },
    assert Hf : ([]<>•s.fine_sch_of ev) τ,
    { apply T₀.schedule _ h h_p, },
    note act := coincidence h_p (h.liveness ev Hc Hf),
    rw [-eventually_eventually],
    apply henceforth_entails_henceforth _ _ act,
    apply eventually_entails_eventually _ ,
    apply T₀.negate },
  { apply ev_np },
end

end soundness

open scheduling nat list

noncomputable def run_one  (p : prog)
  [∀ (x : option p.lbl) σ, decidable (p.guard x σ)]
  (e : option p.lbl) (s : α) : α :=
if h : p.guard e s
then classical.some ((p.event e).fis s h.left h.right)
else s

noncomputable def run' (p : prog)
  [∀ (x : option p.lbl) σ, decidable (p.guard x σ)]
: list (option p.lbl) → α → α
  | nil s := s
  | (cons e es) s := run' es $ run_one p e s

lemma run_cons (p : prog) (xs : list (option p.lbl)) (x : option p.lbl)
  [∀ (x : option p.lbl) σ, decidable (p.guard x σ)]
: run' p (x :: xs) = run' p xs ∘ run_one p x :=
by refl

lemma run_append (p : prog) (xs ys : list (option p.lbl))
  [∀ (x : option p.lbl) σ, decidable (p.guard x σ)]
: run' p (xs ++ ys) = run' p ys ∘ run' p xs :=
begin
  apply funext,
  induction xs with x xs IH
  ; intro σ
  ; unfold function.comp,
  { unfold run',
    simp },
  { simp,
    unfold run',
    rw [IH], }
end

lemma run_concat_eq_comp (p : prog) (xs : list (option p.lbl)) (x : option p.lbl)
  [∀ (x : option p.lbl) σ, decidable (p.guard x σ)]
: run' p (concat xs x) = run_one p x ∘ run' p xs :=
begin
  simp [concat_eq_append,run_append],
  refl,
end

lemma run_concat (p : prog) (xs : list (option p.lbl)) (x : option p.lbl) (σ : α)
  [∀ (x : option p.lbl) σ, decidable (p.guard x σ)]
: run' p (concat xs x) σ = run_one p x (run' p xs σ) :=
by rw run_concat_eq_comp

noncomputable def prog.first_state (s : prog) := (classical.some s.first_fis)

noncomputable def run (s : prog)  [∀ (x : option s.lbl) σ, decidable (s.guard x σ)]
  (τ : stream (option s.lbl))
: stream α :=
λ i, run' s (stream.approx i τ) s.first_state

noncomputable def enabled (s : prog)
  [∀ (x : option s.lbl) σ, decidable (s.guard x σ)]
  (es : list (option s.lbl))
: set (option s.lbl) :=
{ l | s.guard l (run' s es s.first_state) }

open unity has_mem

lemma prog.run_succ  (s : prog) (τ : stream (option s.lbl)) (i : ℕ)
  [Π (x : option (s.lbl)) (σ : α), decidable (prog.guard s x σ)]
: (run s τ (succ i)) = run_one s (τ i) (run s τ i) :=
begin
  unfold run,
  rw [stream.approx_succ_eq_concat,run_concat],
end

lemma prog.run_skip  (s : prog) (τ : stream (option s.lbl)) (i : ℕ)
  [Π (x : option (s.lbl)) (σ : α), decidable (prog.guard s x σ)]
  (Hguard : ¬ prog.guard s (τ i) (run s τ i))
: (run s τ (succ i)) = run s τ i :=
begin
  rw [s.run_succ],
  unfold run_one,
  rw dif_neg Hguard,
end

lemma prog.run_enabled  (s : prog) (τ : stream (option s.lbl)) (i : ℕ)
  [Π (x : option (s.lbl)) (σ : α), decidable (prog.guard s x σ)]
  (Hcoarse : prog.coarse_sch_of s (τ i) (run s τ i))
  (Hfine : prog.fine_sch_of s (τ i) (run s τ i))
: (prog.event s (τ i)).step (run s τ i) Hcoarse Hfine (run s τ (succ i)) :=
begin
  pose Hguard : s.guard (τ i) (run s τ i) := ⟨Hcoarse,Hfine⟩,
  rw [s.run_succ],
  unfold run_one,
  rw [dif_pos Hguard],
  note h := classical.some_spec ((s.event (τ i)).fis (run s τ i) (and.left Hguard) (and.right Hguard)),
  apply h,
end

lemma prog.witness (s : prog)
: ∃ (τ : stream α), prog.ex s τ :=
begin
  note _inst := s.lbl_is_sched,
  assert _inst_1 : ∀ (x : option s.lbl) σ, decidable (s.guard x σ),
  { intros, apply classical.prop_decidable },

  pose evts : list (option s.lbl) → set (option s.lbl) := enabled s,

  apply exists_imp_exists' (run s) _ (sched.sched_str' evts),
  intros τ h,
  apply ex.mk,
  { unfold run,
    apply classical.some_spec },
  { unfold saf_ex,
    intro i,
    simp [action_drop],
    unfold step has_safety.step is_step,
    note Hc : (s.event none).coarse_sch (run s τ i) := trivial,
    note Hf : (s.event none).fine_sch (run s τ i) := trivial,
    destruct (τ i),
    { intros h,
      existsi (τ i),
      rw -h at Hc Hf,
      unfold  step_of event.step_of,
      existsi Hc, existsi Hf,
      apply s.run_enabled, },
    { intros e h,
      cases _inst_1 (τ i) (run s τ i) with Hguard Hguard,
      { existsi none,
        rw step_of_none s,
        rw [s.run_skip _ _ Hguard], },
      { existsi (τ i),
        unfold  step_of event.step_of,
        existsi Hguard.left, existsi Hguard.right,
        apply s.run_enabled, } }, },
  { apply forall_imp_forall _ h,
    intros e Heq Hc Hf i,
    assert inf_evts : ([]<>•mem e) (req_of evts τ),
    { clear Heq h,
      note Hg := coincidence Hc Hf,
      revert evts, simp,
      unfold req_of enabled,
      change (([]<>•mem e) (λ (i : ℕ), {l : option (s.lbl) | s.guard l (run s τ i)})),
      change (([]<>•mem e) ((λ (σ : α), {l : option (s.lbl) | s.guard l σ}) ∘ (run s τ))),
      rw -inf_often_trace_init_trading,
      apply Hg, },
    cases (Heq inf_evts i) with j Heq,
    rw [stream.drop_drop,init_drop,stream.fst_zip',stream.snd_zip'] at Heq,
    cases Heq with He Hguard,
    rename Hguard Hguard',
    assert Hguard : s.guard (τ (j + i)) (run s τ (j + i)),
    { subst e,
      rw [or.comm,or_iff_not_imp] at Hguard',
      apply Hguard',
      apply @set.ne_empty_of_mem _ _ none,
      change true ∧ true,
      simp, },
    clear Hguard',
    unfold eventually, existsi j,
    rw He,
    rw [stream.drop_drop,action_drop],
    unfold prog.step_of event.step_of,
    existsi Hguard.left,existsi Hguard.right,
    apply s.run_enabled },
end

-- instance {α} [sched lbl] : system_sem (prog lbl) :=
instance : unity.system_sem prog :=
  { (_ : unity.system prog) with
    ex := prog.ex
  , safety := @prog.ex.safety _
  , inhabited := prog.witness
  , init_sem := @init_sem
  , transient_sem := @transient.semantics }

open unity

def unless_except (s : prog) (p q : pred' α) (evts : set event) : Prop :=
unless' s p q (λ σ σ', ∃ e, e ∈ evts ∧ event.step_of e σ σ')

theorem unless_except_rule {s : prog} {p q : pred' α} (exp : set event)
  (ACT : ∀ (e : s.lbl) σ Hc Hf σ',
        ¬ s.event' e ∈ exp
      → (s.event' e).step σ Hc Hf σ'
      → p σ → ¬ q σ → p σ' ∨ q σ')
: unless_except s p q exp :=
begin
  intros σ σ' STEP EXP H,
  cases H with Hp Hq,
  unfold step has_safety.step is_step at STEP,
  cases STEP with e STEP,
  unfold prog.step_of event.step_of at STEP,
  cases STEP with Hc STEP,
  cases STEP with Hf STEP,
  cases e with e,
  { unfold prog.event skip event.step at STEP,
    subst σ',
    left, apply Hp },
  { apply ACT e _ Hc Hf _ _ STEP Hp Hq,
    intro Hin,
    apply EXP,
    clear ACT EXP,
    unfold prog.step_of event.step_of prog.event,
    existsi s.event' e, split, apply Hin,
    existsi Hc, existsi Hf,
    apply STEP }
end

theorem unless_rule {s : prog} {p q : pred' α}
  (ACT : ∀ (e : s.lbl) σ Hc Hf σ', (s.event' e).step σ Hc Hf σ' → p σ → ¬ q σ → p σ' ∨ q σ')
: unless s p q :=
begin
  rw unless_eq_unless_except,
  assert H : unless_except s p q ∅,
  { apply unless_except_rule,
    intros,
    apply ACT
    ; try { assumption }, },
  unfold unless_except at H,
  assert Heq : (λ (σ σ' : α), ∃ (e : event), e ∈ (∅ : set event) ∧ e.step_of σ σ')
             = (λ (_x : α), False),
  { apply funext, intro,
    apply funext, intro,
    simp,
    apply eq_false_of_not_eq_true,
    apply eq_true_intro,
    intro H,
    cases H with e H,
    cases H with H₀ H₁,
    apply H₁, },
  apply iff.elim_left _ H,
  rw iff_eq_eq,
  apply congr_arg _ Heq,
end

theorem transient_rule {s : prog} {p : pred' α} (ev : option s.lbl)
   (EN : p ⟹ s.coarse_sch_of ev)
   (FLW : leads_to s (p && s.coarse_sch_of ev) (s.fine_sch_of ev))
   (NEG : ∀ σ σ', p σ → s.step_of ev σ σ' → ¬p σ')
: s.transient p :=
begin
  unfold prog.transient,
  existsi ev,
  apply falsify.mk,
    -- enablement
  { apply EN },
    -- follow
  { intros τ sem H,
    apply inf_often_of_leads_to (system_sem.leads_to_sem FLW _ sem),
    note H' := inf_often_of_stable _ H,
    apply henceforth_entails_henceforth _ _ H',
    apply eventually_entails_eventually _ ,
    apply init_entails_init _ ,
    intros σ Hp,
    apply and.intro Hp,
    apply EN _ Hp },
    -- negation
  { intros σ Hp Hact,
    apply NEG _ _ Hp Hact }
end

end nondet

end nondet
