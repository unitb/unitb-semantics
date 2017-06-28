
import unity.logic
import unity.scheduling
import unity.temporal

import unity.models.nondet

import util.logic

universe variables u u'
namespace ghost

section ghost

open predicate

parameters {α α' : Type}

@[reducible]
def pred := α → Prop
@[reducible]
def pred' := α' → Prop

variables abs : α' → α

structure event : Type :=
  (coarse_sch : pred)
  (fine_sch : pred)
  (step : ∀ s, coarse_sch s → fine_sch s → α → Prop)
  (abs_step : ∀ s, coarse_sch (abs s) → fine_sch (abs s) → α' → Prop)
  (fis : ∀ s CS FS, ∃ s', step s CS FS s')

variables {abs}

def event.step_of (e : event abs) (σ σ' : α) : Prop :=
∃ Hc Hf, e.step σ Hc Hf σ'

structure program : Type 2 :=
  (lbl : Type)
  (lbl_is_sched : scheduling.sched lbl)
  (first : α → Prop)
  (first_fis : ∃ s, first s)
  (abs : α' → α)
  (event' : lbl → event abs)

-- prove that if p ∘ abs ↦ q ∘ abs in P' then
-- p ↦ q in P

-- def concrete : program → nondet.program

def skip : event abs :=
{ coarse_sch := True
, fine_sch := True
, step := λ s _ _ s', s = s'
, abs_step := λ s _ _ s', s = s'
, fis := take s _ _, ⟨s,rfl⟩ }

def program.event (s : program) : option s.lbl → event s.abs
  | none := skip
  | (some e) := s^.event' e

def program.init (s : program) (p : pred) : Prop
:= s^.first ⟹ p

def program.guard  (s : program) (e : option s.lbl) : α → Prop :=
(s^.event e)^.coarse_sch && (s^.event e)^.fine_sch

def program.coarse_sch_of (s : program) (act : option s.lbl) : α → Prop :=
(s.event act).coarse_sch

def program.coarse_sch_of' (s : program) (act : option s.lbl) : α' → Prop :=
program.coarse_sch_of s act ∘ s.abs

@[simp]
lemma program.coarse_sch_of_none (s : program)
: s.coarse_sch_of none = True :=
by refl

def program.fine_sch_of (s : program) (act : option s.lbl) : α → Prop :=
(s.event act).fine_sch

def program.fine_sch_of' (s : program) (act : option s.lbl) : α' → Prop :=
program.fine_sch_of s act ∘ abs

@[simp]
lemma program.fine_sch_of_none (s : program)
: s.fine_sch_of none = True :=
by refl

def program.take_step (s : program)
: ∀ (e : option s.lbl) (σ : α), s^.coarse_sch_of e σ → s^.fine_sch_of e σ → α → Prop
  | none σ _ _ := λ σ', σ = σ'
  | (some e) σ Hc Hf := (s^.event e)^.step σ Hc Hf

def program.step_of (s : program) (act : option s.lbl) : α → α → Prop :=
(s.event act).step_of

def is_step (s : program) (σ σ' : α) : Prop :=
∃ ev, s.step_of ev σ σ'

open temporal

lemma step_of_none  (s : program) : s.step_of none = eq :=
begin
  unfold program.step_of program.event skip,
  apply funext, intro σ,
  apply funext, intro σ',
  unfold event.step_of,
  unfold event.coarse_sch event.fine_sch event.step,
  unfold True lifted₀,
  simp [exists_true],
end

lemma is_step_exists_event  (s : program)
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

lemma is_step_exists_event'  (s : program)
 : temporal.action (is_step s) = (∃∃ ev : option s.lbl, ⟦ s.step_of ev ⟧) :=
begin
  simp [exists_action,or_action],
  apply congr_arg,
  apply funext, intro σ,
  apply funext, intro σ',
  unfold is_step,
  simp [exists_option],
end

lemma is_step_inst' (s : program) (ev : option s.lbl)
: ⟦ s.step_of ev ⟧ ⟹ ⟦ is_step s ⟧ :=
begin
  rw is_step_exists_event',
  intros τ, simp,
  apply exists.intro ev,
end

def pair  (σ σ' : α) : stream α
  | 0 := σ
  | (nat.succ i) := σ'

lemma is_step_inst (s : program) (ev : option s.lbl) (σ σ' : α)
  (h : s.step_of ev σ σ')
: is_step s σ σ' :=
begin
  change ⟦ is_step s ⟧ (pair σ σ'),
  apply is_step_inst' _ ev,
  apply h
end

instance : unity.has_safety program :=
  { σ := α
  , step := is_step }

structure program.ex (s : program) (τ : stream α) : Prop :=
    (init : s^.first (τ 0))
    (safety : unity.saf_ex s τ)
    (liveness : ∀ e, (<>[]• s^.coarse_sch_of e) τ →
                     ([]<>• s^.fine_sch_of e) τ →
                     ([]<> ⟦ s.step_of e ⟧) τ)

-- structure program.falsify (s : program) (act : option s.lbl) (p : pred') : Prop :=
--   (enable : p ⟹ s^.coarse_sch_of' act)
--   (schedule : s.ex ⟹ (<>[]•p ⟶ []<>• s.fine_sch_of' act) )
--   (negate' : ⦃ •p ⟶ ⟦ s^.step_of act ⟧ ⟶ ⊙-•p ⦄)

-- open temporal

-- lemma program.falsify.negate
--    {s : program} {act : option s.lbl} {p : pred}
-- :  s.falsify act p
-- →  •p && ⟦ s.step_of act ⟧ ⟹ <>-•p :=
-- begin
--   intros h₀ τ h₁,
--   note h₂ := h₀.negate' _ h₁^.left h₁^.right,
--   unfold eventually p_not init,
--   existsi 1,
--   apply h₂,
-- end

-- def program.transient (s : program) (p : pred' α) : Prop :=
-- ∃ (act : option s.lbl), s.falsify act p

-- section theorems

-- variable (s : program)

-- open program
-- open event

-- theorem program.transient_false : transient s False :=
-- begin
--   unfold program.transient,
--   existsi none,
--   apply falsify.mk,
--   { intros σ h, cases h },
--   { intros τ i h₀ h₁,
--     simp at h₀,
--     cases h₀, },
--   { intros σ h₀ h₁, cases h₀ with h₂ }
-- end

-- def program.transient_str : ∀ (s : program) {p q : α → Prop}, (∀ (i : α), p i → q i) → s.transient q → s.transient p :=
-- begin
--   intros s p q h,
--   unfold transient,
--   apply exists_imp_exists,
--   intros e h',
--   apply falsify.mk,
--   { apply forall_imp_forall _ h'.enable,
--     intro x,
--     apply imp_imp_imp_left,
--     apply h },
--   { apply forall_imp_forall _ h'.schedule,
--     intro τ,
--     apply forall_imp_forall _,
--     intro j,
--     apply p_imp_p_imp_p_imp_left _,
--     apply stable_entails_stable',
--     apply h },
--   { apply forall_imp_forall _ h'.negate',
--     intro τ,
--     apply imp_mono _ _,
--     { apply h },
--     apply imp_imp_imp_right _,
--     apply next_imp_next _ _,
--     apply entail_contrapos,
--     apply init_entails_init,
--     apply h }
-- end

-- end theorems

-- instance prog_is_system : unity.system program :=
-- { σ := α
-- , transient := program.transient
-- , step := is_step
-- , init   := program.init
-- , transient_false := program.transient_false
-- , transient_str := program.transient_str }

-- section soundness

-- open program

-- variables {s : program} {p : pred' α}
-- variables (τ : stream α)
-- variables (h : ex s τ)
-- include h

-- lemma init_sem
--   (I₀ : init s p)
-- : (•p) τ :=
-- begin
--   unfold temporal.init,
--   unfold init program.init at I₀,
--   apply I₀,
--   apply h.init,
-- end

-- lemma transient.semantics
--   (T₀ : s.transient p)
-- : ([]<>-•p) τ :=
-- begin
--   cases (temporal.em' (•p) τ) with h_p ev_np,
--   { unfold program.transient at T₀,
--     cases T₀ with ev T₀,
--     assert Hc : (<>[]•s.coarse_sch_of ev) τ,
--     { apply stable_entails_stable' _ _ h_p,
--       apply T₀.enable },
--     assert Hf : ([]<>•s.fine_sch_of ev) τ,
--     { apply T₀.schedule _ h h_p, },
--     note act := coincidence h_p (h.liveness ev Hc Hf),
--     rw [-eventually_eventually],
--     apply henceforth_entails_henceforth _ _ act,
--     apply eventually_entails_eventually _ ,
--     apply T₀.negate },
--   { apply ev_np },
-- end

-- end soundness

-- open scheduling nat list

-- noncomputable def program.first_state (s : program) := (classical.some s.first_fis)

-- open unity has_mem

-- lemma program.witness (s : program)
-- : ∃ (τ : stream α), s.ex τ :=
-- begin
--   note _inst := s.lbl_is_sched,
--   assert _inst_1 : ∀ (x : option s.lbl) σ, decidable (s.guard x σ),
--   { intros, apply classical.prop_decidable },

--   pose evts : list (option s.lbl) → set (option s.lbl) := enabled s,

--   apply exists_imp_exists' (run s) _ (sched.sched_str' evts),
--   intros τ h,
--   apply ex.mk,
--   { unfold run,
--     apply classical.some_spec },
--   { unfold saf_ex,
--     intro i,
--     simp [action_drop],
--     unfold step has_safety.step is_step,
--     note Hc : (s.event none).coarse_sch (run s τ i) := trivial,
--     note Hf : (s.event none).fine_sch (run s τ i) := trivial,
--     destruct (τ i),
--     { intros h,
--       existsi (τ i),
--       rw -h at Hc Hf,
--       unfold  step_of event.step_of,
--       existsi Hc, existsi Hf,
--       apply s.run_enabled, },
--     { intros e h,
--       cases _inst_1 (τ i) (run s τ i) with Hguard Hguard,
--       { existsi none,
--         rw step_of_none s,
--         rw [s.run_skip _ _ Hguard], },
--       { existsi (τ i),
--         unfold  step_of event.step_of,
--         existsi Hguard.left, existsi Hguard.right,
--         apply s.run_enabled, } }, },
--   { apply forall_imp_forall _ h,
--     intros e Heq Hc Hf i,
--     assert inf_evts : ([]<>•mem e) (req_of evts τ),
--     { clear Heq h,
--       note Hg := coincidence Hc Hf,
--       revert evts, simp,
--       unfold req_of enabled,
--       change (([]<>•mem e) (λ (i : ℕ), {l : option (s.lbl) | s.guard l (run s τ i)})),
--       change (([]<>•mem e) ((λ (σ : α), {l : option (s.lbl) | s.guard l σ}) ∘ (run s τ))),
--       rw -inf_often_trace_init_trading,
--       apply Hg, },
--     cases (Heq inf_evts i) with j Heq,
--     rw [stream.drop_drop,init_drop,stream.fst_zip',stream.snd_zip'] at Heq,
--     cases Heq with He Hguard,
--     rename Hguard Hguard',
--     assert Hguard : s.guard (τ (j + i)) (run s τ (j + i)),
--     { subst e,
--       rw [or.comm,or_iff_not_imp] at Hguard',
--       apply Hguard',
--       apply @set.ne_empty_of_mem _ _ none,
--       change true ∧ true,
--       simp, },
--     clear Hguard',
--     unfold eventually, existsi j,
--     rw He,
--     rw [stream.drop_drop,action_drop],
--     unfold program.step_of event.step_of,
--     existsi Hguard.left,existsi Hguard.right,
--     apply s.run_enabled },
-- end

-- -- instance {α} [sched lbl] : system_sem (program lbl) :=
-- instance : unity.system_sem program :=
--   { (_ : unity.system program) with
--     ex := program.ex
--   , safety := program.ex.safety _
--   , inhabited := program.witness
--   , init_sem := @init_sem
--   , transient_sem := @transient.semantics }

-- open unity

-- def unless_except (s : program) (p q : pred' α) (evts : set event) : Prop :=
-- unless' s p q (λ σ σ', ∃ e, e ∈ evts ∧ e.step_of σ σ')

-- theorem unless_except_rule {s : program} {p q : pred' α} (exp : set event)
--   (ACT : ∀ (e : s.lbl) σ Hc Hf σ',
--         ¬ s.event' e ∈ exp
--       → (s.event' e).step σ Hc Hf σ'
--       → p σ → ¬ q σ → p σ' ∨ q σ')
-- : unless_except s p q exp :=
-- begin
--   intros σ σ' STEP EXP H,
--   cases H with Hp Hq,
--   unfold step has_safety.step is_step at STEP,
--   cases STEP with e STEP,
--   unfold program.step_of event.step_of at STEP,
--   cases STEP with Hc STEP,
--   cases STEP with Hf STEP,
--   cases e with e,
--   { unfold program.event skip event.step at STEP,
--     subst σ',
--     left, apply Hp },
--   { apply ACT e _ Hc Hf _ _ STEP Hp Hq,
--     intro Hin,
--     apply EXP,
--     clear ACT EXP,
--     unfold program.step_of event.step_of program.event,
--     existsi s.event' e, split, apply Hin,
--     existsi Hc, existsi Hf,
--     apply STEP }
-- end

-- theorem unless_rule {s : program} {p q : pred' α}
--   (ACT : ∀ (e : s.lbl) σ Hc Hf σ', (s.event' e).step σ Hc Hf σ' → p σ → ¬ q σ → p σ' ∨ q σ')
-- : unless s p q :=
-- begin
--   rw unless_eq_unless_except,
--   assert H : unless_except s p q ∅,
--   { apply unless_except_rule,
--     intros,
--     apply ACT
--     ; try { assumption }, },
--   unfold unless_except at H,
--   assert Heq : (λ (σ σ' : α), ∃ (e : event), e ∈ (∅ : set event) ∧ e.step_of σ σ')
--              = (λ (_x : α), False),
--   { apply funext, intro,
--     apply funext, intro,
--     simp,
--     apply eq_false_of_not_eq_true,
--     apply eq_true_intro,
--     intro H,
--     cases H with e H,
--     cases H with H₀ H₁,
--     apply H₁, },
--   apply iff.elim_left _ H,
--   rw iff_eq_eq,
--   apply congr_arg _ Heq,
-- end

-- theorem transient_rule {s : program} {p : pred' α} (ev : option s.lbl)
--    (EN : p ⟹ s.coarse_sch_of ev)
--    (FLW : leads_to s (p && s.coarse_sch_of ev) (s.fine_sch_of ev))
--    (NEG : ∀ σ σ', p σ → s.step_of ev σ σ' → ¬p σ')
-- : s.transient p :=
-- begin
--   unfold program.transient,
--   existsi ev,
--   apply falsify.mk,
--     -- enablement
--   { apply EN },
--     -- follow
--   { intros τ sem H,
--     apply inf_often_of_leads_to (system_sem.leads_to_sem FLW _ sem),
--     have H' := inf_often_of_stable _ H,
--     apply henceforth_entails_henceforth _ _ H',
--     apply eventually_entails_eventually _ ,
--     apply init_entails_init _ ,
--     intros σ Hp,
--     apply and.intro Hp,
--     apply EN _ Hp },
--     -- negation
--   { intros σ Hp Hact,
--     apply NEG _ _ Hp Hact }
-- end

end ghost

end ghost
