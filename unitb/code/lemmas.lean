import unitb.predicate
import unitb.code.syntax
import unitb.code.rules

universe variables u v

open nat predicate

section

parameters (σ : Type) (lbl : Type)

@[reducible]
private def pred := σ → Prop

parameters {σ}


lemma assert_of_first {p q : pred} {c : code lbl p q}
: assert_of (first c) = p :=
begin
  induction c
  ; try { refl },
  case code.seq  p' q' r' c₀ c₁
  { unfold first,
    destruct first c₀,
    case none
    { intro h,
      simp [h],
      destruct first c₁,
      case none
      { intro h',
        simp [h'], unfold assert_of,
        simp [h'] at ih_2, unfold assert_of at ih_2,
        simp [h] at ih_1, unfold assert_of at ih_1,
        subst r', subst q' },
      case some
      { intros x h', simp [h'],
        unfold assert_of assert_of',
        rw h at ih_1, rw h' at ih_2,
        unfold assert_of at ih_1 ih_2,
        subst p', rw ih_2, } },
    case some
    { intros x h,
      simp [h],
      unfold assert_of assert_of',
      rw h at ih_1, unfold assert_of at ih_1,
      rw ih_1 }, }
end

lemma first_eq_none_imp_eq {p q : pred} {c : code lbl p q}
: first c = none → p = q :=
begin
  induction c
  ; unfold first
  ; try { contradiction },
  case code.skip
  { simp },
  case code.seq p' q' r' c₀ c₁
  { destruct first c₀,
    case none
    { intro h', simp [h'],
      intro h'', rw [ih_1 h',ih_2 h''], },
    case some
    { intros pc h,
      simp [h], contradiction }, },
end

local attribute [instance] classical.prop_decidable

lemma assert_of_next {p q : pred} {c : code lbl p q} (pc : option (current c)) (s : σ)
: assert_of (next s pc) = next_assert pc s :=
begin
  cases pc with pc,
  { refl },
  unfold next next_assert,
  induction pc
  ; try { refl }
  ; unfold next' next_assert',
  case current.seq_left
  { rw ← ih_1,
    cases next' s a,
    case none
    { destruct first c₁,
      case none
      { intros h₀,
        simp [h₀],
        unfold assert_of,
        cases c₁ ; try { refl }
        ; unfold first at h₀
        ; try { contradiction },
        { simp at h₀,
          simp [first_eq_none_imp_eq h₀.left,first_eq_none_imp_eq  h₀.right] }, },
      case some
      { intros pc h₀,
        simp,
        rw [h₀,fmap_some],
        unfold assert_of assert_of',
        change assert_of (some pc) = _,
        rw [← h₀,assert_of_first] } },
    case some
    { simp, refl } },
  case current.seq_right
  { rw ← ih_1,
    cases next' s a ; refl },
  case current.if_then_else_cond
  { cases classical.em (t s) with h h,
    { rw [if_pos h,if_pos h],
      destruct first c₀,
      { intros h, simp [h], have h := first_eq_none_imp_eq h,
        unfold assert_of, subst pa },
      { intros pc h, simp [h],
        unfold assert_of assert_of',
        change assert_of (some pc) = _,
        rw [← h,assert_of_first], }, },
    { rw [if_neg h,if_neg h],
      destruct first c₁,
      { intros h, simp [h],
        have h := first_eq_none_imp_eq h,
        unfold assert_of, subst pb },
      { intros pc h, simp [h],
        unfold assert_of assert_of',
        change assert_of (some pc) = _,
        rw [← h,assert_of_first], }, }, },
  case current.if_then_else_left
  { rw ← ih_1, clear ih_1,
    cases next' s a with pc ; simp,
    { refl },
    { unfold assert_of assert_of', }, },
  case current.if_then_else_right
  { rw ← ih_1, clear ih_1,
    cases next' s a with pc ; simp,
    { refl },
    { unfold assert_of assert_of', }, },
  case current.while_cond
  { cases classical.em (w s) with h h ;
    destruct first c_1,
    { intro h',
      rw [if_pos h,if_pos h,h'],
      have h'' := first_eq_none_imp_eq h', subst inv,
      refl, },
    { intros pc h',
      rw [if_pos h,if_pos h,h'],
      simp,
      change assert_of (some pc) = _,
      rw [← h',assert_of_first], },
    { intros h',
      rw [if_neg h,if_neg h], refl },
    { intros pc h',
      rw [if_neg h,if_neg h], refl }, },
  case current.while_body
  { rw ← ih_1, clear ih_1,
    destruct next' s a,
    { intros h',
      simp [h'], refl },
    { intros pc h',
      simp [h'], refl }, },
end

end

section local_correctness

local attribute [instance] classical.prop_decidable

parameters (σ : Type)

parameters (F : nondet.program σ)

@[reducible]
private def lbl := F.lbl

@[reducible]
private def pred := σ → Prop

parameters {σ}

variables {p q : pred}
variable (c : code lbl p q)

structure state_correctness (pc : option $ current c) : Prop :=
  (enabled : ∀ l, selects pc l → assert_of pc ⟹ F.guard (some l))
  (correct : ∀ l, selects pc l →
       ∀ s s', assert_of pc s → F.step_of (some l) s s' → next_assert pc s s')
  (cond_true : ∀ (H : is_control pc),
       ∀ s, assert_of pc s → condition pc H s → next_assert pc s s)
  (cond_false : ∀ (H : is_control pc),
       ∀ s, assert_of pc s → ¬ condition pc H s → next_assert pc s s)

lemma selects_action_imp_eq {l l' : lbl} {p q : pred} {ds : set lbl}
  (pc : option (current $ code.action p q ds l))
  (H : selects pc l')
: l' = l :=
begin
  cases pc with pc,
  { cases H },
  { cases pc, apply H, },
end

lemma assert_of_action {l : lbl} {p q : pred} {ds : set lbl}
  (pc : current $ code.action p q ds l)
: assert_of (some pc) = p :=
begin
  cases pc with pc, refl,
end

lemma next_assert_action {l : lbl} {p q : pred} {ds : set lbl}
  (pc : current $ code.action p q ds l)
  (s : σ)
: next_assert (some pc) s = q :=
begin
  cases pc with pc, refl,
end

section

variables H : correct F c
include H

lemma enabled_of_correct
: ∀ (pc : current c) l, selects (some pc) l → assert_of (some pc) ⟹ F.guard (some l) :=
begin
  induction H,
  { intros pc l Hpc, cases pc, },
  { intros pc l' Hpc, cases pc with pc,
    have Heq_l := selects_action_imp_eq _ Hpc, subst l',
    unfold assert_of assert_of', apply a },
  { intros pc l',
    cases pc with pc pc
    ; unfold selects assert_of selects' assert_of'
    ; intros Hpc,
    { apply ih_1 _ _ Hpc },
    { apply ih_2 _ _ Hpc }, },
  { intros pc l',
    cases pc with pc pc
    ; unfold selects assert_of selects' assert_of'
    ; intros Hpc,
    { cases Hpc },
    { apply ih_1 _ _ Hpc },
    { apply ih_2 _ _ Hpc }, },
  { intros pc l',
    cases pc with pc pc
    ; unfold selects assert_of selects' assert_of'
    ; intros Hpc,
    { cases Hpc },
    { apply ih_1 _ _ Hpc }, },
end

lemma correct_of_correct
: ∀ (pc : current c) l, selects (some pc) l →
       ∀ s s', assert_of (some pc) s → F.step_of (some l) s s' → next_assert (some pc) s s' :=
begin
  induction H,
  { intros pc l Hpc, cases pc, },
  { intros pc l' Hpc, cases pc with pc,
    have Heq_l := selects_action_imp_eq _ Hpc, subst l',
    unfold assert_of assert_of', apply a_1 },
  { intros pc l',
    cases pc with pc pc
    ; unfold selects assert_of selects' assert_of'
    ; intros Hpc,
    { apply ih_1 _ _ Hpc },
    { apply ih_2 _ _ Hpc }, },
  { intros pc l',
    cases pc with pc pc
    ; unfold selects assert_of selects' assert_of'
    ; intros Hpc,
    { cases Hpc },
    { apply ih_1 _ _ Hpc },
    { apply ih_2 _ _ Hpc }, },
  { intros pc l',
    cases pc with pc pc
    ; dunfold selects assert_of selects' assert_of'
    ; intros Hpc,
    { cases Hpc },
    { apply ih_1 _ _ Hpc }, },
end

lemma cond_true_of_correct
: ∀ (pc : current c) (H : is_control $ some pc),
       ∀ s, assert_of (some pc) s → condition (some pc) H s → next_assert (some pc) s s :=
begin
  induction H,
  case correct.skip p'
  { intros pc l Hpc, cases pc, },
  case correct.action p' q' l ds Hgrd Htrip
  { intros pc l' s, cases pc with pc, cases l' },
  case correct.seq p' q' r' c₀ c₁ Hc₀ Hc₁
  { intros pc l',
    cases pc with pc pc
    ; unfold selects assert_of selects' assert_of'
    ; intros Hpc,
    { apply ih_1 _ _ Hpc },
    { apply ih_2 _ _ Hpc }, },
  case correct.ite p' t pa pb q' ds c₀ c₁ Hc₀ Hc₁ Hpa Hpb
  { intros pc,
    cases pc with pc pc
    ; dunfold condition assert_of condition' assert_of' next_assert next_assert'
             is_control is_control'
    ; intros Hpc s Hp Hc,
    case current.if_then_else_cond
    { rw if_pos Hc, apply Hpa _ ⟨Hp,Hc⟩, },
    case current.if_then_else_left
    { apply ih_1 _ _ _ Hp Hc, },
    case current.if_then_else_right
    { apply ih_2 _ _ _ Hp Hc, }, },
  case correct.while t p' inv q' ds b c Htp Hntq Hcvr
  { intros pc,
    cases pc with pc pc
    ; dunfold condition assert_of condition' assert_of' next_assert next_assert'
              is_control is_control'
    ; intros Hpc s Hp Hc,
    { rw if_pos Hc, apply Htp _ ⟨Hp,Hc⟩, },
    { apply ih_1 _ _ _ Hp Hc, }, },
end

lemma cond_false_of_correct
: ∀ (pc : current c) (H : is_control (some pc)),
       ∀ s, assert_of (some pc) s → ¬ condition (some pc) H s → next_assert (some pc) s s :=
begin
  induction H,
  case correct.skip p'
  { intros pc l Hpc, cases pc, },
  case correct.action p' q' l ds Hgrd Htrip
  { intros pc l' s, cases pc with pc, cases l' },
  case correct.seq p' q' r' c₀ c₁ Hc₀ Hc₁
  { intros pc l',
    cases pc with pc pc
    ; unfold selects assert_of selects' assert_of'
    ; intros Hpc,
    { apply ih_1 _ _ Hpc },
    { apply ih_2 _ _ Hpc }, },
  case correct.ite p' t pa pb q' ds c₀ c₁ Hc₀ Hc₁ Hpa Hpb
  { intros pc,
    cases pc with pc pc
    ; unfold condition assert_of condition' assert_of' next_assert next_assert'
             is_control is_control'
    ; intros Hpc s Hp Hc,
    case current.if_then_else_cond
    { rw if_neg Hc, apply Hpb _ ⟨Hp,Hc⟩, },
    case current.if_then_else_left
    { apply ih_1 _ _ _ Hp Hc, },
    case current.if_then_else_right
    { apply ih_2 _ _ _ Hp Hc, }, },
  case correct.while t p' inv q' ds b c Htp Hntq Hcvr
  { intros pc,
    cases pc with pc pc
    ; unfold condition assert_of condition' assert_of' next_assert next_assert'
             is_control is_control'
    ; intros Hpc s Hp Hc,
    { rw if_neg Hc, apply Hntq _ ⟨Hp,Hc⟩, },
    { apply ih_1 _ _ _ Hp Hc, }, },
end

lemma state_correctness_none
: state_correctness c none :=
begin
  apply state_correctness.mk,
  { intros l Hl, cases Hl },
  { intros l Hl, cases Hl },
  { intros H', unfold is_control at H', cases H', },
  { intros H', unfold is_control at H', cases H', },
end

lemma syntactic_imp_state_correctness (pc : option $ current c)
: state_correctness c pc :=
begin
  cases pc with pc,
  { apply state_correctness_none _ H },
  apply state_correctness.mk,
  { apply enabled_of_correct _ H },
  { apply correct_of_correct _ H },
  { apply cond_true_of_correct _ H },
  { apply cond_false_of_correct _ H },
end

end

end local_correctness
