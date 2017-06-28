import unity.predicate
import unity.code.syntax

universe variables u v

open nat predicate

section

parameters (σ : Type) (lbl : Type)

@[reducible]
private def pred := σ → Prop

parameters {σ}

@[reducible]
private def code := @code σ lbl

lemma assert_of_first {p q} {c : code p q}
: assert_of (first c) = p :=
begin
  induction c
  ; try { refl },
  { unfold first,
    destruct first a,
    { intro h,
      simp [h],
      destruct first a_1,
      { intro h',
        simp [h'], unfold assert_of,
        simp [h'] at ih_2, unfold assert_of at ih_2,
        simp [h] at ih_1, unfold assert_of at ih_1,
        subst r, subst q_1 },
      { intros x h', simp [h'],
        unfold assert_of assert_of',
        rw h at ih_1, rw h' at ih_2,
        unfold assert_of at ih_1 ih_2,
        subst p_1, rw ih_2, } },
    { intros x h,
      simp [h],
      unfold assert_of assert_of',
      rw h at ih_1, unfold assert_of at ih_1,
      rw ih_1 }, }
end

lemma first_eq_none_imp_eq {p q : pred} {c : code p q}
: first c = none → p = q :=
begin
  induction c ; unfold first,
  { simp },
  { contradiction, },
  { destruct first a,
    { intro h', simp [h'],
      intro h'', rw [ih_1 h',ih_2 h''], },
    { intros pc h,
      simp [h], contradiction }, },
  { contradiction },
  { contradiction },
end

local attribute [instance] classical.prop_decidable

lemma assert_of_next {p q : pred} {c : code p q} (pc : option (current c)) (s : σ)
: assert_of (next s pc) = next_assert pc s :=
begin
  cases pc with pc,
  { refl },
  unfold next next_assert,
  induction pc
  ; try { refl }
  ; unfold next' next_assert',
  { rw -ih_1,
    cases next' s a,
    destruct first c₁,
    { intros h₀,
      simp [h₀],
      unfold assert_of,
      cases c₁ ; try { refl }
      ; unfold first at h₀
      ; try { contradiction },
      { simp at h₀,
        simp [first_eq_none_imp_eq h₀.left,first_eq_none_imp_eq  h₀.right] }, },
    { intros pc h₀,
      simp,
      rw [h₀,fmap_some],
      unfold assert_of assert_of',
      change assert_of (some pc) = _,
      rw [-h₀,assert_of_first] },
    { simp, refl } },
  { rw -ih_1,
    cases next' s a ; refl },
  { cases classical.em (t s) with h h,
    { rw [if_pos h,if_pos h],
      destruct first c₀,
      { intros h, simp [h], have h := first_eq_none_imp_eq h,
        unfold assert_of, subst pa },
      { intros pc h, simp [h],
        unfold assert_of assert_of',
        change assert_of (some pc) = _,
        rw [-h,assert_of_first], }, },
    { rw [if_neg h,if_neg h],
      destruct first c₁,
      { intros h, simp [h],
        have h := first_eq_none_imp_eq h,
        unfold assert_of, subst pb },
      { intros pc h, simp [h],
        unfold assert_of assert_of',
        change assert_of (some pc) = _,
        rw [-h,assert_of_first], }, }, },
  { rw -ih_1, clear ih_1,
    cases next' s a with pc ; simp,
    { refl },
    { unfold assert_of assert_of', refl }, },
  { rw -ih_1, clear ih_1,
    cases next' s a with pc ; simp,
    { refl },
    { unfold assert_of assert_of', refl }, },
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
      rw [-h',assert_of_first], },
    { intros h',
      rw [if_neg h,if_neg h], refl },
    { intros pc h',
      rw [if_neg h,if_neg h], refl }, },
  { rw -ih_1, clear ih_1,
    destruct next' s a,
    { intros h',
      simp [h'], refl },
    { intros pc h',
      simp [h'], refl }, },
end

end
