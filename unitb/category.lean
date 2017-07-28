
import util.category
import util.predicate

open predicate

universe variables u u' v'

namespace unitb

class finite_disjunctive {α : Type u} (cat : pred' α → pred' α → Sort u')
extends category cat :=
  (disj : ∀ p q r : pred' α, cat p r → cat q r → cat (p || q) r)

class disjunctive {α : Type u} (cat : pred' α → pred' α → Sort u')
extends category cat :=
  (disj : ∀ {t : Type} (p : t → pred' α) r : pred' α, (∀ x, cat (p x) r) → cat (∃∃ x, p x) r)

instance finite_of_disjunctive {α : Type u} (cat : pred' α → pred' α → Sort u')
[_inst : disjunctive cat]
: finite_disjunctive cat :=
 { (_inst.to_category : category cat) with
   disj :=
   begin
     intros p q r X Y,
     let f := λ x : bool, if x then p else q,
     have H : p || q = ∃∃ x, f x,
     { apply mutual_entails,
       apply p_or_entails_of_entails,
       { apply @p_exists_intro _ _ f tt, },
       { apply @p_exists_intro _ _ f false, },
       apply p_exists_elim,
       intro x, cases x,
       { apply p_or_intro_right },
       { apply p_or_intro_left }, },
     rw H, clear H,
     apply _inst.disj,
     apply bool.rec ; revert f
     ; simp
     ; assumption
   end }

class monotonic {α : Type u} (cat : pred' α → pred' α → Sort u')
extends category cat :=
  (mono : ∀ {p p' q q'},
                 p' ⟹ p
               → q  ⟹ q'
               → cat p q → cat p' q')

class cancellative {α : Type u} (cat : pred' α → pred' α → Sort u')
extends category cat :=
  (cancel : ∀ {p} (q) {r b}, cat p (q || b) → cat q r → cat p (r || b))

section lemmas

parameters {α : Type u}
parameters {cat : pred' α → pred' α → Sort v'}
-- def cat' := cat

local infix ` ⤇ `:25 := cat
   -- M-x insert-char RET right*arrow
   -- code point: 0x2907
parameters {t : Type}

lemma monotonic.antimono_left [monotonic cat]
  (p) {p' q}
  (h : p' ⟹ p)
: cat p q → cat p' q :=
monotonic.mono h (by refl)

lemma monotonic.mono_right [monotonic cat]
  {p} (q) {q'}
  (h : q  ⟹ q')
: cat p q → cat p q' :=
monotonic.mono (by refl) h

lemma disjunctive.disj_rng [disjunctive cat]
  {p : t → pred' α} {q : pred' α} {r : t → Prop}
  (h : ∀ i, r i → p i ⤇ q)
: (∃∃ i, (λ _, r i) && p i) ⤇ q :=
begin
  have h' : (∃∃ (i : t), (λ _, r i) && p i) =
              (∃∃ (i : { x : t // r x }), p i),
  { apply funext, intro x,
    rw ← iff_eq_eq, split,
    { intro h, cases h with j h,
      exact ⟨⟨j, h^.left⟩, h^.right⟩ },
    { intro h₀, cases h₀ with j h₀, cases j with j h₁ h₂,
      exact ⟨j,h₁,h₀⟩, } },
  rw h',
  apply disjunctive.disj,
  intro i,
  apply h,
  apply i^.property,
end

theorem induction [disjunctive cat] [cancellative cat] [monotonic cat]
  {β : Type} {lt' : β → β → Prop}
  (wf : well_founded lt')
  (V : α → β)
  {p q : pred' α}
  (P : ∀ v, p && (eq v ∘ V)  ⤇  p && (flip lt' v ∘ V) || q)
: p ⤇ q :=
begin
  let lt := flip lt',
  have P' : (∃∃ v, p && eq v ∘ V)  ⤇ q,
  { apply disjunctive.disj, intro i,
    let PP := λ i, p && eq i ∘ V  ⤇  q,
    change PP i,
    apply @well_founded.recursion _ lt' wf PP,
    intros j IH,
    change _ ⤇ _,
    apply monotonic.mono_right (q || q),
    { intro, simp, exact id },
    apply cancellative.cancel (p && lt j ∘ V) (P _),
    have h' : (p && lt j ∘ V) = (λ s, ∃v, lt j v ∧ p s ∧ v = V s),
    { apply funext,
      intro x,
      rw ← iff_eq_eq, split,
      { intros H₀, cases H₀ with H₀ H₁,
        existsi V x,
        repeat { split, assumption }, refl },
      { intro h, apply exists.elim h,
        intros s h', cases h' with h₀ h₁, cases h₁, subst s,
        exact ⟨a,h₀⟩ }, },
    rw h', clear h',
    apply disjunctive.disj_rng,
    apply IH,
    apply_instance },
  { have h : (∃∃ (v : β), p && eq v ∘ V) = p,
    { apply funext,
      intro x, unfold function.comp,
      simp, rw [exists_one_point_right (V x) _], simp,
      { intro, apply and.right }, },
    rw h at P',
    apply P' }
end

end lemmas

end unitb
