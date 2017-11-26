
import util.category
import util.predicate

open predicate

universe variables u u' v'

namespace unitb

variable {α : Type u}

class lifted_pred (cat : pred' α → pred' α → Sort u')
extends category cat :=
  (imp : ∀ p q, p ⟹ q → cat p q)
  (imp_self_eq_ident : ∀ {p : pred' α}, imp p p (by refl) = ident)
  (imp_comp_imp_eq_imp_trans : ∀ {p q r : pred' α} (h₀ : p ⟹ q) (h₁ : q ⟹ r),
     (imp q r h₁ <<< imp p q h₀) = imp p r (entails_trans _ h₀ h₁))

class finite_disjunctive (cat : pred' α → pred' α → Sort u')
extends lifted_pred cat :=
  (disj : ∀ {p q r : pred' α}, cat p r → cat q r → cat (p ⋁ q) r)
  (comp_over_disj_right : ∀ {p q r r' : pred' α}
                            (Pp : cat p r)
                            (Pq : cat q r)
                            (Pr : cat r r'),
             (Pr <<< disj Pp Pq) = disj (Pr <<< Pp) (Pr <<< Pq))
  (select_left_disj  : ∀ {p q r : pred' α}
                            (Pp : cat p r)
                            (Pq : cat q r),
             (disj Pp Pq <<< imp p _ (p_or_intro_left _ _)) = Pp)
  (disj_imp_imp : ∀ {p q r : pred' α}
                            (Pp : p ⟹ r)
                            (Pq : q ⟹ r),
             disj (imp _ _ Pp) (imp _ _ Pq) =
             imp (p ⋁ q) r (p_or_entails_of_entails Pp Pq))
  (disj_flip : ∀ {p q r : pred' α}
                            (P₀ : cat p r) (P₁ : cat q r),
             disj P₀ P₁ = (disj P₁ P₀ <<< imp _ _ (by rw [p_or_comm])) )

class disjunctive (cat : pred' α → pred' α → Sort u')
extends finite_disjunctive cat :=
  (disj' : ∀ {t : Type} (p : t → pred' α) r : pred' α,
      (∀ x, cat (p x) r) → cat (∃∃ x, p x) r)
  (disj :=
   begin
     intros p q r X Y,
     let f := λ x : bool, if x then p else q,
     have H : p ⋁ q = ∃∃ x, f x,
     { apply mutual_entails,
       apply p_or_entails_of_entails,
       { apply @p_exists_intro _ _ f tt, },
       { apply @p_exists_intro _ _ f ff, },
       apply p_exists_elim,
       intro x, cases x,
       { apply p_or_intro_right },
       { apply p_or_intro_left }, },
     rw H, clear H,
     apply disj',
     apply bool.rec ; revert f
     ; simp
     ; assumption
   end )

export lifted_pred (imp_comp_imp_eq_imp_trans imp_self_eq_ident)
export finite_disjunctive (disj comp_over_disj_right select_left_disj
                           disj_imp_imp disj_flip)
export disjunctive (disj')

section lemmas

parameters {σ : Type u}
parameters (cat : pred' σ → pred' σ → Sort v')
@[reducible]
private def pred := pred' σ

local infix ` ⤇ `:25 := cat
   -- M-x insert-char RET right*arrow
   -- code point: 0x2907
parameters {t : Type}

lemma disj.select_left_disj' [finite_disjunctive cat]
  {p p' q r : pred}
  (H : p' ⟹ p)
  (Pp : cat p r)
  (Pq : cat q r)
: (disj σ Pp Pq <<< lifted_pred.imp _ p' (p ⋁ q)
         (entails_trans p H $ p_or_intro_left _ _)) =
  (Pp <<< lifted_pred.imp _ p' p H) :=
begin
  have h₀ : p' ⟹ p ⋁ q,
  { transitivity p, assumption, apply p_or_intro_left },
  have h₁ := p_or_intro_left p q,
  have H' : lifted_pred.imp cat p' (p ⋁ q) h₀ =
            (lifted_pred.imp cat p (p ⋁ q) h₁ <<< lifted_pred.imp cat p' p H),
  { rw imp_comp_imp_eq_imp_trans },
  rw [H',semigroupoid.assoc,select_left_disj],
end

def select_right_disj [finite_disjunctive cat] {p q r : pred}
  (Pp : cat p r)
  (Pq : cat q r)
: (disj _ Pp Pq <<< lifted_pred.imp cat q _ (p_or_intro_right _ _)) = Pq :=
by rw [disj_flip,← category.assoc,imp_comp_imp_eq_imp_trans,select_left_disj]

def monotonicity [lifted_pred cat]
  {p p' q q'}
  (hp : p' ⟹ p)
  (hq : q  ⟹ q')
  (hcat : cat p q)
: cat p' q' :=
begin
  apply has_comp.comp,
  apply lifted_pred.imp cat _ _ hq,
  apply has_comp.comp _ hcat,
  apply lifted_pred.imp cat _ _ hp,
end

def antimono_left [lifted_pred cat]
  (p) {p' q}
  (h : p' ⟹ p)
: cat p q → cat p' q :=
monotonicity h (by refl)

def lifted_pred.weaken [lifted_pred cat]
  {p q}
  (h : p ⟹ q)
: cat p q :=
lifted_pred.imp cat p q h

def lifted_pred.mono_right [lifted_pred cat]
  {p} (q) {q'}
  (h : q  ⟹ q')
: cat p q → cat p q' :=
monotonicity (by refl) h

def disj_rng [category cat] [disjunctive cat]
  {p : t → pred} {q : pred} {r : t → Prop}
  (h : ∀ i, r i → p i ⤇ q)
: (∃∃ i, (λ _, r i) ⋀ p i) ⤇ q :=
begin
  have h' : (∃∃ (i : t), (λ _, r i) ⋀ p i) =
              (∃∃ (i : { x : t // r x }), p i),
  { apply funext, intro x,
    rw ← iff_eq_eq, split,
    { intro h, cases h with j h,
      exact ⟨⟨j, h^.left⟩, h^.right⟩ },
    { intro h₀, cases h₀ with j h₀, cases j with j h₁ h₂,
      exact ⟨j,h₁,h₀⟩, } },
  rw h',
  apply disj',
  intro i,
  apply h,
  apply i^.property,
end

def gen_disj [finite_disjunctive cat]
  {p₀ p₁ q₀ q₁ : pred' σ}
  (P₀ : p₀ ⤇ q₀)
  (P₁ : p₁ ⤇ q₁)
: p₀ ⋁ p₁ ⤇ q₀ ⋁ q₁ :=
begin
  apply disj,
  { apply lifted_pred.mono_right cat _ _ P₀,
    apply p_or_intro_left },
  { apply lifted_pred.mono_right cat _ _ P₁,
    apply p_or_intro_right },
end

def gen_disj' [disjunctive cat]
  {t : Type} {p q : t → pred' σ}
  (P : ∀ x, p x ⤇ q x)
: (∃∃ x, p x) ⤇ (∃∃ x, q x) :=
begin
  have P' : Π (x : t), cat (p x) (∃∃ (x : t), q x),
  { intro x,
    apply lifted_pred.mono_right cat _ _ (P x),
    apply p_exists_intro },
  apply disj' p _ P',
end

def cancellation'
  [lifted_pred cat] [finite_disjunctive cat]
  {p : pred' σ} (q : pred' σ)
  {r b : pred' σ}
  (P₀ : p ⤇ q ⋁ b)
  (P₁ : q ⤇ r)
: p ⤇ r ⋁ b :=
begin
  apply has_comp.comp _ _ P₀,
  apply gen_disj _ P₁ (ident _),
end

def cancellation
  [lifted_pred cat] [finite_disjunctive cat]
  {p : pred' σ} (q : pred' σ)
  {r b : pred' σ}
  (P₀ : p ⤇ q ⋁ b)
  (P₁ : q ⤇ r ⋁ b)
: p ⤇ r ⋁ b :=
begin
  apply has_comp.comp _ _ P₀,
  apply finite_disjunctive.disj _ P₁,
  apply lifted_pred.imp,
  apply p_or_intro_right,
end

-- set_option pp.implicit true

lemma cancellation_assoc
  [finite_disjunctive cat]
  {p q : pred' σ}
  {r r' b : pred' σ}
  (P₀ : p ⤇ q ⋁ b)
  (P₁ : q ⤇ r ⋁ b)
  (P₂ : r ⤇ r' ⋁ b)
:   cancellation _ (cancellation _ P₀ P₁) P₂
  = cancellation _ P₀ (cancellation _ P₁ P₂)  :=
begin
  unfold cancellation,
  rw [semigroupoid.assoc, comp_over_disj_right, select_right_disj],
end

theorem induction [disjunctive cat]
  {β : Type} {lt' : β → β → Prop}
  (wf : well_founded lt')
  (V : σ → β)
  {p q : pred}
  (P : ∀ v, p ⋀ (eq v ∘ V)  ⤇  p ⋀ (flip lt' v ∘ V) ⋁ q)
: p ⤇ q :=
begin
  let lt := flip lt',
  have P' : (∃∃ v, p ⋀ eq v ∘ V)  ⤇ q,
  { apply disjunctive.disj', intro i,
    let PP := λ i, p ⋀ eq i ∘ V  ⤇  q,
    change PP i,
    apply @well_founded.recursion _ lt' wf PP,
    intros j IH,
    change _ ⤇ _,
    apply lifted_pred.mono_right cat (q ⋁ q),
    { simp [p_or_self] },
    apply cancellation' _ (p ⋀ lt j ∘ V) (P _),
    have h' : (p ⋀ lt j ∘ V) = (λ s, ∃v, lt j v ∧ p s ∧ v = V s),
    { apply funext,
      intro x,
      rw ← iff_eq_eq, split,
      { intros H₀, cases H₀ with H₀ H₁,
        existsi V x,
        repeat { split, assumption }, refl },
      { intro h, apply exists.elim h,
        intros s h', cases h' with h₀ h₁, cases h₁, subst s,
        exact ⟨left,h₀⟩ }, },
    rw h', clear h',
    apply disj_rng,
    apply IH, },
  { have h : (∃∃ (v : β), p ⋀ eq v ∘ V) = p,
    { apply funext,
      intro x, unfold function.comp,
      simp, },
    rw h at P',
    apply P' }
end

end lemmas

end unitb
