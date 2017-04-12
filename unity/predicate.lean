

namespace predicate

universe variable u

variables {α β : Type u}

def pred' α := α → Prop

def False : pred' α := λ_, false
def True : pred' α := λ_, true

@[reducible]
def p_or (p₀ p₁ : pred' α) : pred' α
:= λx, p₀ x ∨ p₁ x

@[reducible]
def p_and (p₀ p₁ : pred' α) : pred' α
:= λx, p₀ x ∧ p₁ x

def p_impl (p₀ p₁ : pred' α) : pred' α
:= λx, p₀ x → p₁ x

def p_entails (p₀ p₁ : pred' α) : Prop
:= ∀ x, p₀ x → p₁ x

@[reducible]
def p_not (p : pred' α) : pred' α
:= λx, ¬ p x

@[simp]
lemma False_eq_false (τ : β) : False τ = false := rfl
@[simp]
lemma True_eq_true (τ : β) : True τ = true := rfl

def ew (p : β → Prop) : Prop :=
∀ x, p x

infixl ` || ` := p_or
infixl ` && ` := p_and
infixl ` ⟶ `:60 := p_impl
infix ` ⟹ `:60 := p_entails
notation `⦃ `:max act ` ⦄` := ew act

notation `~`:75 x := p_not x

lemma p_imp_p_imp_p_imp {p p' q q' : pred' α} {τ}
  (hp : (p' ⟶ p) τ)
  (hq : (q ⟶ q') τ)
: ( p ⟶ q ) τ → ( p' ⟶ q' ) τ :=
take hpq, hq ∘ hpq ∘ hp

lemma p_imp_p_imp_p_imp_left {p p' q : pred' α} {τ}
  (hp : (p' ⟶ p) τ)
: ( p ⟶ q ) τ → ( p' ⟶ q ) τ :=
p_imp_p_imp_p_imp hp id

lemma p_imp_p_imp_p_imp_right {p q q' : pred' α} {τ}
  (hq : (q ⟶ q') τ)
: ( p ⟶ q ) τ → ( p ⟶ q' ) τ :=
p_imp_p_imp_p_imp id hq

lemma p_not_eq_not (p : pred' β) (τ) : ¬ p τ ↔ (~p) τ :=
by refl

end predicate
