

namespace predicate

def pred' α := α → Prop

def False {α} : pred' α := λ_, false
def True {α} : pred' α := λ_, true

@[reducible]
def p_or {α} (p₀ p₁ : pred' α) : pred' α
:= λx, p₀ x ∨ p₁ x

@[reducible]
def p_and {α} (p₀ p₁ : pred' α) : pred' α
:= λx, p₀ x ∧ p₁ x

def p_impl {α} (p₀ p₁ : pred' α) : pred' α
:= λx, p₀ x → p₁ x

def p_entails {α} (p₀ p₁ : pred' α) : Prop
:= ∀ x, p₀ x → p₁ x

@[reducible]
def p_not {α} (p : pred' α) : pred' α
:= λx, ¬ p x

@[simp]
lemma False_eq_false {β} (τ : β) : False τ = false := rfl
@[simp]
lemma True_eq_true {β} (τ : β) : True τ = true := rfl

infixl ` || ` := p_or
infixl ` && ` := p_and
infixl ` ⟶ `:60 := p_impl
infix ` ⟹ `:60 := p_entails

notation `~`:75 x := p_not x

lemma p_imp_p_imp_p_imp {α} {p p' q q' : pred' α} {τ}
  (hp : (p' ⟶ p) τ)
  (hq : (q ⟶ q') τ)
: ( p ⟶ q ) τ → ( p' ⟶ q' ) τ :=
take hpq, hq ∘ hpq ∘ hp

lemma p_imp_p_imp_p_imp_left {α} {p p' q : pred' α} {τ}
  (hp : (p' ⟶ p) τ)
: ( p ⟶ q ) τ → ( p' ⟶ q ) τ :=
p_imp_p_imp_p_imp hp id

lemma p_imp_p_imp_p_imp_right {α} {p q q' : pred' α} {τ}
  (hq : (q ⟶ q') τ)
: ( p ⟶ q ) τ → ( p ⟶ q' ) τ :=
p_imp_p_imp_p_imp id hq

end predicate
