

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

def p_not {α} (p : pred' α) : pred' α
:= λx, ¬ p x

infixl ` || ` := p_or
infixl ` && ` := p_and
infixl ` ⟶ `:60 := p_impl

notation `~`:1 x := p_not x

end predicate
