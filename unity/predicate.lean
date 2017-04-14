

namespace predicate

universe variables u u'

variables {α β : Type u}

@[reducible]
def pred' α := α → Prop

def lifted₀ : Prop → pred' α := λ p _, p
def lifted₁ (op : Prop → Prop) : pred' α → pred' α :=
λ p i, op (p i)
def lifted₂ (op : Prop → Prop → Prop) (p q : pred' α) : pred' α :=
λ i, op (p i) (q i)

def ew (p : pred' α) : Prop :=
∀ i, p i

def False : pred' α := lifted₀ false
def True : pred' α := lifted₀ true

def p_or (p₀ p₁ : pred' α) : pred' α
:= lifted₂ or p₀ p₁

@[simp]
lemma p_or_to_fun (p₀ p₁ : pred' α) (x : α)
: p_or p₀ p₁ x ↔ p₀ x ∨ p₁ x := by refl

def p_and (p₀ p₁ : pred' α) : pred' α
:= lifted₂ and p₀ p₁

@[simp]
lemma p_and_to_fun (p₀ p₁ : pred' α) (x : α)
: p_and p₀ p₁ x ↔ p₀ x ∧ p₁ x := by refl

def p_impl (p₀ p₁ : pred' α) : pred' α
:= lifted₂ implies p₀ p₁

@[simp]
lemma p_impl_to_fun (p₀ p₁ : pred' α) (x : α)
: p_impl p₀ p₁ x ↔ (p₀ x → p₁ x) := by refl


def p_entails (p₀ p₁ : pred' α) : Prop
:= ew (p_impl p₀ p₁)

lemma p_entails_of_fun (p₀ p₁ : pred' α) (x : β)
: p_entails p₀ p₁ ↔ ∀ x, p₀ x → p₁ x := by refl


def p_not (p : pred' α) : pred' α
:= lifted₁ not p

@[simp]
lemma p_not_to_fun (p₀ : pred' α) (x : α)
: p_not p₀ x ↔ ¬ p₀ x := by refl


@[simp]
lemma False_eq_false (τ : β) : False τ = false := rfl
@[simp]
lemma True_eq_true (τ : β) : True τ = true := rfl

infixl ` || ` := p_or
infixl ` && ` := p_and
infixr ` ⟶ `:60 := p_impl
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
