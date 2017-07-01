
import unity.logic
import unity.predicate
import unity.temporal

namespace unity.refinement

open unity
open temporal
open predicate

universe variables u u'

variables {α β : Type u}
variables {σ : Type u'}

def refined (s s' : α) [system_sem α] : Prop :=
system_sem.ex s' ⟹ system_sem.ex s

infix ` ⊑ `:80 := refined

def data_ref [system_sem α] [system_sem β]
    (s : α)  (f : unity.state α  → σ)
    (s' : β) (g : unity.state β  → σ) : Prop :=
∀ τ : stream (unity.state β), system_sem.ex s' τ
→ ∃ τ', system_sem.ex s τ' ∧ (g ∘ τ) = (f ∘ τ')


end unity.refinement
