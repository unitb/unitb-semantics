
import unitb.logic
import unitb.semantics.temporal

import util.predicate

namespace unitb.refinement

open unitb
open temporal
open predicate

universe variables u u'

variables {α β : Type u}
variables {σ : Type u'}

def refined (s s' : α) [system_sem α] : Prop :=
system_sem.ex s' ⟹ system_sem.ex s

infix ` ⊑ `:80 := refined

def data_ref [system_sem α] [system_sem β]
    (s : α)  (f : unitb.state α  → σ)
    (s' : β) (g : unitb.state β  → σ) : Prop :=
∀ τ : stream (unitb.state β), system_sem.ex s' τ
→ ∃ τ', system_sem.ex s τ' ∧ (g ∘ τ) = (f ∘ τ')


end unitb.refinement
