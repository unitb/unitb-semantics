
import unitb.logic

import util.predicate

import temporal_logic

namespace unitb.refinement

open unitb
open temporal
open predicate

universe variables u u'

variables {α β : Type u}
variables {σ : Type u'}

def refined (s s' : α) [system_sem α] : Prop :=
∀ σ, system_sem.ex s' σ ⟹ system_sem.ex s σ

infix ` ⊑ `:80 := refined

def data_ref [system_sem α] [system_sem β]
    (s : α)  (f : var (unitb.state α) σ)
    (s' : β) (g : var (unitb.state β) σ) : Prop :=
∀ σ' Γ,
     Γ ⊢ system_sem.ex s' σ' →
     Γ ⊢ ∃∃ σ, system_sem.ex s σ ⋀ (g ! σ') ≃ (f ! σ)

end unitb.refinement
