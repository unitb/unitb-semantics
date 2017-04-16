
import unity.logic
import unity.predicate
import unity.temporal

namespace unity.refinement

open unity
open temporal
open predicate

universe variables u

variables {α : Type u}

def refined (s s' : α) [system_sem α] : Prop :=
system_sem.ex s' ⟹ system_sem.ex s

infix ` ⊑ `:80 := refined

end unity.refinement
