
import data.set
import unitb.code.syntax

section

open set

parameters σ : Type
parameters (F : nondet.program σ)

@[reducible]
private def pred := σ → Prop

@[reducible]
private def lbl := F.lbl

@[reducible]
private def rel := σ → σ → Prop

parameter {σ}

def hoare (p : pred) (act : rel) (q : pred) :=
∀ s s', p s → act s s' → q s'

def covered : ∀ {p q : pred}, code lbl p q → set lbl
  | .(p) .(p) (code.skip p) := ∅
  | ._ ._ (code.action p q ds l) := ds ∪ { l }
  | ._ ._ (@code.seq ._ ._ _ _ _ c₀ c₁) := covered c₀ ∪ covered c₁
  | ._ ._ (@code.if_then_else ._ ._ _ _ _ _ ds _ c₀ c₁) := ds ∪ (covered c₀ ∩ covered c₁)
  | ._ ._ (@code.while ._ ._ _ _ _ ds _ b) := ds

inductive correct : ∀ {p q : pred}, code lbl p q → Prop
  | skip : ∀ (p : pred),
        correct (code.skip p)
  | action : ∀ (p q : pred) (l : lbl) (ds : set lbl),
        (p ⟹ F.guard (some l))
      → hoare p (F.step_of $ some l) q
      → correct (code.action p q ds l)
  | seq : ∀ (p q r : pred) (c₀ : code lbl p q) (c₁ : code lbl q r),
        correct c₀ → correct c₁
      → correct (code.seq c₀ c₁)
  | ite : ∀ (p t pa pb q : pred)  (ds : set lbl) (c₀ : code lbl pa q) (c₁ : code lbl pb q),
        correct c₀ → correct c₁
      → (p && t ⟹ pa)
      → (p && -t ⟹ pb)
      → correct (if_then_else p ds t c₀ c₁)
  | while : ∀ (t p inv q : pred) (ds : set lbl) (b : code lbl p inv),
        correct b
      → (inv && t ⟹ p)
      → (inv && -t ⟹ q)
      → covered b = univ
      → correct (while q ds t b)

end
