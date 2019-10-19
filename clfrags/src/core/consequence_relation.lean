import data.set
open set

namespace logic

    def reflexivity (R : set Prop → Prop → Prop) :=    
        ∀ α : Prop, R {α} α

    def monotonicity (R : set Prop → Prop → Prop) : Prop :=
        ∀ Γ Δ : set Prop, ∀ α : Prop, Γ ⊆ Δ ∧ R Γ α → R Δ α

    def transitivity (R : set Prop → Prop → Prop) : Prop :=
        ∀ Γ Δ : set Prop, ∀ α : Prop, R (Γ ∪ Δ) α ∧ (∀ β ∈ Δ, R Γ β) → R Γ α
    
    theorem transitivity_single (R : set Prop → Prop → Prop) : Prop :=
        ∀ Γ : set Prop, ∀ α β : Prop, R (Γ ∪ {α}) β ∧ R Γ α → R Γ β

    variables {α β : Prop}
    variables {Γ Δ : set Prop}
    variable R : set Prop → Prop → Prop
    variable {reflCr : reflexivity R}
    variable {monCr : monotonicity R}
    variable {cutCr : transitivity R}

    example (x : Prop) : R {x} x := reflCr x

end logic
