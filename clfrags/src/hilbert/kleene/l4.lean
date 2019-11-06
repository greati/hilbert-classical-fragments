
namespace hidden

constant and : Prop → Prop → Prop
constant or : Prop → Prop → Prop
constant imp : Prop → Prop → Prop
constant neg : Prop → Prop

notation a `or` b := or a b
notation a `imp` b := imp a b
notation a `and` b := and a b

axiom cl₁ : ∀ {a b : Prop}, a → (a imp b) → b
axiom cl₂ : ∀ {a b : Prop}, a imp (b imp a)
axiom cl₃ : ∀ {a b c : Prop}, (a imp (b imp c)) imp ((a imp b) imp (a imp c))
axiom cl₄ : ∀ {a b : Prop}, (a and b) imp a
axiom cl₅ : ∀ {a b : Prop}, (a and b) imp b
axiom cl₆ : ∀ {a b : Prop}, a imp (b imp (a and b))
axiom cl₇ : ∀ {a b : Prop}, a imp (a or b)
axiom cl₈ : ∀ {a b : Prop}, b imp (a or b)
axiom cl₉ : ∀ {a b c : Prop}, (a imp c) imp ((b imp c) imp ((a or b) imp c))
axiom cl₁₀ : ∀ {a b : Prop}, (a imp b) imp ((a imp (neg b)) imp (neg a))
axiom cl₁₁ : ∀ {a : Prop}, (neg (neg a)) imp a

example {a : Prop} : a imp a := 
    have h₁ : (a imp ((a imp a) imp a)) imp ((a imp (a imp a)) imp (a imp a)), from cl₃,
    have h₂ : a imp ((a imp a) imp a), from cl₂,
    have h₃ : ((a imp (a imp a)) imp (a imp a)), from cl₁ h₂ h₁,
    have h₄ : a imp (a imp a), from cl₂,
    show a imp a, from cl₁ h₄ h₃

theorem cl₁₂ {a b c : Prop} (h₁ : a imp b) (h₂ : b imp c) : a imp c := 
    have h₃ : (a imp (b imp c)) imp ((a imp b) imp (a imp c)), from cl₃,
    have h₄ : (b imp c) imp (a imp (b imp c)), from cl₂,
    have h₅ : a imp (b imp c), from cl₁ h₂ h₄,
    have h₆ : (a imp b) imp (a imp c), from cl₁ h₅ h₃,
    show a imp c, from cl₁ h₁ h₆

end hidden
