import core.connectives

namespace clfrags
    namespace hilbert
        namespace wr
            namespace or
                axiom ρ₁ : Π {p q : Prop}, p → or p q
                axiom ρ₂ : Π {p : Prop}, or p p → p
                axiom ρ₃ : Π {p q : Prop}, or p q → or q p
                axiom ρ₄ : Π {p q r : Prop}, or p (or q r) → or (or p q) r
            end or 
        end wr
    end hilbert
end clfrags
