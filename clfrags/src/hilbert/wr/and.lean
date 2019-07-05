import core.connectives

namespace clfrags
    namespace hilbert
        namespace wr
            namespace and
                axiom ρ₁ : Π {p q : Prop}, p → q → and p q
                axiom ρ₂ : Π {p q : Prop}, and p q → p
                axiom ρ₃ : Π {p q : Prop}, and p q → q
            end and
        end wr
    end hilbert
end clfrags
