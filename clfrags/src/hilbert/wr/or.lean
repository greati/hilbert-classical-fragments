import core.connectives

namespace clfrags
    namespace hilbert
        namespace wr
            namespace or
                axiom d₁ : Π {a b : Prop}, a → or a b
                axiom d₂ : Π {a : Prop}, or a a → a
                axiom d₃ : Π {a b : Prop}, or a b → or b a
                axiom d₄ : Π {a b c : Prop}, or a (or b c) → or (or a b) c
            end or 
        end wr
    end hilbert
end clfrags
