import core.connectives

namespace clfrags
    namespace hilbert
        namespace wr
            namespace and
                axiom c₁ : Π {a b : Prop}, a → b → and a b
                axiom c₂ : Π {a b : Prop}, and a b → a
                axiom c₃ : Π {a b : Prop}, and a b → b
            end and
        end wr
    end hilbert
end clfrags
