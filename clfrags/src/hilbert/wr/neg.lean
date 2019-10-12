import core.connectives

namespace clfrags
    namespace hilbert
        namespace wr
            namespace neg
                axiom n₁ : Π {a b : Prop}, a → neg a → b
                axiom n₂ : Π {a : Prop}, a → neg (neg a)
                axiom n₃ : Π {a : Prop}, neg (neg a) → a
            end neg
        end wr
    end hilbert
end clfrags
