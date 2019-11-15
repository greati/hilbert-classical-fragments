import core.connectives

namespace clfrags
    namespace hilbert
        namespace wr
            namespace or
                axiom d₁ : ∀ {a b : Prop}, a → or a b
                axiom d₂ : ∀ {a : Prop}, or a a → a
                axiom d₃ : ∀ {a b : Prop}, or a b → or b a
                axiom d₄ : ∀ {a b c : Prop}, or a (or b c) → or (or a b) c
            end or 
        end wr
    end hilbert
end clfrags
