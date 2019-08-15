import core.connectives

namespace clfrags
    namespace hilbert
        namespace wr
            namespace ka
                axiom ka₁ : Π {a b c : Prop}, a → b → ka a b c
                axiom ka₂ : Π {a b : Prop}, ka a b b → b
                axiom ka₃ : Π {a b c : Prop}, ka a b c → ka a c b
                axiom ka₄ : Π {a b c d : Prop}, ka a b (ka a c d) → ka a (ka a b c) d
                axiom ka₅ : Π {a b c d e : Prop}, ka a b c → ka a b (ka a d e) → ka a b (ka c d e)
                axiom ka₆ : Π {a b c d e : Prop}, ka a c (ka b d e) → ka a c b
                axiom ka₇ : Π {a b c d e : Prop}, ka a c (ka b d e) → ka a c (ka a d e)
            end ka
        end wr
    end hilbert
end clfrags
