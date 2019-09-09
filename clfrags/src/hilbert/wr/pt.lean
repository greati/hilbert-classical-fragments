import core.connectives

namespace clfrags
    namespace hilbert
        namespace wr
            namespace pt
                axiom pt₁ : Π {a b c : Prop}, a → b → c → pt a b c
                axiom pt₂ : Π {a b c : Prop}, pt a b c → pt b a c
                axiom pt₃ : Π {a b c : Prop}, pt a b c → pt a c b
                axiom pt₄ : Π {a b : Prop}, a → pt a b b
                axiom pt₅ : Π {a b : Prop}, pt a b b → a
                axiom pt₆ : Π {a b c d e : Prop}, pt a b (pt c d e) → pt (pt a b c) d e
            end pt
        end wr
    end hilbert
end clfrags
