import core.connectives

namespace clfrags
    namespace hilbert
        namespace wr
            namespace dc
                axiom dc₁ : Π {a b c : Prop}, a → b → dc a b c
                axiom dc₂ : Π {a b : Prop}, dc b a a → a
                axiom dc₃ : Π {a b : Prop}, a → dc b a a
                axiom dc₄ : Π {a b c d e : Prop}, dc d e (dc a b c) → dc e d (dc b a c)
                axiom dc₅ : Π {a b c d e : Prop}, dc d e (dc a b c) → dc e d (dc a c b)
                axiom dc₆ : Π {a b c d e f g : Prop}, 
                    dc f g (dc d e (dc a b c)) → dc f g (dc (dc d e a) (dc d e b) c)
                axiom dc₇ : Π {a b c d e f g : Prop}, 
                    dc f g (dc (dc d e a) (dc d e b) c) → dc f g (dc d e (dc a b c))
            end dc
        end wr
    end hilbert
end clfrags
