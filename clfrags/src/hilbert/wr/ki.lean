import core.connectives

namespace clfrags
    namespace hilbert
        namespace wr
            namespace ki
                axiom ki₁ : Π {a b c : Prop}, b → ki a b c → c
                axiom ki₂ : Π {a b c : Prop}, a → ki a b (ki a c b)
                axiom ki₃ : Π {a b c d e f : Prop}, 
                    ki b f a → 
                    ki b f (ki a (ki a c (ki a d e)) (ki a (ki a c d) (ki a c e)))
                axiom ki₄ : Π {a b c d e : Prop}, 
                    ki b e a →
                    ki b e (ki a (ki a (ki a c d) c) c)
                axiom ki₅ : Π {a b c d : Prop}, ki a b (ki a c d) → ki a (ki b b c) d
                axiom ki₆ : Π {a b c d : Prop}, ki a (ki b b c) d → ki a b (ki a c d)    
                axiom ki₇ : Π {a b c d e : Prop}, ki a e b → ki a e (ki a c d) → ki a e (ki b c d)
                axiom ki₈ : Π {a b c d e : Prop}, ki a e (ki b c d) → ki a e b
                axiom ki₉ : Π {a b c d e : Prop}, ki a e (ki b c d) → ki a e (ki a c d)
            end ki
        end wr
    end hilbert
end clfrags
