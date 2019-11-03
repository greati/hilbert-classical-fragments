import core.connectives

namespace clfrags
    namespace hilbert
        namespace wr
            namespace ad
                axiom ad₁ : Π {a b c : Prop}, c → ad a b c → a
                axiom ad₂ : Π {a b c : Prop}, a → ad (ad c a b) a c
                axiom ad₃ : Π {a b c d e f : Prop}, ad a b c → ad (ad (ad (ad f a d) a (ad e a d)) a (ad (ad f a e) a d)) b c
                axiom ad₄ : Π {a b c d e : Prop}, ad a b c → ad (ad d a (ad d a (ad e a d))) b c
                axiom ad₅ : Π {a b c : Prop}, ad a b c → ad b a b
                axiom ad₆ : Π {a b c : Prop}, a → ad a b c
                axiom ad₇ : Π {a b c d : Prop}, ad (ad c d c) a b → ad (ad c a b) (ad d a b) (ad c a b)
                axiom ad₈ : Π {a b c d : Prop}, ad (ad c a b) (ad d a b) (ad c a b) → ad (ad c d c) a b 
                --axiom ad₉ : Π {a b c d e : Prop}, ad b d e → ad c a b → ad e d c
                axiom ad₉ : Π {a b c d e : Prop}, ad a b c → ad d e a → ad d b c
                axiom ad₁₀ : Π {a b c d e : Prop}, ad (ad e d c) a b → ad (ad e a b) (ad e d c) (ad e a b)
                axiom ad₁₁ : Π {a b c d e : Prop}, ad (ad e a b) (ad e d c) (ad e a b) → ad (ad e d c) a b 
                axiom ad₁₂ : Π {a : Prop}, ad a a a → a
                axiom ad₁₃ : Π {a b : Prop}, ad a b a → ad b a b
                axiom ad₁₄ : Π {a b c : Prop}, ad a (ad b c b) a → ad (ad a b a) c (ad a b a)
                axiom ad₁₅ : Π {a b c d : Prop}, ad d c d → ad d (ad a b c) d → ad d a d
                axiom ad₁₆ : Π {a b c d : Prop}, ad d a d → ad d (ad (ad c a b) a c) d
                axiom ad₁₇ : Π {a b c d e f g : Prop}, ad g (ad a b c) g 
                    → ad g (ad (ad (ad (ad f a d) a (ad e a d)) a (ad (ad f a e) a d)) b c) g
                axiom ad₁₈ : Π {a b c d e f : Prop}, ad f (ad a b c) f → ad f (ad (ad d a (ad d a (ad e a d))) b c) f
                axiom ad₁₉ : Π {a b c d : Prop}, ad d (ad a b c) d → ad d (ad b a b) d
                axiom ad₂₀ : Π {a b c d : Prop}, ad d a d → ad d (ad a b c) d
                axiom ad₂₁ : Π {a b c d e : Prop}, ad e (ad (ad c d c) a b) e → ad e (ad (ad c a b) (ad d a b) (ad c a b)) e
                axiom ad₂₂ : Π {a b c d e : Prop}, ad e (ad (ad c a b) (ad d a b) (ad c a b)) e → ad e (ad (ad c d c) a b) e
                axiom ad₂₃ : Π {a b c d e f : Prop}, ad f (ad b d e) f → ad f (ad c a b) f → ad f (ad e d c) f
                axiom ad₂₄ : Π {a b c d e f : Prop}, ad f (ad (ad e d c) a b) f → ad f (ad (ad e a b) (ad e d c) (ad e a b)) f
                axiom ad₂₅ : Π {a b c d e f : Prop}, ad f (ad (ad e a b) (ad e d c) (ad e a b)) f → ad f (ad (ad e d c) a b) f

                notation a `or` b := ad a b a

                constant M₂ : ∀ {a b c : Prop}, (a → b) → (c → a → b)
                constant R : ∀ {a : Prop}, a → a
                constant T₁ : ∀ {a b c : Prop}, (a → b) → (b → c) → (a → c)
                constant δ_or₁ : ∀ {a b c : Prop}, (a → c) → (b → c) → ((a or b) → c)
                constant T₂ : ∀ {a b c d : Prop}, (d → a → b) → (d → b → c) → (d → a → c)
                constant δ_or₂ : ∀ {a b c d : Prop}, (d → a → c) → (d → b → c) → (d → (a or b) → c)

            end ad
        end wr
    end hilbert
end clfrags
