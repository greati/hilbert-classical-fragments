import hilbert.wr.ka

namespace clfrags
    namespace hilbert
        namespace wr
            namespace ka

                theorem ka₀ {a b c : Prop} (h₁ : ka a b c) : a :=
                    have h₃ : ka (ka a b c) (ka a b c) a, from ka₁ h₁ h₁,
                    have h₄ : ka (ka a b c) a (ka a b c), from ka₃ h₃,
                    have h₅ : ka (ka a b c) a a, from ka₆ h₄,
                    show a, from ka₂ h₅

                theorem ka₄' {a b c d : Prop} (h₁ : ka d (ka d c a) b) : ka d c (ka d a b) :=
                    have h₂ : ka d b (ka d c a), from ka₃ h₁,
                    have h₃ : ka d (ka d b c) a, from ka₄ h₂,
                    have h₄ : ka d a (ka d b c), from ka₃ h₃,
                    have h₅ : ka d (ka d a b) c, from ka₄ h₄,
                    show ka d c (ka d a b), from ka₃ h₅

                theorem ka₁_ast {a b c d e : Prop} (h₁ : ka e d a) (h₂ : ka e d b) : ka e d (ka a b c) :=
                    have h₃ : e, from ka₀ h₂,
                    have h₄ : ka e (ka e d b) c, from ka₁ h₃ h₂,
                    have h₅ : ka e d (ka e b c), from ka₄' h₄,
                    show ka e d (ka a b c), from ka₅ h₁ h₅

                theorem ka₂_ast {a b c d : Prop} (h₁ : ka d c (ka a b b)) : ka d c b :=
                    have h₂ : ka d c (ka d b b), from ka₇ h₁,
                    sorry

                theorem ka₃_ast {a b c d e : Prop} (h₁ : ka e d (ka a b c)) : ka e d (ka a c b) := 
                sorry

                theorem ka₄_ast {a b c d e f : Prop} (h₁ : ka f e (ka a b (ka a c d))) : 
                    ka f e (ka a (ka a b c) d):= 
                sorry

                theorem ka₅_ast {a b c d e f g : Prop} 
                    (h₁ : ka g f (ka a b c)) 
                    (h₂ : ka g f (ka a b (ka a d e))) :
                    ka g f (ka a b (ka c d e)) :=
                sorry

                theorem ka₆_ast {a b c d e f g : Prop} (h₁ : ka g f (ka a c (ka b d e))) :
                    ka g f (ka a c b) :=
                sorry
                
                theorem ka₇_ast {a b c d e f g : Prop} (h₁ : ka g f (ka a c (ka b d e))) :
                    ka g f (ka a c (ka a d e)) :=
                sorry

            end ka
        end wr
    end hilbert
end clfrags
