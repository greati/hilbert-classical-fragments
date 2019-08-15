import hilbert.wr.ka

namespace clfrags
    namespace hilbert
        namespace wr
            namespace ka

                theorem ka₀ {a b c : Prop} (h₁ : ka a b c) : a :=
                sorry

                theorem ka₁_ast {a b c d e : Prop} (h₁ : ka e d a) (h₂ : ka e d b) : ka e d (ka a b c) :=
                sorry

                theorem ka₂_ast {a b c d : Prop} (h₁ : ka d c (ka a b b)) : ka d c b :=
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
