import hilbert.wr.pt

namespace clfrags
    namespace hilbert
        namespace wr
            namespace pt

                theorem pt₇ {a b c d e : Prop} (h₁ : pt (pt a b c) d e) : pt a b (pt c d e) :=
                    sorry

                theorem pt₂_ast {a b c d e : Prop} (h₁ : pt d e (pt a b c)) : pt d e (pt b a c) :=
                    sorry

                theorem pt₃_ast {a b c d e : Prop} (h₁ : pt d e (pt a b c)) : pt d e (pt a c b) :=
                    sorry

                theorem pt₄_ast {a b c d : Prop} (h₁ : pt c d a) : pt c d (pt a b b) :=
                    sorry

                theorem pt₅_ast {a b c d : Prop} (h₁ : pt c d (pt a b b)) : pt c d a :=
                    sorry

                theorem pt₆_ast {a b c d e f g : Prop} (h₁ : pt f g (pt a b (pt c d e))) 
                    : pt f g (pt (pt a b c) d e) :=
                    sorry

                theorem pt₈ {a b c : Prop} (h₁ : pt (pt a b c) a b) : c :=
                    sorry

                theorem pt₉ {a b c : Prop} (h₁ : pt (pt a b c) a c) : b :=
                    sorry

                theorem pt₁₀ {a b c : Prop} (h₁ : pt (pt a b c) b c) : a :=
                    sorry

                theorem pt₁₁ {a b c d : Prop} 
                    (h₁ : pt (pt (pt a b c) a d) (pt (pt a b c) b d) (pt (pt a b c) c d)) : d :=
                    sorry

                theorem pt₁₂ {a b c d e : Prop} (h₁ : pt a b c) (h₂ : d) (h₃ : e) 
                    : pt a b (pt c d e) :=
                    sorry

                theorem pt₁₃ {a b c d e : Prop} (h₁ : pt a b c) (h₂ : pt a b d) (h₃ : e) 
                    : pt a b (pt c d e) :=
                    sorry

                theorem pt₁₄ {a b c d e : Prop} (h₁ : pt a b c) (h₂ : pt a b d) (h₃ : pt a b e) 
                    : pt a b (pt c d e) :=
                    sorry

                theorem pt₄' {a b c : Prop} (h₁ : a) : pt (pt a b c) b c :=
                    sorry

            end pt
        end wr
    end hilbert
end clfrags
