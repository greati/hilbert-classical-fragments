import hilbert.wr.pt

namespace clfrags
    namespace hilbert
        namespace wr
            namespace pt

                theorem pt₇ {a b c d e : Prop} (h₁ : pt (pt a b c) d e) : pt a b (pt c d e) :=
                    have h₂ : pt d (pt a b c) e, from pt₂ h₁,
                    have h₃ : pt d e (pt a b c), from pt₃ h₂,
                    have h₄ : pt (pt d e a) b c, from pt₆ h₃,
                    have h₅ : pt b (pt d e a) c, from pt₂ h₄,
                    have h₆ : pt b c (pt d e a), from pt₃ h₅,
                    have h₇ : pt (pt b c d) e a, from pt₆ h₆,
                    have h₈ : pt e (pt b c d) a, from pt₂ h₇,
                    have h₉ : pt e a (pt b c d), from pt₃ h₈,
                    have h₁₀ : pt (pt e a b) c d, from pt₆ h₉,
                    have h₁₁ : pt c (pt e a b) d, from pt₂ h₁₀,
                    have h₁₂ : pt c d (pt e a b), from pt₃ h₁₁,
                    have h₁₃ : pt (pt c d e) a b, from pt₆ h₁₂,
                    have h₁₄ : pt a (pt c d e) b, from pt₂ h₁₃,
                    show pt a b (pt c d e), from pt₃ h₁₄

                theorem pt₂_ast {a b c d e : Prop} (h₁ : pt d e (pt a b c)) : pt d e (pt b a c) :=
                    have h₂ : pt d (pt a b c) e, from pt₃ h₁,
                    have h₃ : pt (pt a b c) d e, from pt₂ h₂,
                    have h₄ : pt a b (pt c d e), from pt₇ h₃,
                    have h₅ : pt b a (pt c d e), from pt₂ h₄,
                    have h₆ : pt (pt b a c) d e, from pt₆ h₅,
                    have h₇ : pt d (pt b a c) e, from pt₂ h₆,
                    show pt d e (pt b a c), from pt₃ h₇

                theorem pt₃_ast {a b c d e : Prop} (h₁ : pt d e (pt a b c)) : pt d e (pt a c b) :=
                    have h₂ : pt (pt d e a) b c, from pt₆ h₁,
                    have h₃ : pt (pt d e a) c b, from pt₃ h₂,
                    show pt d e (pt a c b), from pt₇ h₃

                theorem pt₄_ast {a b c d : Prop} (h₁ : pt c d a) : pt c d (pt a b b) :=
                    have h₂ : pt (pt c d a) b b, from pt₄ h₁,
                    show pt c d (pt a b b), from pt₇ h₂

                theorem pt₅_ast {a b c d : Prop} (h₁ : pt c d (pt a b b)) : pt c d a :=
                    have h₂ : pt (pt c d a) b b, from pt₆ h₁,
                    show pt c d a, from pt₅ h₂

                theorem pt₆_ast {a b c d e f g : Prop} (h₁ : pt f g (pt a b (pt c d e))) 
                    : pt f g (pt (pt a b c) d e) :=
                    have h₂ : pt f (pt a b (pt c d e)) g, from pt₃ h₁,
                    have h₃ : pt (pt a b (pt c d e)) f g, from pt₂ h₂,
                    have h₄ : pt a b (pt (pt c d e) f g), from pt₇ h₃,
                    have h₅ : pt a b (pt f (pt c d e) g), from pt₂_ast h₄,
                    have h₆ : pt (pt a b f) (pt c d e) g, from pt₆ h₅,
                    have h₇ : pt (pt a b f) g (pt c d e), from pt₃ h₆,
                    have h₈ : pt a b (pt f g (pt c d e)), from pt₇ h₇,
                    have h₉ : pt b a (pt f g (pt c d e)), from pt₂ h₈,
                    have h₁₀ : pt b a (pt f (pt c d e) g), from pt₃_ast h₉,
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
