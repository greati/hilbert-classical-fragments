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

                theorem pt₂_pt {a b c d e : Prop} (h₁ : pt d e (pt a b c)) : pt d e (pt b a c) :=
                    have h₂ : pt d (pt a b c) e, from pt₃ h₁,
                    have h₃ : pt (pt a b c) d e, from pt₂ h₂,
                    have h₄ : pt a b (pt c d e), from pt₇ h₃,
                    have h₅ : pt b a (pt c d e), from pt₂ h₄,
                    have h₆ : pt (pt b a c) d e, from pt₆ h₅,
                    have h₇ : pt d (pt b a c) e, from pt₂ h₆,
                    show pt d e (pt b a c), from pt₃ h₇

                theorem pt₃_pt {a b c d e : Prop} (h₁ : pt d e (pt a b c)) : pt d e (pt a c b) :=
                    have h₂ : pt (pt d e a) b c, from pt₆ h₁,
                    have h₃ : pt (pt d e a) c b, from pt₃ h₂,
                    show pt d e (pt a c b), from pt₇ h₃

                theorem pt₄_pt {a b c d : Prop} (h₁ : pt c d a) : pt c d (pt a b b) :=
                    have h₂ : pt (pt c d a) b b, from pt₄ h₁,
                    show pt c d (pt a b b), from pt₇ h₂

                theorem pt₅_pt {a b c d : Prop} (h₁ : pt c d (pt a b b)) : pt c d a :=
                    have h₂ : pt (pt c d a) b b, from pt₆ h₁,
                    show pt c d a, from pt₅ h₂

                theorem pt₆_pt {a b c d e f g : Prop} (h₁ : pt f g (pt a b (pt c d e))) 
                    : pt f g (pt (pt a b c) d e) :=
                    have h₂ : pt (pt a b (pt c d e)) f g, from pt₂ (pt₃ h₁),
                    have h₃ : pt a b (pt (pt c d e) f g), from pt₇ h₂,
                    have h₄ : pt (pt (pt c d e) f g) a b, from pt₂ (pt₃ h₃),
                    have h₅ : pt (pt c d e) f (pt g a b), from pt₇ h₄, 
                    have h₆ : pt c d (pt e f (pt g a b)), from pt₇ h₅,
                    have h₇ : pt (pt e f (pt g a b)) c d, from pt₂ (pt₃ h₆),
                    have h₈ : pt e f (pt (pt g a b) c d), from pt₇ h₇,
                    have h₉ : pt (pt (pt g a b) c d) e f, from pt₂ (pt₃ h₈),
                    have h₁₀ : pt (pt g a b) c (pt d e f), from pt₇ h₉,
                    have h₁₁ : pt g a (pt b c (pt d e f)), from pt₇ h₁₀,
                    have h₁₂ : pt (pt b c (pt d e f)) g a, from pt₂ (pt₃ h₁₁),
                    have h₁₃ : pt b c (pt (pt d e f) g a), from pt₇ h₁₂,
                    have h₁₄ : pt (pt (pt d e f) g a) b c, from pt₂ (pt₃ h₁₃),
                    have h₁₅ : pt (pt d e f) g (pt a b c), from pt₇ h₁₄,
                    have h₁₆ : pt d e (pt f g (pt a b c)), from pt₇ h₁₅,
                    have h₁₇ : pt (pt f g (pt a b c)) d e, from pt₂ (pt₃ h₁₆),
                    show pt f g (pt (pt a b c) d e), from pt₇ h₁₇

                theorem pt₈ {a b c : Prop} (h₁ : pt (pt a b c) a b) : c :=
                    have h₂ : pt a (pt a b c) b, from pt₂ h₁,
                    have h₃ : pt a b (pt a b c), from pt₃ h₂,
                    have h₄ : pt a b (pt a c b), from pt₃_pt h₃,
                    have h₅ : pt a b (pt c a b), from pt₂_pt h₄,
                    have h₆ : pt a (pt c a b) b, from pt₃ h₅,
                    have h₇ : pt (pt c a b) a b, from pt₂ h₆,
                    have h₈ : pt c a (pt b a b), from pt₇ h₇,
                    have h₉ : pt c a (pt a b b), from pt₂_pt h₈,
                    have h₁₀ : pt c a a, from pt₅_pt h₉,
                    show c, from pt₅ h₁₀

                theorem pt₉ {a b c : Prop} (h₁ : pt (pt a b c) a c) : b :=
                    have h₂ : pt a b (pt c a c), from pt₇ h₁,
                    have h₃ : pt a b (pt a c c), from pt₂_pt h₂,
                    have h₄ : pt a b a, from pt₅_pt h₃,
                    have h₅ : pt b a a, from pt₂ h₄,
                    show b, from pt₅ h₅

                theorem pt₁₀ {a b c : Prop} (h₁ : pt (pt a b c) b c) : a :=
                    have h₂ : pt a b (pt c b c), from pt₇ h₁,
                    have h₃ : pt a b (pt b c c), from pt₂_pt h₂,
                    have h₄ : pt a b b, from pt₅_pt h₃,
                    show a, from pt₅ h₄

                lemma pt₁₁' {a b c d e f : Prop} (h₁ : pt e f (pt (pt a b c) c d))
                    : pt e f (pt a b d) :=
                    have h₂ : pt e f (pt c d (pt a b c)), from pt₃_pt (pt₂_pt h₁),
                    have h₃ : pt e f (pt (pt c d a) b c), from pt₆_pt h₂,
                    have h₄ : pt e f (pt b c (pt c d a)), from pt₃_pt (pt₂_pt h₃),
                    have h₅ : pt e f (pt (pt b c c) d a), from pt₆_pt h₄,
                    have h₆ : pt e f (pt d a (pt b c c)), from pt₃_pt (pt₂_pt h₅),
                    have h₇ : pt e f (pt (pt d a b) c c), from pt₆_pt h₆,
                    have h₈ : pt e f (pt d a b), from pt₅_pt h₇,
                    show pt e f (pt a b d), from pt₃_pt (pt₂_pt h₈)

                lemma pt₁₁'' {a b c d e f : Prop} (h₁ : pt e f (pt (pt a b c) b d))
                    : pt e f (pt a c d) :=
                    have h₂ : pt e f (pt b d (pt a b c)), from pt₃_pt (pt₂_pt h₁),
                    have h₃ : pt e f (pt (pt b d a) b c), from pt₆_pt h₂,
                    have h₄ : pt e f (pt c b (pt b d a)), from pt₂_pt (pt₃_pt (pt₂_pt h₃)),
                    have h₅ : pt e f (pt (pt c b b) d a), from pt₆_pt h₄,
                    have h₆ : pt e f (pt d a (pt c b b)), from pt₃_pt (pt₂_pt h₅),
                    have h₇ : pt e f (pt (pt d a c) b b), from pt₆_pt h₆,
                    have h₈ : pt e f (pt d a c), from pt₅_pt h₇,
                    show pt e f (pt a c d), from pt₃_pt (pt₂_pt h₈)

                lemma pt₁₁''' {a b c d e f : Prop} (h₁ : pt e f (pt (pt a b c) a d))
                    : pt e f (pt b c d) :=
                    have h₂ : pt e f (pt d a (pt a b c)), from pt₂_pt (pt₃_pt (pt₂_pt h₁)),
                    have h₃ : pt e f (pt (pt d a a) b c), from pt₆_pt h₂,
                    have h₄ : pt e f (pt b c (pt d a a)), from pt₃_pt (pt₂_pt h₃),
                    have h₅ : pt e f (pt (pt b c d) a a), from pt₆_pt h₄,
                    show pt e f (pt b c d), from pt₅_pt h₅

                theorem pt₁₁ {a b c d : Prop} 
                    (h₁ : pt (pt (pt a b c) a d) (pt (pt a b c) b d) (pt (pt a b c) c d)) : d :=
                    have h₂ : pt (pt (pt a b c) a d) (pt (pt a b c) b d) (pt a b d), from pt₁₁' h₁,
                    have h₃ : pt (pt (pt a b c) a d) (pt a b d) (pt (pt a b c) b d), from pt₃ h₂,
                    have h₄ : pt (pt (pt a b c) a d) (pt a b d) (pt a c d), from pt₁₁'' h₃,
                    have h₅ : pt (pt a b d) (pt (pt a b c) a d) (pt a c d), from pt₂ h₄,
                    have h₆ : pt (pt a b d) (pt a c d) (pt (pt a b c) a d) , from pt₃ h₅,
                    have h₇ : pt (pt a b d) (pt a c d) (pt b c d) , from pt₁₁''' h₆,
                    have h₈ : pt a b (pt d (pt a c d) (pt b c d)) , from pt₇ h₇,
                    have h₉ : pt a b (pt (pt a c d) d (pt b c d)) , from pt₂_pt h₈,
                    have h₁₀ : pt (pt a b (pt a c d)) d (pt b c d) , from pt₆ h₉,
                    have h₁₁ : pt (pt a b (pt a c d)) d (pt b d c) , from pt₃_pt h₁₀,
                    have h₁₂ : pt (pt a b (pt a c d)) d (pt d b c) , from pt₂_pt h₁₁,
                    have h₁₃ : pt (pt (pt a b (pt a c d)) d d) b c, from pt₆ h₁₂,
                    have h₁₄ : pt b c (pt (pt a b (pt a c d)) d d), from pt₃ (pt₂ h₁₃),
                    have h₁₅ : pt b c (pt a b (pt a c d)), from pt₅_pt h₁₄,
                    have h₁₆ : pt b c (pt b a (pt a c d)), from pt₂_pt h₁₅,
                    have h₁₇ : pt (pt b c b) a (pt a c d), from pt₆ h₁₆,
                    have h₁₈ : pt a (pt a c d) (pt b c b), from pt₃ (pt₂ h₁₇),
                    have h₁₉ : pt a (pt a c d) (pt c b b), from pt₂_pt h₁₈,
                    have h₂₀ : pt a (pt a c d) c, from pt₅_pt h₁₉,
                    have h₂₁ : pt (pt a c d) a c, from pt₂ h₂₀,
                    show d, from pt₈ h₂₁

                theorem pt₁₂ {a b c d e : Prop} (h₁ : pt a b c) (h₂ : d) (h₃ : e) 
                    : pt a b (pt c d e) :=
                    have h₄ : pt (pt a b c) d e, from pt₁ h₁ h₂ h₃,
                    show pt a b (pt c d e), from pt₇ h₄

                theorem pt₁₃ {a b c d e : Prop} (h₁ : pt a b c) (h₂ : pt a b d) (h₃ : e) 
                    : (pt c d e) :=
                    have h₄ : pt a b (pt c (pt a b d) e), from pt₁₂ h₁ h₂ h₃,
                    have h₅ : pt a b (pt (pt a b d) c e), from pt₂_pt h₄,
                    have h₆ : pt (pt a b (pt a b d)) c e, from pt₆ h₅,
                    have h₇ : pt c e (pt a b (pt a b d)), from pt₃ (pt₂ h₆),
                    have h₈ : pt c e (pt (pt a b d) a b), from pt₂_pt (pt₃_pt h₇),
                    have h₉ : pt c e (pt b d b), from pt₁₁''' h₈,
                    have h₁₀ : pt c e (pt d b b), from pt₂_pt h₉,
                    have h₁₁ : pt c e d, from pt₅_pt h₁₀,
                    show pt c d e, from pt₃ h₁₁

                theorem pt₁₄ {a b c d e : Prop} (h₁ : pt a b c) (h₂ : pt a b d) (h₃ : pt a b e) 
                    : pt a b (pt c d e) :=
                    have h₄ : pt c d (pt a b e), from pt₁₃ h₁ h₂ h₃,
                    have h₅ : pt c d (pt e a b), from pt₂_pt (pt₃_pt h₄),
                    have h₅ : pt (pt c d e) a b, from pt₆ h₅,
                    show pt a b (pt c d e), from pt₃ (pt₂ h₅)

                theorem pt₄' {a b c : Prop} (h₁ : a) : pt (pt a b c) b c :=
                    have h₂ : pt a b b, from pt₄ h₁,
                    have h₃ : pt (pt a b b) c c, from pt₄ h₂,
                    have h₄ : pt  a b (pt b c c), from pt₇ h₃,
                    have h₅ : pt  a b (pt c b c), from pt₂_pt h₄,
                    show pt (pt a b c) b c, from pt₆ h₅

            end pt
        end wr
    end hilbert
end clfrags
