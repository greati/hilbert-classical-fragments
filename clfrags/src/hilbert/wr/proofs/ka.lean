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

                lemma ka₄' {a b c d : Prop} (h₁ : ka d (ka d c a) b) : ka d c (ka d a b) :=
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

                lemma ka_aux₁ {a b c : Prop} (h₁ : ka a b (ka a c c)) : ka a b c :=
                    have h₂ : ka a (ka a b c) c, from ka₄ h₁,
                    have h₃ : ka a c (ka a b c), from ka₃ h₂,
                    have h₄ : a, from ka₀ h₂,
                    have h₅ : ka a (ka a c (ka a b c)) b, from ka₁ h₄ h₃,
                    have h₆ : ka a b (ka a c (ka a b c)), from ka₃ h₅,
                    have h₇ : ka a (ka a b c) (ka a b c), from ka₄ h₆,
                    show ka a b c, from ka₂ h₇

                theorem ka₂_ast {a b c d : Prop} (h₁ : ka d c (ka a b b)) : ka d c b :=
                    have h₂ : ka d c (ka d b b), from ka₇ h₁,
                    show ka d c b, from ka_aux₁ h₂

                theorem ka₃_ast {a b c d e : Prop} (h₁ : ka e d (ka a b c)) : ka e d (ka a c b) := 
                    have h₂ : e, from ka₀ h₁,
                    have h₃ : ka e d a, from ka₆ h₁,
                    have h₄ : ka e d (ka e b c), from ka₇ h₁,
                    have h₅ : ka e (ka e d b) c, from ka₄ h₄,
                    have h₆ : ka e (ka e (ka e d b) c) b, from ka₁ h₂ h₅,
                    have h₇ : ka e (ka e d b) (ka e c b), from ka₄' h₆,
                    have h₈ : ka e d (ka e b (ka e c b)), from ka₄' h₇,
                    have h₉ : ka e (ka e b (ka e c b)) d, from ka₃ h₈,
                    have h₁₀ : ka e b (ka e (ka e c b) d), from ka₄' h₉,
                    have h₁₁ : ka e (ka e b (ka e (ka e c b) d)) c, from ka₁ h₂ h₁₀,
                    have h₁₂ : ka e c (ka e b (ka e (ka e c b) d)), from ka₃ h₁₁,
                    have h₁₃ : ka e (ka e c b) (ka e (ka e c b) d), from ka₄ h₁₂,
                    have h₁₄ : ka e (ka e (ka e c b) (ka e c b)) d, from ka₄ h₁₃,
                    have h₁₅ : ka e d (ka e (ka e c b) (ka e c b)), from ka₃ h₁₄,
                    have h₁₆ : ka e d (ka e c b), from ka₂_ast h₁₅,
                    show ka e d (ka a c b), from ka₅ h₃ h₁₆

                theorem ka₄_ast {a b c d e f : Prop} (h₁ : ka f e (ka a b (ka a c d))) : 
                    ka f e (ka a (ka a b c) d):= 
                    have h₂ : ka f e (ka f b (ka a c d)), from ka₇ h₁,
                    have h₃ : ka f (ka f e b) (ka a c d), from ka₄ h₂,
                    have h₄ : ka f (ka f e b) (ka f c d), from ka₇ h₃,
                    have h₅ : ka f (ka f e b) (ka f d c), from ka₃_ast h₄,
                    have h₆ : ka f (ka f (ka f e b) d) c, from ka₄ h₅,
                    have h₇ : f, from ka₀ h₁,
                    have h₈ : ka f (ka f (ka f (ka f e b) d) c) b, from ka₁ h₇ h₆,
                    have h₉ : ka f (ka f (ka f e b) d) (ka f c b), from ka₄' h₈,
                    have h₁₀ : ka f (ka f (ka f e b) d) (ka f b c), from ka₃_ast h₉,
                    have h₁₁ : ka f (ka f e b) (ka f d (ka f b c)), from ka₄' h₁₀,
                    have h₁₂ : ka f (ka f e b) (ka f (ka f b c) d), from ka₃_ast h₁₁,
                    let g := ka f (ka f b c) d in
                        have h₁₃ : ka f (ka f e b) g, from h₁₂,
                        have h₁₄ : ka f e (ka f b g), from ka₄' h₁₃,
                        have h₁₅ : ka f e (ka f g b), from ka₃_ast h₁₄,
                        have h₁₆ : ka f (ka f e g) b, from ka₄ h₁₅,
                        have h₁₇ : ka f (ka f (ka f e g) b) c, from ka₁ h₇ h₁₆,
                        have h₁₈ : ka f (ka f e g) (ka f b c), from ka₄' h₁₇,
                        have h₁₉ : ka f (ka f (ka f e g) (ka f b c)) d, from ka₁ h₇ h₁₈,
                        have h₂₀ : ka f (ka f e g) (ka f (ka f b c) d), from ka₄' h₁₉,
                        have h₂₁ : ka f (ka f e g) g, from h₂₀,
                        have h₂₂ : ka f e (ka f g g), from ka₄' h₂₁,
                        have h₂₃ : ka f e g, from ka₂_ast h₂₂,
                        have h₂₄ : ka f e (ka f (ka f b c) d), from h₂₃,
                        have h₂₅ : ka f e a, from ka₆ h₁,
                        have h₂₆ : ka f (ka f e a) d, from ka₁ h₇ h₂₅,
                        have h₂₇ : ka f e (ka f a d), from ka₄' h₂₆,
                        have h₂₈ : ka f e (ka f d a), from ka₃_ast h₂₇,
                        have h₂₉ : ka f (ka f e d) a, from ka₄ h₂₈,
                        have h₃₀ : ka f e (ka f d (ka f b c)), from ka₃_ast h₂₄,
                        have h₃₁ : ka f (ka f e d) (ka f b c), from ka₄ h₃₀,
                        have h₃₂ : ka f (ka f e d) (ka a b c), from ka₅ h₂₉ h₃₁,
                        have h₃₃ : ka f e (ka f d (ka a b c)), from ka₄' h₃₂,
                        have h₃₄ : ka f e (ka a d (ka a b c)), from ka₅ h₂₅ h₃₃,
                        show ka f e (ka a (ka a b c) d), from ka₃_ast h₃₄

                theorem ka₅_ast {a b c d e f g : Prop} 
                    (h₁ : ka g f (ka a b c)) 
                    (h₂ : ka g f (ka a b (ka a d e))) :
                    ka g f (ka a b (ka c d e)) :=
                    have h₃ : ka g f (ka g b c), from ka₇ h₁,
                    have h₄ : ka g (ka g f b) c, from ka₄ h₃,
                    have h₅ : ka g f (ka g b (ka a d e)), from ka₇ h₂,
                    have h₆ : ka g (ka g f b) (ka a d e), from ka₄ h₅,
                    have h₇ : ka g (ka g f b) (ka g d e), from ka₇ h₆,
                    have h₈ : ka g (ka g f b) (ka c d e), from ka₅ h₄ h₇,
                    have h₉ : ka g f (ka g b (ka c d e)), from ka₄' h₈,
                    have h₁₀ : ka g f a, from ka₆ h₁,
                    show ka g f (ka a b (ka c d e)), from ka₅ h₁₀ h₉

                theorem ka₆_ast {a b c d e f g : Prop} (h₁ : ka g f (ka a c (ka b d e))) :
                    ka g f (ka a c b) :=
                    have h₂ : ka g f (ka g c (ka b d e)), from ka₇ h₁,
                    have h₃ : ka g (ka g f c) (ka b d e), from ka₄ h₂,
                    have h₄ : ka g (ka g f c) b, from ka₆ h₃,
                    have h₅ : ka g f (ka g c b), from ka₄' h₄,
                    have h₆ : ka g f a, from ka₆ h₁,
                    show ka g f (ka a c b), from ka₅ h₆ h₅
                
                theorem ka₇_ast {a b c d e f g : Prop} (h₁ : ka g f (ka a c (ka b d e))) :
                    ka g f (ka a c (ka a d e)) :=
                    sorry

            end ka
        end wr
    end hilbert
end clfrags
