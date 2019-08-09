import hilbert.wr.or

namespace clfrags
    namespace hilbert
        namespace wr
            namespace or

                theorem d₁' {a b : Prop} (h₁ : b) : or a b :=
                    have h₂ : or b a, from or.d₁ h₁,
                    show or a b, from or.d₃ h₂

                theorem d₄' {a b c : Prop} (h₁ : or (or a b) c) : or a (or b c) :=
                    have h₂ : or c (or a b), from or.d₃ h₁,
                    have h₃ : or (or c a) b, from or.d₄ h₂,
                    have h₄ : or b (or c a), from or.d₃ h₃,
                    have h₅ : or (or b c) a, from or.d₄ h₄,
                    show or a (or b c), from or.d₃ h₅
        
                theorem d₁_or {a b d : Prop} (h₁ : or d a) : or d (or a b) :=
                    have h₂ : or (or d a) b, from or.d₁ h₁,
                    show or d (or a b), from or.d₄' h₂

                theorem d₂_or {d a : Prop} (h₁ : or d (or a a)) : or d a :=
                    have h₂ : or (or d a) a, from or.d₄ h₁,
                    have h₃ : or a (or d a), from or.d₃ h₂,
                    have h₄ : or d (or a (or d a)), from or.d₁' h₃,
                    have h₅ : or (or d a) (or d a), from or.d₄ h₄,
                    show or d a, from or.d₂ h₅

                theorem d₃_or {a b d : Prop} (h₁ : or d (or a b)) : or d (or b a) :=
                    have h₂ : or (or d a) b, from or.d₄ h₁,
                    have h₃ : or (or (or d a) b) a, from or.d₁ h₂,
                    have h₄ : or (or d a) (or b a), from or.d₄' h₃,
                    have h₅ : or d (or a (or b a)), from or.d₄' h₄,
                    have h₆ : or (or a (or b a)) d, from or.d₃ h₅,
                    have h₇ : or a (or (or b a) d), from or.d₄' h₆,
                    have h₈ : or b (or a (or (or b a) d)), from or.d₁' h₇,
                    have h₉ : or (or b a) (or (or b a) d), from or.d₄ h₈,
                    have h₁₀ : or (or (or b a) (or b a)) d, from or.d₄ h₉,
                    have h₁₁ : or d (or (or b a) (or b a)), from or.d₃ h₁₀,
                    show or d (or b a), from or.d₂_or h₁₁

                theorem d₄_or {a b c d : Prop} (h₁ : or d (or a (or b c))) : or d (or (or a b) c) :=
                    have h₂ : or (or d a) (or b c), from or.d₄ h₁,
                    have h₃ : or (or d a) (or c b), from or.d₃_or h₂,
                    have h₄ : or (or (or d a) c) b, from or.d₄ h₃,
                    have h₅ : or (or (or (or d a) c) b) a, from or.d₁ h₄,
                    have h₆ : or (or (or d a) c) (or b a), from or.d₄' h₅,
                    have h₇ : or (or (or d a) c) (or a b), from or.d₃_or h₆,
                    have h₈ : or (or d a) (or c (or a b)), from or.d₄' h₇,
                    have h₉ : or (or d a) (or (or a b) c), from or.d₃_or h₈,
                    let e := or (or a b) c in
                        have h₁₀ : or (or d a) e, from h₉,
                        have h₁₁ : or d (or a e), from or.d₄' h₁₀,
                        have h₁₂ : or d (or e a), from or.d₃_or h₁₁,
                        have h₁₃ : or (or d e) a, from or.d₄ h₁₂,
                        have h₁₄ : or (or (or d e) a) b, from or.d₁ h₁₃,
                        have h₁₅ : or (or d e) (or a b), from or.d₄' h₁₄,
                        have h₁₆ : or (or (or d e) (or a b)) c, from or.d₁ h₁₅,
                        have h₁₇ : or (or d e) (or (or a b) c), from or.d₄' h₁₆,
                        have h₁₈ : or (or d e) e, from h₁₇,
                        have h₁₉ : or d (or e e), from or.d₄' h₁₈,
                        have h₂₀ : or d e, from or.d₂_or h₁₉,
                        show or d (or (or a b) c), from h₂₀
            end or 
        end wr
    end hilbert
end clfrags
