import hilbert.wr.pt_neg

namespace clfrags
    namespace hilbert
        namespace wr
            namespace pt_neg

                theorem pt₂_neg {a b c : Prop} (h₁ : neg (pt a b c)) : neg (pt b a c) :=
                    have h₂ : pt a (neg b) c, from ptn₃ h₁,
                    have h₃ : pt (neg b) a c, from pt.pt₂ h₂,
                    show neg (pt b a c), from ptn₂ h₃

                theorem pt₃_neg {a b c : Prop} (h₁ : neg (pt a b c)) : neg (pt a c b) :=
                    have h₂ : pt (neg a) b c, from ptn₁ h₁,
                    have h₃ : pt (neg a) c b, from pt.pt₃ h₂,
                    show neg (pt a c b), from ptn₂ h₃

                theorem pt₄_neg {a b : Prop} (h₁ : neg a) : neg (pt a b b) :=
                    have h₂ : pt (neg a) b b, from pt.pt₄ h₁,
                    show neg (pt a b b), from ptn₂ h₂

                theorem pt₅_neg {a b : Prop} (h₁ : neg (pt a b b)) : neg a :=
                    have h₂ : pt (neg a) b b, from ptn₁ h₁,
                    show neg a, from pt.pt₅ h₂

                theorem pt₆_neg {a b c d e : Prop} (h₁ : neg (pt a b (pt c d e))) : neg (pt (pt a b c) d e) :=
                    have h₂ : pt (neg a) b (pt c d e), from ptn₁ h₁,
                    have h₃ : pt (pt (neg a) b c) d e, from pt.pt₆ h₂,
                    have h₄ : pt d e (pt (neg a) b c), from pt.pt₃ (pt.pt₂ h₃),
                    have h₅ : pt (pt d e (neg a)) b c, from pt.pt₆ h₄,
                    have h₆ : pt b c (pt d e (neg a)), from pt.pt₃ (pt.pt₂ h₅),
                    have h₇ : pt b c (pt (neg a) d e), from pt.pt₂_ast (pt.pt₃_ast h₆),
                    have h₈ : pt (pt (neg a) d e) b c, from pt.pt₂ (pt.pt₃ h₇),
                    have h₉ : pt (neg a) d (pt e b c), from pt.pt₇ h₈,
                    have h₁₀ : neg (pt a d (pt e b c)), from ptn₂ h₉,
                    have h₁₁ : neg (pt d a (pt e b c)), from pt₂_neg h₁₀,
                    have h₁₂ : pt (neg d) a (pt e b c), from ptn₁ h₁₁,
                    have h₁₃ : pt (pt (neg d) a e) b c, from pt.pt₆ h₁₂,
                    have h₁₄ : pt b c (pt (neg d) a e), from pt.pt₃ (pt.pt₂ h₁₃),
                    have h₁₅ : pt b c (pt a (neg d) e), from pt.pt₂_ast h₁₄,
                    have h₁₆ : pt (pt b c a) (neg d) e, from pt.pt₆ h₁₅,
                    have h₁₇ : pt (neg d) e (pt b c a), from pt.pt₃ (pt.pt₂ h₁₆),
                    have h₁₈ : pt (neg d) e (pt a b c), from pt.pt₂_ast (pt.pt₃_ast h₁₇),
                    have h₁₉ : neg (pt d e (pt a b c)), from ptn₂ h₁₈,
                    show neg (pt (pt a b c) d e), from pt₂_neg (pt₃_neg h₁₉)

                theorem pt₇_neg {a b c d e : Prop} (h₁ : neg (pt (pt a b c) d e)) : neg (pt a b (pt c d e))  :=
                    have h₂ : neg (pt d (pt a b c) e), from pt₂_neg h₁,
                    have h₃ : neg (pt d e (pt a b c)), from pt₃_neg h₂,
                    have h₄ : neg (pt (pt d e a) b c), from pt₆_neg h₃,
                    have h₅ : neg (pt b (pt d e a) c), from pt₂_neg h₄,
                    have h₆ : neg (pt b c (pt d e a)), from pt₃_neg h₅,
                    have h₇ : neg (pt (pt b c d) e a), from pt₆_neg h₆,
                    have h₈ : neg (pt e (pt b c d) a), from pt₂_neg h₇,
                    have h₉ : neg (pt e a (pt b c d)), from pt₃_neg h₈,
                    have h₁₀ : neg (pt (pt e a b) c d), from pt₆_neg h₉,
                    have h₁₁ : neg (pt c (pt e a b) d), from pt₂_neg h₁₀,
                    have h₁₂ : neg (pt c d (pt e a b)), from pt₃_neg h₁₁,
                    have h₁₃ : neg (pt (pt c d e) a b), from pt₆_neg h₁₂,
                    have h₁₄ : neg (pt a (pt c d e) b), from pt₂_neg h₁₃,
                    show neg (pt a b (pt c d e)), from pt₃_neg h₁₄

                theorem n₁_ast {a b c d : Prop} (h₁ : pt c d a) (h₂ : pt c d (neg a)) : pt c d b :=
                    have h₃ : pt a c d, from pt.pt₂ (pt.pt₃ h₁),
                    have h₄ : pt (neg a) c d, from pt.pt₂ (pt.pt₃ h₂),
                    have h₅ : neg (pt a c d), from ptn₂ h₄,
                    show pt c d b, from neg.n₁ h₃ h₅

                theorem n₂_ast {a b c : Prop} (h₁ : pt b c a) : pt b c (neg (neg a)) :=
                    have h₂ : pt (pt b c a) (neg a) (neg a), from pt.pt₄ h₁,
                    have h₃ : pt b c (pt a (neg a) (neg a)), from pt.pt₇ h₂,
                    have h₄ : pt (pt a (neg a) (neg a)) b c, from pt.pt₂ (pt.pt₃ h₃),
                    have h₅ : pt a (neg a) (pt (neg a) b c), from pt.pt₇ h₄,
                    have h₆ : pt (neg a) a (pt (neg a) b c), from pt.pt₂ h₅,
                    have h₇ : neg (pt a a (pt (neg a) b c)), from ptn₂ h₆,
                    have h₈ : neg (pt (pt (neg a) b c) a a), from pt₂_neg (pt₃_neg h₇),
                    have h₉ : neg (pt (neg a) b c), from pt₅_neg h₈,
                    have h₁₀ : pt (neg (neg a)) b c, from ptn₁ h₉,
                    show pt b c (neg (neg a)), from pt.pt₃ (pt.pt₂ h₁₀)

                theorem n₃_ast {a b c : Prop} (h₁ : pt b c (neg (neg a))) : pt b c a :=
                    have h₂ : pt (neg (neg a)) b c, from pt.pt₂ (pt.pt₃ h₁),
                    have h₃ : neg (pt (neg a) b c), from ptn₂ h₂,
                    have h₄ : pt (neg (pt (neg a) b c)) a a, from pt.pt₄ h₃,
                    have h₅ : neg (pt (pt (neg a) b c) a a), from ptn₂ h₄,
                    have h₆ : neg (pt a a (pt (neg a) b c)), from pt₃_neg (pt₂_neg h₅),
                    have h₇ : pt (neg a) a (pt (neg a) b c), from ptn₁ h₆,
                    have h₈ : pt (pt (neg a) a (neg a)) b c, from pt.pt₆ h₇,
                    have h₉ : pt b c (pt (neg a) a (neg a)), from pt.pt₃ (pt.pt₂ h₈),
                    have h₁₀ : pt b c (pt a (neg a) (neg a)), from pt.pt₂_ast h₉,
                    show pt b c a, from pt.pt₅_ast h₁₀

                theorem ptn₁_ast {a b c d e : Prop} (h₁ : pt d e (neg (pt a b c))) : pt d e (pt (neg a) b c) :=
                    have h₂ : pt (neg (pt a b c)) d e, from pt.pt₂ (pt.pt₃ h₁),
                    have h₃ : neg (pt (pt a b c) d e), from ptn₂ h₂,
                    have h₄ : neg (pt a b (pt c d e)), from pt₇_neg h₃,
                    have h₅ : pt (neg a) b (pt c d e), from ptn₁ h₄,
                    have h₆ : pt (pt (neg a) b c) d e, from pt.pt₆ h₅,
                    show pt d e (pt (neg a) b c), from pt.pt₃ (pt.pt₂ h₆)

                theorem ptn₂_ast {a b c d e : Prop} (h₁ : pt d e (pt (neg a) b c))  : pt d e (neg (pt a b c)) :=
                    have h₂ : pt (pt (neg a) b c) d e, from pt.pt₂ (pt.pt₃ h₁),
                    have h₃ : pt (neg a) b (pt c d e), from pt.pt₇ h₂,
                    have h₄ : neg (pt a b (pt c d e)), from ptn₂ h₃,
                    have h₅ : neg (pt (pt a b c) d e), from pt₆_neg h₄,
                    have h₆ : pt (neg (pt a b c)) d e, from ptn₁ h₅,
                    show pt d e (neg (pt a b c)), from pt.pt₃ (pt.pt₂ h₆)

                theorem ptn₃_ast {a b c d e : Prop} (h₁ : pt d e (neg (pt a b c))) : pt d e (pt a (neg b) c) :=
                    have h₂ : pt (neg (pt a b c)) d e, from pt.pt₂ (pt.pt₃ h₁),
                    have h₃ : neg (pt (pt a b c) d e), from ptn₂ h₂,
                    have h₄ : neg (pt a b (pt c d e)), from pt₇_neg h₃,
                    have h₅ : neg (pt b a (pt c d e)), from pt₂_neg h₄,
                    have h₆ : pt (neg b) a (pt c d e), from ptn₁ h₅,
                    have h₇ : pt a (neg b) (pt c d e), from pt.pt₂ h₆,
                    have h₈ : pt (pt a (neg b) c) d e, from pt.pt₆ h₇,
                    show pt d e (pt a (neg b) c), from pt.pt₃ (pt.pt₂ h₈)

            end pt_neg
        end wr
    end hilbert
end clfrags
