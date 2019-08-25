import hilbert.wr.ki

namespace clfrags
    namespace hilbert
        namespace wr
            namespace ki

                theorem ki₁₀ {a b c : Prop} (h₁ : a) (h₂ : c) : ki a b c :=
                    have h₃ : ki a c (ki a b c), from ki₂ h₁,
                    show ki a b c, from ki₁ h₂ h₃

                theorem ki'₃ {a b c d : Prop} (h₁ : a) :  
                    ki a (ki a b (ki a c d)) (ki a (ki a b c) (ki a b d)) :=
                    have h₂ : ki a a a, from ki₁₀ h₁ h₁,
                    have h₃ : ki a a (ki a (ki a b (ki a c d)) (ki a (ki a b c) (ki a b d))), from ki₃ h₂,
                    show ki a (ki a b (ki a c d)) (ki a (ki a b c) (ki a b d)), from ki₁ h₁ h₃

                theorem ki'₄ {a b c : Prop} (h₁ : a) :  
                    ki a (ki a (ki a c b) c) c :=
                    have h₂ : ki a a a, from ki₁₀ h₁ h₁,
                    have h₃ : ki a a (ki a (ki a (ki a c b) c) c), from ki₄ h₂,
                    show ki a (ki a (ki a c b) c) c, from ki₁ h₁ h₃

                theorem ki₀ {a b c : Prop} (h₁ : ki a b c) : a :=
                    let r := ki a b c in
                        have h₂ : r, from h₁,
                        have h₃ : ki r r (ki a b c), from ki₁₀ h₂ h₂,
                        have h₄ : ki r r a, from ki₈ h₃,
                        show a, from ki₁ h₂ h₄
            
                theorem ki₁₁ {a b : Prop} (h₁ : a) : ki a b b :=
                    have h₂ : ki a (ki a b (ki a a b)) (ki a (ki a b a) (ki a b b)), from ki'₃ h₁,
                    have h₃ : ki a b (ki a a b), from ki₂ h₁,
                    have h₄ : ki a (ki a b a) (ki a b b), from ki₁ h₃ h₂,
                    have h₅ : ki a b a, from ki₁₀ h₁ h₁,
                    show ki a b b, from ki₁ h₅ h₄

                theorem ki₁₂ {a b c d : Prop} (h₁ : ki a b (ki a c d)) : ki a c (ki a b d) :=
                    sorry

                theorem ki₁₃ {a b c : Prop} (h₁ : ki a b (ki a b c)) : ki a b c :=
                    have h₂ : a, from ki₀ h₁,
                    have h₃ : ki a (ki a b (ki a b c)) (ki a (ki a b b) (ki a b c)), from ki'₃ h₂,
                    have h₄ : ki a (ki a b b) (ki a b c), from ki₁ h₁ h₃,
                    have h₅ : ki a b b, from ki₁₁ h₂,
                    show ki a b c, from ki₁ h₅ h₄

                theorem ki₁₄ {a b c d : Prop} (h₁ : ki a b d) : ki b b (ki a c d) :=
                    sorry

                theorem ki₁₅ {a b c d : Prop} (h₁ : ki a b d) : ki c c (ki a b d) :=
                    sorry

                theorem ki₁₆ {a b c d : Prop} (h₁ : ki a b c) (h₂ : ki a c d) : 
                    ki a b d :=
                    have h₃ : a, from ki₀ h₁,
                    have h₄ : ki a (ki a b (ki a c d)) (ki a (ki a b c) (ki a b d)), from ki'₃ h₃,
                    have h₅ : ki a b (ki a c d), from ki₁₀ h₃ h₂,
                    have h₆ : ki a (ki a b c) (ki a b d), from ki₁ h₅ h₄,
                    show ki a b d, from ki₁ h₁ h₆

                theorem ki₁_ast {a b c d e : Prop} (h₁ : ki d e b) (h₂ : ki d e (ki a b c)) : ki d e c :=
                    sorry

                theorem ki₂_ast {a b c d e : Prop} (h₁ : ki d e a) : ki d e (ki a b (ki a c b)) :=
                    sorry

                theorem ki₃_ast {a b c d e f g h : Prop}
                    (h₁ : ki g h (ki b f a)) : 
                    ki g h (ki b f (ki a (ki a c (ki a d e)) (ki a (ki a c d) (ki a c e)))) :=
                    sorry

            end ki
        end wr
    end hilbert
end clfrags
