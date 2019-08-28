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
                    have h₂ : a, from ki₀ h₁,
                    have h₃ : ki a (ki a b (ki a c d)) (ki a (ki a b c) (ki a b d)), from ki'₃ h₂,
                    have h₄ : ki a (ki a b c) (ki a b d), from ki₁ h₁ h₃,
                    have h₅ : ki a c (ki a (ki a b c) (ki a b d)), from ki₁₀ h₂ h₄,
                    let r := ki a b d, q := ki a b c in
                        have h₆ : ki a (ki a c (ki a q r)) (ki a (ki a c q) (ki a c r)), from ki'₃ h₂,
                        have h₇ : ki a (ki a c q) (ki a c r), from ki₁ h₅ h₆,
                        have h₈ : ki a c q, from ki₂ h₂,
                        have h₉ : ki a c r, from ki₁ h₈ h₇,
                        show ki a c (ki a b d), from h₉

                theorem ki₁₃ {a b c : Prop} (h₁ : ki a b (ki a b c)) : ki a b c :=
                    have h₂ : a, from ki₀ h₁,
                    have h₃ : ki a (ki a b (ki a b c)) (ki a (ki a b b) (ki a b c)), from ki'₃ h₂,
                    have h₄ : ki a (ki a b b) (ki a b c), from ki₁ h₁ h₃,
                    have h₅ : ki a b b, from ki₁₁ h₂,
                    show ki a b c, from ki₁ h₅ h₄

                theorem ki₁₄ {a b c d : Prop} (h₁ : ki a b d) : ki a (ki b b c) d :=
                    have h₂ : a, from ki₀ h₁,
                    have h₃ : ki a c (ki a b d), from ki₁₀ h₂ h₁,
                    have h₄ : ki a b (ki a c d), from ki₁₂ h₃,
                    show ki a (ki b b c) d, from ki₅ h₄

                theorem ki₁₅ {a b c d : Prop} (h₁ : ki a b d) : ki a (ki c c b) d :=
                    have h₂ : a, from ki₀ h₁,
                    have h₃ : ki a c (ki a b d), from ki₁₀ h₂ h₁,
                    show ki a (ki c c b) d, from ki₅ h₃

                theorem ki₁₆ {a b c d : Prop} (h₁ : ki a b c) (h₂ : ki a c d) : 
                    ki a b d :=
                    have h₃ : a, from ki₀ h₁,
                    have h₄ : ki a (ki a b (ki a c d)) (ki a (ki a b c) (ki a b d)), from ki'₃ h₃,
                    have h₅ : ki a b (ki a c d), from ki₁₀ h₃ h₂,
                    have h₆ : ki a (ki a b c) (ki a b d), from ki₁ h₅ h₄,
                    show ki a b d, from ki₁ h₁ h₆

                theorem ki₁_ast {a b c d e : Prop} (h₁ : ki d e b) (h₂ : ki d e (ki a b c)) : ki d e c :=
                    have h₃ : ki d e (ki d b c), from ki₉ h₂,
                    have h₄ : ki d b (ki d e c), from ki₁₂ h₃,
                    have h₅ : ki d e (ki d e c), from ki₁₆ h₁ h₄,
                    show ki d e c, from ki₁₃ h₅

                theorem ki₂_ast {a b c d e : Prop} (h₁ : ki d e a) : ki d e (ki a b (ki a c b)) :=
                    have h₂ : d, from ki₀ h₁,
                    have h₃ : ki d b (ki d c b), from ki₂ h₂,
                    have h₄ : ki d (ki e e b) (ki d c b), from ki₁₅ h₃,
                    have h₅ : ki d (ki e e b) a, from ki₁₄ h₁,
                    have h₆ : ki d (ki e e b) (ki a c b), from ki₇ h₅ h₄,
                    have h₇ : ki d e (ki d b (ki a c b)), from ki₆ h₆,
                    show ki d e (ki a b (ki a c b)), from ki₇ h₁ h₇

                theorem ki₃_ast {a b c d e f g h : Prop}
                    (h₁ : ki g h (ki b f a)) : 
                    ki g h (ki b f (ki a (ki a c (ki a d e)) (ki a (ki a c d) (ki a c e)))) :=
                    have h₂ : ki g h (ki g f a), from ki₉ h₁,
                    have h₃ : ki g (ki h h f) a, from ki₅ h₂,
                    have h₄ : ki g (ki h h f) (ki a (ki a c (ki a d e)) (ki a (ki a c d) (ki a c e))), from ki₃ h₃,
                    have h₅ : ki g h (ki g f (ki a (ki a c (ki a d e)) (ki a (ki a c d) (ki a c e)))), from ki₆ h₄,
                    have h₆ : ki g h b, from ki₈ h₁,
                    show ki g h (ki b f (ki a (ki a c (ki a d e)) (ki a (ki a c d) (ki a c e)))), from ki₇ h₆ h₅

                theorem ki₄_ast {a b c d e f g : Prop}
                    (h₁ : ki f g (ki b e a)) :
                    ki f g (ki b e (ki a (ki a (ki a c d) c) c)) :=
                    have h₂ : ki f g (ki f e a), from ki₉ h₁,
                    have h₃ : ki f (ki g g e) a, from ki₅ h₂,
                    have h₄ : ki f (ki g g e) (ki a (ki a (ki a c d) c) c), from ki₄ h₃,
                    have h₅ : ki f g (ki f e (ki a (ki a (ki a c d) c) c)), from ki₆ h₄,
                    have h₆ : ki f g b, from ki₈ h₁,
                    show ki f g (ki b e (ki a (ki a (ki a c d) c) c)), from ki₇ h₆ h₅

                theorem ki₅_ast {a b c d e f : Prop} (h₁ : ki e f (ki a b (ki a c d))) : 
                    ki e f (ki a (ki b b c) d) :=
                    sorry

                theorem ki₆_ast {a b c d e f : Prop} (h₁ : ki e f (ki a (ki b b c) d)) :
                    ki e f (ki a b (ki a c d)) :=
                    sorry

                theorem ki₇_ast {a b c d e f g : Prop} (h₁ : ki f g (ki a e b)) (h₂ : ki f g (ki a e (ki a c d))) :
                    ki f g (ki a e (ki b c d)) :=
                    have h₃ : ki f g (ki f e b), from ki₉ h₁,
                    have h₄ : ki f (ki g g e) b, from ki₅ h₃,
                    have h₅ : ki f g a, from ki₈ h₁,
                    have h₆ : ki f g (ki f e (ki a c d)), from ki₉ h₂,
                    have h₇ : ki f (ki g g e) (ki a c d), from ki₅ h₆,
                    have h₈ : ki f (ki g g e) (ki f c d), from ki₉ h₇,
                    have h₉ : ki f (ki g g e) (ki b c d), from ki₇ h₄ h₈,
                    have h₁₀ : ki f g (ki f e (ki b c d)), from ki₆ h₉,
                    show ki f g (ki a e (ki b c d)), from ki₇ h₅ h₁₀

                theorem ki₈_ast {a b c d e f g : Prop} (h₁ : ki f g (ki a e (ki b c d))) :
                    ki f g (ki a e b) :=
                    have h₂ : ki f g (ki f e (ki b c d)), from ki₉ h₁,
                    have h₃ : ki f (ki g g e) (ki b c d), from ki₅ h₂, 
                    have h₄ : ki f (ki g g e) b, from ki₈ h₃, 
                    have h₅ : ki f g (ki f e b), from ki₆ h₄,
                    have h₆ : ki f g a, from ki₈ h₁,
                    show ki f g (ki a e b), from ki₇ h₆ h₅

                theorem ki₉_ast {a b c d e f g : Prop} (h₁ : ki f g (ki a e (ki b c d))) :
                    ki f g (ki a e (ki a c d)) :=
                    have h₂ : ki f g a, from ki₈ h₁,
                    have h₃ : ki f g (ki f e (ki b c d)), from ki₉ h₁,
                    have h₄ : ki f (ki g g e) (ki b c d), from ki₅ h₃,
                    have h₅ : ki f (ki g g e) (ki f c d), from ki₉ h₄,
                    have h₆ : ki f (ki g g e) a, from ki₁₄ h₂,
                    have h₇ : ki f (ki g g e) (ki a c d), from ki₇ h₆ h₅,
                    have h₈ : ki f g (ki f e (ki a c d)), from ki₆ h₇,
                    show ki f g (ki a e (ki a c d)), from ki₇ h₂ h₈

            end ki
        end wr
    end hilbert
end clfrags
