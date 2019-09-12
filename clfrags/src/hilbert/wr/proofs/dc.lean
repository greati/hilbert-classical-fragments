import hilbert.wr.dc

namespace clfrags
    namespace hilbert
        namespace wr
            namespace dc

                theorem dc₄' {a b c : Prop} (h₁ : dc a b c) : dc b a c :=
                    have h₂ : dc (dc b a c) (dc a b c) (dc a b c), from dc₃ h₁,
                    have h₃ : dc (dc a b c) (dc b a c) (dc b a c), from dc₄ h₂,
                    show dc b a c, from dc₂ h₃

                theorem dc₅' {a b c : Prop} (h₁ : dc a b c) : dc a c b :=
                    have h₂ : dc (dc a c b) (dc a b c) (dc a b c), from dc₃ h₁,
                    have h₃ : dc (dc a b c) (dc a c b) (dc a c b), from dc₅ h₂,
                    show dc a c b, from dc₂ h₃

                theorem dc₆' {a b c d e : Prop}
                    (h₁ : dc d e (dc a b c)) : dc (dc d e a) (dc d e b) c :=
                    let f := dc d e (dc a b c), g := dc (dc d e a) (dc d e b) c in
                        have h₂ : dc g f f, from dc₃ h₁,
                        have h₃ : dc g f g, from dc₆ h₂,
                        have h₄ : dc f g g, from dc₄' h₃,
                        show g, from dc₂ h₄

                theorem dc₇' {a b c d e : Prop}
                    (h₁ : dc (dc d e a) (dc d e b) c) : dc d e (dc a b c) :=
                    let f := dc d e (dc a b c), g := dc (dc d e a) (dc d e b) c in
                        have h₂ : dc f g g, from dc₃ h₁,
                        have h₃ : dc f g f, from dc₇ h₂,
                        have h₄ : dc g f f, from dc₄' h₃,
                        show f, from dc₂ h₄

                theorem dc₁_ast {a b c d e : Prop} (h₁ : dc d e a) (h₂ : dc d e b) :
                    dc d e (dc a b c) :=
                    have h₂ : dc (dc d e a) (dc d e b) c, from dc₁ h₁ h₂,
                    show dc d e (dc a b c), from dc₇' h₂

                theorem dc₂_ast {a b c d : Prop} (h₁ : dc c d (dc b a a)) : dc c d a :=
                    have h₂ : dc d c (dc a b a), from dc₄ h₁,
                    have h₃ : dc c d (dc a a b), from dc₅ h₂,
                    have h₄ : dc (dc c d a) (dc c d a) b, from dc₆' h₃,
                    have h₅ : dc b (dc c d a) (dc c d a), from dc₄' (dc₅' h₄),
                    show dc c d a, from dc₂ h₅

                theorem dc₃_ast {a b c d : Prop} (h₁ : dc c d a) : dc c d (dc b a a) :=
                    have h₂ : dc b (dc c d a) (dc c d a), from dc₃ h₁,
                    have h₃ : dc (dc c d a) (dc c d a) b, from dc₅' (dc₄' h₂),
                    have h₄ : dc c d (dc a a b), from dc₇' h₃,
                    have h₅ : dc d c (dc a b a), from dc₅ h₄,
                    show dc c d (dc b a a), from dc₄ h₅

                theorem dc₄_ast {a b c d e f g : Prop} (h₁ : dc f g (dc d e (dc a b c))) : 
                    dc f g (dc e d (dc b a c)) :=
                    have h₂ : dc g f (dc e d (dc a b c)), from dc₄ h₁,
                    have h₃ : dc g f (dc (dc e d a) (dc e d b) c), from dc₆ h₂,
                    have h₄ : dc f g (dc (dc e d b) (dc e d a) c), from dc₄ h₃,
                    show dc f g (dc e d (dc b a c)), from dc₇ h₄

                theorem dc₅_ast {a b c d e f g : Prop} (h₁ : dc f g (dc d e (dc a b c))) : 
                    dc f g (dc e d (dc a c b)) :=
                    have h₂ : dc g f (dc e d (dc a b c)), from dc₄ h₁,
                    have h₃ : dc (dc g f e) (dc g f d) (dc a b c), from dc₆' h₂,
                    have h₄ : dc (dc g f d) (dc g f e) (dc a c b), from dc₅ h₃,
                    have h₅ : dc g f (dc d e (dc a c b)), from dc₇' h₄,
                    show dc f g (dc e d (dc a c b)), from dc₄ h₅

                theorem dc₆_ast {a b c d e f g h i : Prop}
                    (h₁ : dc h i (dc f g (dc d e (dc a b c)))) 
                    : dc h i (dc f g (dc (dc d e a) (dc d e b) c)) :=
                    have h₂ : dc (dc h i f) (dc h i g) (dc d e (dc a b c)), from dc₆' h₁,
                    have h₃ : dc (dc h i f) (dc h i g) (dc (dc d e a) (dc d e b) c), from dc₆ h₂,
                    show dc h i (dc f g (dc (dc d e a) (dc d e b) c)), from dc₇' h₃

                theorem dc₇_ast {a b c d e f g h i : Prop}
                    (h₁ : dc h i (dc f g (dc (dc d e a) (dc d e b) c))) :
                    dc h i (dc f g (dc d e (dc a b c))) :=
                    have h₂ : dc (dc h i f) (dc h i g) (dc (dc d e a) (dc d e b) c), from dc₆' h₁,
                    have h₃ : dc (dc h i f) (dc h i g) (dc d e (dc a b c)), from dc₇ h₂,
                    show dc h i (dc f g (dc d e (dc a b c))), from dc₇' h₃

            end dc
        end wr
    end hilbert
end clfrags
