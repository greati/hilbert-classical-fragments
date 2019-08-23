import hilbert.wr.ki

namespace clfrags
    namespace hilbert
        namespace wr
            namespace ki

                theorem ka₁₀ {a b c : Prop} (h₁ : a) (h₂ : c) : ki a b c :=
                    sorry

                theorem ka'₃ {a b c d : Prop} (h₁ : a) :  
                    ki a (ki a b (ki a c d)) (ki a (ki a b c) (ki a b d)) :=
                    sorry

                theorem ka'₄ {a b c d : Prop} (h₁ : a) :  
                    ki a (ki a c b) c :=
                    sorry

                theorem ka₀ {a b c : Prop} (h₁ : ki a b c) : a :=
                    sorry
            
                theorem ka₁₁ {a b : Prop} (h₁ : a) : ki a b b :=
                    sorry

                theorem ka₁₂ {a b c d : Prop} (h₁ : ki a b (ki a c d)) : ki a c (ki a b d) :=
                    sorry

                theorem ka₁₃ {a b c : Prop} (h₁ : ki a b (ki a b c)) : ki a b c :=
                    sorry

                theorem ka₁₄ {a b c d : Prop} (h₁ : ki a b d) : ki b b (ki a c d) :=
                    sorry

                theorem ka₁₅ {a b c d : Prop} (h₁ : ki a b d) : ki c c (ki a b d) :=
                    sorry

                theorem ka₁₆ {a b c d : Prop} (h₁ : ki a b c) (h₂ : ki a c d) : 
                    ki a b d :=
                    sorry

            end ki
        end wr
    end hilbert
end clfrags
