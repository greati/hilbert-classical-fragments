import hilbert.wr.and_or
import hilbert.wr.proofs.or

namespace clfrags
    namespace hilbert
        namespace wr
            namespace and_or

                theorem c₁ {a b : Prop} (h₁ : a) (h₂ : b) : and a b :=
                    have h₃ : or (and a b) a, from or.ρ₁' h₁,
                    have h₄ : or (and a b) b, from or.ρ₁' h₂,
                    have h₅ : or (and a b) (and a b), from cd₁ h₃ h₄,
                    show and a b, from or.ρ₂ h₅

                theorem c₂ {a b : Prop} (h₁ : and a b) : a :=
                    have h₂ : or a (and a b), from or.ρ₁' h₁, 
                    have h₃ : or a a, from cd₂ h₂,
                    show a, from or.ρ₂ h₃

                theorem c₃ {a b : Prop} (h₁ : and a b) : b :=
                    have h₂ : or b (and a b), from or.ρ₁' h₁, 
                    have h₃ : or b b, from cd₃ h₂,
                    show b, from or.ρ₂ h₃

            end and_or 
        end wr
    end hilbert
end clfrags
