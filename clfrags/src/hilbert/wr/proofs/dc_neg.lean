import hilbert.wr.dc_neg
import hilbert.wr.proofs.dc

namespace clfrags
    namespace hilbert
        namespace wr
            namespace dc_neg

                theorem dcn₁_dc {a b c d e f : Prop} (h₁ : dc e f (dc c d (dc b a (neg a)))) 
                : dc e f (dc c d b) :=
                    have h₂ : dc (dc e f c) (dc e f d) (dc b a (neg a)), from dc.dc₆' h₁,
                    have h₃ : dc (dc e f c) (dc e f d) b, from dcn₁ h₂,
                    show dc e f (dc c d b), from dc.dc₇' h₃

                theorem dcn₂_dc {a b c d e f : Prop} (h₁ : dc e f (dc c d b)) 
                : dc e f (dc c d (dc b a (neg a))) :=
                    have h₂ : dc (dc e f c) (dc e f d) b, from dc.dc₆' h₁,
                    have h₃ : dc (dc e f c) (dc e f d) (dc b a (neg a)), from dcn₂ h₂,
                    show dc e f (dc c d (dc b a (neg a))), from dc.dc₇' h₃

                theorem dcn₃ {a b : Prop} (h₁ : a) (h₂ : neg a) : b :=
                    have h₂ : dc a (neg a) b, from dc.dc₁ h₁ h₂,
                    have h₃ : dc (dc a (neg a) b) a b, from dc.dc₁ h₂ h₁,
                    have h₄ : dc a b (dc a (neg a) b), from dc.dc₅' (dc.dc₄' h₃),
                    have h₅ : dc a b (dc b a (neg a)), from dc.dc₄ (dc.dc₅ h₄),
                    have h₆ : dc a b b, from dcn₁ h₅,
                    show b, from dc.dc₂ h₆
            
                theorem dcn₄ {a b : Prop} (h₁ : b) : dc b a (neg a) :=
                    have h₂ : dc a b b, from dc.dc₃ h₁,
                    have h₃ : dc a b (dc b a (neg a)), from dcn₂ h₂,
                    have h₄ : dc (dc a b b) (dc a b a) (neg a), from dc.dc₆' h₃,
                    have h₅ : dc (neg a) (dc a b b) (dc a b a), from dc.dc₄' (dc.dc₅' h₄),
                    have h₆ : dc (neg a) (dc a b b) (dc b a a), from dc.dc₅ (dc.dc₄ h₅),
                    have h₇ : dc (neg a) (dc a b b) a, from dc.dc₂_dc h₆,
                    have h₈ : dc (neg a) a (dc a b b), from dc.dc₅' h₇,
                    have h₉ : dc (neg a) a b, from dc.dc₂_dc h₈,
                    show dc b a (neg a), from dc.dc₅' (dc.dc₄' (dc.dc₅' h₉))

            end dc_neg 
        end wr
    end hilbert
end clfrags
