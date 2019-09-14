import hilbert.wr.dc_neg
import hilbert.wr.proofs.dc

namespace clfrags
    namespace hilbert
        namespace wr
            namespace dc_neg

                theorem dcn₁_ast {a b c d e f : Prop} (h₁ : dc e f (dc c d (dc b a (neg a)))) 
                : dc e f (dc c d b) :=
                    have h₂ : dc (dc e f c) (dc e f d) (dc b a (neg a)), from dc.dc₆' h₁,
                    have h₃ : dc (dc e f c) (dc e f d) b, from dcn₁ h₂,
                    show dc e f (dc c d b), from dc.dc₇' h₃

                theorem dcn₂_ast {a b c d e f : Prop} (h₁ : dc e f (dc c d b)) 
                : dc e f (dc c d (dc b a (neg a))) :=
                    have h₂ : dc (dc e f c) (dc e f d) b, from dc.dc₆' h₁,
                    have h₃ : dc (dc e f c) (dc e f d) (dc b a (neg a)), from dcn₂ h₂,
                    show dc e f (dc c d (dc b a (neg a))), from dc.dc₇' h₃

            end dc_neg 
        end wr
    end hilbert
end clfrags
