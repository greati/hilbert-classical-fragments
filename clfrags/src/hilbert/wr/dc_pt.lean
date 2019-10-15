import core.connectives

import hilbert.wr.pt
import hilbert.wr.proofs.pt
import hilbert.wr.dc
import hilbert.wr.proofs.dc

namespace clfrags
    namespace hilbert
        namespace wr
            namespace dc_pt
                axiom dcpt₁ : Π {a b c d e : Prop}, dc a b (pt c d e) → pt (dc a b c) (dc a b d) (dc a b e)
                axiom dcpt₂ : Π {a b c d e : Prop}, pt (dc a b c) (dc a b d) (dc a b e) → dc a b (pt c d e)
                axiom dcpt₃ : Π {a b c d e : Prop}, pt a b (dc c d e) → dc (pt a b c) (pt a b d) (pt a b e)
                axiom dcpt₄ : Π {a b c d e : Prop}, dc (pt a b c) (pt a b d) (pt a b e) → pt a b (dc c d e) 

                -- needed in dc₄_pt dc₅_pt dc₆_pt dc₇_pt
                -- dcpt₃_dc
                axiom dcpt₅ : Π {a b c d e f g : Prop}, dc f g (pt a b (dc c d e)) → 
                    dc f g (dc (pt a b c) (pt a b d) (pt a b e))
                -- dcpt₄_dc
                axiom dcpt₆ : Π {a b c d e f g : Prop}, dc f g (dc (pt a b c) (pt a b d) (pt a b e)) → 
                    dc f g (pt a b (dc c d e)) 

                -- needed in pt₆_dc
                -- dcpt₁_pt
                axiom dcpt₇ : Π {a b c d e f g : Prop}, pt f g (dc a b (pt c d e)) → 
                    pt f g (pt (dc a b c) (dc a b d) (dc a b e))
                -- dcpt₂_pt
                axiom dcpt₈ : Π {a b c d e f g : Prop}, pt f g (pt (dc a b c) (dc a b d) (dc a b e)) → 
                    pt f g (dc a b (pt c d e))

            end dc_pt
        end wr
    end hilbert
end clfrags
