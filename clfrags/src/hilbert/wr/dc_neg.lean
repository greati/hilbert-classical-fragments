import core.connectives

import hilbert.wr.dc

namespace clfrags
    namespace hilbert
        namespace wr
            namespace dc_neg
                axiom dcn₁ : Π {a b c d : Prop}, dc c d (dc b a (neg a)) → dc c d b
                axiom dcn₂ : Π {a b c d : Prop}, dc c d b → dc c d (dc b a (neg a))
            end dc_neg
        end wr
    end hilbert
end clfrags
