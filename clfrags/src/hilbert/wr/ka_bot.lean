import core.connectives

import hilbert.wr.ka

namespace clfrags
    namespace hilbert
        namespace wr
            namespace ka_bot
                axiom kab₁ : Π {a b c : Prop}, ka b a bot → ka b a c
            end ka_bot
        end wr
    end hilbert
end clfrags
