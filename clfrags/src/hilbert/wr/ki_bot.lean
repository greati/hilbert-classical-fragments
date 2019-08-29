import core.connectives

import hilbert.wr.ki

namespace clfrags
    namespace hilbert
        namespace wr
            namespace ki_bot
                axiom kib₁ : Π {a b c : Prop}, ki b a bot → ki b a c
            end ki_bot
        end wr
    end hilbert
end clfrags
