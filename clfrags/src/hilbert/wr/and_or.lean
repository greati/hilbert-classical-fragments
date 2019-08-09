import core.connectives

import hilbert.wr.or

namespace clfrags
    namespace hilbert
        namespace wr
            namespace and_or
                axiom cd₁ : Π {a b c : Prop}, or c a → or c b → or c (and a b)
                axiom cd₂ : Π {a b c : Prop}, or c (and a b) → or c a
                axiom cd₃ : Π {a b c : Prop}, or c (and a b) → or c b
            end and_or 
        end wr
    end hilbert
end clfrags
