import wr_connectives

namespace clfrags

    axiom wr_or_1 : Pi {p q : Prop}, p -> wr_or p q
    axiom wr_or_2 : Pi {p : Prop}, wr_or p p -> p
    axiom wr_or_3 : Pi {p q : Prop}, wr_or p q -> wr_or q p
    axiom wr_or_4 : Pi {p q r : Prop}, wr_or r (wr_or p q) -> wr_or (wr_or r p) q

    #check(wr_or_1)
    #check(wr_or_2)
    #check(wr_or_3)
    #check(wr_or_4)

end clfrags
