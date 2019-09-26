/- Declaration of the connectives for the fragments of Classical Logic.
 -
 - @author Vitor Greati
 -/
namespace clfrags

    constant or : Prop → Prop → Prop
    notation a ∨ b := or a b

    constant and : Prop → Prop → Prop
    notation a ∧ b := and a b

    constant ka : Prop → Prop → Prop → Prop

    constant ki : Prop → Prop → Prop → Prop

    constant pt : Prop → Prop → Prop → Prop

    constant dc : Prop → Prop → Prop → Prop

    constant ad : Prop → Prop → Prop → Prop

    constant neg : Prop → Prop

    constant top : Prop

    constant bot : Prop

end clfrags
