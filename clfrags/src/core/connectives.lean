/- Declaration of the connectives for the fragments of Classical Logic
 - as presented by Rautenberg (1981).
 -
 - @author Vitor Greati
 -/
namespace clfrags

    -- ∨
    constant or : Prop → Prop → Prop
    -- ∧
    constant and : Prop → Prop → Prop
    -- ka
    constant ka : Prop → Prop → Prop → Prop
    -- ki
    constant ki : Prop → Prop → Prop → Prop
    -- +₃
    constant pt : Prop → Prop → Prop → Prop
    -- d
    constant dc : Prop → Prop → Prop → Prop
    -- ad
    constant ad : Prop → Prop → Prop → Prop
    -- ¬
    constant neg : Prop → Prop
    -- 1
    constant top : Prop
    -- 0
    constant bot : Prop

end clfrags
