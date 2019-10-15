import hilbert.wr.dc_pt

namespace clfrags
    namespace hilbert
        namespace wr
            namespace dc_pt

                theorem dc₁_pt {a b c d e : Prop}  (h₁ : pt d e a) (h₂ : pt d e b) : pt d e (dc a b c) :=
                    have h₃ : dc (pt d e a) (pt d e b) (pt d e c), from dc.dc₁ h₁ h₂,
                    show pt d e (dc a b c), from dcpt₄ h₃

                theorem dc₂_pt {a b c d : Prop} (h₁ : pt c d (dc b a a)) : pt c d a :=
                    dc.dc₂ (dcpt₃ h₁)

                theorem dc₃_pt {a b c d: Prop} (h₁ : pt c d a) : pt c d (dc b a a) :=
                    dcpt₄ (dc.dc₃ h₁)

                theorem dc₄_pt {a b c d e f g : Prop} (h₁ : pt f g (dc d e (dc a b c))) :
                    pt f g (dc e d (dc b a c)) :=
                    have h₂ : dc (pt f g d) (pt f g e) (pt f g (dc a b c)), from dcpt₃ h₁,
                    have h₃ : dc (pt f g d) (pt f g e) (dc (pt f g a) (pt f g b) (pt f g c)), from dcpt₅ h₂,
                    have h₄ : dc (pt f g e) (pt f g d) (dc (pt f g b) (pt f g a) (pt f g c)), from dc.dc₄ h₃,
                    have h₅ : dc (pt f g e) (pt f g d) (pt f g (dc b a c)), from dcpt₆ h₄,
                    show pt f g (dc e d (dc b a c)), from dcpt₄ h₅                    

                theorem dc₅_pt {a b c d e f g : Prop} (h₁ : pt f g (dc d e (dc a b c))) : 
                    pt f g (dc e d (dc a c b)) :=
                    have h₂ : dc (pt f g d) (pt f g e) (pt f g (dc a b c)), from dcpt₃ h₁,
                    have h₃ : dc (pt f g d) (pt f g e) (dc (pt f g a) (pt f g b) (pt f g c)), from dcpt₅ h₂,
                    have h₄ : dc (pt f g e) (pt f g d) (dc (pt f g a) (pt f g c) (pt f g b)), from dc.dc₅ h₃,
                    have h₅ : dc (pt f g e) (pt f g d) (pt f g (dc a c b)), from dcpt₆ h₄,
                    show pt f g (dc e d (dc a c b)), from dcpt₄ h₅                    

                theorem dc₆_pt {a b c d e f g : Prop}
                    (h₁ : pt f g (dc d e (dc a b c))) : pt f g (dc (dc d e a) (dc d e b) c) :=
                    sorry

                theorem dc₇_pt {a b c d e f g : Prop}
                    (h₁ : pt f g (dc (dc d e a) (dc d e b) c)) : pt f g (dc d e (dc a b c)) :=
                    sorry

                theorem dc₆'_pt {a b c d e f g : Prop}
                    (h₁ : pt f g (dc d e (dc a b c))) : pt f g (dc (dc d e a) (dc d e b) c) :=
                    let h := pt f g (dc d e (dc a b c)), i := pt f g (dc (dc d e a) (dc d e b) c) in
                        sorry

                theorem pt₁_dc {a b c d e : Prop} (h₁ : dc d e a) (h₂ : dc d e b) (h₃ : dc d e c) 
                    : dc d e (pt a b c) :=
                    dcpt₂ (pt.pt₁ h₁ h₂ h₃)

                theorem pt₂_dc {a b c d e : Prop} (h₁ : dc d e (pt a b c)) : dc d e (pt b a c) :=
                    dcpt₂ (pt.pt₂ (dcpt₁ h₁))

                theorem pt₃_dc {a b c d e : Prop} (h₁ : dc d e (pt a b c)) : dc d e (pt a c b) :=
                    dcpt₂ (pt.pt₃ (dcpt₁ h₁))

                theorem pt₄_dc {a b c d : Prop} (h₁ : dc c d a) : dc c d (pt a b b) :=
                    dcpt₂ (pt.pt₄ h₁)

                theorem pt₅_dc {a b c d : Prop} (h₁ : dc c d (pt a b b)) : dc c d a :=
                    pt.pt₅ (dcpt₁ h₁)

                theorem pt₆_dc {a b c d e f g : Prop} (h₁ : dc f g (pt a b (pt c d e))) : 
                    dc f g (pt (pt a b c) d e) :=
                    have h₂ : pt (dc f g a) (dc f g b) (dc f g (pt c d e)), from dcpt₁ h₁,
                    have h₃ : pt (dc f g a) (dc f g b) (pt (dc f g c) (dc f g d) (dc f g e)), from dcpt₇ h₂,
                    have h₄ : pt (pt (dc f g a) (dc f g b) (dc f g c)) (dc f g d) (dc f g e), from pt.pt₆ h₃,
                    have h₅ : pt (dc f g d) (dc f g e) (pt (dc f g a) (dc f g b) (dc f g c)), from pt.pt₃ (pt.pt₂ h₄),
                    have h₆ : pt (dc f g d) (dc f g e) (dc f g (pt a b c)), from dcpt₈ h₅,
                    have h₇ : pt (dc f g (pt a b c)) (dc f g d) (dc f g e) , from pt.pt₂ (pt.pt₃ h₆),
                    show dc f g (pt (pt a b c) d e), from dcpt₂ h₇
        

            end dc_pt
        end wr
    end hilbert
end clfrags
