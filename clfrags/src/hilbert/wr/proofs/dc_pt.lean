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

                theorem dcpt₅_dc {a b c d e f g h i : Prop} (h₁ : dc h i (dc f g (pt a b (dc c d e)))) :
                    dc h i (dc f g (dc (pt a b c) (pt a b d) (pt a b e))) :=
                    dc.dc₇' (dcpt₅ (dc.dc₆' h₁))
                
                theorem dcpt₆_dc {a b c d e f g h i : Prop} (h₁ : dc h i (dc f g (dc (pt a b c) (pt a b d) (pt a b e)))) :
                    dc h i (dc f g (pt a b (dc c d e))) :=
                    dc.dc₇' (dcpt₆ (dc.dc₆' h₁))
        
                theorem dc₆_pt {a b c d e f g h i : Prop}
                    (h₁ : pt h i (dc f g (dc d e (dc a b c)))) : pt h i (dc f g (dc (dc d e a) (dc d e b) c)) :=
                    let f' := pt h i f, g' := pt h i g, d' := pt h i d, e' := pt h i e in
                        have h₂ : dc f' g' (pt h i (dc d e (dc a b c))), 
                            from dcpt₃ h₁,
                        have h₃ : dc f' g' (dc d' e' (pt h i (dc a b c))), 
                            from dcpt₅ h₂,
                        have h₄ : dc (dc f' g' d') (dc f' g' e') ((pt h i (dc a b c))), 
                            from dc.dc₆' h₃,
                        have h₅ : dc (dc f' g' d') (dc f' g' e') (dc (pt h i a) (pt h i b) (pt h i c)), 
                            from dcpt₅ h₄,
                        have h₆ : dc f' g' (dc d' e' (dc (pt h i a) (pt h i b) (pt h i c))),
                            from dc.dc₇' h₅,
                        have h₇ : dc f' g' (dc (dc d' e' (pt h i a)) (dc d' e' (pt h i b)) (pt h i c)),
                            from dc.dc₆ h₆,
                        have h₈ : dc g' f' (dc (dc d' e' (pt h i a)) (pt h i c) (dc d' e' (pt h i b))),
                            from dc.dc₅ h₇,
                        have h₉ : dc g' f' (dc (dc d' e' (pt h i a)) (pt h i c) (pt h i (dc d e b))), 
                            from dcpt₆_dc h₈,
                        have h₁₀ : dc g' f' (dc (pt h i c) (pt h i (dc d e b)) (dc d' e' (pt h i a))), 
                            from dc.dc₅ (dc.dc₄ h₉),
                        have h₁₁ : dc g' f' (dc (pt h i c) (pt h i (dc d e b)) (pt h i (dc d e a))), 
                            from dcpt₆_dc h₁₀,
                        have h₁₂ : dc f' g' (dc (pt h i (dc d e a)) (pt h i (dc d e b)) (pt h i c)), 
                            from dc.dc₅ (dc.dc₄ (dc.dc₅ h₁₁)),
                        have h₁₃ : dc f' g' (pt h i (dc (dc d e a) (dc d e b) c)), 
                            from dcpt₆ h₁₂,
                        show pt h i (dc f g (dc (dc d e a) (dc d e b) c)), 
                            from dcpt₄ h₁₃

                theorem dc₇_pt {a b c d e f g h i: Prop}
                    (h₁ : pt h i (dc f g (dc (dc d e a) (dc d e b) c))) : pt h i (dc f g (dc d e (dc a b c))) :=
                    let f' := pt h i f, g' := pt h i g, d' := pt h i d, e' := pt h i e in
                        have h₂ : dc f' g' (pt h i (dc (dc d e a) (dc d e b) c)), 
                            from dcpt₃ h₁,
                        have h₃ : dc f' g' (dc (pt h i (dc d e a)) (pt h i (dc d e b)) (pt h i c)), 
                            from dcpt₅ h₂,
                        have h₄ : dc g' f' (dc (pt h i (dc d e a)) (pt h i c) (pt h i (dc d e b))), 
                            from dc.dc₅ h₃,
                        have h₅ : dc g' f' (dc (pt h i (dc d e a)) (pt h i c) (dc d' e' (pt h i b))), 
                            from dcpt₅_dc h₄,
                        have h₆ : dc g' f' (dc (pt h i c) (dc d' e' (pt h i b)) (pt h i (dc d e a))), 
                            from dc.dc₅ (dc.dc₄ h₅),
                        have h₇ : dc g' f' (dc (pt h i c) (dc d' e' (pt h i b)) (dc d' e' (pt h i a))), 
                            from dcpt₅_dc h₆,
                        have h₈ : dc f' g' (dc (dc d' e' (pt h i a)) (dc d' e' (pt h i b)) (pt h i c)), 
                            from dc.dc₅ (dc.dc₄ (dc.dc₅ h₇)),
                        have h₉ : dc f' g' (dc d' e' (dc (pt h i a) (pt h i b) (pt h i c))),
                            from dc.dc₇ h₈,
                        have h₁₀ : dc f' g' (dc d' e' (pt h i (dc a b c))),
                            from dcpt₆_dc h₉,
                        have h₁₁ : dc f' g' (pt h i (dc d e (dc a b c))),
                            from dcpt₆ h₁₀,
                        show pt h i (dc f g (dc d e (dc a b c))), 
                            from dcpt₄ h₁₁

                theorem dc₄'_pt {a b c d e : Prop} (h₁ : pt d e (dc a b c)) : pt d e (dc b a c) :=
                    have h₂ : pt d e (dc (dc b a c) (dc a b c) (dc a b c)), from dc₃_pt h₁,
                    have h₃ : pt d e (dc (dc a b c) (dc b a c) (dc b a c)), from dc₄_pt h₂,
                    show pt d e (dc b a c), from dc₂_pt h₃

                theorem dc₅'_pt {a b c d e : Prop} (h₁ : pt d e (dc a b c)) : pt d e (dc a c b) :=
                    have h₂ : pt d e (dc (dc a c b) (dc a b c) (dc a b c)), from dc₃_pt h₁,
                    have h₃ : pt d e (dc (dc a b c) (dc a c b) (dc a c b)), from dc₅_pt h₂,
                    show pt d e (dc a c b), from dc₂_pt h₃

                theorem dc₆'_pt {a b c d e f g : Prop}
                   (h₁ : pt f g (dc d e (dc a b c))) : pt f g (dc (dc d e a) (dc d e b) c) :=
                   let h := dc d e (dc a b c), i := dc (dc d e a) (dc d e b) c in
                       have h₂ : pt f g (dc i h h), from dc₃_pt h₁,
                       have h₃ : pt f g (dc i h i), from dc₆_pt h₂,
                       have h₄ : pt f g (dc h i i), from dc₄'_pt h₃,
                       show pt f g i, from dc₂_pt h₄

                theorem dc₇'_pt {a b c d e f g : Prop}
                    (h₁ : pt f g (dc (dc d e a) (dc d e b) c)) : pt f g (dc d e (dc a b c)) :=
                    let h := dc d e (dc a b c), i := dc (dc d e a) (dc d e b) c in
                        have h₂ : pt f g (dc h i i), from dc₃_pt h₁,
                        have h₃ : pt f g (dc h i h), from dc₇_pt h₂,
                        have h₄ : pt f g (dc i h h), from dc₄'_pt h₃,
                        show pt f g h, from dc₂_pt h₄

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

                theorem dcpt₁_dc {a b c d e f g : Prop} (h₁ : dc f g (dc a b (pt c d e))) : 
                    dc f g (pt (dc a b c) (dc a b d) (dc a b e)) :=
                    let a' := dc f g a, b' := dc f g b, d' := dc a b d, e' := dc a b e in
                        have h₁ : dc a' b' (pt c d e), 
                            from dc.dc₆' h₁,
                        have h₂ : pt (dc a' b' c) (dc a' b' d) (dc a' b' e), 
                            from dcpt₁ h₁,
                        have h₃ : pt (dc a' b' c) (dc a' b' d) (dc f g e'), 
                            from dc₇'_pt h₂,
                        have h₄ : pt (dc a' b' c) (dc f g e') (dc a' b' d), 
                            from pt.pt₃ h₃,
                        have h₅ : pt (dc a' b' c) (dc f g e') (dc f g d'), 
                            from dc₇'_pt h₄,
                        have h₆ : pt (dc f g e') (dc f g d') (dc a' b' c), 
                            from pt.pt₃ (pt.pt₂ h₅),
                        have h₇ : pt (dc f g e') (dc f g d') (dc f g (dc a b c)), 
                            from dc₇'_pt h₆,
                        have h₈ : pt (dc f g (dc a b c)) (dc f g d') (dc f g e'), 
                            from pt.pt₂ (pt.pt₃ (pt.pt₂ h₇)),
                        show dc f g (pt (dc a b c) d' e'), 
                            from dcpt₂ h₈

                theorem dcpt₂_dc {a b c d e f g : Prop} (h₁ : dc f g (pt (dc a b c) (dc a b d) (dc a b e))) : 
                    dc f g (dc a b (pt c d e)) :=
                    let a' := dc f g a, b' := dc f g b, d' := dc a b d, e' := dc a b e in
                        have h₂ : pt (dc f g (dc a b c)) (dc f g d') (dc f g e'), 
                            from dcpt₁ h₁,
                        have h₃ : pt (dc f g (dc a b c)) (dc f g d') (dc a' b' e), 
                            from dc₆'_pt h₂,
                        have h₄ : pt (dc f g (dc a b c)) (dc a' b' e) (dc f g d'), 
                            from pt.pt₃ h₃,
                        have h₅ : pt (dc f g (dc a b c)) (dc a' b' e) (dc a' b' d), 
                            from dc₆'_pt h₄,
                        have h₆ : pt (dc a' b' e) (dc a' b' d) (dc f g (dc a b c)), 
                            from pt.pt₃ (pt.pt₂ h₅),
                        have h₇ : pt (dc a' b' e) (dc a' b' d) (dc a' b' c), 
                            from dc₆'_pt h₆,
                        have h₈ : pt (dc a' b' c) (dc a' b' d) (dc a' b' e), 
                            from pt.pt₂ (pt.pt₃ (pt.pt₂ h₇)),
                        have h₉ : dc a' b' (pt c d e), 
                            from dcpt₂ h₈,
                        show dc f g (dc a b (pt c d e)), 
                            from dc.dc₇' h₉

                theorem dcpt₃_dc {a b c d e f g : Prop} (h₁ : dc f g (pt a b (dc c d e))) :
                    dc f g (dc (pt a b c) (pt a b d) (pt a b e)) := dcpt₅ h₁

                theorem dcpt₄_dc {a b c d e f g : Prop} (h₁ : dc f g (dc (pt a b c) (pt a b d) (pt a b e))) : 
                    dc f g (pt a b (dc c d e)) := dcpt₆ h₁

                -- dcpt₅_dc : done above

                -- dcpt₆_dc : done above

                theorem dcpt₇_dc {a b c d e f g h i : Prop} (h₁ : dc h i (pt f g (dc a b (pt c d e)))) : 
                    dc h i (pt f g (pt (dc a b c) (dc a b d) (dc a b e))) :=
                    let f' := dc h i f, g' := dc h i g, a' := dc h i a, b' := dc h i b in
                        have h₂ : pt f' g' (dc h i (dc a b (pt c d e))), from dcpt₁ h₁,
                        have h₃ : pt f' g' (dc a' b' (pt c d e)), from dc₆'_pt h₂,
                        have h₄ : pt f' g' (pt (dc a' b' c) (dc a' b' d) (dc a' b' e)), 
                            from dcpt₇ h₃,
                        have h₅ : pt (pt f' g' (dc a' b' c)) (dc a' b' d) (dc a' b' e), 
                            from pt.pt₆ h₄,
                        have h₆ : pt (pt f' g' (dc a' b' c)) (dc a' b' d) (dc h i (dc a b e)), 
                            from dc₇'_pt h₅,
                        have h₇ : pt (pt f' g' (dc a' b' c)) (dc h i (dc a b e)) (dc a' b' d), 
                            from pt.pt₃ h₆,
                        have h₈ : pt (pt f' g' (dc a' b' c)) (dc h i (dc a b e)) (dc h i (dc a b d)), 
                            from dc₇'_pt h₇,
                        have h₉ : pt f' g' (pt (dc a' b' c) (dc h i (dc a b e)) (dc h i (dc a b d))), 
                            from pt.pt₇ h₈,
                        have h₁₀ : pt f' g' (pt (dc h i (dc a b e)) (dc h i (dc a b d)) (dc a' b' c)), 
                            from pt.pt₃_pt (pt.pt₂_pt h₉),
                        have h₁₁ : pt (pt f' g' (dc h i (dc a b e))) (dc h i (dc a b d)) (dc a' b' c), 
                            from pt.pt₆ h₁₀,
                        have h₁₂ : pt (pt f' g' (dc h i (dc a b e))) (dc h i (dc a b d)) (dc h i (dc a b c)), 
                            from dc₇'_pt h₁₁,
                        have h₁₃ : pt f' g' (pt (dc h i (dc a b e)) (dc h i (dc a b d)) (dc h i (dc a b c))), 
                            from pt.pt₇ h₁₂,
                        have h₁₄ : pt f' g' (pt (dc h i (dc a b c)) (dc h i (dc a b d)) (dc h i (dc a b e))), 
                            from pt.pt₂_pt (pt.pt₃_pt (pt.pt₂_pt h₁₃)),
                        have h₁₅ : pt f' g' (dc h i (pt (dc a b c) (dc a b d) (dc a b e))), 
                            from dcpt₈ h₁₄,
                        show dc h i (pt f g (pt (dc a b c) (dc a b d) (dc a b e))), 
                            from dcpt₂ h₁₅

                theorem dcpt₈_dc {a b c d e f g h i : Prop} (h₁ : dc h i (pt f g (pt (dc a b c) (dc a b d) (dc a b e)))) : 
                    dc h i (pt f g (dc a b (pt c d e))) :=
                    let f' := dc h i f, g' := dc h i g, a' := dc h i a, b' := dc h i b in
                        have h₂ : pt f' g' (dc h i (pt (dc a b c) (dc a b d) (dc a b e))), 
                            from dcpt₁ h₁,
                        have h₃ : pt f' g' (pt (dc h i (dc a b c)) (dc h i (dc a b d)) (dc h i (dc a b e))), 
                            from dcpt₇ h₂,
                        have h₄ : pt (pt f' g' (dc h i (dc a b c))) (dc h i (dc a b d)) (dc h i (dc a b e)), 
                            from pt.pt₆ h₃,
                        have h₅ : pt (pt f' g' (dc h i (dc a b c))) (dc h i (dc a b d)) (dc a' b' e), 
                            from dc₆'_pt h₄,
                        have h₆ : pt (pt f' g' (dc h i (dc a b c))) (dc a' b' e) (dc h i (dc a b d)), 
                            from pt.pt₃ h₅,
                        have h₇ : pt (pt f' g' (dc h i (dc a b c))) (dc a' b' e) (dc a' b' d), 
                            from dc₆'_pt h₆,
                        have h₈ : pt f' g' (pt (dc h i (dc a b c)) (dc a' b' e) (dc a' b' d)), 
                            from pt.pt₇ h₇,
                        have h₉ : pt f' g' (pt (dc a' b' e) (dc a' b' d) (dc h i (dc a b c))), 
                            from pt.pt₃_pt (pt.pt₂_pt h₈),
                        have h₁₀ : pt (pt f' g' (dc a' b' e)) (dc a' b' d) (dc h i (dc a b c)), 
                            from pt.pt₆ h₉,
                        have h₁₁ : pt (pt f' g' (dc a' b' e)) (dc a' b' d) (dc a' b' c), 
                            from dc₆'_pt h₁₀,
                        have h₁₂ : pt f' g' (pt (dc a' b' e) (dc a' b' d) (dc a' b' c)), 
                            from pt.pt₇ h₁₁,
                        have h₁₃ : pt f' g' (pt (dc a' b' c) (dc a' b' d) (dc a' b' e)), 
                            from pt.pt₂_pt (pt.pt₃_pt (pt.pt₂_pt h₁₂)),
                        have h₁₄ : pt f' g' (dc a' b' (pt c d e)), 
                            from dcpt₈ h₁₃,
                        have h₁₅ : pt f' g' (dc h i (dc a b (pt c d e))), 
                            from dc₇'_pt h₁₄,
                        show dc h i (pt f g (dc a b (pt c d e))), 
                            from dcpt₂ h₁₅

                theorem pt₇_dc {a b c d e f g : Prop} (h₁ : dc f g (pt (pt a b c) d e)) : dc f g (pt a b (pt c d e)) :=
                    have h₂ : dc f g (pt d (pt a b c) e), from pt₂_dc h₁,
                    have h₃ : dc f g (pt d e (pt a b c)), from pt₃_dc h₂,
                    have h₄ : dc f g (pt (pt d e a) b c), from pt₆_dc h₃,
                    have h₅ : dc f g (pt b (pt d e a) c), from pt₂_dc h₄,
                    have h₆ : dc f g (pt b c (pt d e a)), from pt₃_dc h₅,
                    have h₇ : dc f g (pt (pt b c d) e a), from pt₆_dc h₆,
                    have h₈ : dc f g (pt e (pt b c d) a), from pt₂_dc h₇,
                    have h₉ : dc f g (pt e a (pt b c d)), from pt₃_dc h₈,
                    have h₁₀ : dc f g (pt (pt e a b) c d), from pt₆_dc h₉,
                    have h₁₁ : dc f g (pt c (pt e a b) d), from pt₂_dc h₁₀,
                    have h₁₂ : dc f g (pt c d (pt e a b)), from pt₃_dc h₁₁,
                    have h₁₃ : dc f g (pt (pt c d e) a b), from pt₆_dc h₁₂,
                    have h₁₄ : dc f g (pt a (pt c d e) b), from pt₂_dc h₁₃,
                    show dc f g (pt a b (pt c d e)), from pt₃_dc h₁₄

                theorem dcpt₁_pt {a b c d e f g : Prop} (h₁ : pt f g (dc a b (pt c d e))) : 
                    pt f g (pt (dc a b c) (dc a b d) (dc a b e)) := dcpt₇ h₁

                theorem dcpt₂_pt {a b c d e f g : Prop} (h₁ : pt f g (pt (dc a b c) (dc a b d) (dc a b e))) : 
                    pt f g (dc a b (pt c d e)) := dcpt₈ h₁

                theorem dcpt₃_pt {a b c d e f g : Prop} (h₁ : pt f g (pt a b (dc c d e))) :
                    pt f g (dc (pt a b c) (pt a b d) (pt a b e)) := 
                    let a' := pt f g a, c' := pt a b c, d' := pt a b d, e' := pt a b e in
                        have h₂ : pt a' b (dc c d e), from pt.pt₆ h₁,
                        have h₃ : dc (pt a' b c) (pt a' b d) (pt a' b e), from dcpt₃ h₂,
                        have h₄ : dc (pt a' b c) (pt a' b d) (pt f g e'), from pt₇_dc h₃,
                        have h₅ : dc (pt a' b c) (pt f g e') (pt a' b d), from dc.dc₅' h₄,
                        have h₆ : dc (pt a' b c) (pt f g e') (pt f g d'), from pt₇_dc h₅,
                        have h₇ : dc (pt f g e') (pt f g d') (pt a' b c), from dc.dc₅' (dc.dc₄' h₆),
                        have h₈ : dc (pt f g e') (pt f g d') (pt f g c'), from pt₇_dc h₇,
                        have h₉ : dc (pt f g c') (pt f g d') (pt f g e'), from dc.dc₄' (dc.dc₅' (dc.dc₄' h₈)),
                        show pt f g (dc c' d' e'), from dcpt₄ h₉

                theorem dcpt₄_pt {a b c d e f g : Prop} (h₁ : pt f g (dc (pt a b c) (pt a b d) (pt a b e))) : 
                    pt f g (pt a b (dc c d e)) :=
                    let a' := pt f g a, c' := pt a b c, d' := pt a b d, e' := pt a b e in
                        have h₂ : dc (pt f g c') (pt f g (pt a b d)) (pt f g e'), from dcpt₃ h₁, 
                        have h₃ : dc (pt f g c') (pt f g (pt a b d)) (pt a' b e), from pt₆_dc h₂, 
                        have h₄ : dc (pt f g c') (pt a' b e) (pt f g (pt a b d)), from dc.dc₅' h₃, 
                        have h₅ : dc (pt f g c') (pt a' b e) (pt a' b d), from pt₆_dc h₄, 
                        have h₆ : dc (pt a' b e) (pt a' b d) (pt f g c'), from dc.dc₅' (dc.dc₄' h₅), 
                        have h₇ : dc (pt a' b e) (pt a' b d) (pt a' b c), from pt₆_dc h₆, 
                        have h₈ : dc (pt a' b c) (pt a' b d) (pt a' b e), from dc.dc₄' (dc.dc₅' (dc.dc₄' h₇)), 
                        have h₉ : pt a' b (dc c d e), from dcpt₄ h₈,
                        show pt f g (pt a b (dc c d e)), from pt.pt₇ h₉

                theorem dcpt₅_pt {a b c d e f g h i : Prop} (h₁ : pt h i (dc f g (pt a b (dc c d e)))) :
                    pt h i (dc f g (dc (pt a b c) (pt a b d) (pt a b e))) :=
                    let f' := pt h i f, g' := pt h i g, a' := pt h i a, d' := pt a b d, e' := pt a b e in
                        have h₂ : dc f' g' (pt h i (pt a b (dc c d e))), 
                            from dcpt₃ h₁,
                        have h₃ : dc f' g' (pt a' b (dc c d e)), 
                            from pt₆_dc h₂,
                        have h₄ : dc f' g' (dc (pt a' b c) (pt a' b d) (pt a' b e)), 
                            from dcpt₅ h₃,
                        have h₅ : dc (dc f' g' (pt a' b c)) (dc f' g' (pt a' b d)) (pt a' b e), 
                            from dc.dc₆' h₄,
                        have h₆ : dc (dc f' g' (pt a' b c)) (dc f' g' (pt a' b d)) (pt h i e'), 
                            from pt₇_dc h₅,
                        have h₇ : dc f' g' (dc (pt a' b c) (pt a' b d) (pt h i e')), 
                            from dc.dc₇' h₆,
                        have h₈ : dc g' f' (dc (pt a' b c) (pt h i e') (pt a' b d)), 
                            from dc.dc₅ h₇,
                        have h₉ : dc (dc g' f' (pt a' b c)) (dc g' f' (pt h i e')) (pt a' b d), 
                            from dc.dc₆' h₈,
                        have h₁₀ : dc (dc g' f' (pt a' b c)) (dc g' f' (pt h i e')) (pt h i d'), 
                            from pt₇_dc h₉,
                        have h₁₁ : dc g' f' (dc (pt a' b c) (pt h i e') (pt h i d')),
                            from dc.dc₇' h₁₀,
                        have h₁₂ : dc g' f' (dc (pt h i e') (pt h i d') (pt a' b c)),
                            from dc.dc₅ (dc.dc₄ h₁₁),
                        have h₁₃ : dc (dc g' f' (pt h i e')) (dc g' f' (pt h i d')) (pt a' b c),
                            from dc.dc₆' h₁₂,
                        have h₁₄ : dc (dc g' f' (pt h i e')) (dc g' f' (pt h i d')) (pt h i (pt a b c)),
                            from pt₇_dc h₁₃,
                        have h₁₅ : dc g' f' (dc (pt h i e') (pt h i d') (pt h i (pt a b c))),
                            from dc.dc₇' h₁₄,
                        have h₁₆ : dc f' g' (dc (pt h i (pt a b c)) (pt h i d') (pt h i e')),
                            from dc.dc₄ (dc.dc₅ (dc.dc₄ h₁₅)),
                        have h₁₇ : dc f' g' (pt h i (dc (pt a b c) d' e')),
                            from dcpt₆ h₁₆,
                        show pt h i (dc f g (dc (pt a b c) d' e')), 
                            from dcpt₄ h₁₇
                
                theorem dcpt₆_pt {a b c d e f g h i : Prop} (h₁ : pt h i (dc f g (dc (pt a b c) (pt a b d) (pt a b e)))) :
                    pt h i (dc f g (pt a b (dc c d e))) :=
                    let f' := pt h i f, g' := pt h i g, a' := pt h i a, d' := pt a b d, e' := pt a b e in
                        have h₂ : dc f' g' (pt h i (dc (pt a b c) d' e')), 
                            from dcpt₃ h₁,
                        have h₃ : dc f' g' (dc (pt h i (pt a b c)) (pt h i d') (pt h i e')),
                            from dcpt₅ h₂,
                        have h₄ : dc g' f' (dc (pt h i e') (pt h i d') (pt h i (pt a b c))),
                            from dc.dc₄ (dc.dc₅ (dc.dc₄ h₃)),
                        have h₅ : dc (dc g' f' (pt h i e')) (dc g' f' (pt h i d')) (pt h i (pt a b c)),
                            from dc.dc₆' h₄,
                        have h₆ : dc (dc g' f' (pt h i e')) (dc g' f' (pt h i d')) (pt a' b c),
                            from pt₆_dc h₅,
                        have h₇ : dc g' f' (dc (pt h i e') (pt h i d') (pt a' b c)),
                            from dc.dc₇' h₆,
                        have h₈ : dc g' f' (dc (pt a' b c) (pt h i e') (pt h i d')),
                            from dc.dc₄ (dc.dc₅ h₇),
                        have h₉ : dc (dc g' f' (pt a' b c)) (dc g' f' (pt h i e')) (pt h i d'), 
                            from dc.dc₆' h₈,
                        have h₁₀ : dc (dc g' f' (pt a' b c)) (dc g' f' (pt h i e')) (pt a' b d), 
                            from pt₆_dc h₉,
                        have h₁₁ : dc g' f' (dc (pt a' b c) (pt h i e') (pt a' b d)), 
                            from dc.dc₇' h₁₀,
                        have h₁₂ : dc f' g' (dc (pt a' b c) (pt a' b d) (pt h i e')), 
                            from dc.dc₅ h₁₁,
                        have h₁₃ : dc (dc f' g' (pt a' b c)) (dc f' g' (pt a' b d)) (pt h i e'),
                            from dc.dc₆' h₁₂,
                        have h₁₄ : dc (dc f' g' (pt a' b c)) (dc f' g' (pt a' b d)) (pt a' b e),
                            from pt₆_dc h₁₃,
                        have h₁₅ : dc f' g' (dc (pt a' b c) (pt a' b d) (pt a' b e)), 
                            from dc.dc₇' h₁₄,
                        have h₁₆ : dc f' g' (pt a' b (dc c d e)),
                            from dcpt₆ h₁₅,
                        have h₁₇ : dc f' g' (pt h i (pt a b (dc c d e))), 
                            from pt₇_dc h₁₆,
                        show pt h i (dc f g (pt a b (dc c d e))), 
                            from dcpt₄ h₁₇

                theorem dcpt₇_pt {a b c d e f g h i : Prop} (h₁ : pt h i (pt f g (dc a b (pt c d e)))) : 
                    pt h i (pt f g (pt (dc a b c) (dc a b d) (dc a b e))) :=
                    have h₂ : pt (pt h i f) g (dc a b (pt c d e)), from pt.pt₆ h₁,
                    have h₃ : pt (pt h i f) g (pt (dc a b c) (dc a b d) (dc a b e)), from dcpt₇ h₂,
                    show pt h i (pt f g (pt (dc a b c) (dc a b d) (dc a b e))), from pt.pt₇ h₃

                theorem dcpt₈_pt {a b c d e f g h i : Prop} (h₁ : pt h i (pt f g (pt (dc a b c) (dc a b d) (dc a b e)))) : 
                    pt h i (pt f g (dc a b (pt c d e))) :=
                    have h₂ : pt (pt h i f) g (pt (dc a b c) (dc a b d) (dc a b e)), from pt.pt₆ h₁,
                    have h₃ : pt (pt h i f) g (dc a b (pt c d e)), from dcpt₈ h₂,
                    show pt h i (pt f g (dc a b (pt c d e))), from pt.pt₇ h₃

            end dc_pt
        end wr
    end hilbert
end clfrags
